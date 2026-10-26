#!/usr/bin/env python3
"""Compare the human-written gold spec with the verified (Claude-written) spec of the same crate.

For each public function that both specs cover, the script generates Verus obligations from the
two spec files and runs Verus on them in a scratch copy of the crate.

  Claude => gold  Does the verified contract give everything the gold contract asks for?
                  A wrapper with the gold contract calls the verified function, so Verus checks
                  gold_pre ==> claude_pre (at the call) and
                  gold_pre && claude_post ==> gold_post (the wrapper's ensures).
  gold => Claude  Does the gold contract give everything the verified contract promises?
                  A wrapper with Claude's contract calls a stand-in that has the gold contract
                  (inherent functions only; trait methods inherit their specs from vstd).

Conventions applied to the gold spec (each one is listed in the report):
  * the gold `View` impls become a `GoldView` trait (`x@` -> `x.gv()`), because the crate has its
    own `View` for `Slab`;
  * `x@.valid()` on a slab is read as the gold invariant `slab_rep_ok` (--invariant);
  * the gold file's `broadcast axiom`s are in force;
  * an obligation whose gold contract mentions capacity is also checked with capacity removed,
    so that "differs only in capacity" is reported separately (Claude's spec never mentions it).

Proofs go in a separate file (--proofs): lemmas (`proof fn`) and `proof { }` hint blocks, each
after a marker `// @hint <obligation> before|after`. The obligations themselves are generated
from the spec files on every run, so proofs cannot change what is proved; the proofs file may
not contain assume, admit, external_body, axioms or other trusted constructs.

Usage (from verus/):  python3 compare_specs.py [--keep] [--gold FILE] [--crate DIR]
                      [--proofs FILE] [--report FILE] [--invariant NAME]
Exit status: 0 if every comparable obligation in the Claude => gold direction is proved (or
differs only in capacity), 1 otherwise, 2 if the generated code does not compile.
"""
import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))

# ------------------------------------------------------------------------------ tokens


TOKEN_RE = re.compile(r'''
    (?P<ws>\s+)
  | (?P<lcomment>//[^\n]*)
  | (?P<bcomment>/\*)
  | (?P<rawstr>b?r(?P<hashes>\#*)")
  | (?P<str>b?"(?:\\.|[^"\\])*")
  | (?P<char>b?'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^'\\\n])')
  | (?P<lifetime>'[A-Za-z_]\w*)
  | (?P<num>\d[\w]*(?:\.\d[\w]*)?(?:[eE][+-]?\d+)?)
  | (?P<ident>r\#[A-Za-z_]\w*|[A-Za-z_]\w*)
  | (?P<punct><==>|==>|<==|=~~=|=~=|&&&|\|\|\||::|->|=>|==|!=|<=|>=|&&|\|\||\+=|-=|\*=|/=|%=|\^=|&=|\|=|\.\.=|\.\.\.|\.\.|[^\s])
''', re.VERBOSE | re.DOTALL)


class Tok:
    __slots__ = ('t', 's', 'e')

    def __init__(self, t, s, e):
        self.t, self.s, self.e = t, s, e

    def __repr__(self):
        return self.t


def tokenize(text):
    """Tokens of Rust/Verus source, without whitespace and comments."""
    toks, i = [], 0
    while i < len(text):
        m = TOKEN_RE.match(text, i)
        kind = m.lastgroup
        if kind == 'bcomment':
            depth, j = 1, m.end()
            while depth:
                if text.startswith('/*', j):
                    depth, j = depth + 1, j + 2
                elif text.startswith('*/', j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            i = j
            continue
        if kind == 'rawstr':
            end = text.index('"' + m.group('hashes'), m.end()) + 1 + len(m.group('hashes'))
            toks.append(Tok(text[i:end], i, end))
            i = end
            continue
        if kind not in ('ws', 'lcomment', 'hashes'):
            toks.append(Tok(m.group(), i, m.end()))
        i = m.end()
    return toks


OPEN, CLOSE = '([{', ')]}'


def match_close(toks, i):
    """Index of the bracket closing toks[i] (one of `([{`)."""
    depth = 0
    for j in range(i, len(toks)):
        t = toks[j].t if isinstance(toks[j], Tok) else toks[j]
        if t in OPEN:
            depth += 1
        elif t in CLOSE:
            depth -= 1
            if depth == 0:
                return j
    raise ValueError('unbalanced brackets')


def match_angle(toks, i):
    """Index of the `>` closing the `<` at toks[i] (in generics; `->` is one token)."""
    depth = 0
    for j in range(i, len(toks)):
        t = toks[j].t
        if t == '<':
            depth += 1
        elif t == '>':
            depth -= 1
            if depth == 0:
                return j
        elif t in OPEN:
            pass
    raise ValueError('unbalanced generics')


def text_of(src, toks, a, b):
    """Source text of toks[a..=b]."""
    return src[toks[a].s:toks[b].e]


def line_indent(src, offset):
    start = src.rfind('\n', 0, offset) + 1
    return len(src[start:offset]) - len(src[start:offset].lstrip(' ')), src[start:offset].strip() == ''

# ------------------------------------------------------------------------------- items

ITEM_KINDS = {'fn', 'struct', 'enum', 'union', 'trait', 'impl', 'mod', 'use', 'type', 'const',
              'static', 'extern', 'macro_rules', 'broadcast_use', 'broadcast_group'}
MODIFIERS = {'pub', 'const', 'unsafe', 'async', 'open', 'closed', 'spec', 'proof', 'exec',
             'uninterp', 'broadcast', 'axiom', 'tracked', 'ghost', 'default'}
CLAUSE_KWS = {'requires', 'ensures', 'recommends', 'decreases', 'opens_invariants', 'no_unwind',
              'returns', 'invariant'}


class Item:
    def __init__(self, **kw):
        self.__dict__.update(kw)


def parse_items(src, toks, lo, hi):
    """Items in toks[lo:hi]: kind, token span, modifiers, body span and (for impls) members."""
    items, i = [], lo
    while i < hi:
        start = i
        while i < hi and toks[i].t == '#':
            j = i + 1 + (toks[i + 1].t == '!')
            i = match_close(toks, j) + 1
        if i >= hi:
            break
        if toks[i].t == ';':
            i += 1
            continue
        mods, vis = [], None
        if toks[i].t == 'pub':
            vis = i
            i += 1
            if toks[i].t == '(':
                i = match_close(toks, i) + 1
        while toks[i].t in MODIFIERS:
            if toks[i].t == 'const' and toks[i + 1].t not in ('fn', 'unsafe', 'extern'):
                break
            if toks[i].t == 'broadcast' and toks[i + 1].t in ('use', 'group'):
                break
            mods.append(toks[i].t)
            i += 1
        if toks[i].t == 'extern' and toks[i + 1].t.startswith('"'):
            i += 2
        kw = i
        kind = toks[i].t
        if kind == 'broadcast':
            kind = 'broadcast_' + toks[i + 1].t
        if kind not in ITEM_KINDS:
            raise ValueError(f'unexpected token {kind!r} at offset {toks[i].s}')
        item = Item(kind=kind, start=start, kw=kw, vis=vis, mods=mods, body=None, members=[])
        if kind == 'fn':
            indent, _ = line_indent(src, toks[start].s)
            k, saw_clause = kw + 1, False
            while True:
                t = toks[k].t
                if t == '{':
                    col, alone = line_indent(src, toks[k].s)
                    if not saw_clause or (alone and col == indent):
                        item.body = (k, match_close(toks, k))
                        item.end = item.body[1]
                        break
                    k = match_close(toks, k) + 1
                    continue
                if t in '([':
                    k = match_close(toks, k) + 1
                    continue
                if t == ';':
                    item.end = k
                    break
                if t in CLAUSE_KWS and toks[k - 1].t != '.':
                    saw_clause = True
                k += 1
        elif kind in ('impl', 'trait', 'struct', 'enum', 'union', 'mod'):
            k = kw + 1
            while toks[k].t not in ('{', ';'):
                k = match_close(toks, k) + 1 if toks[k].t in '([' else k + 1
            if toks[k].t == ';':
                item.end = k
            else:
                item.body = (k, match_close(toks, k))
                item.end = item.body[1]
                if kind == 'impl':
                    item.members = parse_items(src, toks, k + 1, item.body[1])
        else:  # use, type, const, static, extern crate, broadcast use, ...
            k = kw
            while toks[k].t != ';':
                k = match_close(toks, k) + 1 if toks[k].t in OPEN else k + 1
            item.end = k
        items.append(item)
        i = item.end + 1
    return items

# --------------------------------------------------------------------------- signatures


def split_top(toks, lo, hi, angle=False):
    """Split toks[lo:hi] at top-level commas (not inside brackets, generics or `|..|` binders)."""
    parts, cur, depth, adepth, binder = [], [], 0, 0, False
    for t in toks[lo:hi]:
        s = t.t
        if s in OPEN:
            depth += 1
        elif s in CLOSE:
            depth -= 1
        elif angle and s == '<':
            adepth += 1
        elif angle and s == '>':
            adepth -= 1
        elif s == '|' and depth == 0:
            binder = not binder
        if s == ',' and depth == 0 and adepth == 0 and not binder:
            parts.append(cur)
            cur = []
        else:
            cur.append(t)
    if cur:
        parts.append(cur)
    return parts


class Sig:
    pass


def parse_sig(src, toks, item):
    """Name, generics, receiver, params, return, where and clauses of a fn item."""
    sg = Sig()
    k = item.kw + 1
    sg.name = toks[k].t
    k += 1
    sg.generics = ''
    if toks[k].t == '<':
        e = match_angle(toks, k)
        sg.generics = text_of(src, toks, k + 1, e - 1)
        k = e + 1
    pe = match_close(toks, k)
    params = split_top(toks, k + 1, pe, angle=True)
    sg.receiver, sg.params = None, []
    for p in params:
        ts = [t.t for t in p]
        if 'self' in ts and ':' not in ts:
            sg.receiver = '&mut' if ts[:2] == ['&', 'mut'] or (len(ts) > 2 and ts[0] == '&' and ts[2] == 'mut') \
                else '&' if ts[0] == '&' else 'self'
            continue
        colon = ts.index(':')
        sg.params.append((''.join(ts[:colon]).replace('mut', ''), text_of(src, p, colon + 1, len(p) - 1)))
    k = pe + 1
    sg.ret_name = sg.ret_type = None
    end = item.body[0] if item.body else item.end
    if toks[k].t == '->':
        k += 1
        if toks[k].t == '(' and toks[k + 1].t not in ('(', ')') and toks[k + 2].t == ':':
            e = match_close(toks, k)
            sg.ret_name = toks[k + 1].t
            sg.ret_type = text_of(src, toks, k + 3, e - 1)
            k = e + 1
        else:
            a, depth = k, 0
            while k < end and not (depth == 0 and toks[k].t in CLAUSE_KWS | {'where'}):
                depth += toks[k].t == '<'
                depth -= toks[k].t == '>'
                k = match_close(toks, k) + 1 if toks[k].t in '([' else k + 1
            sg.ret_type = text_of(src, toks, a, k - 1)
    sg.where = ''
    if toks[k].t == 'where':
        a = k + 1
        while k < end and not (toks[k].t in CLAUSE_KWS and toks[k - 1].t != '.'):
            k = match_close(toks, k) + 1 if toks[k].t in '([' else k + 1
        sg.where = text_of(src, toks, a, k - 1).rstrip(',')
    sg.clauses = {}
    is_kw = lambda k: toks[k].t in CLAUSE_KWS and toks[k - 1].t != '.'  # not `f.requires(..)`
    while k < end:
        if is_kw(k):
            kwd, a = toks[k].t, k + 1
            k += 1
            while k < end and not is_kw(k):
                k = match_close(toks, k) + 1 if toks[k].t in OPEN else k + 1
            sg.clauses[kwd] = [c for c in split_top(toks, a, k) if c]
        else:
            k += 1
    return sg


def impl_parts(src, toks, item):
    """(generics text, trait text or None, self type text) of an impl item."""
    k = item.kw + 1
    gen = ''
    if toks[k].t == '<':
        e = match_angle(toks, k)
        gen = text_of(src, toks, k + 1, e - 1)
        k = e + 1
    head_end = item.body[0]
    w = next((j for j in range(k, head_end) if toks[j].t == 'where'), head_end)
    f = None
    depth = 0
    for j in range(k, w):
        depth += toks[j].t == '<'
        depth -= toks[j].t == '>'
        if toks[j].t == 'for' and depth == 0:
            f = j
    if f is None:
        return gen, None, text_of(src, toks, k, w - 1)
    return gen, text_of(src, toks, k, f - 1), text_of(src, toks, f + 1, w - 1)


def core_type(ty):
    """`&'a mut crate::Slab<T>` -> ('&mut ', 'Slab')."""
    ts = [t.t for t in tokenize(ty)]
    prefix = ''
    while ts and ts[0] in ('&', 'mut') or (ts and ts[0].startswith("'")):
        if ts[0] == '&':
            prefix += '&'
        elif ts[0] == 'mut':
            prefix += 'mut '
        ts = ts[1:]
    name = ''
    depth = 0
    for t in ts:
        if t == '<':
            depth += 1
        elif t == '>':
            depth -= 1
        elif depth == 0 and re.match(r'[A-Za-z_]\w*$', t):
            name = t
    return prefix.strip(), name


def fn_key(self_ty, trait, name):
    pre, base = core_type(self_ty)
    tr = core_type(trait)[1] if trait else ''
    return ((pre + ' ' if pre else '') + base, tr, name)

# ----------------------------------------------------------------------- the two specs


def is_contract_only(item):
    return item.kind == 'fn' and item.body is None and not set(item.mods) & {
        'spec', 'proof', 'uninterp', 'axiom', 'open', 'closed'}


def parse_gold(path):
    src = open(path).read()
    toks = tokenize(src)
    v = next(i for i in range(len(toks)) if toks[i].t == 'verus' and toks[i + 1].t == '!')
    vclose = match_close(toks, v + 2)
    items = parse_items(src, toks, v + 3, vclose)
    g = Item(src=src, toks=toks, defs=[], views={}, contracts=[], uninterp=set(), axioms=[],
             axiom_covered=set(), field_types={})
    for it in items:
        if it.kind == 'fn' and 'uninterp' in it.mods:
            g.uninterp.add(toks[it.kw + 1].t)
        if it.kind == 'fn' and 'axiom' in it.mods and 'broadcast' in it.mods:
            g.axioms.append(toks[it.kw + 1].t)
            for j in range(it.kw, it.end):
                if toks[j].t == '#' and toks[j + 2].t == 'trigger':
                    g.axiom_covered.add(toks[j + 4].t)
        if it.kind == 'impl':
            gen, trait, self_ty = impl_parts(src, toks, it)
            if trait and core_type(trait)[1] == 'View':
                g.views[core_type(self_ty)[1]] = it
                g.defs.append(it)
            elif any(is_contract_only(m) for m in it.members):
                for m in it.members:
                    if is_contract_only(m):
                        g.contracts.append((gen, trait, self_ty, m))
            else:
                g.defs.append(it)
        else:
            g.defs.append(it)
    # which viewed types are placeholders: their view uses an uninterpreted function no axiom covers
    g.placeholder_types = set()
    for name, it in g.views.items():
        used = {toks[j].t for j in range(it.start, it.end)} & g.uninterp
        if used - g.axiom_covered:
            g.placeholder_types.add(name)
    # the fields of each view's model struct (`type V = M<..>;` with `struct M { f: .., .. }`)
    structs = {toks[it.kw + 1].t: it for it in items if it.kind == 'struct' and it.body}
    g.model_fields = {}
    for name, it in g.views.items():
        j = next((j for j in range(it.start, it.end) if toks[j].t == 'type' and toks[j + 1].t == 'V'), None)
        st = structs.get(toks[j + 3].t) if j is not None else None
        if st:
            lo, hi = st.body
            g.model_fields[name] = [toks[k].t for k in range(lo + 1, hi)
                                    if toks[k + 1].t == ':' and toks[k - 1].t in ('{', ',', 'pub', ')')]
    return g


def parse_crate(crate):
    """Verified (in `verus!`) and trusted (outside it) exec fns of the crate, by key."""
    verified, trusted, field_types = {}, set(), {}
    trusted_types = set()
    lib = os.path.join(crate, 'src', 'lib.rs')
    files = [lib] + [os.path.join(crate, 'src', f) for f in os.listdir(os.path.join(crate, 'src'))
                     if f.endswith('.rs') and f not in ('lib.rs',)]
    for path in files:
        src = open(path).read()
        toks = tokenize(src)
        regions, gaps, i, last = [], [], 0, 0
        while i < len(toks):
            if toks[i].t == 'verus' and i + 2 < len(toks) and toks[i + 1].t == '!' and toks[i + 2].t == '{':
                c = match_close(toks, i + 2)
                gaps.append((last, i))
                regions.append((i + 3, c))
                i = last = c + 1
            else:
                i += 1
        gaps.append((last, len(toks)))
        for (lo, hi), in_verus in [(r, True) for r in regions] + [(g, False) for g in gaps]:
            try:
                items = parse_items(src, toks, lo, hi)
            except (ValueError, IndexError):
                continue
            for it in items:
                if it.kind == 'struct' and not in_verus:
                    trusted_types.add(toks[it.kw + 1].t)
                if it.kind == 'struct' and it.body:
                    sname = toks[it.kw + 1].t
                    for f in split_top(toks, it.body[0] + 1, it.body[1], angle=True):
                        ts = [t.t for t in f]
                        if ':' in ts:
                            fname = ts[ts.index(':') - 1]
                            field_types[(sname, fname)] = core_type(text_of(src, f, ts.index(':') + 1, len(f) - 1))[1]
                if it.kind != 'impl':
                    continue
                gen, trait, self_ty = impl_parts(src, toks, it)
                for m in it.members:
                    if m.kind != 'fn' or set(m.mods) & {'spec', 'proof', 'uninterp', 'axiom', 'open', 'closed'}:
                        continue
                    key = fn_key(self_ty, trait, toks[m.kw + 1].t)
                    if in_verus and path == lib:
                        sig = parse_sig(src, toks, m)
                        verified[key] = Item(src=src, toks=toks, sig=sig, gen=gen, trait=trait, self_ty=self_ty)
                    elif not in_verus:
                        trusted.add(key)
    return verified, trusted, field_types, trusted_types

# ---------------------------------------------------------------------------- rewriting


def retok(s):
    return [t.t for t in tokenize(s)]


def expr_before(ts, i):
    """Start index of the postfix expression that ends at ts[i-1] (e.g. `old(self)`, `self.slab`)."""
    j = i - 1
    while j >= 0:
        if ts[j] == ')':
            depth = 0
            while True:
                depth += ts[j] == ')'
                depth -= ts[j] == '('
                if depth == 0:
                    break
                j -= 1
            if j > 0 and re.match(r'[A-Za-z_]\w*$', ts[j - 1]):
                j -= 1
        if j > 1 and ts[j - 1] == '.':
            j -= 2
            continue
        if j > 0 and ts[j - 1] == '*':
            j -= 1
        return j
    return 0


def expr_type(ts, a, b, env, field_types):
    """Core type of ts[a:b] (`slf`, `old(slf)`, `final(slf)`, `slf.slab`, a param, ...), or None."""
    e = [t for t in ts[a:b] if t not in ('*', '(', ')', 'old', 'final')]
    if not e or e[0] not in env:
        return None
    ty = env[e[0]]
    for k in range(1, len(e) - 1, 2):
        if e[k] != '.':
            return None
        ty = field_types.get((ty, e[k + 1]))
        if ty is None:
            return None
    return ty


def expr_after(ts, i):
    """End index (exclusive) of the operand of a binary `==` that starts at ts[i]."""
    stop = {',', ';', '&&', '||', '&&&', '|||', '==>', '<==>', '<==', '=>', '==', '!='}
    depth, j = 0, i
    while j < len(ts):
        t = ts[j]
        if t in OPEN:
            depth += 1
        elif t in CLOSE:
            if depth == 0:
                break
            depth -= 1
        elif depth == 0 and t in stop:
            break
        j += 1
    return j


def rewrite_contract(ts, self_ty, env, gold, field_types, invariant_type, nocap=False):
    """Apply the gold-spec conventions to a contract clause (a list of token strings)."""
    out = []
    for k, t in enumerate(ts):  # receiver and Self
        if t == 'self':
            out.append('slf')
        elif t == 'Self':
            out += retok(f'<{self_ty}>') if k + 1 < len(ts) and ts[k + 1] == '::' else retok(self_ty)
        else:
            out.append(t)
    ts = out
    # A model equality `x@ == y` is compared field by field (the same meaning, and each field
    # then gets Verus's automatic extensional equality); the capacity-free variant drops
    # `capacity`.
    k = 0
    while k < len(ts):
        if ts[k] == '==' and k > 0 and ts[k - 1] == '@':
            a = expr_before(ts, k - 1)
            ty = expr_type(ts, a, k - 1, env, field_types)
            if ty in gold.model_fields and ty not in gold.placeholder_types:
                b = expr_after(ts, k + 1)
                x, y = ts[a:k - 1], ts[k + 1:b]
                new = ['(']
                for f in gold.model_fields[ty]:
                    if not (nocap and f == 'capacity'):
                        new += (['&&'] if len(new) > 1 else []) + x + ['@', '.', f, '==', '('] + y + [')', '.', f]
                new.append(')')
                ts = ts[:a] + new + ts[b:]
                k = a + len(new)
                continue
        k += 1
    out, k = [], 0
    while k < len(ts):  # x@.valid() -> x.gold_inv(); x@ -> x.gv()
        if ts[k] == '@':
            a = len(out) - (k - expr_before(ts, k))
            ty = expr_type(ts, expr_before(ts, k), k, env, field_types)
            if invariant_type and ty == invariant_type and ts[k + 1:k + 5] == ['.', 'valid', '(', ')']:
                out += ['.', 'gold_inv', '(', ')']
                k += 5
                continue
            if ty in gold.views:
                out += ['.', 'gv', '(', ')']
                k += 1
                continue
        out.append(ts[k])
        k += 1
    return out


def rewrite_def_text(src, toks, item, gold, field_types):
    """Source of a gold definition with `x@` -> `x.gv()` for viewed types, `View` -> `GoldView`
    and crate-level visibility."""
    edits = []
    env_by_fn = []

    def visit(it):
        if it.vis is not None and toks[it.vis + 1].t != '(':
            edits.append((it.vis, it.vis, 'pub(crate)'))
        if it.kind == 'fn':
            sg = parse_sig(src, toks, it)
            env = {n: core_type(t)[1] for n, t in sg.params}
            env_by_fn.append((it.start, it.end, env))
        for m in it.members:
            visit(m)
    visit(item)
    impl_self = None
    if item.kind == 'impl':
        _, trait, self_ty = impl_parts(src, toks, item)
        impl_self = core_type(self_ty)[1]
        if trait and core_type(trait)[1] == 'View':
            j = next(j for j in range(item.kw, item.body[0]) if toks[j].t == 'View')
            edits.append((j, j, 'GoldView'))
            for j in range(item.body[0], item.end):
                if toks[j].t == 'view' and toks[j - 1].t == 'fn':
                    edits.append((j, j, 'gv'))
                if toks[j].t == 'closed' and toks[j + 1].t == 'spec':
                    edits.append((j, j, 'open'))
    names = [t.t for t in toks]
    for j in range(item.start, item.end + 1):
        if toks[j].t != '@':
            continue
        a = expr_before(names, j)
        env = {}
        for s, e, en in env_by_fn:
            if s <= j <= e:
                env = dict(en)
        if impl_self:
            env['self'] = impl_self
        if expr_type(names, a, j, env, field_types) in gold.views:
            edits.append((j, j, '.gv()'))
    out, pos = [], toks[item.start].s
    for a, b, rep in sorted(edits):
        out.append(src[pos:toks[a].s])
        out.append(rep)
        pos = toks[b].e
    out.append(src[pos:toks[item.end].e])
    return ''.join(out)

# -------------------------------------------------------------------------- generation


def safe_name(key):
    s, tr, f = key
    return '__'.join(x for x in (s.replace('&mut ', 'refmut_').replace('&', 'ref_'), tr, f) if x)


def mentions_capacity(clauses):
    return any(c[k] == '.' and c[k + 1] == 'capacity' for c in clauses for k in range(len(c) - 1))


class Gen:
    """Accumulates the generated module and remembers which lines hold which clause."""

    def __init__(self):
        self.lines, self.where = [], {}

    def add(self, text, tag=None):
        for l in text.split('\n'):
            self.lines.append(l)
            if tag:
                self.where[len(self.lines)] = tag


def join(ts):
    return ' '.join(ts)


def subst_self(text, self_ty):
    """`Self` in a type or path -> the impl's self type."""
    if not text or 'Self' not in text:
        return text
    ts = retok(text)
    out = []
    for k, t in enumerate(ts):
        if t == 'Self':
            out.append(f'<{self_ty}>' if k + 1 < len(ts) and ts[k + 1] == '::' else self_ty)
        else:
            out.append(t)
    return ' '.join(out)


def hint_lines(proofs, name, pos):
    """Hint blocks for an obligation: those for every obligation (`*`), then its own (a hint for
    `X` also covers `X__nocap`)."""
    h = proofs['hints']
    own = h.get((name, pos), h.get((name.replace('__nocap', ''), pos), []))
    return h.get(('*', pos), []) + own


def emit_fn(gen, name, generics, recv, self_ty, params, ret, where, requires, ensures, body,
            attrs='', axioms=()):
    params = [(n, subst_self(t, self_ty)) for n, t in params]
    ret = (ret[0], subst_self(ret[1], self_ty)) if ret else None
    where = subst_self(where, self_ty)
    recv_param = {'&': f'slf: &{self_ty}', '&mut': f'slf: &mut {self_ty}', 'self': f'slf: {self_ty}',
                  None: None}[recv]
    ps = ', '.join([p for p in [recv_param] if p] + [f'{n}: {t}' for n, t in params])
    rt = f' -> ({ret[0]}: {ret[1]})' if ret and ret[0] else (f' -> {ret[1]}' if ret else '')
    gen.add(f'{attrs}fn {name}{"<" + generics + ">" if generics else ""}({ps}){rt}', (name, 'sig', None))
    if where:
        gen.add(f'    where {where},')
    for kw, cl in (('requires', requires), ('ensures', ensures)):
        if cl:
            gen.add(f'    {kw}')
            for c, orig in cl:
                gen.add(f'        {join(c)},', (name, kw, orig))
    gen.add('{', (name, 'body', None))
    if axioms and not attrs:
        gen.add('    proof {', (name, 'body', None))
        gen.add('        broadcast use ' + ', '.join(axioms) + ';', (name, 'body', None))
        gen.add('    }', (name, 'body', None))
    for l in body:
        gen.add('    ' + l, (name, 'body', None))
    gen.add('}', (name, 'body', None))
    gen.add('')


def generate(gold, verified, trusted, field_types, proofs, invariant, trusted_types=()):
    gsrc, gtoks = gold.src, gold.toks
    # gold definitions about types the verified crate leaves trusted cannot be checked
    usable = [d for d in gold.defs if not ({gtoks[j].t for j in range(d.start, d.end + 1)} & set(trusted_types))]
    dropped_types = {t for t in gold.views if t in trusted_types}
    inv_type = None
    if invariant:
        inv_item = next((d for d in gold.defs if d.kind == 'fn' and gtoks[d.kw + 1].t == invariant), None)
        if inv_item is None:
            sys.exit(f'invariant {invariant!r} is not a gold spec function')
        inv_type = core_type(parse_sig(gsrc, gtoks, inv_item).params[0][1])[1]
    g = Gen()
    g.add('//! GENERATED by compare_specs.py from the gold spec and the verified crate. Do not edit.')
    g.add('#![allow(unused_imports, unused_variables, unused_mut, dead_code, non_snake_case)]')
    g.add('use crate::spec::*;\nuse crate::*;\nuse alloc::vec::Vec;\nuse vstd::prelude::*;\n\nverus! {\n')
    g.add('pub(crate) trait GoldView {\n    type V;\n    spec fn gv(&self) -> Self::V;\n}\n')
    if inv_type:
        g.add('pub(crate) trait GoldInv {\n    spec fn gold_inv(&self) -> bool;\n}\n')
        g.add(f'// convention: `x@.valid()` on a {inv_type} is read as the gold invariant `{invariant}`')
        g.add(f'impl<T> GoldInv for {inv_type}<T> {{\n    open spec fn gold_inv(&self) -> bool {{\n'
              f'        {invariant}(self)\n    }}\n}}\n')
    g.add('// ---- gold spec definitions ----')
    for d in usable:
        g.add(rewrite_def_text(gsrc, gtoks, d, gold, field_types) + '\n')
    g.add('\n// ---- proofs (lemmas from the proofs file) ----')
    g.add(proofs['lemmas'])
    g.add('// ---- obligations ----\n')

    results = []
    for gen_txt, trait, self_ty, m in gold.contracts:
        sg = parse_sig(gsrc, gtoks, m)
        key = fn_key(self_ty, trait, sg.name)
        st = core_type(self_ty)[1]
        r = Item(key=key, name=safe_name(key), wrappers=[], note='', h2a=None)
        results.append(r)
        if key not in verified:
            r.note = 'trusted in the verified crate' if key in trusted else 'no verified counterpart'
            continue
        env = {'slf': st, **{n: core_type(subst_self(t, self_ty))[1] for n, t in sg.params}}
        if sg.ret_name:
            env[sg.ret_name] = core_type(subst_self(sg.ret_type, self_ty))[1]
        req = [[t.t for t in c] for c in sg.clauses.get('requires', [])]
        ens = [[t.t for t in c] for c in sg.clauses.get('ensures', [])]
        orig = lambda c: ' '.join(gsrc[c[0].s:c[-1].e].split())
        req_o = [orig(c) for c in sg.clauses.get('requires', [])]
        ens_o = [orig(c) for c in sg.clauses.get('ensures', [])]
        used = set()
        for cl in req + ens:
            ts = ['slf' if t == 'self' else t for t in cl]
            for k, t in enumerate(ts):
                if t == '@':
                    used.add(expr_type(ts, expr_before(ts, k), k, env, field_types))
            used |= set(ts) & (gold.uninterp - gold.axiom_covered)
        holes = (used & gold.placeholder_types) | (used & gold.uninterp)
        if holes:
            r.note = 'gold placeholder (uses ' + ', '.join(sorted(holes)) + ')'
            continue
        generics = ', '.join(x for x in (gen_txt, sg.generics) if x)
        args = ', '.join((['slf'] if sg.receiver else []) + [n for n, _ in sg.params])
        call = f'<{self_ty} as {trait}>::{sg.name}({args})' if trait else f'<{self_ty}>::{sg.name}({args})'
        ret = (sg.ret_name or 'ret', sg.ret_type) if sg.ret_type else None
        needs_nocap = mentions_capacity(req + ens) or any(
            rewrite_contract(c, self_ty, env, gold, field_types, inv_type, True)
            != rewrite_contract(c, self_ty, env, gold, field_types, inv_type) for c in req + ens)
        variants = [('', False)] + ([('__nocap', True)] if needs_nocap else [])
        for suffix, nocap in variants:
            name = 'claude_implies_gold__' + r.name + suffix
            rq = [(rewrite_contract(c, self_ty, env, gold, field_types, inv_type, nocap), o)
                  for c, o in zip(req, req_o) if not (nocap and mentions_capacity([c]))]
            en = []
            for c, o in zip(ens, ens_o):
                if nocap and mentions_capacity([c]):
                    continue
                new = rewrite_contract(c, self_ty, env, gold, field_types, inv_type, nocap)
                changed = nocap and new != rewrite_contract(c, self_ty, env, gold, field_types, inv_type)
                en.append((new, o + (' [without capacity]' if changed else '')))
            body = []
            if sg.receiver:
                body.append('let ghost pre = ' + ('*slf;' if sg.receiver in ('&', '&mut') else 'slf;'))
            body += hint_lines(proofs, name, 'before')
            body.append(f'let ret = {call};' if ret else f'{call};')
            body += hint_lines(proofs, name, 'after')
            if ret:
                body.append('ret')
            emit_fn(g, name, generics, sg.receiver, self_ty, sg.params, ret, sg.where, rq, en, body,
                    axioms=gold.axioms)
            r.wrappers.append((name, nocap))
        # gold => Claude: inherent functions with explicit verified contracts
        ai = verified[key]
        if not trait and (ai.sig.clauses.get('requires') or ai.sig.clauses.get('ensures')):
            gname = 'gold_contract__' + r.name
            rq = [(rewrite_contract(c, self_ty, env, gold, field_types, inv_type), o) for c, o in zip(req, req_o)]
            en = [(rewrite_contract(c, self_ty, env, gold, field_types, inv_type), o) for c, o in zip(ens, ens_o)]
            emit_fn(g, gname, generics, sg.receiver, self_ty, sg.params, ret, sg.where, rq, en,
                    ['unimplemented!()'], attrs='#[verifier::external_body]\n')
            asg = ai.sig
            aenv = {}
            arq = [(rewrite_contract([t.t for t in c], self_ty, aenv, gold, field_types, None),
                    ' '.join(ai.src[c[0].s:c[-1].e].split())) for c in asg.clauses.get('requires', [])]
            aen = [(rewrite_contract([t.t for t in c], self_ty, aenv, gold, field_types, None),
                    ' '.join(ai.src[c[0].s:c[-1].e].split())) for c in asg.clauses.get('ensures', [])]
            hname = 'gold_implies_claude__' + r.name
            agen = ', '.join(x for x in (ai.gen, asg.generics) if x)
            aargs = ', '.join((['slf'] if asg.receiver else []) + [n for n, _ in asg.params])
            aret = (asg.ret_name or 'ret', asg.ret_type) if asg.ret_type else None
            body = []
            if asg.receiver:
                body.append('let ghost pre = ' + ('*slf;' if asg.receiver in ('&', '&mut') else 'slf;'))
            body += hint_lines(proofs, hname, 'before')
            body.append(f'let ret = {gname}({aargs});' if aret else f'{gname}({aargs});')
            body += hint_lines(proofs, hname, 'after')
            if aret:
                body.append('ret')
            emit_fn(g, hname, agen, asg.receiver, self_ty, asg.params, aret, asg.where, arq, aen, body,
                    axioms=gold.axioms)
            r.h2a = hname
    g.add('} // verus!')
    return g, results

# ------------------------------------------------------------------------------ proofs

FORBIDDEN = re.compile(r'\b(assume|admit|assume_specification|external_body|external_fn_specification|'
                       r'external_type_specification|uninterp|axiom|unsafe)\b|verifier::external|'
                       r'#\[verifier::(?!via_fn)')


def read_proofs(path):
    lemmas, hints, notes, cur, note = [], {}, {}, None, None
    if not os.path.exists(path):
        return {'lemmas': '', 'hints': {}, 'notes': {}}
    for n, l in enumerate(open(path).read().split('\n'), 1):
        m = re.match(r'\s*//\s*@note\s+(\S+)\s*$', l)
        if m:
            note = m.group(1)
            notes[note] = []
            continue
        if note and re.match(r'\s*//', l):  # the note runs on to the last comment line
            notes[note].append(re.sub(r'^\s*//\s?', '', l).strip())
            continue
        note = None
        m = re.match(r'\s*//\s*@hint\s+(\S+)\s+(before|after)\s*$', l)
        if m:
            cur = (m.group(1), m.group(2))
            hints.setdefault(cur, [])
            continue
        code = l.split('//')[0]
        if FORBIDDEN.search(code):
            sys.exit(f'{path}:{n}: proofs may not use trusted constructs: {l.strip()}')
        if cur:
            hints[cur].append(l)
        else:
            lemmas.append(l)
    for key, body in hints.items():
        text = '\n'.join(body).strip()
        if text and not (text.startswith('proof {') and text.endswith('}')):
            sys.exit(f'{path}: hint {key[0]} {key[1]} must be a single `proof {{ ... }}` block')
        hints[key] = [l for l in body if l.strip()]
    lemma_text = '\n'.join(lemmas)
    for m in re.finditer(r'^\s*(?:pub\S*\s+)?((?:open |closed )?(?:spec|proof|exec)?\s*fn)\s', lemma_text, re.M):
        if not re.search(r'(spec|proof)\s*fn', m.group(1)):
            sys.exit(f'{path}: only `proof fn` and `spec fn` items are allowed: {m.group(0).strip()}')
    return {'lemmas': lemma_text, 'hints': hints, 'notes': {k: ' '.join(v) for k, v in notes.items()}}

# ------------------------------------------------------------------------------ running


def run(args):
    gold = parse_gold(args.gold)
    verified, trusted, field_types, trusted_types = parse_crate(args.crate)
    proofs = read_proofs(args.proofs)
    g, results = generate(gold, verified, trusted, field_types, proofs, args.invariant, trusted_types)
    tmp = tempfile.mkdtemp(prefix='compare-specs-')
    crate = os.path.join(tmp, 'crate')
    shutil.copytree(args.crate, crate, ignore=shutil.ignore_patterns('target', '.verus-solver-log'))
    open(os.path.join(crate, 'src', 'gold_check.rs'), 'w').write('\n'.join(g.lines) + '\n')
    lib = os.path.join(crate, 'src', 'lib.rs')
    open(lib, 'a').write('\n#[cfg(verus_keep_ghost)]\nmod gold_check;\n')
    cmd = [os.environ.get('VERUS', 'verus'), '--crate-type=lib', '--cfg', 'feature="std"',
           '--verify-only-module', 'gold_check', '--multiple-errors', '1000', 'src/lib.rs']
    r = subprocess.run(cmd, cwd=crate, capture_output=True, text=True)
    out = r.stdout + r.stderr
    open(os.path.join(tmp, 'verus_output.txt'), 'w').write(out)
    if args.keep:
        print(f'kept: {crate}/src/gold_check.rs')
    return gold, g, results, out, crate, tmp


def read_line(crate, path, line):
    try:
        return open(os.path.join(crate, path)).read().split('\n')[line - 1].strip()
    except (OSError, IndexError):
        return ''


def classify(g, results, out, crate):
    m = re.search(r'verification results:: (\d+) verified, (\d+) errors', out)
    if not m:
        errs = [b for b in re.split(r'\n(?=error)', out) if b.startswith('error')]
        return None, errs
    failures, foreign = {}, []
    for block in re.split(r'\n(?=(?:error|warning|note)(?:\[\w+\])?: )', out):
        if not block.startswith('error: ') or 'aborting due' in block:
            continue
        msg = block.split('\n')[0][7:]
        locs = re.findall(r'(?:-->|:::) (\S+):(\d+):(\d+)', block)
        prim = next(((p, int(l)) for p, l, _ in locs if p.endswith('gold_check.rs')), None)
        tag = g.where.get(prim[1]) if prim else None
        if not tag:
            # an error in a lemma or a gold definition: every result that depends on it is void
            where = f'{prim[0]}:{prim[1]}: {read_line(crate, prim[0], prim[1])}' if prim else 'unknown location'
            foreign.append(f'{msg} ({where})')
            continue
        name, role, clause = tag
        if role in ('requires', 'ensures') and msg.startswith('postcondition'):
            what = f'ensures: {clause}'
        elif msg.startswith('precondition'):
            callee, cur_file, cur_line = None, None, None  # the source line labeled `failed precondition`
            for bl in block.split('\n'):
                fm = re.search(r'(?:-->|:::) (\S+):(\d+):\d+', bl)
                if fm:
                    cur_file = fm.group(1)
                lm = re.match(r'\s*(\d+) \|', bl)
                if lm:
                    cur_line = int(lm.group(1))
                if 'failed precondition' in bl and cur_file and cur_line:
                    callee = (cur_file, cur_line)
                    break
            text = read_line(crate, callee[0], callee[1]) if callee else '?'
            if callee and callee[0].endswith('gold_check.rs') and g.where.get(callee[1]):
                text = g.where[callee[1]][2] or text  # the gold clause as written
            what = 'requires of the callee: ' + text.rstrip(',')
        else:
            what = msg
        failures.setdefault(name, []).append(what)
    if foreign:
        return None, ['Lemmas or gold definitions do not verify, so no obligation result can be '
                      'trusted:'] + foreign
    return failures, None


def report(args, gold, results, failures, compile_errors, crate, notes):
    lines = ['# Gold spec vs. verified spec', '',
             f'Generated by `compare_specs.py`. Gold spec: `{os.path.relpath(args.gold, os.path.dirname(os.path.abspath(args.report)))}`; '
             f'verified crate: `{os.path.relpath(args.crate, os.path.dirname(os.path.abspath(args.report)))}`; '
             f'proofs: `{os.path.relpath(args.proofs, os.path.dirname(os.path.abspath(args.report)))}`.', '',
             '- **Claude ⇒ gold**: the verified contract gives everything the gold contract asks for '
             '(gold pre ⇒ Claude pre, and gold pre ∧ Claude post ⇒ gold post).',
             '- **gold ⇒ Claude**: the gold contract gives everything the verified contract promises '
             '(inherent functions only).',
             '- Conventions: the gold `View` is renamed `GoldView`; '
             + (f'`x@.valid()` on a slab is read as `{args.invariant}`; ' if args.invariant else '')
             + 'gold axioms in force: ' + (', '.join(f'`{a}`' for a in gold.axioms) or 'none') + '.',
             '- *capacity only*: the obligation fails, but holds once capacity clauses are removed '
             '(Claude\'s spec says nothing about capacity).', '']
    if compile_errors is not None:
        lines += ['**The generated obligations do not compile or the proofs do not verify:**', '', '```'] + \
            [e[:1500] for e in compile_errors[:10]] + ['```']
        open(args.report, 'w').write('\n'.join(lines) + '\n')
        return 2
    def status(name):
        return 'proved' if name not in failures else 'UNPROVED'
    rows, details, bad, noted, capacity_only = [], [], 0, set(), set()
    for r in results:
        if not r.wrappers:
            rows.append(f'| `{r.key[0]}{"::" + r.key[1] if r.key[1] else ""}::{r.key[2]}` | — | — | {r.note} |')
            continue
        full = next(n for n, nc in r.wrappers if not nc)
        nocap = next((n for n, nc in r.wrappers if nc), None)
        s = status(full)
        if s != 'proved' and nocap and status(nocap) == 'proved':
            s = 'capacity only'
        if s == 'UNPROVED':
            bad += 1
        h = status(r.h2a) if r.h2a else '—'
        rows.append(f'| `{r.key[0]}{"::" + r.key[1] if r.key[1] else ""}::{r.key[2]}` | {s} | {h} | {r.note} |')
        for n in [x for x, _ in r.wrappers] + ([r.h2a] if r.h2a else []):
            if n in failures:
                details += ['', f'### `{n}`', ''] + [f'- {w}' for w in failures[n]]
                note = notes.get(n, notes.get(n.replace('__nocap', '')))
                if n == full and s == 'capacity only':
                    capacity_only.add(n)
                    details += ['', '*Capacity only:* the capacity-free variant is proved.']
                elif note:
                    noted.add(n)
                    details += ['', f'*Note (an explanation, not checked):* {note}']
    def summary(col, label):
        counts = {}
        for row in rows:
            c = row.split('|')[col].strip()
            counts[c] = counts.get(c, 0) + 1
        return f'{label}: ' + ', '.join(f'{v} {k}' for k, v in sorted(counts.items()) if k != '—') \
            + f', {counts.get("—", 0)} not compared.'
    lines += ['| function | Claude ⇒ gold | gold ⇒ Claude | note |', '|---|---|---|---|'] + rows
    lines += ['', summary(2, 'Claude ⇒ gold'), '', summary(3, 'gold ⇒ Claude')]
    wrappers = {n for r in results for n, _ in r.wrappers} | {r.h2a for r in results if r.h2a}
    stale = sorted(k for k in notes if k not in failures and k + '__nocap' not in failures)
    if stale:
        lines += ['', 'Notes for obligations that are proved or do not exist: '
                  + ', '.join(f'`{k}`' + ('' if k in wrappers else ' (does not exist)') for k in stale) + '.']
    if details:
        lines += ['', f'## Unproved obligations ({len(failures)}: {len(capacity_only)} capacity only, '
                  f'{len(noted)} with a note, {len(failures) - len(capacity_only) - len(noted)} unexplained)'] + details
    open(args.report, 'w').write('\n'.join(lines) + '\n')
    print('\n'.join(l for l in lines if l.startswith(('Claude ⇒ gold:', 'gold ⇒ Claude:', 'Notes for', '## Unproved'))))
    return 1 if bad else 0


def main():
    ap = argparse.ArgumentParser(description='Compare the gold spec with the verified spec.')
    ap.add_argument('--gold', default=os.path.join(HERE, 'humen_written_spec.rs'))
    ap.add_argument('--crate', default=os.path.join(HERE, 'slab'))
    ap.add_argument('--proofs', default=os.path.join(HERE, 'spec_proofs.rs'))
    ap.add_argument('--report', default=os.path.join(HERE, 'spec_comparison.md'))
    ap.add_argument('--invariant', default='slab_rep_ok',
                    help='gold spec function that `x@.valid()` on a slab is read as ("" to disable)')
    ap.add_argument('--keep', action='store_true', help='keep the scratch crate')
    args = ap.parse_args()
    gold, g, results, out, crate, tmp = run(args)
    failures, compile_errors = classify(g, results, out, crate)
    code = report(args, gold, results, failures, compile_errors, crate, read_proofs(args.proofs)['notes'])
    if compile_errors is not None:
        print('generated obligations do not compile, or lemmas do not verify; see', args.report)
    if not args.keep:
        shutil.rmtree(tmp, ignore_errors=True)
    print('report:', args.report)
    sys.exit(code)


if __name__ == '__main__':
    main()
