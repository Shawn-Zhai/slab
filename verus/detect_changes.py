#!/usr/bin/env python3
"""Detect changes that verification made to a crate's executable code.

Both crates (upstream and annotated) are compiled to macro-expanded Rust with `rustc
-Zunpretty=expanded`. In a normal build the `verus!` macro erases ghost code (specifications,
proof blocks, spec and proof functions), so the expanded annotated crate is the code that
actually runs. The two expansions are split into items (functions, impl blocks and their
methods, structs, ...), matched by name rather than by file, so code that only moved between
files or modules is not reported as changed, and compared token by token, ignoring formatting
and comments.

Every difference is reported: changed, added and removed items, imports, other files (Cargo.toml,
tests/), and the trust-boundary markers in the annotated source (`verifier::external`,
`assume_specification`, `unsafe`, ...). A difference passes only if `approved_changes.json`
records it with the same fingerprint and a non-empty `reviewer`. The script never fills in
`reviewer`; a human does. If either side of an approved difference changes, its fingerprint
changes and it needs review again.

Usage (from verus/):
    python3 detect_changes.py                 # check; exit status 1 if anything is unreviewed
    python3 detect_changes.py --template      # also write unreviewed entries to approvals file
Options: --upstream DIR, --annotated DIR, --approvals FILE, --report FILE, --json FILE,
         --toolchain NAME, --config "CARGO FEATURE FLAGS" (repeatable; default: "--features serde"
         and "--no-default-features").
"""
import argparse
import difflib
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))

# ----------------------------------------------------------------------------------- expansion


def toolchain_of(crate):
    path = os.path.join(crate, 'rust-toolchain.toml')
    if os.path.exists(path):
        m = re.search(r'channel\s*=\s*"([^"]+)"', open(path).read())
        if m:
            return m.group(1)
    return None


def expand(crate, flags, toolchain, target_dir):
    """The crate's library, macro-expanded, as rustc sees it in a normal (non-Verus) build."""
    cmd = ['cargo'] + ([f'+{toolchain}'] if toolchain else []) + [
        'rustc', '-q', '--lib', '--target-dir', target_dir] + flags.split() + [
        '--', '-Zunpretty=expanded']
    env = dict(os.environ, RUSTC_BOOTSTRAP='1')  # allows -Z on a stable toolchain
    r = subprocess.run(cmd, cwd=crate, env=env, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f'expansion failed in {crate} ({" ".join(cmd)}):\n{r.stderr}')
    return r.stdout

# ------------------------------------------------------------------------------- tokenization


TOKEN_RE = re.compile(r'''
    (?P<ws>\s+)
  | (?P<doc>///(?!/)[^\n]*|//![^\n]*)
  | (?P<lcomment>//[^\n]*)
  | (?P<bcomment>/\*)
  | (?P<rawstr>b?r(?P<hashes>\#*)")
  | (?P<str>b?"(?:\\.|[^"\\])*")
  | (?P<char>b?'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^'\\\n])')
  | (?P<lifetime>'[A-Za-z_]\w*)
  | (?P<num>\d[\w]*(?:\.\d[\w]*)?(?:[eE][+-]?\d+)?)
  | (?P<ident>r\#[A-Za-z_]\w*|[A-Za-z_]\w*)
  | (?P<punct>::|->|=>|==|!=|<=|>=|&&|\|\||\+=|-=|\*=|/=|%=|\^=|&=|\|=|\.\.=|\.\.\.|\.\.|[^\s])
''', re.VERBOSE | re.DOTALL)


def tokenize(text):
    """Tokens as (text, start offset, end offset); comments and whitespace are dropped."""
    toks, i = [], 0
    while i < len(text):
        m = TOKEN_RE.match(text, i)
        kind = m.lastgroup
        if kind == 'bcomment':  # nested block comment
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
            toks.append((text[i:end], i, end))
            i = end
            continue
        if kind == 'doc':  # `/// text` is `#[doc = " text"]`; `//! text` is `#![doc = ...]`
            toks.append((('DOC:' if m.group()[2] == '/' else 'IDOC:') + m.group()[3:], i, m.end()))
        elif kind not in ('ws', 'lcomment', 'hashes'):
            toks.append((m.group(), i, m.end()))
        i = m.end()
    return normalize_docs(toks)


def unescape(lit):
    """The value of a Rust string literal (the escapes that rustc's printer emits)."""
    body = lit[1:-1]
    return re.sub(r'\\(u\{[0-9a-fA-F]+\}|x[0-9a-fA-F]{2}|.)', lambda m: {
        'n': '\n', 't': '\t', 'r': '\r', '0': '\0', '\\': '\\', '"': '"', "'": "'"}.get(
        m.group(1), chr(int(m.group(1)[2:-1] if m.group(1)[0] == 'u' else m.group(1)[1:], 16))
        if m.group(1)[0] in 'ux' else m.group(1)), body)


def normalize_docs(toks):
    """`#[doc = "x"]` and `#![doc = "x"]` attributes become the same tokens as `///x` and `//!x`."""
    out, i = [], 0
    while i < len(toks):
        t = [x[0] for x in toks[i:i + 6]]
        inner = t[:2] == ['#', '!']
        o = 1 if inner else 0
        if (t[:1] == ['#'] and len(t) >= 6 + o - 1 and t[1 + o:4 + o] == ['[', 'doc', '=']
                and i + 5 + o < len(toks) and toks[i + 5 + o][0] == ']'
                and toks[i + 4 + o][0].startswith('"')):
            text = unescape(toks[i + 4 + o][0])
            out.append((('IDOC:' if inner else 'DOC:') + text, toks[i][1], toks[i + 5 + o][2]))
            i += 6 + o
            continue
        out.append(toks[i])
        i += 1
    return out


def drop_trailing_commas(toks):
    """Remove `,` before a closing bracket: the printer adds them when it wraps a line. Kept in
    one-element tuples, where `(x,)` and `(x)` differ."""
    out = []
    for k, t in enumerate(toks):
        if t[0] == ',' and k + 1 < len(toks) and toks[k + 1][0] in ')]}':
            if toks[k + 1][0] == ')':
                depth, other_comma = 0, False
                for x in reversed(out):
                    if x[0] in ')]}':
                        depth += 1
                    elif x[0] in '([{':
                        if depth == 0:
                            break
                        depth -= 1
                    elif x[0] == ',' and depth == 0:
                        other_comma = True
                        break
                if not other_comma:
                    out.append(t)
            continue
        out.append(t)
    return out


def drop_erased_blocks(toks):
    """Remove what `verus!` leaves of erased ghost code: `{}` statements (from `proof { ... }`)
    and then `else {}` (from an `else` that held only a proof block). Neither does anything."""
    out = []
    for t in toks:
        if (t[0] == '}' and out and out[-1][0] == '{' and len(out) >= 2
                and out[-2][0] in (';', '{', '}')):
            out.pop()
            continue
        out.append(t)
    toks, out = out, []
    for t in toks:
        if t[0] == '}' and len(out) >= 2 and out[-1][0] == '{' and out[-2][0] == 'else':
            del out[-2:]
            continue
        out.append(t)
    return out

# ------------------------------------------------------------------------------- item parsing

OPEN, CLOSE = '([{', ')]}'
ITEM_KINDS = ('fn', 'struct', 'enum', 'union', 'trait', 'impl', 'mod', 'use', 'type',
              'const', 'static', 'extern', 'macro_rules')
SEMI_ITEMS = ('use', 'type', 'const', 'static', 'extern')


def match_close(toks, i):
    """Index of the bracket that closes toks[i]."""
    depth = 0
    for j in range(i, len(toks)):
        if toks[j][0] in OPEN:
            depth += 1
        elif toks[j][0] in CLOSE:
            depth -= 1
            if depth == 0:
                return j
    raise ValueError('unbalanced brackets')


def strip_generics(toks):
    """Header tokens without `<...>` groups and lifetimes: `impl<'a, T> X for &'a S<T>` -> X for &S."""
    out, depth = [], 0
    for t in toks:
        if t == '<':
            depth += 1
        elif t == '>' and depth:
            depth -= 1
        elif depth == 0 and not t.startswith("'"):
            out.append(t)
    return out


def parse_items(toks, lo, hi, path, out):
    """Append (key, module path, kind, token slice) for every item in toks[lo:hi]."""
    i = lo
    while i < hi:
        start = i
        while i < hi and (toks[i][0] == '#' or toks[i][0].startswith(('DOC:', 'IDOC:'))):
            if toks[i][0] == '#':  # attribute
                i = match_close(toks, i + (2 if toks[i + 1][0] == '!' else 1)) + 1
            else:
                i += 1
        if i < hi and toks[i][0] == ';':
            i += 1
            continue
        if i >= hi:
            break
        # visibility and qualifiers
        j = i
        if toks[j][0] == 'pub':
            j += 1
            if toks[j][0] == '(':
                j = match_close(toks, j) + 1
        while toks[j][0] in ('unsafe', 'async', 'default', 'auto', 'const') and \
                toks[j + 1][0] in ('fn', 'impl', 'trait', 'unsafe', 'async', 'extern', 'const'):
            j += 1  # qualifiers: `const fn`, `unsafe fn`, `unsafe impl`, ...
        if toks[j][0] == 'extern' and toks[j + 1][0].startswith('"'):
            j += 2  # extern "C" fn
        kind = toks[j][0]
        if kind not in ITEM_KINDS:
            raise ValueError(f'unexpected token {kind!r} in {"::".join(path) or "crate"}')
        # end of the item
        k = j
        end = None
        while k < hi:
            t = toks[k][0]
            if t == ';' and (kind in SEMI_ITEMS or end is None):
                end = k
                break
            if t == '{' and kind not in SEMI_ITEMS:
                end = match_close(toks, k)
                break
            if t in '([':
                k = match_close(toks, k)
            k += 1
        if kind in SEMI_ITEMS:
            k = j
            while toks[k][0] != ';':
                k = match_close(toks, k) if toks[k][0] in OPEN else k
                k += 1
            end = k
        name = toks[j + 1][0] if j + 1 < hi else ''
        body = toks[start:end + 1]
        if kind == 'impl':
            hdr_end = next(x for x in range(j, end + 1) if toks[x][0] in ('{', 'where'))
            header = ' '.join(strip_generics([t[0] for t in toks[j + 1:hdr_end]]))
            brace = next(x for x in range(j, end + 1) if toks[x][0] == '{')
            members = []
            parse_items(toks, brace + 1, end, path, members)
            if members or ' for ' in f' {header} ':  # an empty inherent impl is erased ghost code
                out.append((f'impl {header}', path, 'impl', toks[start:brace + 1] + [toks[end]]))
            for key, _, mkind, mtoks in members:
                out.append((f'impl {header} :: {key}', path, mkind, mtoks))
        elif kind == 'mod' and toks[end][0] == '}':
            brace = next(x for x in range(j, end + 1) if toks[x][0] == '{')
            parse_items(toks, brace + 1, end, path + [name], out)
        elif kind == 'use' or kind == 'extern':
            out.append((' '.join(t[0] for t in toks[i:end + 1]), path, kind, body))
        elif kind == 'macro_rules':
            out.append((f'macro_rules {toks[j + 2][0]}', path, kind, body))
        else:
            out.append((f'{kind} {name}', path, kind, body))
        i = end + 1


def items_of(text):
    toks = drop_trailing_commas(drop_erased_blocks(tokenize(text)))
    out = []
    parse_items(toks, 0, len(toks), [], out)
    items = {}
    for key, path, kind, itoks in out:
        if kind == 'impl':  # a type may have several impl blocks: compare their distinct headers
            hdr = [t[0] for t in itoks if not t[0].startswith(('DOC:', 'IDOC:'))]
            same = [k for k, v in items.items() if v['kind'] == 'impl' and
                    (k == key or k.startswith(key + ' #'))]
            if any([t[0] for t in items[k]['toks'] if not t[0].startswith(('DOC:', 'IDOC:'))] == hdr
                   for k in same):
                continue
            if same:
                key = f"{key} #{len(same) + 1}"
        elif key in items:  # same name in two modules: keep both, qualified
            key = '::'.join(path + [key])
        items[key] = dict(path=path, kind=kind, toks=itoks)
    return items


def split_docs(itoks):
    """(doc lines, other tokens): documentation is compared separately from code."""
    docs = [t[0].split(':', 1)[1] for t in itoks if t[0].startswith(('DOC:', 'IDOC:'))]
    rest = [t[0] for t in itoks if not t[0].startswith(('DOC:', 'IDOC:'))]
    return docs, rest


def source_of(text, itoks):
    """The item's expanded text, without comments and erased `{}` lines, for display."""
    code = [t for t in itoks if not t[0].startswith(('DOC:', 'IDOC:'))]
    chunk = text[code[0][1]:code[-1][2]]
    chunk = re.sub(r'(?<=[{;])\s*\{\}', '', chunk)
    chunk = re.sub(r'\s*else\s*\{\s*\}', '', chunk)
    lines = [l for l in chunk.split('\n')
             if l.strip() not in ('{}', '') and not l.strip().startswith('//')]
    indent = min((len(l) - len(l.lstrip()) for l in lines[1:]), default=0)
    return [lines[0].strip()] + [l[min(indent, len(l) - len(l.lstrip())):] for l in lines[1:]]

# ---------------------------------------------------------------------------------------- hints

HINTS = [  # (description, pattern on removed lines or None, pattern on added lines or None)
    ('`unreachable!()` -> vstd `unreached()` (still panics, different message)',
     r'entered unreachable code', r'unreached\(\)'),
    ('`assert!` -> vstd `runtime_assert` (still panics, different message)',
     r'panic\("assertion failed', r'runtime_assert\('),
    ('`debug_assert*!` removed (debug builds no longer check it)', r'if true \{|assert_failed', None),
    ('`panic!(msg)` -> `.expect(msg)`', r'panic\("([^"]*)"\)', r'\.expect\('),
    ('std call -> verified stand-in from std_ext.rs', None,
     r'\b(vec_get_mut|slice_get_mut|mem_replace)\('),
    ('reference pattern -> match ergonomics', r'&(mut )?Entry::\w+\(|\(ref (mut )?\w+\)',
     r'Entry::\w+\((?!ref )\w+\)'),
    ('result bound to a variable before returning it', None, r'^\s*let (\w+) =\s*$|^\s*let (\w+) = .*;$'),
    ('`.into()` -> `Some(..)`', r'\.into\(\)', r'Some\('),
    ('loop rewritten (`for` / `while let` -> `while` / `loop`)', r'^\s*(for|while let) ',
     r'^\s*(while|loop)\b'),
    ('`self.len += 1` moved', r'^\s*self\.len \+= 1;', r'^\s*self\.len \+= 1;'),
]


def hints(diff, new_fns=()):
    removed = [l[1:] for l in diff if l.startswith('-') and not l.startswith('---')]
    added = [l[1:] for l in diff if l.startswith('+') and not l.startswith('+++')]
    out = []
    for desc, rem, add in HINTS:
        if (rem is None or any(re.search(rem, l) for l in removed)) and \
                (add is None or any(re.search(add, l) for l in added)):
            out.append(desc)
    called = sorted({n for n in new_fns for l in added if re.search(rf'\b{n}\(', l)} -
                    {n for n in new_fns for l in removed if re.search(rf'\b{n}\(', l)})
    if called:
        out.append('calls functions that verification added: ' + ', '.join(f'`{n}`' for n in called))
    return out

# --------------------------------------------------------------------------------- comparison


def fingerprint(*parts):
    h = hashlib.sha256()
    for p in parts:
        h.update(json.dumps(p).encode())
        h.update(b'\0')
    return h.hexdigest()[:16]


def import_lines(items):
    return sorted(f"{'::'.join(v['path']) or 'crate'}: {k.split('::', 1)[-1] if v['path'] and k.startswith('::'.join(v['path']) + '::') else k}"
                  for k, v in items.items() if v['kind'] in ('use', 'extern'))


def compare(up_text, ann_text, config):
    up, ann = items_of(up_text), items_of(ann_text)
    findings = []
    ui, ai = import_lines(up), import_lines(ann)
    if ui != ai:
        findings.append(dict(key='imports', status='changed', config=config, kind='use',
                             fp=fingerprint(ui, ai),
                             diff=[l for l in difflib.unified_diff(ui, ai, 'upstream', 'annotated',
                                                                   lineterm='', n=0)
                                   if not l.startswith('@@')]))
    up = {k: v for k, v in up.items() if v['kind'] not in ('use', 'extern')}
    ann = {k: v for k, v in ann.items() if v['kind'] not in ('use', 'extern')}
    for key in sorted(set(up) | set(ann)):
        u, a = up.get(key), ann.get(key)
        if u and a:
            udocs, ucode = split_docs(u['toks'])
            adocs, acode = split_docs(a['toks'])
            what = []
            if ucode != acode:
                what.append('code')
            if udocs != adocs:
                what.append('docs')
            if not what:
                if u['path'] != a['path']:
                    findings.append(dict(key=key, status='moved', config=config, kind=u['kind'],
                                         note=f"{'::'.join(u['path']) or 'crate'} -> "
                                              f"{'::'.join(a['path']) or 'crate'}"))
                continue
            status = 'changed' if 'code' in what else 'docs changed'
            diff = list(difflib.unified_diff(source_of(up_text, u['toks']),
                                             source_of(ann_text, a['toks']),
                                             'upstream', 'annotated', lineterm='', n=2))
            findings.append(dict(key=key, status=status, config=config, kind=u['kind'],
                                 fp=fingerprint(ucode, acode, udocs, adocs), diff=diff))
        elif a:
            _, acode = split_docs(a['toks'])
            findings.append(dict(key=key, status='added', config=config, kind=a['kind'],
                                 fp=fingerprint(None, acode),
                                 diff=['+' + l for l in source_of(ann_text, a['toks'])]))
        else:
            _, ucode = split_docs(u['toks'])
            findings.append(dict(key=key, status='removed', config=config, kind=u['kind'],
                                 fp=fingerprint(ucode, None),
                                 diff=['-' + l for l in source_of(up_text, u['toks'])]))
    return findings


def compare_files(upstream, annotated):
    """Non-library files: Cargo.toml and tests/ must match, or be approved."""
    findings = []
    names = ['Cargo.toml', 'rust-toolchain.toml']
    for d in ('tests', 'benches', 'examples'):
        for root in (upstream, annotated):
            if os.path.isdir(os.path.join(root, d)):
                names += [os.path.join(d, f) for f in os.listdir(os.path.join(root, d))]
    for name in sorted(set(names)):
        up_p, ann_p = os.path.join(upstream, name), os.path.join(annotated, name)
        u = open(up_p).read().split('\n') if os.path.exists(up_p) else None
        a = open(ann_p).read().split('\n') if os.path.exists(ann_p) else None
        if u == a:
            continue
        diff = list(difflib.unified_diff(u or [], a or [], 'upstream', 'annotated',
                                         lineterm='', n=1))
        status = 'changed' if u and a else ('added' if a else 'removed')
        findings.append(dict(key=f'file {name}', status=status, config='files', kind='file',
                             fp=fingerprint(u, a), diff=diff))
    return findings


# Lines that make code trusted rather than verified, or where the program Verus checks (built
# with `verus_keep_ghost`) and the program that runs (built without it) can differ.
TRUST_RE = re.compile(r'verifier::external\b|external_body|external_fn_specification|'
                      r'assume_specification|\badmit\s*\(|\bassume\s*\(|\baxiom\b|'
                      r'\buninterp\b|verifier::(?:truncate|exec_allows_no_decreases_clause|'
                      r'assume_termination|nonlinear)|\bunsafe\b|verus_keep_ghost')


def trust_markers(upstream, annotated):
    """Lines in the annotated source, not in upstream's, that make something trusted rather
    than verified (or that add `unsafe`)."""
    up_lines = set()
    for root, _, files in os.walk(os.path.join(upstream, 'src')):
        for f in files:
            if f.endswith('.rs'):
                up_lines |= {l.strip() for l in open(os.path.join(root, f))}
    findings = []
    src = os.path.join(annotated, 'src')
    for root, _, files in os.walk(src):
        for f in sorted(files):
            if not f.endswith('.rs'):
                continue
            path = os.path.relpath(os.path.join(root, f), annotated)
            src_lines = open(os.path.join(root, f)).read().split('\n')
            for n, line in enumerate(src_lines, 1):
                s = line.strip()
                if s.startswith('//') or not TRUST_RE.search(s) or s in up_lines:
                    continue
                if s.startswith('#['):  # an attribute: show the item it applies to
                    nxt = next((l.strip() for l in src_lines[n:] if l.strip() and not
                                l.strip().startswith(('#[', '//'))), '')
                    s = f'{s} {nxt}'
                findings.append(dict(key=f'trust {path}: {s}', status='trust marker',
                                     config='source', kind='trust', line=n,
                                     fp=fingerprint(path, s)))
    # one entry per distinct (file, text); keep the first line number
    seen, out = set(), []
    for x in findings:
        if x['key'] not in seen:
            seen.add(x['key'])
            out.append(x)
    return out

# ---------------------------------------------------------------------------------- reporting


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--upstream', default=os.path.join(HERE, '..'))
    ap.add_argument('--annotated', default=os.path.join(HERE, 'slab'))
    ap.add_argument('--approvals', default=os.path.join(HERE, 'approved_changes.json'))
    ap.add_argument('--report', default=os.path.join(HERE, 'changes_report.md'))
    ap.add_argument('--toolchain', default=None)
    ap.add_argument('--config', action='append')
    ap.add_argument('--template', action='store_true',
                    help='add unreviewed findings to the approvals file, with an empty reviewer')
    ap.add_argument('--json', help='also write the findings, with their review status, here')
    args = ap.parse_args()
    upstream, annotated = os.path.abspath(args.upstream), os.path.abspath(args.annotated)
    toolchain = args.toolchain or toolchain_of(annotated)
    configs = args.config or ['--features serde', '--no-default-features']

    findings = []
    with tempfile.TemporaryDirectory(prefix='detect-changes-') as tmp:
        for cfg in configs:
            up = expand(upstream, cfg, toolchain, os.path.join(tmp, 'up'))
            ann = expand(annotated, cfg, toolchain, os.path.join(tmp, 'ann'))
            findings += compare(up, ann, cfg)
    findings += compare_files(upstream, annotated)
    findings += trust_markers(upstream, annotated)

    # merge the same finding seen under several configurations
    merged = {}
    for f in findings:
        k = (f['key'], f['status'], f.get('fp'))
        if k in merged:
            merged[k]['config'] += f", {f['config']}"
        else:
            merged[k] = f
    findings = list(merged.values())

    approvals = json.load(open(args.approvals)) if os.path.exists(args.approvals) else []
    approved = {(e['key'], e['fingerprint']): e for e in approvals if e.get('reviewer')}
    entries = {(e['key'], e['fingerprint']): e for e in approvals}
    for f in findings:
        if f['status'] == 'moved':
            f['review'] = 'info'
        else:
            e = approved.get((f['key'], f['fp']))
            f['review'] = f"approved by {e['reviewer']}" if e else 'UNREVIEWED'
            f['note'] = (e or {}).get('note', '')
            f['agent_note'] = entries.get((f['key'], f['fp']), {}).get('agent_note', '')
    pending = [f for f in findings if f['review'] == 'UNREVIEWED']
    stale = [e for e in approvals if e.get('reviewer') and
             not any(f['key'] == e['key'] and f.get('fp') == e['fingerprint'] for f in findings)]

    order = ['changed', 'added', 'removed', 'docs changed', 'trust marker', 'moved']
    new_fns = {m.group(1) for f in findings if f['status'] == 'added'
               for m in [re.search(r'\bfn (\w+)$', f['key'])] if m}
    findings.sort(key=lambda f: (order.index(f['status']), f['kind'] == 'file', f['key']))
    for f in findings:
        f['hints'] = hints(f.get('diff', []), new_fns) if f['status'] == 'changed' else []
    rep = ['# Changes made by verification', '',
           'Generated by `detect_changes.py`. Each item of the annotated crate, with Verus ghost code',
           'erased (as in a normal build), is compared with the same item upstream, matched by name.',
           'Ignored: formatting, comments, trailing commas, the empty `{}` and `else {}` that erased',
           'proof blocks leave, and which file or module an item is in. Documentation is compared',
           'separately. Hints are heuristics to speed up review, not checks.', '',
           f'- Upstream: `{os.path.relpath(upstream, os.path.dirname(os.path.abspath(args.report)))}`',
           f'- Annotated: `{os.path.relpath(annotated, os.path.dirname(os.path.abspath(args.report)))}`',
           f'- Toolchain: `{toolchain}`; configurations: ' + ', '.join(f'`{c}`' for c in configs), '',
           '| finding | count | unreviewed |', '|---|---|---|']
    for st in order:
        fs = [f for f in findings if f['status'] == st]
        if fs:
            rep.append(f"| {st} | {len(fs)} | {sum(f['review'] == 'UNREVIEWED' for f in fs)} |")
    if stale:
        rep += ['', f'**{len(stale)} approvals match nothing** (the code changed since review, or the '
                'change was undone):'] + [f"- `{e['key']}`" for e in stale]
    titles = {'changed': 'Changed', 'added': 'Added (not upstream)', 'removed': 'Removed',
              'docs changed': 'Documentation changed', 'trust marker': 'Trust boundary (new lines '
              'that make code trusted rather than verified, or add `unsafe`)'}
    for st in order[:-1]:
        fs = [f for f in findings if f['status'] == st]
        if not fs:
            continue
        rep += ['', f'## {titles[st]}']
        for f in fs:
            rep += ['', f"### `{f['key']}`", '',
                    f"Review: **{f['review']}**" + (f" — {f['note']}" if f.get('note') else '')
                    + (f"  \nAgent's explanation (to be checked): {f['agent_note']}"
                       if f.get('agent_note') else '')
                    + f"  \nConfigurations: {f['config']}  \nFingerprint: `{f['fp']}`"
                    + (f"  \nLine: {f['line']}" if f.get('line') else '')
                    + (''.join(f"  \nHint: {h}" for h in f['hints']))]
            if f.get('diff'):
                rep += ['', '```diff'] + f['diff'] + ['```']
    moved = [f for f in findings if f['status'] == 'moved']
    if moved:
        rep += ['', '## Moved, otherwise unchanged (information only)', '',
                '| item | from -> to |', '|---|---|'] + [f"| `{f['key']}` | {f['note']} |" for f in moved]
    open(args.report, 'w').write('\n'.join(rep) + '\n')

    if args.json:
        json.dump([{k: f.get(k) for k in ('key', 'status', 'review', 'fp', 'config', 'hints')}
                   for f in findings], open(args.json, 'w'), indent=1)
    if args.template and pending:
        known = {(e['key'], e['fingerprint']) for e in approvals}
        for f in pending:
            if (f['key'], f['fp']) not in known:
                approvals.append(dict(key=f['key'], status=f['status'], fingerprint=f['fp'],
                                      reviewer='', note=''))
        json.dump(approvals, open(args.approvals, 'w'), indent=2)
        open(args.approvals, 'a').write('\n')

    counts = {s: sum(f['status'] == s for f in findings) for s in order}
    print(', '.join(f'{n} {s}' for s, n in counts.items() if n))
    print(f'{len(pending)} unreviewed, {len(stale)} stale approvals; report: {args.report}')
    sys.exit(1 if pending else 0)


if __name__ == '__main__':
    main()
