#!/usr/bin/env python3
"""Negative controls for detect_changes.py: edit a scratch copy of the annotated crate and check
that benign edits (ghost code, comments, formatting) pass, and that real ones are flagged.

The baseline approves every current finding, so each case starts from a clean check.
Usage (from verus/): python3 test_detect_changes.py
"""
import json
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, 'slab')
CONFIG = '--features serde'  # one configuration keeps the run short

# (name, file, old text, new text, expected): expected is None for a clean check, or
# (status, key) of a finding that must be UNREVIEWED.
CASES = [
    ('unchanged copy', None, None, None, None),
    ('ghost code added (proof block, assertion)', 'src/lib.rs',
     '    pub fn clear(&mut self)',
     '    pub fn clear(&mut self)', None),  # replaced below with a real proof-block insertion
    ('comment and formatting', 'src/trusted.rs',
     '    pub fn capacity(&self) -> usize {\n        self.entries.capacity()\n    }',
     '    pub fn capacity(&self) -> usize {\n        // a new comment\n        self.entries\n'
     '            .capacity()\n    }', None),
    ('condition changed in verified code', 'src/lib.rs',
     '        if key1 > key2 {', '        if key1 >= key2 {',
     ('changed', 'impl Slab :: fn get2_mut')),
    ('call changed in trusted code', 'src/trusted.rs',
     '        self.entries.capacity()\n', '        self.entries.len()\n',
     ('changed', 'impl Slab :: fn capacity')),
    ('executable helper added', 'src/trusted.rs',
     '// ===== T2: raw pointers and unchecked access =====',
     'fn helper() -> usize {\n    1\n}\n\n// ===== T2: raw pointers and unchecked access =====',
     ('added', 'fn helper')),
    ('code hidden from Verus with cfg(not(verus_keep_ghost))', 'src/trusted.rs',
     '// ===== T2: raw pointers and unchecked access =====',
     '#[cfg(not(verus_keep_ghost))]\nimpl<T> Slab<T> {\n    pub fn extra(&self) {}\n}\n\n'
     '// ===== T2: raw pointers and unchecked access =====',
     ('trust marker', 'trust src/trusted.rs: #[cfg(not(verus_keep_ghost))] impl<T> Slab<T> {')),
    ('verified function made trusted (external_body)', 'src/lib.rs',
     '    pub fn is_empty(&self)', '    #[verifier::external_body]\n    pub fn is_empty(&self)',
     ('trust marker', 'trust src/lib.rs: #[verifier::external_body] pub fn is_empty(&self) -> (empty: bool)')),
    ('documentation changed', 'src/lib.rs',
     '    /// Return the number of stored values.', '    /// Return the number of values.',
     ('docs changed', 'impl Slab :: fn len')),
]


def run(annotated, approvals, out_json):
    cmd = [sys.executable, os.path.join(HERE, 'detect_changes.py'), '--annotated', annotated,
           '--upstream', os.path.join(HERE, '..'), '--approvals', approvals, '--config', CONFIG,
           '--report', out_json + '.md', '--json', out_json]
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode not in (0, 1):
        sys.exit(f'detect_changes.py failed:\n{r.stdout}{r.stderr}')
    return json.load(open(out_json))


def main():
    tmp = tempfile.mkdtemp(prefix='detect-changes-test-')
    copy = os.path.join(tmp, 'slab')
    ignore = shutil.ignore_patterns('target', '.verus-solver-log')
    shutil.copytree(SRC, copy, ignore=ignore)

    # baseline: approve everything the detector reports today
    approvals = os.path.join(tmp, 'approvals.json')
    subprocess.run([sys.executable, os.path.join(HERE, 'detect_changes.py'), '--annotated', copy,
                    '--upstream', os.path.join(HERE, '..'), '--approvals', approvals,
                    '--config', CONFIG, '--report', os.path.join(tmp, 'r.md'), '--template'],
                   capture_output=True, text=True)
    entries = json.load(open(approvals))
    for e in entries:
        e['reviewer'] = 'baseline'
    json.dump(entries, open(approvals, 'w'))

    failures = 0
    for name, path, old, new, expected in CASES:
        shutil.rmtree(copy)
        shutil.copytree(SRC, copy, ignore=ignore)
        if name.startswith('ghost code added'):  # a proof block and a ghost assertion
            path = 'src/lib.rs'
            text = open(os.path.join(copy, path)).read()
            i = text.index('    pub fn clear(&mut self)')
            j = text.index('    {\n', i) + len('    {\n')
            text = text[:j] + '        proof {\n            assert(true);\n        }\n' + text[j:]
            open(os.path.join(copy, path), 'w').write(text)
        elif path:
            p = os.path.join(copy, path)
            text = open(p).read()
            if text.count(old) != 1:
                print(f'SETUP ERROR  {name}: pattern found {text.count(old)} times')
                failures += 1
                continue
            open(p, 'w').write(text.replace(old, new))
        findings = run(copy, approvals, os.path.join(tmp, 'out.json'))
        unreviewed = [(f['status'], f['key']) for f in findings if f['review'] == 'UNREVIEWED']
        if expected is None:
            ok = not unreviewed
            detail = 'clean' if ok else f'unexpected: {unreviewed}'
        else:
            ok = expected in unreviewed
            detail = f'flagged {expected[0]} `{expected[1]}`' if ok else f'missed; got {unreviewed}'
        failures += not ok
        print(f"{'PASS' if ok else 'FAIL':<5} {name}: {detail}", flush=True)
    shutil.rmtree(tmp)
    print(f'{len(CASES) - failures}/{len(CASES)} passed')
    sys.exit(1 if failures else 0)


if __name__ == '__main__':
    main()
