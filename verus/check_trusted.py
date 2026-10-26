#!/usr/bin/env python3
"""Check that slab/src/trusted.rs is upstream code: every item in it (with its doc comments and
attributes) must appear verbatim in upstream ../src/lib.rs. The `shrink_to_fit` shell is the one
expected exception. Usage: python3 check_trusted.py (from verus/)."""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
UPSTREAM = open(os.path.join(HERE, '..', 'src', 'lib.rs')).read()
LINES = open(os.path.join(HERE, 'slab', 'src', 'trusted.rs')).read().split('\n')
EXPECTED_CHANGED = {'shrink_to_fit'}


def parse(block, indent=''):
    """Split `block` into (prefix, body) items at the given indentation."""
    items, prefix, i = [], [], 0
    while i < len(block):
        line = block[i]
        rest = line[len(indent):]
        if not line.strip() or (line.startswith(indent) and rest.startswith(('//', '#['))):
            prefix.append(line)
            i += 1
            continue
        body = [line]
        if not line.rstrip().endswith(('{}', ';')):
            i += 1
            while block[i] != indent + '}':
                body.append(block[i])
                i += 1
            body.append(block[i])
        items.append((prefix, body))
        prefix = []
        i += 1
    return items


start = next(i for i, line in enumerate(LINES) if line.startswith('// ====='))
units = []
for prefix, body in parse(LINES[start:]):
    if body[0] == 'impl<T> Slab<T> {':
        units += parse(body[1:-1], '    ')  # check each method on its own
    else:
        units.append((prefix, body))

failures = 0
for prefix, body in units:
    kept = [line for line in prefix if line.strip().startswith(('///', '#['))]
    head = re.sub(r'\s+', ' ', body[0].strip())
    name = re.search(r'fn (\w+)', '\n'.join(body))
    if '\n'.join(kept + body) in UPSTREAM:
        status = 'verbatim'
    elif name and name.group(1) in EXPECTED_CHANGED and head.startswith('pub fn'):
        status = 'changed (expected)'
    else:
        status = 'CHANGED'
        failures += 1
    print(f'{status:<20} {head}')
print(f'{len(units)} items, {failures} unexpected changes')
sys.exit(1 if failures else 0)
