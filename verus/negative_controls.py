#!/usr/bin/env python3
"""Negative controls for VERIFICATION.md: inject one bug at a time into a scratch copy of
verus/slab and check that Verus rejects it. Prints one line per mutant: id, verdict,
description, first Verus error and its location (in the mutated copy), and the totals."""
import os, re, shutil, subprocess, sys, tempfile

# Usage: python3 negative_controls.py [M1 M2 ...]   (VERUS=/path/to/verus to override `verus` on PATH)
SRC = os.path.join(os.path.dirname(os.path.abspath(__file__)), "slab")
VERUS = os.environ.get("VERUS", shutil.which("verus") or "verus")
WORK = tempfile.mkdtemp(prefix="slab-mutants-")

MUTANTS = [
    ("M1", "try_remove does not push the freed key (drops `self.next = key`)", "src/lib.rs",
     "                self.len -= 1;\n                self.next = key;\n",
     "                self.len -= 1;\n"),
    ("M2", "try_remove links the freed entry to itself", "src/lib.rs",
     "match mem_replace(entry, Entry::Vacant(self.next))",
     "match mem_replace(entry, Entry::Vacant(key))"),
    ("M3", "insert_at forgets `len += 1`", "src/lib.rs",
     "        self.len += 1;\n        proof {\n            if list.len() > 0 {",
     "        proof {\n            if list.len() > 0 {"),
    ("M4", "insert_at increments `len` first, as upstream does", "src/lib.rs",
     """        if key == self.entries.len() {
            self.entries.push(Entry::Occupied(val));""",
     """        self.len += 1;
        if key == self.entries.len() {
            self.entries.push(Entry::Occupied(val));"""),
    ("M5", "insert_at (reuse case) sets `next` past the slot instead of following its link", "src/lib.rs",
     "                Some(Entry::Vacant(next)) => *next,\n                _ => unreached(),\n            };\n            self.entries[key] = Entry::Occupied(val);",
     "                Some(Entry::Vacant(_next)) => key + 1,\n                _ => unreached(),\n            };\n            self.entries[key] = Entry::Occupied(val);"),
    ("M6", "recreate_vacant_list links each vacant entry to itself", "src/lib.rs",
     "            if let Entry::Vacant(next) = &mut self.entries[i] {\n                *next = self.next;",
     "            if let Entry::Vacant(next) = &mut self.entries[i] {\n                *next = i;"),
    ("M7", "recreate_vacant_list stops one vacant entry early", "src/lib.rs",
     "                if remaining_vacant == 0 {\n                    proof {",
     "                if remaining_vacant <= 1 {\n                    proof {"),
    ("M8", "shrink_to_fit's tail removal skips repairing the vacant list", "src/lib.rs",
     "        if self.entries.len() != len_before {",
     "        if false && self.entries.len() != len_before {"),
    ("M9", "shrink_to_fit's tail removal pops occupied entries", "src/lib.rs",
     "while matches!(self.entries.last(), Some(Entry::Vacant(_)))",
     "while matches!(self.entries.last(), Some(_))"),
    ("M10", "retain removes the entries the closure keeps", "src/lib.rs",
     "            if !keep {\n                self.remove(i);",
     "            if keep {\n                self.remove(i);"),
    ("M11", "get2_mut returns the first key's value twice (other key in one branch)", "src/lib.rs",
     "            entry1 = slice_get_mut(slice2, 0);\n            entry2 = slice_get_mut(slice1, key2);",
     "            entry1 = slice_get_mut(slice2, 0);\n            entry2 = slice_get_mut(slice1, key1 - 1);"),
    ("M12", "contains reports vacant keys", "src/lib.rs",
     "matches!(self.entries.get(key), Some(Entry::Occupied(_)))",
     "matches!(self.entries.get(key), Some(_))"),
    ("M13", "vacant_key returns len", "src/lib.rs",
     "            key == self.next_key(),\n    {\n        self.next\n    }",
     "            key == self.next_key(),\n    {\n        self.len\n    }"),
    ("M14", "Builder::build without the #102 fix (first hole keeps its bogus link)", "src/builder.rs",
     "        } else if let Some(first_vacant_index) = self.first_vacant_index {",
     "        } else if let Some(first_vacant_index) = None::<usize> {"),
    ("M15", "Builder::pair does not mark the list broken when filling a hole", "src/builder.rs",
     "                self.vacant_list_broken = true;\n",
     ""),
    ("M16", "Builder::pair inserts one hole too many", "src/builder.rs",
     "            while slab.entries.len() < key\n",
     "            while slab.entries.len() <= key\n"),
    ("M17", "mem_replace stand-in returns the new value", "src/std_ext.rs",
     "    core::mem::swap(dest, &mut src);\n    src",
     "    core::mem::swap(dest, &mut src);\n    core::mem::swap(dest, &mut src);\n    src"),
    ("M18", "Iter::next does not decrement len", "src/lib.rs",
     "                if let Entry::Occupied(ref v) = *entry {\n                    *len -= 1;\n",
     "                if let Entry::Occupied(ref v) = *entry {\n"),
    ("M19", "Iter::next does not advance the key", "src/lib.rs",
     "                *front += 1;\n",
     ""),
    ("M20", "Iter::next_back yields the key one past the entry", "src/lib.rs",
     "        let key = front + (n - 1);",
     "        let key = front + n;"),
    ("M21", "iter() starts counting keys at 1", "src/lib.rs",
     "            front: 0,\n",
     "            front: 1,\n"),
    ("M22", "index_mut always returns the value at key 0", "src/lib.rs",
     "let value = match vec_get_mut(&mut self.entries, key) {",
     "let value = match vec_get_mut(&mut self.entries, 0) {"),
]

def run(mid, desc, path, old, new, extra=None):
    d = os.path.join(WORK, mid)
    shutil.rmtree(d, ignore_errors=True)
    shutil.copytree(SRC, d, ignore=shutil.ignore_patterns("target", "*.long-type-*"))
    edits = [(path, old, new)] + (extra or [])
    for (p, o, n) in edits:
        fp = os.path.join(d, p)
        s = open(fp).read()
        if s.count(o) != 1:
            return f"{mid:4} SETUP-ERROR: pattern found {s.count(o)}x in {p}"
        s = s.replace(o, n)
        open(fp, "w").write(s)
    r = subprocess.run([VERUS, "--crate-type=lib", "--no-cheating", "--cfg", 'feature="std"',
                        "--triggers-mode", "silent", "src/lib.rs"], cwd=d, capture_output=True, text=True)
    out = r.stdout + r.stderr
    m = re.search(r"verification results:: (\d+) verified, (\d+) errors", out)
    lines = out.splitlines()
    first = ""
    for i, l in enumerate(lines):
        if l.startswith("error") and "aborting" not in l:
            loc = ""
            for j in range(i + 1, min(i + 4, len(lines))):
                mm = re.match(r"\s*--> (\S+)", lines[j])
                if mm:
                    loc = mm.group(1); break
            first = f"{l.removeprefix('error: ')} @ {loc}"
            break
    verdict = "REJECTED" if r.returncode != 0 else "ACCEPTED (!)"
    res = m.group(0) if m else "no verification results"
    return f"{mid:4} {verdict:12} | {desc} | {first} | {res}"

sel = set(sys.argv[1:])
for (mid, desc, path, old, new) in MUTANTS:
    if sel and mid not in sel:
        continue
    extra = None
    if mid == "M4":  # also remove the moved increment, restoring upstream's order
        extra = [("src/lib.rs",
                  "        // Moved after the branch (upstream increments first): the branch does not read `len`.\n        self.len += 1;\n",
                  "")]
    print(run(mid, desc, path, old, new, extra), flush=True)
