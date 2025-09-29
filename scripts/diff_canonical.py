#!/usr/bin/env python3
"""Compare two canonical mapping JSON files produced by extract_py_snapshot.py.

Each file is expected to be a JSON object mapping canonical full-combo keys to a
sorted list of covering-producers lists (each covering-producers list is a list
of [factName, [args...]] entries). This script reports:
 - keys present in A but not B and vice-versa
 - for common keys, whether the covering producers sets differ (and prints a
   concise summary of differences)

Usage:
  python3 scripts/diff_canonical.py a.canonical.json b.canonical.json

Output is written to stdout; exit code 0 if no differences, 2 if differences
found.
"""

import json
import sys
from typing import Any, Dict, List


def load(path: str) -> Dict[str, Any]:
    with open(path, 'r', encoding='utf-8') as fh:
        return json.load(fh)


def canonicalize_entry(e):
    # Convert a producers-cover list to a deterministic JSON string for comparison
    return json.dumps(e, sort_keys=True)


def main(a_path: str, b_path: str) -> int:
    A = load(a_path)
    B = load(b_path)

    keysA = set(A.keys())
    keysB = set(B.keys())

    onlyA = sorted(keysA - keysB)
    onlyB = sorted(keysB - keysA)

    diffs = []

    common = sorted(keysA & keysB)
    for k in common:
        a_val = A[k]
        b_val = B[k]
        # both are lists of covering producers; compare as sets of JSON strings
        a_set = set(canonicalize_entry(x) for x in a_val)
        b_set = set(canonicalize_entry(x) for x in b_val)
        if a_set != b_set:
            diffs.append((k, sorted(a_set - b_set), sorted(b_set - a_set)))

    if not onlyA and not onlyB and not diffs:
        print("No differences found; canonical mappings are identical.")
        return 0

    print("Differences detected:")
    if onlyA:
        print(f" Keys only in {a_path}: {len(onlyA)}")
        for k in onlyA[:20]:
            print("  ", k)
        if len(onlyA) > 20:
            print("   (...)")
    if onlyB:
        print(f" Keys only in {b_path}: {len(onlyB)}")
        for k in onlyB[:20]:
            print("  ", k)
        if len(onlyB) > 20:
            print("   (...)")

    if diffs:
        print(f" Keys with differing covering-producers: {len(diffs)}")
        for k, a_extra, b_extra in diffs[:50]:
            print("- key:", k)
            if a_extra:
                print(f"   entries in {a_path} but not {b_path}: {len(a_extra)}")
                for s in a_extra[:5]:
                    print("     ", s)
                if len(a_extra) > 5:
                    print("     (...)")
            if b_extra:
                print(f"   entries in {b_path} but not {a_path}: {len(b_extra)}")
                for s in b_extra[:5]:
                    print("     ", s)
                if len(b_extra) > 5:
                    print("     (...)")
    return 2


if __name__ == '__main__':
    if len(sys.argv) != 3:
        print("Usage: diff_canonical.py a.canonical.json b.canonical.json", file=sys.stderr)
        sys.exit(2)
    rc = main(sys.argv[1], sys.argv[2])
    sys.exit(rc)
