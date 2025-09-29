#!/usr/bin/env python3
"""Stream-extract a single snapshot from a large JSON-lines diagnostics file.

The input file is expected to be JSON-lines where each line is a JSON object
with a top-level key "type" equal to either "header" or "combo". A header
contains: {"type":"header","data":{...}} and a combo contains
{"type":"combo","index":N,"data":{...}} as produced by the
instrumented `env.py`.

This script will scan the input file line-by-line, find a header matching the
criteria (by default `allPossibleCombos == 48`), then collect the following
`combo` lines for that header until the expected count is reached. The
collector then writes a compact JSON file with that single snapshot and also
writes a deterministic, canonical mapping for easier diffs.

Usage examples:
  python3 scripts/extract_py_snapshot.py /path/to/py-60.jsonl --target-count 48
  python3 scripts/extract_py_snapshot.py /path/to/py-60.jsonl --match-disjunction-sizes '[ ["D3",4], ["D8",3], ["D12",2], ["D91",2] ]'

The script stops once it has extracted the requested snapshot, so it will not
read the whole huge file in common cases.
"""

import argparse
import json
import ast
import sys
from typing import Any, Dict, List, Tuple


def canonical_full_combo_key(full_combo: List[List[Any]]) -> str:
    # full_combo is something like [["D3", 0], ["D8", 2], ...]
    # Produce a deterministic string key: sorted by label then joined
    pairs = sorted((str(x[0]), int(x[1])) for x in full_combo)
    return "|".join(f"{lbl}:{idx}" for lbl, idx in pairs)


def canonicalize_producers(producers_for_cov: List[Tuple]) -> List[Tuple]:
    # Each producer entry is (factName, argsTuple) or (None,None)
    # For deterministic comparison, convert argsTuple to list and sort by name+args
    normalized = []
    for p in producers_for_cov:
        name, args = p
        if name is None:
            normalized.append([None, None])
        else:
            # args may already be a list or tuple
            normalized.append([name, list(args)])
    # stable sort by name then args
    normalized.sort(key=lambda x: (str(x[0]), json.dumps(x[1], sort_keys=True)))
    return normalized


def extract_snapshot(in_path: str, out_base: str, target_count: int = None, match_disjunction_sizes: Any = None, header_index: int = 0):
    """Stream the input file and extract the header+combo block matching criteria.

    - target_count: find a header where header.data.allPossibleCombos == target_count
    - match_disjunction_sizes: Python literal (list of [label,size]) to match exactly (order-insensitive)
    - header_index: if there are multiple matches, pick the Nth (0-based)

    Returns the path of the compact snapshot JSON written, or None if not found.
    """
    fh_in = open(in_path, "r", encoding="utf-8")
    current_match = -1
    collecting = False
    combo_collect = []
    header_obj = None
    expected_count = None

    for lineno, line in enumerate(fh_in, start=1):
        line = line.strip()
        if not line:
            continue
        try:
            obj = json.loads(line)
        except json.JSONDecodeError:
            # skip malformed lines
            continue

        typ = obj.get("type")
        if typ == "header":
            data = obj.get("data", {})
            apc = data.get("allPossibleCombos")
            dsizes = data.get("disjunctionSizes")

            # Normalize dsizes for comparison: order-insensitive list of pairs
            norm_ds = None
            if dsizes is not None:
                try:
                    norm_ds = sorted((str(x[0]), int(x[1])) for x in dsizes)
                except Exception:
                    norm_ds = dsizes

            match = True
            if target_count is not None and apc != target_count:
                match = False
            if match_disjunction_sizes is not None:
                # match_disjunction_sizes may be provided as Python list or JSON-string
                wanted = match_disjunction_sizes

                try:
                    wanted_norm = sorted((str(x[0]), int(x[1])) for x in wanted)
                except Exception:
                    wanted_norm = wanted

                if norm_ds != wanted_norm:
                    match = False

            if match:
                current_match += 1
                if current_match == header_index:
                    # start collecting following combo records
                    header_obj = data
                    expected_count = apc
                    collecting = True
                    combo_collect = []
                    # If expected_count is None, we can't know when to stop; collect until next header
                    if expected_count is None:
                        expected_count = None
                    # continue to next line for combos
                    continue
                else:
                    # continue scanning for nth match
                    collecting = False
                    continue
            else:
                # header didn't match -> if we were collecting, end collection
                if collecting:
                    break
                collecting = False

        elif typ == "combo" and collecting:
            combo_collect.append(obj.get("data"))
            # If we know expected_count and reached it, stop early
            if expected_count is not None and len(combo_collect) >= expected_count:
                collecting = False
                break

    fh_in.close()

    if header_obj is None:
        return None

    # write compact snapshot file
    snapshot = {"header": header_obj, "combos": combo_collect}
    compact_path = out_base + ".snapshot.json"
    with open(compact_path, "w", encoding="utf-8") as fh:
        json.dump(snapshot, fh, separators=(',', ':'), sort_keys=True)

    # produce canonical mapping for diffs
    canon = {}
    for c in combo_collect:
        full_combo = c.get("full_combo", [])
        covered_by = c.get("covered_by", [])
        producers = c.get("producers", [])

        key = canonical_full_combo_key(full_combo)
        # For each covering observed combo, canonicalize its producers list
        cov_list = []
        for prod_list in producers:
            cov_list.append(canonicalize_producers(prod_list))
        # Sort the list of covering producers deterministically for stable comparison
        # We serialize each covering producers list to JSON string for easy sorting
        cov_list_sorted = sorted(cov_list, key=lambda x: json.dumps(x, sort_keys=True))
        canon[key] = cov_list_sorted

    canon_path = out_base + ".canonical.json"
    with open(canon_path, "w", encoding="utf-8") as fh:
        json.dump(canon, fh, indent=2, sort_keys=True)

    return compact_path, canon_path


if __name__ == "__main__":
    p = argparse.ArgumentParser(description="Extract a snapshot from a large py diagnostics JSON-lines file")
    p.add_argument("input", help="Path to JSON-lines diagnostics file (py-60.jsonl or similar)")
    p.add_argument("--out-base", default="./py_snapshot", help="Base path for output files (adds .snapshot.json and .canonical.json)")
    p.add_argument("--target-count", type=int, default=48, help="Match header with allPossibleCombos == N (default 48)")
    p.add_argument('--match-disjunction-sizes', default=None, help='Optional Python literal for disjunctionSizes to match, e.g. "[[\"D3\",4], [\"D8\",3]]"')
    p.add_argument("--header-index", type=int, default=0, help="If multiple matching headers exist pick the Nth (0-based)")

    args = p.parse_args()

    mds = None
    if args.match_disjunction_sizes:
        try:
            mds = ast.literal_eval(args.match_disjunction_sizes)
        except Exception:
            try:
                mds = json.loads(args.match_disjunction_sizes)
            except Exception:
                print("Could not parse --match-disjunction-sizes; provide a Python literal or JSON array.", file=sys.stderr)
                sys.exit(2)

    res = extract_snapshot(args.input, args.out_base, target_count=args.target_count, match_disjunction_sizes=mds, header_index=args.header_index)
    if res is None:
        print("No matching snapshot/header found.")
        sys.exit(1)
    else:
        compact_path, canon_path = res
        print(f"Wrote compact snapshot to: {compact_path}")
        print(f"Wrote canonical mapping to: {canon_path}")
