import sys
import json
import re
import ast

def normalize_combo(obj):
    # obj can be dict, list of pairs, or list of 2-tuples
    pairs = []
    if isinstance(obj, dict):
        pairs = sorted(obj.items())
    elif isinstance(obj, list):
        # list of pairs or list of {"D":n} etc
        if all(isinstance(x, list) or isinstance(x, tuple) for x in obj):
            pairs = sorted((str(k), int(v)) for (k, v) in obj)
        elif all(isinstance(x, dict) for x in obj):
            # flatten list of single-key dicts
            flat = {}
            for d in obj:
                flat.update(d)
            pairs = sorted(flat.items())
        else:
            # fallback: try to interpret as list of 2-tuples via ast earlier
            pairs = sorted((str(k), int(v)) for (k, v) in obj)
    else:
        raise ValueError("Unknown combo object: %r" % (obj,))
    return tuple(f"{k}={v}" for (k,v) in pairs)

def extract_python_contradictions(path):
    seen = set()
    total_lines = 0
    with open(path, 'r') as f:
        for line in f:
            total_lines += 1
            line = line.strip()
            if not line:
                continue
            try:
                obj = json.loads(line)
            except Exception:
                continue
            t = obj.get('type') or obj.get('msg') or ''
            if isinstance(t, str) and 'contradict' in t.lower() or t == 'contradiction':
                combo = obj.get('combo') or obj.get('goal_combo') or obj.get('cover_combo')
                if combo is None:
                    # sometimes stored under 'combo_str'
                    combo = obj.get('combo_str')
                if combo is None:
                    continue
                try:
                    nc = normalize_combo(combo)
                    seen.add(nc)
                except Exception:
                    # try parsing string
                    try:
                        parsed = ast.literal_eval(combo) if isinstance(combo,str) else combo
                        nc = normalize_combo(parsed)
                        seen.add(nc)
                    except Exception:
                        pass
    return seen, total_lines

def extract_haskell_recorded(path):
    seen = set()
    last_allcovered = None
    pattern = re.compile(r'recording goal combo.*?->\s*(\[[^\]]*\])')
    allcov_re = re.compile(r'allCovered\s*=\s*(True|False)')
    with open(path, 'r') as f:
        for line in f:
            m = pattern.search(line)
            if m:
                txt = m.group(1)
                try:
                    parsed = ast.literal_eval(txt)
                    nc = normalize_combo(parsed)
                    seen.add(nc)
                except Exception:
                    # try to transform Haskell tuple style ("D3",1) -> ('D3',1)
                    try:
                        parsed = ast.literal_eval(txt.replace('(', '(').replace(')', ')'))
                        nc = normalize_combo(parsed)
                        seen.add(nc)
                    except Exception:
                        pass
            m2 = allcov_re.search(line)
            if m2:
                last_allcovered = True if m2.group(1) == 'True' else False
            # also detect explicit "DEBUG allCovered = True" phrase
            if 'allCovered = True' in line:
                last_allcovered = True
            elif 'allCovered = False' in line:
                last_allcovered = False
    return seen, last_allcovered

def main():
    if len(sys.argv) != 3:
        print("Usage: python3 compare_coverage.py python_run_60.jsonl haskell_log.txt")
        sys.exit(2)
    py_path = sys.argv[1]
    hs_path = sys.argv[2]
    py_seen, py_lines = extract_python_contradictions(py_path)
    hs_seen, hs_allcov = extract_haskell_recorded(hs_path)

    only_hs = sorted(hs_seen - py_seen)
    only_py = sorted(py_seen - hs_seen)
    both = sorted(hs_seen & py_seen)

    print("Python JSONL file:", py_path)
    print("Haskell log file:", hs_path)
    print()
    print(f"Python contradiction combos: {len(py_seen)} (scanned {py_lines} lines)")
    print(f"Haskell recorded combos: {len(hs_seen)}")
    print("Haskell reported allCovered =", hs_allcov)
    print()
    print("Combos recorded by Haskell but NOT by Python (sample up to 50):")
    for c in only_hs[:50]:
        print("  ", c)
    if len(only_hs) > 50:
        print("  ... +", len(only_hs)-50, "more")
    print()
    print("Combos recorded by Python but NOT by Haskell (sample up to 50):")
    for c in only_py[:50]:
        print("  ", c)
    if len(only_py) > 50:
        print("  ... +", len(only_py)-50, "more")
    print()
    print("Combos recorded by both (count):", len(both))
    print()
    if hs_allcov:
        print("NOTE: Haskell claimed allCovered = True. If Python has fewer combos than Haskell or Python leaves combos uncovered, Haskell is over-claiming.")
    else:
        print("NOTE: Haskell did NOT claim allCovered = True (or it wasn't detected).")

if __name__ == '__main__':
    main()
