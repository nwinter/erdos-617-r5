#!/usr/bin/env python3
"""SAT probe: does a balanced 5-colouring of K_25 exist with NO monochromatic
K_5 in any colour? (Empirically every sampled balanced colouring has exactly
25 mono-K_5s, 5 per class; UNSAT here would prove mono-K_5s are forced.)

Also supports --n and --allow-colours k (forbid mono K_5 only in colours >= k).

Usage: python3 tools/probe_nomono.py --n 25 --out X.cnf
"""
import argparse, json, sys, os
from itertools import combinations

sys.path.insert(0, os.path.dirname(__file__))
from sat_encode import build


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=25)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    r = 5
    nv, clauses, edges = build(r, a.n, {"rowsort", "colourprec"})
    eidx = {e: i for i, e in enumerate(edges)}
    v = lambda k, c: k * r + c + 1
    extra = 0
    for c in range(r):
        for S in combinations(range(a.n), 5):
            clauses.append([-v(eidx[(x, y)], c) for x, y in combinations(S, 2)])
            extra += 1
    with open(a.out, "w") as f:
        f.write(f"p cnf {nv} {len(clauses)}\n")
        for cl in clauses:
            f.write(" ".join(map(str, cl)) + " 0\n")
    with open(a.out.replace(".cnf", "") + ".map.json", "w") as f:
        json.dump({"r": r, "n": a.n, "edges": edges, "sym": ["rowsort", "colourprec"]}, f)
    print(f"wrote {a.out}: {nv} vars, {len(clauses)} clauses ({extra} no-mono-K5 clauses)")


if __name__ == "__main__":
    main()
