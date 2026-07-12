#!/usr/bin/env python3
"""probe_h4 with one sound residual-symmetry cut (v2, for faster UNSAT).

Same question as probe_h4.py: balanced 5-colouring of K_25 + colour 0 +
T = {0,1,2,3} with alpha(G_0 - T) <= 4?

Residual symmetry after the WLOG: S_4 (within T) x S_21 (vertices 4..24) x
S_4 (colours 1..4). Cuts on top of a WLOG must compose with it and each
other; outside-sorting relabels rows (breaking T-internal cuts) and value-
based sorts conflict with colour precedence, so we include exactly ONE cut,
sound in isolation:

  (iii) outside vertices sorted: colour(0,w) <= colour(0,w+1) for w=4..23.
        Permutations of {4..24} fix T pointwise, fix the colour-0
        designation, map the h4 clause family C({4..24},5) to itself, and
        permute the values (colour(0,w))_w freely; hence every model has a
        sorted representative. Kills most of S_21.

Usage: python3 tools/probe_h4b.py --out X.cnf
"""
import argparse, json, sys, os
from itertools import combinations

sys.path.insert(0, os.path.dirname(__file__))
from sat_encode import edge_order


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    r, n = 5, 25
    edges = edge_order(n)
    m = len(edges)
    eidx = {e: k for k, e in enumerate(edges)}
    v = lambda k, c: k * r + c + 1
    nv = m * r
    clauses = []
    for k in range(m):
        clauses.append([v(k, c) for c in range(r)])
        for c1 in range(r):
            for c2 in range(c1 + 1, r):
                clauses.append([-v(k, c1), -v(k, c2)])
    for S in combinations(range(n), 6):
        ks = [eidx[(x, y)] for x, y in combinations(S, 2)]
        for c in range(r):
            clauses.append([v(k, c) for k in ks])
    # h4 condition: alpha(G_0 - {0,1,2,3}) <= 4
    for S in combinations(range(4, n), 5):
        clauses.append([v(eidx[(x, y)], 0) for x, y in combinations(S, 2)])
    # (iii) outside vertices sorted by colour(0, w)
    for w in range(4, n - 1):
        k1, k2 = eidx[(0, w)], eidx[(0, w + 1)]
        for c in range(1, r):
            for cp in range(c):
                clauses.append([-v(k1, c), -v(k2, cp)])
    with open(a.out, "w") as f:
        f.write(f"p cnf {nv} {len(clauses)}\n")
        for cl in clauses:
            f.write(" ".join(map(str, cl)) + " 0\n")
    with open(a.out.replace(".cnf", "") + ".map.json", "w") as f:
        json.dump({"r": r, "n": n, "edges": edges, "sym": ["rowsort-outside"]}, f)
    print(f"wrote {a.out}: {nv} vars, {len(clauses)} clauses")


if __name__ == "__main__":
    main()
