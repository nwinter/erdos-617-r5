#!/usr/bin/env python3
"""SAT probe: does a balanced r-colouring of K_n exist in which the first k
colour classes have NO independent r-set (i.e. alpha(G_c) <= r-1 for c < k)?

Motivation (NOTES.md): a class with alpha <= 4 (r=5) consumes none of the
one-vertex-extension budget, so such colourings of K_25 would be prime
candidates for extension to K_26. Conversely UNSAT here is a structural lemma
("every class of a balanced 5-colouring of K_25 has alpha exactly 5").

Encoding: base CNF from sat_encode.build (one-hot + covering + symmetry;
colour symmetry restricted to the classes NOT pinned dense, i.e. colourprec
is dropped when k>0 — pinning colours 0..k-1 breaks S_r anyway; rowsort kept,
it only permutes vertices). Extra clauses: for c < k, every r-subset contains
an edge of colour c.

Usage: python3 tools/probe_dense.py --r 5 --n 25 --dense 1 --out X.cnf
"""
import argparse, json, sys, os
from itertools import combinations

sys.path.insert(0, os.path.dirname(__file__))
from sat_encode import build, edge_order


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--r", type=int, required=True)
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--dense", type=int, required=True, help="first k classes must have alpha<=r-1")
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    # rowsort is vertex-only, sound regardless of colour pinning; colourprec
    # would clash with the asymmetric role of colours 0..k-1, so: keep
    # colour-permutation freedom only among the dense block and among the rest;
    # simplest sound choice: no colourprec. (Dense classes are interchangeable,
    # and so are the others; we accept that residual symmetry.)
    nv, clauses, edges = build(a.r, a.n, {"rowsort"})
    eidx = {e: i for i, e in enumerate(edges)}
    v = lambda k, c: k * a.r + c + 1
    extra = 0
    for c in range(a.dense):
        for S in combinations(range(a.n), a.r):
            clauses.append([v(eidx[(x, y)], c) for x, y in combinations(S, 2)])
            extra += 1
    with open(a.out, "w") as f:
        f.write(f"p cnf {nv} {len(clauses)}\n")
        for cl in clauses:
            f.write(" ".join(map(str, cl)) + " 0\n")
    with open(a.out.replace(".cnf", "") + ".map.json", "w") as f:
        json.dump({"r": a.r, "n": a.n, "edges": edges, "sym": ["rowsort"], "dense": a.dense}, f)
    print(f"wrote {a.out}: {nv} vars, {len(clauses)} clauses ({extra} dense clauses, k={a.dense})")


if __name__ == "__main__":
    main()
