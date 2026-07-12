#!/usr/bin/env python3
"""CNF encoder for the balanced r-colouring problem on K_n.

Encodes: does K_n admit an r-colouring of its edges such that every
(r+1)-subset of vertices sees all r colours?  (SAT = balanced colouring exists.)

Variables: v[e][c] = "edge e has colour c", e in lex order with all edges at
vertex 0 first: (0,1),(0,2),...,(0,n-1),(1,2),(1,3),...  One-hot per edge.
Covering: for every (r+1)-subset S and colour c: OR of v[e][c] over the
C(r+1,2) edges inside S.

Symmetry breaking (optional, each SOUND for UNSAT — every colouring has an
image under the colour/vertex symmetry group satisfying them; see NOTES.md):

  rowsort    Vertices 1..n-1 sorted by colour of their edge to vertex 0:
             colour(0,j) <= colour(0,j+1). Sound: relabel vertices 1..n-1.
  colourprec Colours numbered by first appearance along the edge order:
             edge e_k may use colour c>0 only if colour c-1 appears among
             e_1..e_{k-1}. Aux vars u[k][c] = "colour c used among first k
             edges". Sound: relabel colours by first appearance; composes
             with rowsort (sort vertices by the relabelled colour).

Usage:
  python3 tools/sat_encode.py --r 5 --n 26 --sym rowsort,colourprec --out X.cnf
  (writes X.cnf and X.map.json for tools/sat_decode.py)
"""
import argparse, json, sys
from itertools import combinations


def edge_order(n):
    """(0,1),(0,2),...,(0,n-1), then remaining edges lex."""
    edges = [(0, j) for j in range(1, n)]
    edges += [(i, j) for i in range(1, n) for j in range(i + 1, n)]
    return edges


def build(r, n, sym):
    edges = edge_order(n)
    m = len(edges)
    eidx = {e: k for k, e in enumerate(edges)}
    nv = m * r
    v = lambda k, c: k * r + c + 1
    clauses = []

    # one-hot per edge
    for k in range(m):
        clauses.append([v(k, c) for c in range(r)])
        for c1 in range(r):
            for c2 in range(c1 + 1, r):
                clauses.append([-v(k, c1), -v(k, c2)])

    # covering: every (r+1)-set sees every colour
    for S in combinations(range(n), r + 1):
        ks = [eidx[(a, b)] for a, b in combinations(S, 2)]
        for c in range(r):
            clauses.append([v(k, c) for k in ks])

    if "rowsort" in sym:
        # colour(0,j) <= colour(0,j+1): forbid v[j-1][c] & v[j][c'] with c' < c
        for j in range(1, n - 1):
            k1, k2 = eidx[(0, j)], eidx[(0, j + 1)]
            for c in range(1, r):
                for cp in range(c):
                    clauses.append([-v(k1, c), -v(k2, cp)])

    if "colourprec" in sym:
        # u[k][c] (k=1..m): colour c used among edges e_0..e_{k-1}
        base = nv
        u = lambda k, c: base + (k - 1) * r + c + 1
        nv += m * r
        for k in range(1, m + 1):
            for c in range(r):
                # u[k][c] <- u[k-1][c];  u[k][c] <- v[k-1][c]
                if k > 1:
                    clauses.append([-u(k - 1, c), u(k, c)])
                clauses.append([-v(k - 1, c), u(k, c)])
                # closure (not logically needed for symmetry soundness, keeps
                # u tight): u[k][c] -> u[k-1][c] or v[k-1][c]
                cl = [-u(k, c), v(k - 1, c)]
                if k > 1:
                    cl.append(u(k - 1, c))
                clauses.append(cl)
        # edge k may use colour c>0 only if c-1 used before: v[k][c] -> u[k][c-1]
        for k in range(1, m):
            for c in range(1, r):
                clauses.append([-v(k, c), u(k, c - 1)])
        # edge 0 must be colour 0
        clauses.append([v(0, 0)])

    return nv, clauses, edges


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--r", type=int, required=True)
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--sym", default="", help="comma list: rowsort,colourprec")
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    sym = set(s for s in a.sym.split(",") if s)
    nv, clauses, edges = build(a.r, a.n, sym)
    with open(a.out, "w") as f:
        f.write(f"p cnf {nv} {len(clauses)}\n")
        for cl in clauses:
            f.write(" ".join(map(str, cl)) + " 0\n")
    with open(a.out.replace(".cnf", "") + ".map.json", "w") as f:
        json.dump({"r": a.r, "n": a.n, "edges": edges, "sym": sorted(sym)}, f)
    print(f"wrote {a.out}: {nv} vars, {len(clauses)} clauses (r={a.r}, n={a.n}, sym={sorted(sym)})")


if __name__ == "__main__":
    main()
