#!/usr/bin/env python3
"""Independent checker for claimed witnesses of the graph-level probes.
Pure stdlib, no SAT dependencies — validates against the plain definitions.

Input: JSON on stdin or as a file argument:
  {"n": 25, "edges": [[i,j],...], "T": [v,...](optional)}

Checks and reports:
  alpha(G) (exact, B&B), max 6-set edge count (cap), e(G),
  and if T given: alpha(G - T), edges spanned inside T.

Usage: .venv/bin/python tools/check_witness.py [FILE.json]
"""
import json, sys
from itertools import combinations


def alpha_exact(n, adj, verts=None):
    verts = sorted(verts if verts is not None else range(n))
    best = 0

    def rec(cand, cur):
        nonlocal best
        if cur > best:
            best = cur
        if not cand or cur + len(cand) <= best:
            return
        v = cand[0]
        rec([u for u in cand[1:] if not adj[v][u]], cur + 1)
        rec(cand[1:], cur)

    rec(verts, 0)
    return best


def main():
    d = json.load(open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin)
    n = d["n"]
    adj = [[False] * n for _ in range(n)]
    for i, j in d["edges"]:
        adj[i][j] = adj[j][i] = True
    e = len(d["edges"])
    a = alpha_exact(n, adj)
    dense = 0
    worst = 0
    for S in combinations(range(n), 6):
        k = sum(adj[x][y] for x, y in combinations(S, 2))
        worst = max(worst, k)
        if k >= 12:
            dense += 1
    print(f"n={n}, e={e}, alpha={a}, max 6-set edges={worst}, dense(>=12) 6-sets={dense}")
    if "T" in d:
        T = d["T"]
        rest = [v for v in range(n) if v not in T]
        aT = alpha_exact(n, adj, rest)
        own = sum(1 for i, j in d["edges"] if i in T and j in T)
        print(f"T={sorted(T)}: alpha(G-T)={aT}, own edges={own}")


if __name__ == "__main__":
    main()
