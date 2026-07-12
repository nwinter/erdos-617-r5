#!/usr/bin/env python3
"""Structural analysis of a (possibly unbalanced) 5-colouring of K_n.

Reports: violation count and structure (which colours go missing, vertex
involvement), per-class edge count, independence number (exact, via simple
branch and bound), K_6 count, and the 6-set edge-density cap violations.

Usage: python3 tools/analyze26.py FILE.json
"""
import json, sys
from itertools import combinations


def alpha_atmost(adj, n, k):
    """Is alpha(G) <= k? Exact small B&B on the complement-greedy order."""
    best = [0]
    verts = list(range(n))

    def grow(cand, size):
        if size > k:
            return False  # found independent set bigger than k
        if not cand:
            best[0] = max(best[0], size)
            return True
        if size + len(cand) <= k:  # cannot exceed k from here; prune as OK
            return True
        v = cand[0]
        rest = cand[1:]
        # branch 1: take v
        newc = [u for u in rest if not adj[v][u]]
        if not grow(newc, size + 1):
            return False
        # branch 2: skip v (only useful if we could still exceed k)
        if size + len(rest) > k:
            if not grow(rest, size):
                return False
        return True

    return grow(verts, 0)


def main():
    d = json.load(open(sys.argv[1]))
    M, n, r = d["colours"], d["n"], d["r"]
    viol = []
    for S in combinations(range(n), 6):
        seen = set(M[a][b] for a, b in combinations(S, 2))
        if len(seen) < r:
            viol.append((S, [c for c in range(r) if c not in seen]))
    print(f"n={n}: {len(viol)} violated 6-sets")
    from collections import Counter
    mc = Counter(c for _, miss in viol for c in miss)
    print("missing-colour histogram:", dict(sorted(mc.items())))
    vc = Counter(v for S, _ in viol for v in S)
    print("top-8 vertices by violation count:", vc.most_common(8))
    for c in range(r):
        adj = [[M[i][j] == c for j in range(n)] for i in range(n)]
        e = sum(adj[i][j] for i in range(n) for j in range(i + 1, n))
        a5 = alpha_atmost(adj, n, 5)
        k6 = sum(1 for S in combinations(range(n), 6)
                 if all(adj[x][y] for x, y in combinations(S, 2)))
        dense = sum(1 for S in combinations(range(n), 6)
                    if sum(adj[x][y] for x, y in combinations(S, 2)) >= 12)
        print(f"class {c}: {e} edges, alpha<=5: {a5}, K_6 count: {k6}, dense(>=12e) 6-sets: {dense}")


if __name__ == "__main__":
    main()
