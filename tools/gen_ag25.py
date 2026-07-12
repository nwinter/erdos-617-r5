#!/usr/bin/env python3
"""Generate candidate balanced 5-colourings of K_25 from the affine plane AG(2,5).

Points: F_5 x F_5, indexed p = 5*x + y.
Directions (parallel classes of lines): slopes m in {0,1,2,3,4} (lines y = m x + b)
plus the vertical direction 'inf' (lines x = a). Every pair of distinct points
lies on a unique line, whose direction colours the edge: a 6-colouring where
each class is 5 disjoint K_5's.

To get 5 colours, merge two directions into colour 0; remaining four directions
become colours 1..4. Claim (verified by tools/verify.py, the referee):
the result is balanced (every 6-set of points sees all 5 colours).

Writes data/candidates/ag25_merge_<a>_<b>.json for chosen merges.
Usage: python3 tools/gen_ag25.py [--all-merges]
"""
import json, os, sys
from itertools import combinations

DIRS = [0, 1, 2, 3, 4, "inf"]  # slopes over F_5 plus vertical


def direction(p, q):
    """Direction of the line through distinct points p, q in F_5^2."""
    x1, y1 = divmod(p, 5)
    x2, y2 = divmod(q, 5)
    if x1 == x2:
        return "inf"
    return ((y2 - y1) * pow(x2 - x1, -1, 5)) % 5


def build(merge_pair):
    """5-colouring matrix of K_25: directions in merge_pair -> colour 0, rest -> 1..4."""
    rest = [d for d in DIRS if d not in merge_pair]
    cmap = {d: 0 for d in merge_pair}
    for i, d in enumerate(rest):
        cmap[d] = i + 1
    n = 25
    M = [[-1] * n for _ in range(n)]
    for p, q in combinations(range(n), 2):
        c = cmap[direction(p, q)]
        M[p][q] = M[q][p] = c
    return M


def main():
    outdir = os.path.join(os.path.dirname(__file__), "..", "data", "candidates")
    os.makedirs(outdir, exist_ok=True)
    merges = list(combinations(DIRS, 2)) if "--all-merges" in sys.argv else [(0, 1)]
    for a, b in merges:
        M = build((a, b))
        name = f"ag25_merge_{a}_{b}.json"
        with open(os.path.join(outdir, name), "w") as f:
            json.dump({"r": 5, "n": 25, "colours": M}, f)
        print("wrote", name)


if __name__ == "__main__":
    main()
