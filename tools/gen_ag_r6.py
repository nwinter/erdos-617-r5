#!/usr/bin/env python3
"""Balanced 6-colouring of K_26 from AG(2,5) UNMERGED + one vertex  (N(6) >= 26).

General pattern (Erdős–Gyárfás lower bound): N(r) >= (r-1)^2 + 1 whenever r-1 is a prime power.
Take AG(2, r-1): its (r-1)+1 = r direction classes give an UNMERGED r-colouring of K_{(r-1)^2}
in which each colour class is (r-1) disjoint K_{r-1}'s, so alpha = r-1 <= r -> balanced. Adding
one vertex (edges coloured arbitrarily) leaves every class at alpha <= (r-1)+1 = r, still
balanced. For r=6, r-1=5: K_25 unmerged (each class 5 disjoint K_5s, alpha=5) + vertex 25 -> K_26.

This is a much better lower bound / warm start than climbing cold from below. Output:
data/r6/candidates/balanced_n26.json (then validate with tools/score6 and tools/verify.py).

Usage: python3 tools/gen_ag_r6.py
"""
import json, os
from itertools import combinations

Q = 5          # r-1, a prime power; AG(2,Q) has Q+1 = 6 directions -> 6 colours (r=6)
R = 6

def direction(p, q):
    """Direction (parallel class) of the line through distinct points p,q in F_Q^2; Q..0 or 'inf'."""
    x1, y1 = divmod(p, Q); x2, y2 = divmod(q, Q)
    if x1 == x2:
        return Q                      # vertical class -> colour index Q (=5)
    return ((y2 - y1) * pow(x2 - x1, -1, Q)) % Q   # slope 0..Q-1 -> colours 0..4

def main():
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    n25 = Q * Q                       # 25
    n = n25 + 1                       # 26
    M = [[-1] * n for _ in range(n)]
    # unmerged AG(2,5): colour each old edge by its direction (6 classes, each 5 disjoint K_5s)
    for p, q in combinations(range(n25), 2):
        c = direction(p, q)
        M[p][q] = M[q][p] = c
    # extra vertex 25: any edge colouring keeps every class at alpha <= 6 (theorem); pick a
    # simple deterministic spread so the classes stay balanced in size.
    for i in range(n25):
        c = i % R
        M[i][n25] = M[n25][i] = c
    out = os.path.join(root, "data", "r6", "candidates", "balanced_n26.json")
    os.makedirs(os.path.dirname(out), exist_ok=True)
    json.dump({"r": R, "n": n, "colours": M}, open(out, "w"))
    print("wrote", out)

if __name__ == "__main__":
    main()
