#!/usr/bin/env python3
"""Two-vertex extension solver: given a balanced 5-colouring of K_n (n=24
intended), decide whether TWO new vertices x,y can be added (all 2n+1 new
edges coloured) so the K_{n+2} colouring is balanced.

Constraints (r=5): with old vertex set V, new x,y and edge-colour z = c(xy):
  A. 6-sets {x} u F, F in C(V,5):  colours(F) u phi_x(F)  = all 5
  B. 6-sets {y} u F:               colours(F) u phi_y(F)  = all 5
  C. 6-sets {x,y} u G, G in C(V,4): colours(G) u phi_x(G) u phi_y(G) u {z} = all
(A/B are the 1-extension systems; C couples them.)

Usage: .venv/bin/python tools/extend2.py CAND24.json [--out PREFIX]
"""
import sys, json
from itertools import combinations
from pysat.solvers import Cadical195


def main():
    path = sys.argv[1]
    prefix = None
    if "--out" in sys.argv:
        prefix = sys.argv[sys.argv.index("--out") + 1]
    d = json.load(open(path))
    r, n, M = d["r"], d["n"], d["colours"]
    assert r == 5
    vx = lambda p, c: p * r + c + 1
    vy = lambda p, c: (n + p) * r + c + 1
    vz = lambda c: 2 * n * r + c + 1
    s = Cadical195()
    for base in (vx, vy):
        for p in range(n):
            s.add_clause([base(p, c) for c in range(r)])
            for c1 in range(r):
                for c2 in range(c1 + 1, r):
                    s.add_clause([-base(p, c1), -base(p, c2)])
    s.add_clause([vz(c) for c in range(r)])
    for c1 in range(r):
        for c2 in range(c1 + 1, r):
            s.add_clause([-vz(c1), -vz(c2)])
    full = (1 << r) - 1
    ncl = 0
    for F in combinations(range(n), 5):
        seen = 0
        for a, b in combinations(F, 2):
            seen |= 1 << M[a][b]
        for c in range(r):
            if not (seen >> c) & 1:
                s.add_clause([vx(p, c) for p in F]); ncl += 1
                s.add_clause([vy(p, c) for p in F]); ncl += 1
    for G in combinations(range(n), 4):
        seen = 0
        for a, b in combinations(G, 2):
            seen |= 1 << M[a][b]
        for c in range(r):
            if not (seen >> c) & 1:
                s.add_clause([vx(p, c) for p in G] + [vy(p, c) for p in G] + [vz(c)])
                ncl += 1
    print(f"{path}: 2-extension instance {2*n*r+r} vars, {ncl} covering clauses")
    if s.solve():
        m = set(l for l in s.get_model() if l > 0)
        phix = [next(c for c in range(r) if vx(p, c) in m) for p in range(n)]
        phiy = [next(c for c in range(r) if vy(p, c) in m) for p in range(n)]
        z = next(c for c in range(r) if vz(c) in m)
        print(f"SAT: phix={phix} phiy={phiy} z={z}")
        if prefix:
            M2 = [row[:] + [phix[i], phiy[i]] for i, row in enumerate(M)]
            M2.append(phix + [-1, z])
            M2.append(phiy + [z, -1])
            out = f"{prefix}.json"
            json.dump({"r": r, "n": n + 2, "colours": M2}, open(out, "w"))
            print(f"wrote {out} - RUN tools/verify.py NOW")
    else:
        print("UNSAT: no 2-vertex extension")
    s.delete()


if __name__ == "__main__":
    main()
