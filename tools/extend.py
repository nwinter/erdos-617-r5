#!/usr/bin/env python3
"""One-vertex extension solver for balanced r-colourings.

Given a balanced r-colouring of K_n (JSON, verify.py format), decide whether a
new vertex x can be joined to all n old vertices so that the K_{n+1} colouring
is balanced. Only (r+1)-subsets containing x are at issue; such a subset is
{x} ∪ F for an r-subset F of old vertices, and it sees all r colours iff

    colours_inside(F)  ∪  {φ(p) : p ∈ F}  =  {0..r-1}

where φ(p) is the colour of edge {x,p}. So for every r-subset F with missing
colour set M(F) ≠ ∅, the map φ must use every colour of M(F) somewhere on F.
This is encoded to SAT (vars v[p,c] = "φ(p)=c") and solved with pysat.

Usage:
    .venv/bin/python tools/extend.py CANDIDATE.json [--enumerate K] [--out PREFIX]

Prints stats on the constraint system, then SAT/UNSAT. On SAT, writes the
extended colouring(s) as JSON (new vertex has index n) — run tools/verify.py
on them immediately; verify.py remains the referee.
"""
import sys, json, os
from itertools import combinations
from pysat.solvers import Cadical195


def load(path):
    with open(path) as f:
        d = json.load(f)
    return d["r"], d["n"], d["colours"]


def missing_sets(r, n, M):
    """Yield (F, missing) for every r-subset F of range(n) with missing != 0 (bitmask)."""
    full = (1 << r) - 1
    out = []
    for F in combinations(range(n), r):
        seen = 0
        for a in range(r - 1):
            row = M[F[a]]
            for b in range(a + 1, r):
                seen |= 1 << row[F[b]]
            if seen == full:
                break
        if seen != full:
            out.append((F, full & ~seen))
    return out


def main():
    path = sys.argv[1]
    enum_k = 1
    if "--enumerate" in sys.argv:
        enum_k = int(sys.argv[sys.argv.index("--enumerate") + 1])
    prefix = None
    if "--out" in sys.argv:
        prefix = sys.argv[sys.argv.index("--out") + 1]

    r, n, M = load(path)
    cons = missing_sets(r, n, M)
    hist = {}
    for _, miss in cons:
        k = bin(miss).count("1")
        hist[k] = hist.get(k, 0) + 1
    from math import comb
    print(f"input: r={r}, n={n}; {comb(n, r)} {r}-subsets, "
          f"{len(cons)} with >=1 missing colour; |missing| histogram: {dict(sorted(hist.items()))}")

    var = lambda p, c: p * r + c + 1  # 1-based DIMACS-style
    solver = Cadical195()
    # exactly-one colour per new edge
    for p in range(n):
        solver.add_clause([var(p, c) for c in range(r)])
        for c1 in range(r):
            for c2 in range(c1 + 1, r):
                solver.add_clause([-var(p, c1), -var(p, c2)])
    # covering constraints
    nclauses = 0
    for F, miss in cons:
        for c in range(r):
            if (miss >> c) & 1:
                solver.add_clause([var(p, c) for p in F])
                nclauses += 1
    print(f"SAT instance: {n * r} vars, {nclauses} covering clauses (+{n} exactly-one groups)")

    found = 0
    while found < enum_k and solver.solve():
        model = set(l for l in solver.get_model() if l > 0)
        phi = [next(c for c in range(r) if var(p, c) in model) for p in range(n)]
        found += 1
        print(f"SAT #{found}: phi = {phi}")
        if prefix:
            M2 = [row[:] + [phi[i]] for i, row in enumerate(M)]
            M2.append([phi[i] for i in range(n)] + [-1])
            out = f"{prefix}_{found}.json"
            with open(out, "w") as f:
                json.dump({"r": r, "n": n + 1, "colours": M2}, f)
            print(f"  wrote {out}  — run tools/verify.py on it now")
        solver.add_clause([-var(p, phi[p]) for p in range(n)])  # block this solution
    if found == 0:
        print("UNSAT: this colouring of K_n admits NO balanced one-vertex extension.")
    elif found < enum_k:
        print(f"(exactly {found} extension(s) exist; enumeration exhausted)")
    solver.delete()


if __name__ == "__main__":
    main()
