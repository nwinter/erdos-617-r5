#!/usr/bin/env python3
"""Test structural hypotheses on saved balanced 5-colourings of K_25.

H1: every colour class contains 5 disjoint monochromatic K_5s covering all 25
    vertices (a resolution/partition).
Orthogonality: parts of different classes' partitions meet in <=1 point
    (automatic from edge-disjointness; verified anyway).
Relaxed extension (partition-transversal) question: given the five partitions
    P_0..P_4, does there exist a partition T_0..T_4 of the 25 points with
    T_c a transversal of P_d for every d != c?  (This is NECESSARY for a
    one-vertex extension whenever H1 holds: each part of P_d is a mono-K_5,
    i.e. a 5-set missing every colour but d, so every other colour's T must
    hit it; sizes then force |T_c|=5 and exact transversality.)
    If even this relaxation is UNSAT, the extension obstruction is already
    at the orthogonal-resolution level (Conjecture C).

Usage: .venv/bin/python tools/structure25.py FILE.json [FILE2.json ...]
Output: one line per file: H1 verdict, partitions found, relaxed-SAT verdict.
"""
import json, sys
from itertools import combinations
from pysat.solvers import Cadical195


def mono_k5s(M, n, c):
    out = []
    for F in combinations(range(n), 5):
        if all(M[a][b] == c for a, b in combinations(F, 2)):
            out.append(F)
    return out


def find_partition(k5s, n=25):
    """Find 5 pairwise-disjoint K_5s covering 0..24 (exact cover, tiny search)."""
    k5sets = [frozenset(F) for F in k5s]

    def rec(chosen, covered):
        if len(chosen) == 5:
            return list(chosen)
        # smallest uncovered vertex must be in some part
        v = min(set(range(n)) - covered)
        for F in k5sets:
            if v in F and not (F & covered):
                r = rec(chosen + [F], covered | F)
                if r:
                    return r
        return None

    return rec([], frozenset())


def relaxed_transversal_sat(partitions):
    """SAT: partition 25 points into T_0..T_4, T_c transversal of P_d (d!=c)."""
    var = lambda p, c: p * 5 + c + 1
    s = Cadical195()
    for p in range(25):
        s.add_clause([var(p, c) for c in range(5)])
        for c1 in range(5):
            for c2 in range(c1 + 1, 5):
                s.add_clause([-var(p, c1), -var(p, c2)])
    for d, P in enumerate(partitions):
        for part in P:
            for c in range(5):
                if c != d:
                    s.add_clause([var(p, c) for p in part])  # T_c hits this part
    ok = s.solve()
    sol = None
    if ok:
        m = set(l for l in s.get_model() if l > 0)
        sol = [next(c for c in range(5) if var(p, c) in m) for p in range(25)]
    s.delete()
    return ok, sol


def main():
    for path in sys.argv[1:]:
        d = json.load(open(path))
        M, n = d["colours"], d["n"]
        parts, h1 = [], True
        permono = []
        for c in range(5):
            k5 = mono_k5s(M, n, c)
            permono.append(len(k5))
            P = find_partition(k5, n)
            if P is None:
                h1 = False
                break
            parts.append([sorted(F) for F in P])
        if not h1:
            print(f"{path}: H1 FALSE (class {len(parts)} has no K_5-resolution; mono counts {permono})")
            continue
        # orthogonality check
        orth = all(len(set(A) & set(B)) <= 1
                   for i in range(5) for j in range(i + 1, 5)
                   for A in parts[i] for B in parts[j])
        ok, sol = relaxed_transversal_sat(parts)
        print(f"{path}: H1 ok (mono per class {permono}), orthogonal={orth}, "
              f"relaxed-transversal {'SAT ' + str(sol) if ok else 'UNSAT'}")


if __name__ == "__main__":
    main()
