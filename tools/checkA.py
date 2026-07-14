#!/usr/bin/env python3
"""INDEPENDENT brute-force checker for r=6 "object A" (task #77). Shares no code with the C
search scorer (tools/locsearch6a.c) — house rule: any hit is re-verified by a separate program.

Given a 6-colouring JSON ({"r":6,"n":N,"colours":[[...]]}) it directly enumerates all 6-sets and
7-sets and reports, as raw counts:

  A-profile (the target — all three must be 0 for object A):
    V_cap    = # (7-set, colour) with >= 17 same-colour edges           [cap-16]
    V_missed = # (7-set, colour c in 1..5) with 0 colour-c edges        [alpha(G_c) <= 6]
    V_alpha0 = # 6-sets with 0 colour-0 edges                           [alpha(G_0) <= 5]

  Extra profile (for documenting the refutation scope; NOT part of the A target):
    V_omega  = # (6-set, colour) that is a monochromatic K_6            [omega(G_c) <= 5]
    V_balance= # 7-sets missing at least one of the 6 colours           [balanced?]

Object A exists iff V_cap = V_missed = V_alpha0 = 0. If additionally V_omega = 0 the hit also has
every class K_6-free (the omega invariant in r6/feasibility.md); if additionally V_balance = 0 it
is a balanced colouring (a "B-object"). tools/verify.py remains the referee for balance.

Usage: python3 tools/checkA.py CAND.json
Exit: 0 iff object A (V_cap=V_missed=V_alpha0=0), else 1; 2 on malformed input.
"""
import sys, json
from itertools import combinations


def main():
    if len(sys.argv) != 2:
        sys.exit("usage: checkA.py CAND.json")
    d = json.load(open(sys.argv[1]))
    r, n, M = d["r"], d["n"], d["colours"]
    if r != 6:
        sys.exit(f"checkA is for r=6 (got r={r})")
    # validate matrix shape / symmetry / range independently
    assert len(M) == n and all(len(row) == n for row in M), "matrix not n x n"
    for i in range(n):
        assert M[i][i] == -1, f"diagonal ({i},{i}) != -1"
        for j in range(i + 1, n):
            assert M[i][j] == M[j][i], f"asymmetric at ({i},{j})"
            assert 0 <= M[i][j] < 6, f"colour out of range at ({i},{j})"

    V_cap = V_missed = V_alpha0 = V_omega = V_balance = 0

    # 7-set conditions: cap-16, alpha(G_c)<=6 (c=1..5), and balance (all 6 colours present)
    for S in combinations(range(n), 7):
        cnt = [0] * 6
        for a in range(7):
            Ma = M[S[a]]
            for b in range(a + 1, 7):
                cnt[Ma[S[b]]] += 1
        for c in range(6):
            if cnt[c] >= 17:
                V_cap += 1
            if c >= 1 and cnt[c] == 0:
                V_missed += 1
        if any(cnt[c] == 0 for c in range(6)):
            V_balance += 1

    # 6-set conditions: alpha(G_0)<=5 (colour-0 present) and omega (no monochromatic K_6)
    for S in combinations(range(n), 6):
        cnt = [0] * 6
        for a in range(6):
            Ma = M[S[a]]
            for b in range(a + 1, 6):
                cnt[Ma[S[b]]] += 1
        if cnt[0] == 0:
            V_alpha0 += 1
        for c in range(6):
            if cnt[c] == 15:          # all C(6,2)=15 edges colour c => K_6 in class c
                V_omega += 1

    is_A = (V_cap == 0 and V_missed == 0 and V_alpha0 == 0)
    print(f"checkA: n={n}")
    print(f"  A-profile:  V_cap={V_cap}  V_missed={V_missed}  V_alpha0={V_alpha0}   -> {'OBJECT A CONFIRMED' if is_A else 'NOT object A'}")
    print(f"  extra:      V_omega={V_omega} (K6-free per class iff 0)   V_balance={V_balance} (balanced iff 0)")
    if is_A:
        scope = ["refutes the weak-hypothesis [MH2]-analogue (cap-16, alpha (5,6,6,6,6,6))"]
        if V_omega == 0:
            scope.append("also K6-free per class (omega<=5): refutes the full feasibility.md statement")
        if V_balance == 0:
            scope.append("also BALANCED: refutes the balanced-hypothesis version too (a B-object)")
        for s in scope:
            print("  =>", s)
    sys.exit(0 if is_A else 1)


if __name__ == "__main__":
    main()
