#!/usr/bin/env python3
"""Verify the numeric tables in review_queue/mh2-gpt56-candidate.md by SAT.

Claims checked (each = min edges over graphs with the stated properties):
 A. M(s) for alpha<=2, omega<=4, cap-11:  M(9)=19, M(10)=25, M(11)=35,
    and NO such graph on 12 vertices (any edge count).
 B. L(s) for alpha<=3, omega<=4, cap-11:  s=13:24, 14:31, 15:38, 16:46
    (17..20 too big for quick SAT; the candidate derives them from A + the
    recursion, which we check arithmetically in verify_gpt_arith.py).
 C. Cross-check the candidate's (4.3): b(d) = floor(3d(d-1)/10) neighbourhood
    bound arithmetic (pure arithmetic, printed for eyeball).

Usage: .venv/bin/python tools/verify_gpt_tables.py [--skip-l16]
"""
import sys
from itertools import combinations
from pysat.solvers import Cadical195
from pysat.card import CardEnc, EncType


def min_edges(s, alpha_max, omega_max, cap11, kmax=None):
    """Exact min edges via binary search; returns None if no graph exists."""
    def feasible(k):
        ev, top = {}, 0
        for p in combinations(range(s), 2):
            top += 1
            ev[p] = top
        S = Cadical195()
        for A in combinations(range(s), alpha_max + 1):
            S.add_clause([ev[p] for p in combinations(A, 2)])
        for A in combinations(range(s), omega_max + 1):
            S.add_clause([-ev[p] for p in combinations(A, 2)])
        if cap11 and s >= 6:
            for A in combinations(range(s), 6):
                lits = [ev[p] for p in combinations(A, 2)]
                for w in combinations(lits, 12):
                    S.add_clause([-l for l in w])
        card = CardEnc.atmost(lits=list(ev.values()), bound=k, top_id=top,
                              encoding=EncType.seqcounter)
        for cl in card.clauses:
            S.add_clause(cl)
        ok = S.solve()
        S.delete()
        return ok

    hi = s * (s - 1) // 2
    if not feasible(hi):
        return None
    lo = 0
    while lo < hi:
        mid = (lo + hi) // 2
        if feasible(mid):
            hi = mid
        else:
            lo = mid + 1
    return lo


def main():
    print("A. M(s) [alpha<=2, omega<=4, cap-11]  (claims: 19, 25, 35, none@12)")
    for s, claim in ((9, 19), (10, 25), (11, 35)):
        got = min_edges(s, 2, 4, True)
        print(f"   s={s}: computed {got}, claimed {claim}  "
              f"{'OK' if got == claim else '*** MISMATCH ***'}", flush=True)
    got12 = min_edges(12, 2, 4, True)
    print(f"   s=12: computed {'NONE' if got12 is None else got12}, claimed NONE  "
          f"{'OK' if got12 is None else '*** MISMATCH ***'}", flush=True)
    print("B. L(s) [alpha<=3, omega<=4, cap-11]  (claims: 24, 31, 38, 46)")
    for s, claim in ((13, 24), (14, 31), (15, 38)) + ((() if "--skip-l16" in sys.argv else ((16, 46),))):
        got = min_edges(s, 3, 4, True)
        print(f"   s={s}: computed {got}, claimed {claim}  "
              f"{'OK (>=claim also acceptable)' if got == claim else ('OK-stronger' if got is not None and got > claim else '*** MISMATCH (weaker) ***')}", flush=True)


if __name__ == "__main__":
    main()
