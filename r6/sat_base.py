#!/usr/bin/env python3
"""SAT computation of the r=6 recursion base and low levels.
M6(s) = min edges over graphs on s vertices with alpha<=2, omega<=5, cap-16
        (every 7-set spans <=16 edges).  Analogue of r=5's M(s) (alpha<=2, omega<=4,
        cap-11) whose SAT values M(9)=19,M(10)=25,M(11)=none were essential.

Also computes L6(s) (alpha<=3) and N6(s) (alpha<=4) directly where cheap, to
validate the DP.  Cap encoded as a cardinality atmost per (r+1)-set (cheap),
NOT as C(cap+1) forbidden subsets (blows up at cap-16).

Usage: r6/../.venv/bin/python r6/sat_base.py <mode> [args]
  mode = M  s_lo s_hi        -> M6(s) exact for s in [s_lo,s_hi]
  mode = exist alpha s_lo s_hi -> existence (any edge count) for alpha, s range
  mode = min  alpha s        -> min edges for given alpha, single s
"""
import sys
from itertools import combinations
from pysat.solvers import Cadical195
from pysat.card import CardEnc, EncType


def min_edges(s, alpha_max, omega_max, cap, capset, kmax=None, existence_only=False):
    """Exact min edges; None if no graph exists. cap on capset-sets."""
    def build():
        ev, top = {}, 0
        for p in combinations(range(s), 2):
            top += 1
            ev[p] = top
        S = Cadical195()
        # alpha<=alpha_max : every (alpha_max+1)-set has an edge
        for A in combinations(range(s), alpha_max + 1):
            S.add_clause([ev[p] for p in combinations(A, 2)])
        # omega<=omega_max : every (omega_max+1)-set has a non-edge
        for A in combinations(range(s), omega_max + 1):
            S.add_clause([-ev[p] for p in combinations(A, 2)])
        return S, ev, top

    def feasible(k):
        S, ev, top = build()
        # cap: every capset-set spans <= cap edges  (cardinality atmost)
        tid = top
        if s >= capset:
            for A in combinations(range(s), capset):
                lits = [ev[p] for p in combinations(A, 2)]
                enc = CardEnc.atmost(lits=lits, bound=cap, top_id=tid, encoding=EncType.seqcounter)
                tid = enc.nv
                for cl in enc.clauses:
                    S.add_clause(cl)
        if k is not None:
            enc = CardEnc.atmost(lits=list(ev.values()), bound=k, top_id=tid, encoding=EncType.seqcounter)
            for cl in enc.clauses:
                S.add_clause(cl)
        ok = S.solve()
        S.delete()
        return ok

    hi = s * (s - 1) // 2
    if not feasible(hi):
        return None
    if existence_only:
        return "EXISTS"
    lo = 0
    while lo < hi:
        mid = (lo + hi) // 2
        if feasible(mid):
            hi = mid
        else:
            lo = mid + 1
    return lo


def main():
    mode = sys.argv[1]
    CAP, CAPSET, OMEGA = 16, 7, 5  # r=6 parameters
    if mode == "M":
        lo, hi = int(sys.argv[2]), int(sys.argv[3])
        for s in range(lo, hi + 1):
            v = min_edges(s, 2, OMEGA, CAP, CAPSET)
            print(f"M6({s}) [a<=2,w<=5,cap16] = {v}", flush=True)
    elif mode == "exist":
        alpha = int(sys.argv[2]); lo, hi = int(sys.argv[3]), int(sys.argv[4])
        for s in range(lo, hi + 1):
            v = min_edges(s, alpha, OMEGA, CAP, CAPSET, existence_only=True)
            print(f"exist(alpha<={alpha},w<=5,cap16, s={s}) = {v}", flush=True)
    elif mode == "min":
        alpha = int(sys.argv[2]); s = int(sys.argv[3])
        v = min_edges(s, alpha, OMEGA, CAP, CAPSET)
        print(f"min_edges(alpha<={alpha},w<=5,cap16, s={s}) = {v}", flush=True)


if __name__ == "__main__":
    main()
