#!/usr/bin/env python3
"""Design probe for the MH'' pincer: do K pairwise-orthogonal partitions of a
21-set into parts of sizes (5,4,4,4,4) exist? (Orthogonal = parts from
different partitions share <= 1 point, equivalently no pair of points lies in
a same part twice.)

Context (review_queue/mh2-handproof-wip.md): if an h4-witness at n=25 has
e(G_0[V_out]) = 74 (the budget maximum), the other four classes each sit at
their alpha<=5 Turan floor on 21 points, i.e. each is EXACTLY a disjoint
clique partition with sizes (5,4,4,4,4), and edge-disjointness of classes =
pairwise orthogonality. Nonexistence for K=4 kills e=74 outright; the defect
version quantifies how much below 74 the top of the window drops.

WLOG partition 0 is {0..4},{5..8},{9..12},{13..16},{17..20} (vertex relabel).

Usage: .venv/bin/python tools/orth_partitions.py K [--model]
"""
import sys
from itertools import combinations
from pysat.solvers import Cadical195
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

NPTS = 21
SIZES = [5, 4, 4, 4, 4]


def main():
    K = int(sys.argv[1])
    pool = IDPool()
    x = {}  # x[c,p,v] = vertex v in part p of partition c   (c >= 1; c=0 fixed)
    for c in range(1, K):
        for p in range(5):
            for v in range(NPTS):
                x[c, p, v] = pool.id(f"x{c}_{p}_{v}")
    s = Cadical195()
    fixed = [list(range(0, 5)), list(range(5, 9)), list(range(9, 13)),
             list(range(13, 17)), list(range(17, 21))]
    for c in range(1, K):
        for v in range(NPTS):
            s.add_clause([x[c, p, v] for p in range(5)])
            for p1 in range(5):
                for p2 in range(p1 + 1, 5):
                    s.add_clause([-x[c, p1, v], -x[c, p2, v]])
        for p in range(5):
            enc_le = CardEnc.atmost(lits=[x[c, p, v] for v in range(NPTS)],
                                    bound=SIZES[p], top_id=pool.top,
                                    encoding=EncType.seqcounter)
            pool.top = max(pool.top, enc_le.nv)
            enc_ge = CardEnc.atleast(lits=[x[c, p, v] for v in range(NPTS)],
                                     bound=SIZES[p], top_id=pool.top,
                                     encoding=EncType.seqcounter)
            pool.top = max(pool.top, enc_ge.nv)
            for cl in enc_le.clauses + enc_ge.clauses:
                s.add_clause(cl)
    # orthogonality with the fixed partition 0:
    for c in range(1, K):
        for part in fixed:
            for u, v in combinations(part, 2):
                for p in range(5):
                    s.add_clause([-x[c, p, u], -x[c, p, v]])
    # pairwise orthogonality among free partitions: pair (u,v) same-part in
    # at most one c: for c < c', not(same_c(u,v) and same_c'(u,v)):
    # same_c(u,v) <-> OR_p (x[c,p,u] & x[c,p,v]); use aux y.
    y = {}
    for c in range(1, K):
        for u, v in combinations(range(NPTS), 2):
            yv = pool.id(f"y{c}_{u}_{v}")
            y[c, u, v] = yv
            for p in range(5):
                s.add_clause([-x[c, p, u], -x[c, p, v], yv])
            # reverse direction (y -> some shared part) not needed for the
            # "at most one" constraint to be sound: y only appears negatively
            # below, and the forward implication forces y=1 when truly shared.
    for u, v in combinations(range(NPTS), 2):
        for c1 in range(1, K):
            for c2 in range(c1 + 1, K):
                s.add_clause([-y[c1, u, v], -y[c2, u, v]])
    if "--alpha4" in sys.argv:
        # G := pairs co-parted in NO partition (the forced hitter class at
        # e = 74). Require alpha(G) <= 4: every 5-subset has a G-edge.
        # Exact y both ways via part-level aux w.
        fixed_same = set()
        for part in fixed:
            for u, v in combinations(part, 2):
                fixed_same.add((u, v))
        yy = {}  # yy[c,(u,v)] exact
        for c in range(1, K):
            for u, v in combinations(range(NPTS), 2):
                ws = []
                for p in range(5):
                    w = pool.id(f"w{c}_{p}_{u}_{v}")
                    s.add_clause([-w, x[c, p, u]])
                    s.add_clause([-w, x[c, p, v]])
                    s.add_clause([-x[c, p, u], -x[c, p, v], w])
                    ws.append(w)
                yv2 = pool.id(f"yy{c}_{u}_{v}")
                for w in ws:
                    s.add_clause([-w, yv2])
                s.add_clause([-yv2] + ws)
                yy[c, (u, v)] = yv2
        g = {}
        for u, v in combinations(range(NPTS), 2):
            gv = pool.id(f"g{u}_{v}")
            g[(u, v)] = gv
            if (u, v) in fixed_same:
                s.add_clause([-gv])  # co-parted in partition 0
            else:
                lits = [yy[c, (u, v)] for c in range(1, K)]
                # g <-> none of the y's
                for l in lits:
                    s.add_clause([-gv, -l])
                s.add_clause([gv] + lits)
        for S in combinations(range(NPTS), 5):
            s.add_clause([g[(a, b)] for a, b in combinations(S, 2)])
    ok = s.solve()
    tag = " + alpha(complement-G)<=4" if "--alpha4" in sys.argv else ""
    print(f"K={K} pairwise-orthogonal (5,4,4,4,4)-partitions of 21 points{tag}: "
          f"{'SAT (exist)' if ok else 'UNSAT (do not exist)'}")
    if ok and "--model" in sys.argv:
        m = set(l for l in s.get_model() if l > 0)
        for c in range(1, K):
            parts = [[v for v in range(NPTS) if x[c, p, v] in m] for p in range(5)]
            print(f"  partition {c}: {parts}")
    s.delete()


if __name__ == "__main__":
    main()
