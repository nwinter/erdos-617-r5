#!/usr/bin/env python3
"""r=4 validation of the extension-obstruction chain (answer known: ErGy
proved K_17 has no balanced 4-colouring, so the chain's two machine lemmas
SHOULD both be UNSAT if the chain is the right shape; if not, the chain is
not how r=4 dies and its r=5 instantiation deserves less prior trust).

MH''_4: balanced 4-colouring of K_16 with a 3-set T = {0,1,2} such that
        alpha(G_0 - T) <= 3?   [UNSAT wanted]
MM_4:   graph on 16 vertices, alpha<=4, every 5-set spans <=7 edges,
        e <= 30 (= floor(C(16,2)/4)), with a 4-set T, alpha(G-T)<=3,
        T spanning <=3 own edges?   [UNSAT wanted]

Usage: .venv/bin/python tools/chain_r4.py mh | mm
"""
import sys
from itertools import combinations
from pysat.solvers import Cadical195
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool


def mh():
    r, n = 4, 16
    pool = IDPool()
    ev = {}
    for p in combinations(range(n), 2):
        for c in range(r):
            ev[(p, c)] = pool.id(f"{p}c{c}")
    s = Cadical195()
    for p in combinations(range(n), 2):
        s.add_clause([ev[(p, c)] for c in range(r)])
        for c1 in range(r):
            for c2 in range(c1 + 1, r):
                s.add_clause([-ev[(p, c1)], -ev[(p, c2)]])
    # balance: every 5-set sees all 4 colours
    for S in combinations(range(n), r + 1):
        for c in range(r):
            s.add_clause([ev[(p, c)] for p in combinations(S, 2)])
    # T = {0,1,2}: alpha(G_0 - T) <= 3: every 4-subset of {3..15} has a 0-edge
    for S in combinations(range(3, n), r):
        s.add_clause([ev[(p, 0)] for p in combinations(S, 2)])
    print("MH''_4 (balanced K_16 + 3-set hitting class 0):",
          "SAT (chain-shape fails at r=4!)" if s.solve() else "UNSAT (as the chain predicts)")
    s.delete()


def mm():
    n, ebound = 16, 30
    pool = IDPool()
    ev = {p: pool.id(f"e{p}") for p in combinations(range(n), 2)}
    tv = {v: pool.id(f"t{v}") for v in range(n)}
    yv = {p: pool.id(f"y{p}") for p in combinations(range(n), 2)}
    s = Cadical195()
    for S in combinations(range(n), 5):  # alpha <= 4
        s.add_clause([ev[p] for p in combinations(S, 2)])
        # cap: 5-sets span <= 7 edges: every 8-subset of pairs has a non-edge
        for T in combinations(list(combinations(S, 2)), 8):
            s.add_clause([-ev[p] for p in T])
    card = CardEnc.atmost(lits=list(ev.values()), bound=ebound,
                          top_id=pool.top, encoding=EncType.seqcounter)
    pool.top = max(pool.top, card.nv)
    for cl in card.clauses:
        s.add_clause(cl)
    c1 = CardEnc.atmost(lits=list(tv.values()), bound=4, top_id=pool.top,
                        encoding=EncType.seqcounter)
    pool.top = max(pool.top, c1.nv)
    c2 = CardEnc.atleast(lits=list(tv.values()), bound=4, top_id=pool.top,
                         encoding=EncType.seqcounter)
    pool.top = max(pool.top, c2.nv)
    for cl in c1.clauses + c2.clauses:
        s.add_clause(cl)
    for S in combinations(range(n), 4):  # alpha(G-T) <= 3
        s.add_clause([tv[v] for v in S] + [ev[p] for p in combinations(S, 2)])
    for (i, j), y in yv.items():
        s.add_clause([-ev[(i, j)], -tv[i], -tv[j], y])
    c3 = CardEnc.atmost(lits=list(yv.values()), bound=3, top_id=pool.top,
                        encoding=EncType.seqcounter)
    pool.top = max(pool.top, c3.nv)
    for cl in c3.clauses:
        s.add_clause(cl)
    print("MM_4 (16 vtx, alpha<=4, 5-sets<=7e, e<=30, 4-set T own<=3):",
          "SAT (chain-shape fails at r=4!)" if s.solve() else "UNSAT (as the chain predicts)")
    s.delete()


if __name__ == "__main__":
    (mh if sys.argv[1] == "mh" else mm)()
