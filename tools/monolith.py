#!/usr/bin/env python3
"""Monolithic DIMACS generators: full cap-11 family encoded directly
(every 6-set: at most 11 of its 15 edges present, as all C(15,12)=455
width-12 negative clauses — no aux vars), replacing the open-ended CEGAR.

Modes:
  mm  N EBOUND OUT.cnf   Lemma M probe: alpha<=5, full cap-11, e<=EBOUND,
                         exists 5-set T with alpha(G-T)<=4 and <=6 own edges.
                         (N=25, EBOUND=60 for the chain's [MM].)
  l5  N EBOUND OUT.cnf   L5' minority probe: alpha<=5, full cap-11, e<=EBOUND.
                         (N=26, EBOUND=65.)

Cardinalities (global edge bound, |T|=5, own<=6) via pysat seqcounter.
UNSAT of these instances = the full lemma directly (no relaxation caveat).

Usage: .venv/bin/python tools/monolith.py mm 25 60 data/sat/mm_full.cnf
"""
import sys
from itertools import combinations
from pysat.card import CardEnc, EncType


def main():
    mode, n, eb, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    ev, top = {}, 0
    for p in combinations(range(n), 2):
        top += 1
        ev[p] = top
    lines = []

    def emit(cl):
        lines.append(" ".join(map(str, cl)) + " 0")

    # alpha(G) <= 5 and full cap-11, per 6-set
    for S in combinations(range(n), 6):
        lits = [ev[p] for p in combinations(S, 2)]
        emit(lits)
        for w in combinations(lits, 12):
            emit([-l for l in w])

    card = CardEnc.atmost(lits=list(range(1, len(ev) + 1)), bound=eb,
                          top_id=top, encoding=EncType.seqcounter)
    top = max(top, card.nv)
    for cl in card.clauses:
        emit(cl)

    if mode == "mm":
        tv = {}
        for v in range(n):
            top += 1
            tv[v] = top
        yv = {}
        for p in combinations(range(n), 2):
            top += 1
            yv[p] = top
        c1 = CardEnc.atmost(lits=list(tv.values()), bound=5, top_id=top,
                            encoding=EncType.seqcounter)
        top = max(top, c1.nv)
        c2 = CardEnc.atleast(lits=list(tv.values()), bound=5, top_id=top,
                             encoding=EncType.seqcounter)
        top = max(top, c2.nv)
        for cl in c1.clauses + c2.clauses:
            emit(cl)
        for S in combinations(range(n), 5):
            emit([tv[v] for v in S] + [ev[p] for p in combinations(S, 2)])
        for (i, j), y in yv.items():
            emit([-ev[(i, j)], -tv[i], -tv[j], y])
        c3 = CardEnc.atmost(lits=list(yv.values()), bound=6, top_id=top,
                            encoding=EncType.seqcounter)
        top = max(top, c3.nv)
        for cl in c3.clauses:
            emit(cl)

    with open(out, "w") as f:
        f.write(f"p cnf {top} {len(lines)}\n")
        f.write("\n".join(lines) + "\n")
    print(f"wrote {out}: {top} vars, {len(lines)} clauses")


if __name__ == "__main__":
    main()
