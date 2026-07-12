#!/usr/bin/env python3
"""Static DIMACS export of the Lemma M constraint system (see tools/lemma_m.py)
for independent verification: different solver (kissat), different cardinality
encoding (totalizer everywhere vs seqcounter), DRAT-checkable.

Includes the local 6-set density caps from a converged lemma_m run
(data/sat/lemma_m_caps_e<EB>.json). UNSAT of this CNF is sound for Lemma M:
its constraints are a SUBSET of the full valid family.

Usage: .venv/bin/python tools/lemma_m_export.py EDGEBOUND OUT.cnf
"""
import json, sys
from itertools import combinations
from pysat.card import CardEnc, EncType

N = 25


def add_card(clauses, lits, bound, top, atleast=False):
    enc = (CardEnc.atleast if atleast else CardEnc.atmost)(
        lits=lits, bound=bound, top_id=top, encoding=EncType.totalizer)
    clauses.extend(enc.clauses)
    return max(top, enc.nv)


def main():
    eb = int(sys.argv[1])
    out = sys.argv[2]
    caps = json.load(open(f"data/sat/lemma_m_caps_e{eb}.json"))
    ev, top = {}, 0
    for p in combinations(range(N), 2):
        top += 1
        ev[p] = top
    tv = {}
    for v in range(N):
        top += 1
        tv[v] = top
    yv = {}
    for p in combinations(range(N), 2):
        top += 1
        yv[p] = top
    clauses = []
    for S in combinations(range(N), 6):
        clauses.append([ev[p] for p in combinations(S, 2)])
    top = add_card(clauses, list(ev.values()), eb, top)
    top = add_card(clauses, list(tv.values()), 5, top)
    top = add_card(clauses, list(tv.values()), 5, top, atleast=True)
    for S in combinations(range(N), 5):
        clauses.append([tv[v] for v in S] + [ev[p] for p in combinations(S, 2)])
    for (i, j), y in yv.items():
        clauses.append([-ev[(i, j)], -tv[i], -tv[j], y])
    top = add_card(clauses, list(yv.values()), 6, top)
    for S in caps["capped"]:
        lits = [ev[tuple(sorted(p))] for p in combinations(S, 2)]
        top = add_card(clauses, lits, 11, top)
    with open(out, "w") as f:
        f.write(f"p cnf {top} {len(clauses)}\n")
        for cl in clauses:
            f.write(" ".join(map(str, cl)) + " 0\n")
    print(f"wrote {out}: {top} vars, {len(clauses)} clauses, {len(caps['capped'])} caps")


if __name__ == "__main__":
    main()
