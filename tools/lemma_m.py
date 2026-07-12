#!/usr/bin/env python3
"""Lemma M probe (the second machine lemma of the extension-obstruction chain).

Question: does there exist a graph G on 25 vertices with
  (a) alpha(G) <= 5                      [every 6-set has an edge]
  (b) every 6-set spans <= 11 G-edges    [density cap; CEGAR]
  (c) e(G) <= 60                         [minority class bound at n=25]
  (d) SOME 5-set T with alpha(G - T) <= 4 that spans <= 6 G-edges?

UNSAT => Lemma M: in any balanced 5-colouring of K_25 (whose every class
satisfies (a),(b) and whose minority class satisfies (c)), the minority class
admits no "usable" extension hitter (any T_c serving a one-vertex extension
must span <= 6 own-colour edges — see NOTES.md chain — but no such T exists).
Combined with Lemma H (all |T_c| = 5), this proves no balanced 5-colouring of
K_26 exists.

Encoding: edge vars e_ij; T-indicator vars t_v, exactly 5 true; y_ij aux
(y >= e_ij & t_i & t_j) with sum(y) <= 6; alpha(G-T)<=4 as width-15 clauses
(5 t-lits + 10 e-lits per 5-subset). Density caps CEGAR'd; the caps actually
added are saved for independent re-verification.

Usage: .venv/bin/python tools/lemma_m.py [EDGEBOUND=60]
"""
import json, sys
from itertools import combinations
from pysat.solvers import Cadical195
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

N = 25


def main():
    ebound = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    pool = IDPool()
    ev = {p: pool.id(f"e{p}") for p in combinations(range(N), 2)}
    tv = {v: pool.id(f"t{v}") for v in range(N)}
    yv = {p: pool.id(f"y{p}") for p in combinations(range(N), 2)}
    s = Cadical195()
    # (a) alpha(G) <= 5
    for S in combinations(range(N), 6):
        s.add_clause([ev[p] for p in combinations(S, 2)])
    # (c) e(G) <= ebound
    card = CardEnc.atmost(lits=list(ev.values()), bound=ebound,
                          top_id=pool.top, encoding=EncType.seqcounter)
    pool.top = max(pool.top, card.nv)
    for cl in card.clauses:
        s.add_clause(cl)
    # |T| = 5
    c1 = CardEnc.atmost(lits=list(tv.values()), bound=5, top_id=pool.top,
                        encoding=EncType.seqcounter)
    pool.top = max(pool.top, c1.nv)
    c2 = CardEnc.atleast(lits=list(tv.values()), bound=5, top_id=pool.top,
                         encoding=EncType.seqcounter)
    pool.top = max(pool.top, c2.nv)
    for cl in c1.clauses + c2.clauses:
        s.add_clause(cl)
    # alpha(G - T) <= 4: every 5-subset intersects T or contains an edge
    for S in combinations(range(N), 5):
        s.add_clause([tv[v] for v in S] + [ev[p] for p in combinations(S, 2)])
    # y_ij >= e_ij & t_i & t_j ; sum y <= 6
    for (i, j), y in yv.items():
        s.add_clause([-ev[(i, j)], -tv[i], -tv[j], y])
    c3 = CardEnc.atmost(lits=list(yv.values()), bound=6, top_id=pool.top,
                        encoding=EncType.seqcounter)
    pool.top = max(pool.top, c3.nv)
    for cl in c3.clauses:
        s.add_clause(cl)

    capped, rounds = [], 0
    while True:
        ok = s.solve()
        if not ok:
            print(f"lemma M probe (n={N}, e<={ebound}): UNSAT after {rounds} cegar rounds "
                  f"-- no usable hitter exists; Lemma M HOLDS at this bound", flush=True)
            break
        model = set(l for l in s.get_model() if l > 0)
        adj = [[False] * N for _ in range(N)]
        for (i, j), v in ev.items():
            if v in model:
                adj[i][j] = adj[j][i] = True
        viol = 0
        for S in combinations(range(N), 6):
            pairs = list(combinations(S, 2))
            if sum(adj[x][y] for x, y in pairs) > 11:
                viol += 1
                capped.append(S)
                loc = CardEnc.atmost(lits=[ev[p] for p in pairs], bound=11,
                                     top_id=pool.top, encoding=EncType.totalizer)
                pool.top = max(pool.top, loc.nv)
                for cl in loc.clauses:
                    s.add_clause(cl)
        rounds += 1
        print(f"  cegar round {rounds}: {viol} dense 6-sets blocked", flush=True)
        if viol == 0:
            T = sorted(v for v, x in tv.items() if x in model)
            E = sorted(p for p, x in ev.items() if x in model)
            own = sum(1 for (i, j) in E if i in T and j in T)
            print(f"SAT: counterexample graph, {len(E)} edges, T={T} (own edges {own})")
            print(f"edges: {E}")
            break
    with open(f"data/sat/lemma_m_caps_e{ebound}.json", "w") as f:
        json.dump({"n": N, "ebound": ebound, "capped": [list(S) for S in capped]}, f)


if __name__ == "__main__":
    main()
