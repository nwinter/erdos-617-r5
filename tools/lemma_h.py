#!/usr/bin/env python3
"""Lemma H probe: does a graph exist on N vertices with alpha <= 4 and every
6-subset spanning at most 11 edges?

Context: in a balanced 5-colouring of K_25, a colour class G_c with a hitting
set T (|T| <= 4) killing all its independent 5-sets would leave W = V - T,
|W| >= 21, with alpha(G_c[W]) <= 4; G_c[W] inherits the 6-set density cap
(<= 11 of 15 edges; a 6-set with >= 12 edges of one colour sees <= 4 colours).
UNSAT at N=21 proves h_c >= 5 for every class of every balanced 5-colouring
of K_n, n >= 25 (monotone: delete vertices to reach 21).

Encoding: edge booleans; 5-subsets: at least one edge (alpha<=4);
6-subset density caps added lazily (CEGAR, totalizer per violated subset).
Usage: .venv/bin/python tools/lemma_h.py N
"""
import sys
from itertools import combinations
from pysat.solvers import Cadical195
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool


def main():
    n = int(sys.argv[1])
    pool = IDPool()
    ev = {}
    for i, j in combinations(range(n), 2):
        ev[(i, j)] = pool.id(f"e{i}_{j}")
    s = Cadical195()
    for S in combinations(range(n), 5):
        s.add_clause([ev[(x, y)] for x, y in combinations(S, 2)])
    rounds = 0
    while True:
        ok = s.solve()
        if not ok:
            print(f"n={n}, alpha<=4, all 6-sets<=11 edges: UNSAT (after {rounds} cegar rounds)")
            return
        model = set(l for l in s.get_model() if l > 0)
        adj = [[False] * n for _ in range(n)]
        for (i, j), v in ev.items():
            if v in model:
                adj[i][j] = adj[j][i] = True
        viol = 0
        for S in combinations(range(n), 6):
            pairs = [(x, y) for x, y in combinations(S, 2)]
            if sum(adj[x][y] for x, y in pairs) > 11:
                viol += 1
                loc = CardEnc.atmost(lits=[ev[p] for p in pairs], bound=11,
                                     top_id=pool.top, encoding=EncType.totalizer)
                pool.top = max(pool.top, loc.nv)
                for cl in loc.clauses:
                    s.add_clause(cl)
        rounds += 1
        print(f"  cegar round {rounds}: {viol} dense 6-sets blocked", flush=True)
        if viol == 0:
            print(f"n={n}, alpha<=4, all 6-sets<=11 edges: SAT (witness exists)")
            edges = sorted(e for e, v in ev.items() if v in model)
            print(f"witness ({len(edges)} edges): {edges}")
            return


if __name__ == "__main__":
    main()
