#!/usr/bin/env python3
"""Min-edge feasibility: exists graph on N vertices, alpha<=A, omega<=W, edges<=M?
Usage: .venv/bin/python tools/rt_min.py N A W M [--model]"""
import sys
from itertools import combinations
from pysat.solvers import Cadical195
from pysat.card import CardEnc, EncType

def main():
    n, a, w, m = map(int, sys.argv[1:5])
    ev, k = {}, 0
    for i, j in combinations(range(n), 2):
        k += 1; ev[(i, j)] = k
    s = Cadical195()
    for S in combinations(range(n), a + 1):
        s.add_clause([ev[(x, y)] for x, y in combinations(S, 2)])
    for S in combinations(range(n), w + 1):
        s.add_clause([-ev[(x, y)] for x, y in combinations(S, 2)])
    card = CardEnc.atmost(lits=list(range(1, k + 1)), bound=m, top_id=k, encoding=EncType.seqcounter)
    for cl in card.clauses:
        s.add_clause(cl)
    ok = s.solve()
    print(f"n={n} alpha<={a} omega<={w} edges<={m}: {'SAT' if ok else 'UNSAT'}", flush=True)
    if ok and "--model" in sys.argv:
        mod = set(l for l in s.get_model() if l > 0)
        print("witness:", sorted(e for e, v in ev.items() if v in mod))
    s.delete()

if __name__ == "__main__":
    main()
