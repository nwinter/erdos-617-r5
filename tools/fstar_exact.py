#!/usr/bin/env python3
"""Exact floors f**(m): minimum edges of a graph H on m vertices with
  (i)  alpha(H) <= 3
  (ii) for every vertex u: alpha(H - N_H[u]) <= 2
  (iii) optional --cap: every 6-set spans <= 11 edges (inherited cap-11)
  (iv) optional --no-octahedron: no K_{2,2,2} subgraph (subsumed by --cap)
via SAT with binary search on the edge count.

These are valid lower bounds for e(G_0[W_v]) in the MH'' hand-proof framework
(review_queue/mh2-handproof-wip.md): both (i) and (ii) are intrinsic to the
induced subgraph H = G_0[W_v] (the level-2 deletion sets coincide), and (iii)
is inherited from balance.

Usage: .venv/bin/python tools/fstar_exact.py M_MIN M_MAX [--cap]
Prints a table m -> f**(m) with the SAT/UNSAT boundary certified per value.
"""
import sys
from itertools import combinations
from pysat.solvers import Cadical195
from pysat.card import CardEnc, EncType


def turan_ex(m, r):
    q, s = divmod(m, r)
    intra = s * (q + 1) * q // 2 + (r - s) * q * (q - 1) // 2
    return m * (m - 1) // 2 - intra


def feasible(m, k, cap):
    ev, top = {}, 0
    for p in combinations(range(m), 2):
        top += 1
        ev[p] = top
    s = Cadical195()
    for S in combinations(range(m), 4):          # alpha <= 3
        s.add_clause([ev[p] for p in combinations(S, 2)])
    for u in range(m):                            # level-2: alpha(H - N[u]) <= 2
        for S in combinations([x for x in range(m) if x != u], 3):
            cl = [ev[tuple(sorted((u, x)))] for x in S]
            cl += [ev[p] for p in combinations(S, 2)]
            s.add_clause(cl)
    if cap:
        for S in combinations(range(m), 6):       # cap-11
            lits = [ev[p] for p in combinations(S, 2)]
            for w in combinations(lits, 12):
                s.add_clause([-l for l in w])
    card = CardEnc.atmost(lits=list(ev.values()), bound=k, top_id=top,
                          encoding=EncType.seqcounter)
    for cl in card.clauses:
        s.add_clause(cl)
    ok = s.solve()
    s.delete()
    return ok


def main():
    m0, m1 = int(sys.argv[1]), int(sys.argv[2])
    cap = "--cap" in sys.argv
    for m in range(m0, m1 + 1):
        lo = m * (m - 1) // 2 - turan_ex(m, 3)   # f(m), known valid floor
        hi = m * (m - 1) // 2
        # find min feasible k in [lo, hi] (feasible is monotone in k)
        while lo < hi:
            mid = (lo + hi) // 2
            if feasible(m, mid, cap):
                hi = mid
            else:
                lo = mid + 1
        print(f"m={m}: f**={lo}  (f={m*(m-1)//2 - turan_ex(m,3)})", flush=True)


if __name__ == "__main__":
    main()
