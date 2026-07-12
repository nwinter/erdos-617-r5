#!/usr/bin/env python3
"""Minority-class lemma probe (the ErGy99 proof engine, computed exactly).

Question: what is the minimum number of edges of a graph on n vertices with
no K_{a+1} (clique of size a+1) and no independent set of size a+1?
(For the balanced-colouring problem: a = r, n = r^2+1. If the minimum exceeds
floor(C(n,2)/r), then the minority colour class of any r-colouring of K_n
contains K_{r+1} (a 6-set missing the other colours) or an independent
(r+1)-set (a 6-set missing the minority colour) — either way the colouring is
not balanced, settling the case.)

ErGy99's own lemmas in this form:
  r=3: min edges (K_4-free, alpha<=3, n=10) >= 16 > 15 = floor(45/3)   [Lemma 1]
  r=4: min edges (K_5-free, alpha<=4, n=17) >= 35 > 34 = floor(136/4)  [Lemma 2]
  r=5: min edges (K_6-free, alpha<=5, n=26) vs 65 = floor(325/5)       [OPEN]

CORRECTED subset-density condition (the actual ErGy phenomenon): in a balanced
r-colouring, an (r+1)-set with >= C(r+1,2)-(r-2) edges in ONE class sees at
most 1+(r-2) = r-1 colours, so it misses a colour. Hence the minority class
also satisfies: every (r+1)-set spans at most D := C(r+1,2)-(r-1) of its edges.
(r=3: 4-sets span <=4 of 6 — no K_4, no K_4-e, ErGy Lemma 1 proof;
 r=4: 5-sets span <=7 of 10 — ErGy's condition (*);
 r=5: 6-sets span <=11 of 15.)

Encoding: one boolean per edge of K_n. For every (a+1)-subset S:
  - at least one edge inside S            (alpha <= a)
  - with --cap: at most D edges inside S, via all C(.,D+1) negative clauses
    (fine for a=3,4; for a=5 use --cegar: lazily add per-subset caps)
  - without --cap: just K_{a+1}-freeness (at least one non-edge)
plus a cardinality constraint  sum(edges) <= m  (pysat seqcounter).

Usage:
  .venv/bin/python tools/minority.py N A M [--cap|--cegar] [--model]
Exit prints SAT/UNSAT. Solve with cadical via pysat.
"""
import sys
from itertools import combinations
from pysat.solvers import Cadical195
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool


def solve(n, a, m, want_model=False, cap=False, cegar=False):
    pool = IDPool()
    ev = {}
    for i, j in combinations(range(n), 2):
        ev[(i, j)] = pool.id(f"e{i}_{j}")
    D = (a + 1) * a // 2 - (a - 1)  # max edges an (a+1)-set may span
    s = Cadical195()
    for S in combinations(range(n), a + 1):
        lits = [ev[(x, y)] for x, y in combinations(S, 2)]
        s.add_clause(lits)                 # some edge: alpha <= a
        if cap:
            # at most D edges: every (D+1)-subset of pairs has a non-edge
            for T in combinations(lits, D + 1):
                s.add_clause([-l for l in T])
        else:
            s.add_clause([-l for l in lits])   # some non-edge: no K_{a+1}
    card = CardEnc.atmost(lits=list(ev.values()), bound=m,
                          top_id=pool.top, encoding=EncType.seqcounter)
    for cl in card.clauses:
        s.add_clause(cl)
    pool.top = max(pool.top, card.nv)  # CRITICAL: reserve the card aux ids,
    # else CEGAR-added local totalizers would collide with them (this bug
    # produced a spurious UNSAT on 2026-07-05; see ATTACKS.md)

    rev = {v: e for e, v in ev.items()}
    rounds = 0
    capped = []  # subsets given local <=D caps (for independent re-verification)
    while True:
        ok = s.solve()
        if not ok or not cegar:
            break
        # CEGAR: check per-subset density cap on the model; add violated caps lazily
        model = set(l for l in s.get_model() if l > 0)
        adj = [[False] * n for _ in range(n)]
        for v in ev.values():
            if v in model:
                i, j = rev[v]
                adj[i][j] = adj[j][i] = True
        viol = 0
        for S in combinations(range(n), a + 1):
            pairs = [(x, y) for x, y in combinations(S, 2)]
            k = sum(adj[x][y] for x, y in pairs)
            if k > D:
                viol += 1
                capped.append(S)
                # block: at most D of these edges (full local cap via totalizer)
                loc = CardEnc.atmost(lits=[ev[p] for p in pairs], bound=D,
                                     top_id=pool.top, encoding=EncType.totalizer)
                pool.top = max(pool.top, loc.nv)
                for cl in loc.clauses:
                    s.add_clause(cl)
        rounds += 1
        print(f"  cegar round {rounds}: {viol} dense subsets blocked", flush=True)
        if viol == 0:
            break
    if cegar:
        import json as _json
        with open(f"data/sat/minority_caps_n{n}_a{a}_m{m}.json", "w") as f:
            _json.dump({"n": n, "a": a, "m": m, "D": D,
                        "capped_subsets": [list(S) for S in capped]}, f)
    model_edges = None
    if ok and want_model:
        model = set(l for l in s.get_model() if l > 0)
        model_edges = [e for e, v in ev.items() if v in model]
    s.delete()
    return ok, model_edges


def main():
    n, a, m = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    cap, cegar = "--cap" in sys.argv, "--cegar" in sys.argv
    ok, edges = solve(n, a, m, "--model" in sys.argv, cap, cegar)
    D = (a + 1) * a // 2 - (a - 1)
    desc = f"all {a+1}-sets<={D}e" if (cap or cegar) else f"K_{a+1}-free"
    print(f"n={n}, {desc}, alpha<={a}, edges<={m}: {'SAT' if ok else 'UNSAT'}")
    if edges is not None:
        print(f"witness ({len(edges)} edges): {sorted(edges)}")


if __name__ == "__main__":
    main()
