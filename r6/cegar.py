#!/usr/bin/env python3
"""CEGAR construction of a class-0 graph: alpha<=5, omega<=5 (K_6-free), cap-16 on
31 vertices at <= E edges. Lazily add violated 6-set/7-set clauses. Returns an
explicit graph (or UNSAT => no such graph at <=E edges, tightening the min)."""
import sys, json
from itertools import combinations
from pysat.solvers import Cadical195
from pysat.card import CardEnc, EncType

N = 31
FULL = (1 << N) - 1
pairs = list(combinations(range(N), 2))
vid = {p: i + 1 for i, p in enumerate(pairs)}
TOP = len(pairs)

def adj_from(model):
    mset = set(v for v in model if v > 0)
    adj = [0] * N
    for p in pairs:
        if vid[p] in mset:
            a, b = p; adj[a] |= 1 << b; adj[b] |= 1 << a
    return adj

def find_clique(adj, k, cand=None, chosen=0):
    if cand is None: cand = FULL
    if bin(chosen).count("1") == k: return chosen
    c = cand
    while c:
        v = (c & -c).bit_length() - 1; c &= c - 1
        if chosen & ~adj[v]: continue
        r = find_clique(adj, k, cand & adj[v] & ~((1 << (v + 1)) - 1), chosen | (1 << v))
        if r is not None: return r
    return None

def indep(adj, k):
    comp = [(~adj[v]) & FULL & ~(1 << v) for v in range(N)]
    return find_clique(comp, k)

def cap_bad(adj, cap=16):
    for Sv in combinations(range(N), 7):
        m = 0
        for v in Sv: m |= 1 << v
        if sum(bin(adj[v] & m).count("1") for v in Sv) // 2 > cap:
            return Sv
    return None

def solve(E, cap=16, log=True):
    S = Cadical195()
    enc = CardEnc.atmost(lits=list(vid.values()), bound=E, top_id=TOP, encoding=EncType.seqcounter)
    for cl in enc.clauses: S.add_clause(cl)
    rounds = 0
    while True:
        rounds += 1
        if not S.solve():
            return None, rounds  # UNSAT: no graph at <=E edges
        adj = adj_from(S.get_model())
        # check alpha<=5
        bad = indep(adj, 6)
        if bad is not None:
            vs = [v for v in range(N) if bad >> v & 1]
            S.add_clause([vid[(min(a, b), max(a, b))] for a, b in combinations(vs, 2)])
            continue
        # check omega<=5
        c6 = find_clique(adj, 6)
        if c6 is not None:
            vs = [v for v in range(N) if c6 >> v & 1]
            S.add_clause([-vid[(min(a, b), max(a, b))] for a, b in combinations(vs, 2)])
            continue
        # check cap-16
        cb = cap_bad(adj, cap)
        if cb is not None:
            lits = [vid[(min(a, b), max(a, b))] for a, b in combinations(cb, 2)]
            # forbid >cap of these 21 edges: atmost-cap
            e2 = CardEnc.atmost(lits=lits, bound=cap, top_id=S.nof_vars(), encoding=EncType.seqcounter)
            for cl in e2.clauses: S.add_clause(cl)
            continue
        return adj, rounds  # valid!

if __name__ == "__main__":
    E = int(sys.argv[1]) if len(sys.argv) > 1 else 110
    adj, rounds = solve(E)
    if adj is None:
        print(f"UNSAT at E<={E} after {rounds} rounds  => min edges > {E}")
    else:
        e = sum(bin(a).count("1") for a in adj) // 2
        print(f"FOUND at E<={E}: edges={e}, rounds={rounds}")
        degs = sorted(bin(a).count("1") for a in adj)
        print("  degrees:", degs)
        # final independent verification
        assert indep(adj, 6) is None and find_clique(adj, 6) is None and cap_bad(adj) is None
        print("  VERIFIED alpha<=5, omega<=5, cap-16")
        out = {"n": N, "edges": e, "degrees": degs,
               "adj": [[adj[i] >> j & 1 for j in range(N)] for i in range(N)]}
        json.dump(out, open(f"data/r6/candidates/class0_n31_E{e}.json", "w"))
        print(f"  wrote data/r6/candidates/class0_n31_E{e}.json")
