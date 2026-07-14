#!/usr/bin/env python3
"""CEGAR v2: alpha<=5 clauses UPFRONT (binding constraint), lazily add omega<=5
and cap-16. Finds an explicit class-0 graph at <=E edges or proves min>E."""
import sys, json, time
from itertools import combinations
from pysat.solvers import Cadical195
from pysat.card import CardEnc, EncType

N = 31
FULL = (1 << N) - 1
pairs = list(combinations(range(N), 2))
vid = {p: i + 1 for i, p in enumerate(pairs)}
TOP = len(pairs)

def lit(a, b): return vid[(min(a, b), max(a, b))]

def adj_from(model):
    ms = set(v for v in model if v > 0)
    adj = [0] * N
    for p in pairs:
        if vid[p] in ms:
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
    # smarter: only 7-sets with a vertex of high local degree can be dense.
    for Sv in combinations(range(N), 7):
        m = 0
        for v in Sv: m |= 1 << v
        if sum(bin(adj[v] & m).count("1") for v in Sv) // 2 > cap:
            return Sv
    return None

def solve(E, cap=16):
    t0 = time.time()
    S = Cadical195()
    # upfront alpha<=5: every 6-set has an edge
    na = 0
    for A in combinations(range(N), 6):
        S.add_clause([lit(a, b) for a, b in combinations(A, 2)]); na += 1
    print(f"  added {na} alpha-clauses in {time.time()-t0:.0f}s", flush=True)
    enc = CardEnc.atmost(lits=list(vid.values()), bound=E, top_id=TOP, encoding=EncType.seqcounter)
    for cl in enc.clauses: S.add_clause(cl)
    rounds = 0
    while True:
        rounds += 1
        if not S.solve():
            return None, rounds
        adj = adj_from(S.get_model())
        c6 = find_clique(adj, 6)
        if c6 is not None:
            vs = [v for v in range(N) if c6 >> v & 1]
            S.add_clause([-lit(a, b) for a, b in combinations(vs, 2)]); continue
        cb = cap_bad(adj, cap)
        if cb is not None:
            lits = [lit(a, b) for a, b in combinations(cb, 2)]
            e2 = CardEnc.atmost(lits=lits, bound=cap, top_id=S.nof_vars(), encoding=EncType.seqcounter)
            for cl in e2.clauses: S.add_clause(cl)
            if rounds % 20 == 0: print(f"  round {rounds}: cap fixes ongoing ({time.time()-t0:.0f}s)", flush=True)
            continue
        return adj, rounds

if __name__ == "__main__":
    E = int(sys.argv[1]) if len(sys.argv) > 1 else 120
    adj, rounds = solve(E)
    if adj is None:
        print(f"UNSAT at E<={E} ({rounds} rounds) => min edges > {E}")
    else:
        e = sum(bin(a).count("1") for a in adj) // 2
        assert indep(adj, 6) is None and find_clique(adj, 6) is None and cap_bad(adj) is None
        degs = sorted(bin(a).count("1") for a in adj)
        print(f"FOUND E<={E}: edges={e}, rounds={rounds}, VERIFIED. degrees={degs}")
        json.dump({"n": N, "edges": e, "degrees": degs,
                   "adj": [[adj[i] >> j & 1 for j in range(N)] for i in range(N)]},
                  open(f"data/r6/candidates/class0_n31_E{e}.json", "w"))
        print(f"  wrote data/r6/candidates/class0_n31_E{e}.json")
