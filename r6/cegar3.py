#!/usr/bin/env python3
"""CEGAR v3: numpy-accelerated cap check, batch-add all violations per round."""
import sys, json, time
import numpy as np
from itertools import combinations
from pysat.solvers import Cadical195
from pysat.card import CardEnc, EncType

N = 31; FULL = (1 << N) - 1
pairs = list(combinations(range(N), 2))
vid = {p: i + 1 for i, p in enumerate(pairs)}
TOP = len(pairs)
sevens = np.array(list(combinations(range(N), 7)), dtype=np.int8)  # (C(31,7),7)

def lit(a, b): return vid[(min(a, b), max(a, b))]

def adj_np(model):
    ms = set(v for v in model if v > 0)
    A = np.zeros((N, N), dtype=np.int8)
    for p in pairs:
        if vid[p] in ms:
            a, b = p; A[a, b] = A[b, a] = 1
    return A

def find_clique_bm(adj, k, cand=None, chosen=0):
    if cand is None: cand = FULL
    if bin(chosen).count("1") == k: return chosen
    c = cand
    while c:
        v = (c & -c).bit_length() - 1; c &= c - 1
        if chosen & ~adj[v]: continue
        r = find_clique_bm(adj, k, cand & adj[v] & ~((1 << (v + 1)) - 1), chosen | (1 << v))
        if r is not None: return r
    return None

def bm_from_np(A):
    return [int(sum(int(A[v, u]) << u for u in range(N))) for v in range(N)]

def cap_violations(A, cap=16, limit=200):
    """return list of bad 7-sets (as vertex tuples), up to limit, via numpy."""
    S = sevens
    # edge count in each 7-set: sum over pairs within
    ec = np.zeros(len(S), dtype=np.int16)
    for i in range(7):
        for j in range(i + 1, 7):
            ec += A[S[:, i], S[:, j]]
    bad_idx = np.where(ec > cap)[0]
    return [tuple(int(x) for x in S[k]) for k in bad_idx[:limit]]

def solve(E, cap=16, tlim=1500):
    t0 = time.time()
    s = Cadical195()
    for Ac in combinations(range(N), 6):
        s.add_clause([lit(a, b) for a, b in combinations(Ac, 2)])
    enc = CardEnc.atmost(lits=list(vid.values()), bound=E, top_id=TOP, encoding=EncType.seqcounter)
    for cl in enc.clauses: s.add_clause(cl)
    print(f"  alpha+card loaded {time.time()-t0:.0f}s", flush=True)
    rnd = 0
    while time.time() - t0 < tlim:
        rnd += 1
        if not s.solve():
            return None, rnd
        model = s.get_model()
        adjbm = adj_np(model)  # numpy
        bm = bm_from_np(adjbm)
        c6 = find_clique_bm(bm, 6)
        if c6 is not None:
            vs = [v for v in range(N) if c6 >> v & 1]
            s.add_clause([-lit(a, b) for a, b in combinations(vs, 2)]); continue
        bad = cap_violations(adjbm, cap)
        if bad:
            for cb in bad:
                lits = [lit(a, b) for a, b in combinations(cb, 2)]
                e2 = CardEnc.atmost(lits=lits, bound=cap, top_id=s.nof_vars(), encoding=EncType.seqcounter)
                for cl in e2.clauses: s.add_clause(cl)
            print(f"  round {rnd}: +{len(bad)} cap cuts ({time.time()-t0:.0f}s)", flush=True)
            continue
        return bm, rnd
    return "TIMEOUT", rnd

if __name__ == "__main__":
    E = int(sys.argv[1]) if len(sys.argv) > 1 else 120
    res, rnd = solve(E)
    if res is None:
        print(f"UNSAT at E<={E} ({rnd} rounds) => min > {E}")
    elif res == "TIMEOUT":
        print(f"TIMEOUT at E<={E} after {rnd} rounds")
    else:
        e = sum(bin(a).count("1") for a in res) // 2
        # final verify
        comp = [(~res[v]) & FULL & ~(1 << v) for v in range(N)]
        assert find_clique_bm(comp, 6) is None, "alpha fail"
        assert find_clique_bm(res, 6) is None, "omega fail"
        A = np.array([[res[i] >> j & 1 for j in range(N)] for i in range(N)], dtype=np.int8)
        assert not cap_violations(A), "cap fail"
        degs = sorted(bin(a).count("1") for a in res)
        print(f"FOUND E<={E}: edges={e}, rounds={rnd}, VERIFIED alpha<=5,omega<=5,cap-16. degs={degs}")
        json.dump({"n": N, "edges": e, "degrees": degs, "adj": A.tolist()},
                  open(f"data/r6/candidates/class0_n31_E{e}.json", "w"))
        print(f"  wrote data/r6/candidates/class0_n31_E{e}.json")
