#!/usr/bin/env python3
"""Construct + BRUTE-FORCE VERIFY an explicit class-0 graph on 31 vertices with
alpha<=5, omega<=5 (K_6-free -- forced by the section-5 analogue), cap-16, minimal
edges.  Greedy edge-removal local search from K_31.  Adjacency = list of 31 ints."""
import random, sys, json
from itertools import combinations

N = 31
FULL = (1 << N) - 1


def find_clique(adj, k, cand=None, chosen=0):
    """return a k-clique (bitmask) or None. cand defaults to all."""
    if cand is None:
        cand = FULL
    if bin(chosen).count("1") == k:
        return chosen
    # branch
    c = cand
    while c:
        v = (c & -c).bit_length() - 1
        c &= c - 1
        # v adjacent to all chosen?  chosen subset of adj[v]?
        if chosen & ~adj[v]:
            continue
        r = find_clique(adj, k, cand & adj[v] & ~((1 << (v + 1)) - 1), chosen | (1 << v))
        if r is not None:
            return r
    return None


def find_indep(adj, k):
    """independent k-set = clique in complement."""
    comp = [(~adj[v]) & FULL & ~(1 << v) for v in range(N)]
    return find_clique(comp, k)


def cap_ok(adj, cap=16):
    """every 7-set spans <= cap edges. returns (True) or a bad 7-set."""
    # only dense 7-sets can fail; but do honest full check via bitset counting.
    verts = range(N)
    for S in combinations(verts, 7):
        mask = 0
        for v in S:
            mask |= (1 << v)
        e = 0
        for v in S:
            e += bin(adj[v] & mask).count("1")
        if e // 2 > cap:
            return S
    return None


def edges(adj):
    return sum(bin(a).count("1") for a in adj) // 2


def verify(adj, need_K6_free=True):
    i6 = find_indep(adj, 6)
    if i6 is not None:
        return f"FAIL alpha: independent 6-set {[v for v in range(N) if i6>>v&1]}"
    if need_K6_free:
        c6 = find_clique(adj, 6)
        if c6 is not None:
            return f"FAIL omega: K_6 {[v for v in range(N) if c6>>v&1]}"
    bad = cap_ok(adj)
    if bad is not None:
        return f"FAIL cap-16: 7-set {bad}"
    return "OK"


def greedy_min(seed=0, need_K6_free=True):
    random.seed(seed)
    adj = [FULL & ~(1 << v) for v in range(N)]  # K_31
    # 1) reduce omega to 5 (break K_6s) keeping alpha<=5
    while True:
        c6 = find_clique(adj, 6)
        if c6 is None:
            break
        vs = [v for v in range(N) if c6 >> v & 1]
        # try removing an edge inside the K_6 that keeps alpha<=5
        random.shuffle(vs)
        done = False
        for a in vs:
            for b in vs:
                if a < b and (adj[a] >> b & 1):
                    adj[a] &= ~(1 << b); adj[b] &= ~(1 << a)
                    if find_indep(adj, 6) is None:
                        done = True; break
                    adj[a] |= (1 << b); adj[b] |= (1 << a)  # revert
            if done: break
        if not done:
            return None, "stuck breaking K_6 without creating indep-6"
    # ensure cap-16 (K_6-free on 7 vtcs already <= t_5(7)=19; may exceed 16)
    # 2) greedily remove any edge whose removal keeps alpha<=5, omega<=5
    pairs = [(a, b) for a in range(N) for b in range(a + 1, N)]
    improved = True
    while improved:
        improved = False
        random.shuffle(pairs)
        for a, b in pairs:
            if adj[a] >> b & 1:
                adj[a] &= ~(1 << b); adj[b] &= ~(1 << a)
                if find_indep(adj, 6) is None:  # still alpha<=5 (omega only drops)
                    improved = True
                else:
                    adj[a] |= (1 << b); adj[b] |= (1 << a)
    return adj, verify(adj, need_K6_free)


if __name__ == "__main__":
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    adj, status = greedy_min(seed)
    if adj is None:
        print("construction failed:", status); sys.exit(1)
    print(f"seed={seed}: edges={edges(adj)}  verify: {status}")
    if status == "OK":
        out = {"n": N, "edges": edges(adj),
               "adj": [[ (adj[i] >> j & 1) for j in range(N)] for i in range(N)],
               "degrees": sorted(bin(a).count("1") for a in adj)}
        with open(f"data/r6/candidates/class0_n31_greedy_s{seed}.json", "w") as f:
            json.dump(out, f)
        print("  degrees:", out["degrees"])
        print(f"  wrote data/r6/candidates/class0_n31_greedy_s{seed}.json")
