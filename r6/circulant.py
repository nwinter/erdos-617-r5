#!/usr/bin/env python3
"""Search circulants C_31(S) for alpha<=5, omega<=5, cap-16, minimising degree.
Vertex-transitive => cheap. Also a SANITY CHECK on the DP e(H)>=98 lower bound:
any valid graph found below 98 edges would REFUTE the bound."""
from itertools import combinations
N = 31
FULL = (1 << N) - 1

def build(S):
    Sset = set()
    for s in S:
        Sset.add(s % N); Sset.add((-s) % N)
    adj = [0]*N
    for v in range(N):
        m = 0
        for s in Sset:
            m |= 1 << ((v+s) % N)
        adj[v] = m
    return adj

def find_clique(adj, k, cand=None, chosen=0):
    if cand is None: cand = FULL
    if bin(chosen).count("1") == k: return chosen
    c = cand
    while c:
        v = (c & -c).bit_length()-1; c &= c-1
        if chosen & ~adj[v]: continue
        r = find_clique(adj, k, cand & adj[v] & ~((1<<(v+1))-1), chosen|(1<<v))
        if r is not None: return r
    return None

def alpha_ge(adj, k):
    comp = [(~adj[v]) & FULL & ~(1<<v) for v in range(N)]
    return find_clique(comp, k) is not None

def cap_bad(adj, cap=16):
    for Sv in combinations(range(N), 7):
        mask = 0
        for v in Sv: mask |= 1<<v
        e = sum(bin(adj[v]&mask).count("1") for v in Sv)//2
        if e > cap: return True
    return False

def edges(adj): return sum(bin(a).count("1") for a in adj)//2

found = []
for pairs in range(3, 6):                      # 3 pairs=deg6, 4=deg8, 5=deg10
    for S in combinations(range(1, 16), pairs):
        adj = build(S)
        # quick: alpha<=5 (no indep 6) and omega<=5 (no K6)
        if alpha_ge(adj, 6): continue
        if find_clique(adj, 6) is not None: continue
        e = edges(adj)
        capbad = cap_bad(adj)
        found.append((e, pairs, S, not capbad))
        print(f"  C_31{S}: deg={2*pairs} edges={e}  alpha<=5,omega<=5 OK  cap16={'OK' if not capbad else 'FAIL'}", flush=True)
    if found and min(f[0] for f in found) < 999:
        # keep scanning this degree fully; stop after first degree with a full pass
        if any(f[1]==pairs and f[3] for f in found):
            break
print("\nvalid (incl cap-16):", [(e,S) for e,p,S,ok in sorted(found) if ok][:8])
if found:
    best = min((f for f in found if f[3]), default=None, key=lambda x:x[0])
    print("best cap-OK circulant edges:", best[0] if best else None,
          "  (DP lower bound is 98; anything <98 would refute it)")
