"""Base (2,9) classification analysis.

Goal: confirm EXACTLY TWO iso classes of triangle-free, alpha<=4, e=17 graphs on 9 vertices,
matching base9A2 (degseq [3,3,4^7]) and base9A1 (degseq [2,4^8]); then probe a rooting
reduction that could make the Lean classification decidable/native_decide-able.
"""
from itertools import combinations
import sys

N = 9

def base9A2_adj(a, b):
    if a == b: return False
    if a == 8: return b in (0,1,4)
    if b == 8: return a in (0,1,4)
    diff_half = (a//4) != (b//4)
    removed = (a==4 and b in (0,1)) or (b==4 and a in (0,1))
    return diff_half and not removed

def base9A1_adj(a, b):
    if a == b: return False
    if a == 8: return b in (0,4)
    if b == 8: return a in (0,4)
    diff_half = (a//4) != (b//4)
    removed = (a==4 and b==0) or (b==4 and a==0)
    return diff_half and not removed

def adj_matrix(fn):
    return [[fn(a,b) for b in range(N)] for a in range(N)]

def edges(M):
    return [(a,b) for a in range(N) for b in range(a+1,N) if M[a][b]]

def degseq(M):
    return sorted(sum(1 for b in range(N) if M[a][b]) for a in range(N))

def triangle_free(M):
    for a,b,c in combinations(range(N),3):
        if M[a][b] and M[b][c] and M[a][c]:
            return False
    return True

def alpha(M):
    best = 0
    for k in range(N,0,-1):
        for S in combinations(range(N),k):
            if all(not M[a][b] for a,b in combinations(S,2)):
                return k
    return 0

for name, fn in [("base9A2", base9A2_adj), ("base9A1", base9A1_adj)]:
    M = adj_matrix(fn)
    E = edges(M)
    print(f"{name}: e={len(E)}, degseq={degseq(M)}, triangle_free={triangle_free(M)}, alpha={alpha(M)}")

# Canonical form via brute permutation (9! = 362880) — feasible.
from math import factorial
def canon(M):
    import itertools
    best = None
    verts = list(range(N))
    for perm in itertools.permutations(verts):
        # relabel: new vertex i is old perm[i]
        bits = 0
        idx = 0
        for a in range(N):
            for b in range(a+1,N):
                if M[perm[a]][perm[b]]:
                    bits |= (1<<idx)
                idx += 1
        if best is None or bits < best:
            best = bits
    return best

print("\nComputing canonical forms (9! perms each)...")
c2 = canon(adj_matrix(base9A2_adj))
c1 = canon(adj_matrix(base9A1_adj))
print(f"canon(base9A2)={c2}")
print(f"canon(base9A1)={c1}")
print(f"distinct classes: {c2 != c1}")
