"""Independent enumeration: ALL triangle-free, alpha<=4, e=17 graphs on 9 vertices, up to iso.
Backtracking over the 36 vertex-pairs with triangle-free + degree<=4 pruning + e=17 target.
Then canonicalize (9! brute) and dedupe. Confirms the '<=2 iso classes' claim."""
from itertools import combinations, permutations
import sys

N = 9
PAIRS = [(a,b) for a in range(N) for b in range(a+1,N)]
M = len(PAIRS)  # 36
TARGET = 17

results = set()  # canonical bitmasks

def canon(adj):
    best = None
    for perm in permutations(range(N)):
        bits = 0; idx = 0
        for a in range(N):
            for b in range(a+1,N):
                if adj[perm[a]][perm[b]]:
                    bits |= (1<<idx)
                idx += 1
        if best is None or bits < best:
            best = bits
    return best

def alpha_le4(adj):
    for S in combinations(range(N),5):
        if all(not adj[a][b] for a,b in combinations(S,2)):
            return False
    return True

adj = [[False]*N for _ in range(N)]
deg = [0]*N
count_graphs = 0

def bt(i, ecount):
    global count_graphs
    # prune: can't reach TARGET or overshoot
    remaining = M - i
    if ecount + remaining < TARGET: return
    if ecount > TARGET: return
    if i == M:
        if ecount == TARGET and alpha_le4(adj):
            results.add(canon(adj))
            count_graphs += 1
        return
    a,b = PAIRS[i]
    # try NOT including edge (a,b)
    bt(i+1, ecount)
    # try including edge (a,b): triangle-free + degree<=4
    if deg[a] < 4 and deg[b] < 4:
        # triangle check: no common neighbor
        ok = True
        for c in range(N):
            if c!=a and c!=b and adj[a][c] and adj[b][c]:
                ok = False; break
        if ok:
            adj[a][b] = adj[b][a] = True
            deg[a]+=1; deg[b]+=1
            bt(i+1, ecount+1)
            adj[a][b] = adj[b][a] = False
            deg[a]-=1; deg[b]-=1

bt(0,0)
print(f"labeled graphs found (with multiplicity of construction order): {count_graphs}")
print(f"distinct iso classes: {len(results)}")
print(f"canonical forms: {sorted(results)}")
