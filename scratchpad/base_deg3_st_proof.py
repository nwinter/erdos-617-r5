"""Verify the s~t proof outline for the [3,3,4^7] case.
Claim chain (assuming s NOT~ t, tri-free, alpha<=4, degseq [3,3,4^7]):
  Rest := common non-neighbors of s,t (in V\{s,t}), |Rest| = 1 + k, k=|N(s)∩N(t)|.
  (1) Rest is independent.
  (2) Rest ∪ {s,t} independent ⇒ |Rest|+2 <= alpha=4 ⇒ |Rest|<=2 ⇒ k<=1.
  (3) k=0 and k=1 each yield a contradiction.
We brute-force ALL abstract graphs on 9 labelled vertices consistent with the s NOT~ t hypothesis
+ degseq + tri-free, confirm none exist, and characterise the obstruction for k=0,1.
We do a constrained backtracking build with s=7,t=8 fixed, s NOT~ t, deg(s)=deg(t)=3, others deg 4."""
from itertools import combinations, product

N=9
S,T=7,8

def build_all():
    # vertices 0..6 are the 'others' (deg 4), 7=s,8=t (deg 3), s NOT~ t.
    # enumerate adjacency among all pairs with backtracking + tri-free + degree caps + s!~t.
    pairs=[(i,j) for i in range(N) for j in range(i+1,N)]
    adj=[[False]*N for _ in range(N)]
    deg=[0]*N
    target={v:(3 if v in (S,T) else 4) for v in range(N)}
    sols=[]
    forbidden={(S,T)}  # s not adjacent t
    def bt(idx):
        if idx==len(pairs):
            if all(deg[v]==target[v] for v in range(N)):
                sols.append([row[:] for row in adj])
            return
        i,j=pairs[idx]
        rem=len(pairs)-idx
        # prune: if remaining can't fill degrees
        # try excluding
        # (branch: not adjacent)
        bt(idx+1)
        # branch: adjacent, if allowed
        if (i,j) in forbidden: return
        if deg[i]<target[i] and deg[j]<target[j]:
            # tri-free: no common neighbor
            if not any(adj[i][c] and adj[j][c] for c in range(N) if c!=i and c!=j):
                adj[i][j]=adj[j][i]=True; deg[i]+=1; deg[j]+=1
                bt(idx+1)
                adj[i][j]=adj[j][i]=False; deg[i]-=1; deg[j]-=1
    bt(0)
    return sols

def alpha(adj):
    for k in range(N,0,-1):
        for St in combinations(range(N),k):
            if all(not adj[x][y] for x,y in combinations(St,2)): return k
    return 0

sols=build_all()
print(f"tri-free graphs with s=7,t=8 NON-adjacent, degseq[3,3,4^7]: {len(sols)} (labelled, s,t fixed)")
# among them, how many have alpha<=4?
al4=[a for a in sols if alpha(a)<=4]
print(f"...with alpha<=4: {len(al4)}  (should be 0 to confirm s~t forced under alpha<=4)")
# distribution of k and alpha
from collections import Counter
kc=Counter(); ac=Counter()
for a in sols:
    Ns=set(v for v in range(N) if a[S][v]); Nt=set(v for v in range(N) if a[T][v])
    k=len(Ns&Nt); kc[k]+=1; ac[(k,alpha(a))]+=1
print("k distribution among s!~t solutions:", dict(kc))
print("(k, alpha) distribution:", dict(sorted(ac.items())))
