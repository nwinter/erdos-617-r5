"""Fast check: for k = |N(s)∩N(t)| in {0,1} (already shown k<=1 via Rest-independent + alpha),
fix s,t and their 3-neighborhoods with overlap k, then backtrack only the 7-set internal edges,
requiring tri-free + all degrees hit [3,3,4^7] + alpha<=4. Confirm ZERO completions for k=0,1
(so s~t is forced). Vertices: s=7, t=8 (NON-adjacent). N(s),N(t) chosen among 0..6."""
from itertools import combinations
N=9; S,T=7,8
def alpha_le4(adj):
    for St in combinations(range(N),5):
        if all(not adj[x][y] for x,y in combinations(St,2)): return False
    return True

def count_for_k(k):
    # N(s) = {0,1,2}; N(t) overlaps N(s) in first k, rest fresh.
    Ns=[0,1,2]
    Nt=Ns[:k]+[3,4,5][:3-k]  # e.g. k=0: [3,4,5]; k=1:[0,3,4]
    Nt=Ns[:k]+ [x for x in [3,4,5,6] if x not in Ns][:3-k]
    base=[[False]*N for _ in range(N)]
    for v in Ns: base[S][v]=base[v][S]=True
    for v in Nt: base[T][v]=base[v][T]=True
    # s NOT~ t already (we never add it)
    # remaining editable pairs: among 0..6 (the 7-set), excluding s,t edges already set.
    editable=[(i,j) for i in range(7) for j in range(i+1,7)]
    target={v:(3 if v in (S,T) else 4) for v in range(N)}
    # current degrees from base
    deg=[sum(base[v]) for v in range(N)]
    sols=[0]
    adj=[row[:] for row in base]
    def ok_trifree(i,j):
        return not any(adj[i][c] and adj[j][c] for c in range(N) if c!=i and c!=j)
    def bt(idx):
        if idx==len(editable):
            if all(deg[v]==target[v] for v in range(N)) and alpha_le4(adj):
                sols[0]+=1
            return
        i,j=editable[idx]
        bt(idx+1)
        if deg[i]<target[i] and deg[j]<target[j] and ok_trifree(i,j):
            adj[i][j]=adj[j][i]=True; deg[i]+=1; deg[j]+=1
            bt(idx+1)
            adj[i][j]=adj[j][i]=False; deg[i]-=1; deg[j]-=1
    bt(0)
    return sols[0], Ns, Nt

for k in (0,1,2,3):
    c,Ns,Nt=count_for_k(k)
    print(f"k={k}: N(s)={Ns}, N(t)={Nt} -> completions (tri-free, degseq[3,3,4^7], alpha<=4, s!~t): {c}")
print("\n(k<=1 proven via alpha; k=2,3 shown for completeness. All should be 0 => s~t forced.)")
