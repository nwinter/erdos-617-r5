"""
RELAXED probe: for each G in G_{n,r} and EVERY vertex x with c=n-deg(x)>=2 whose
neighbourhood D=N(x) is (r-1)-partite, look at every proper (r-1)-colouring with a
size-<=1 part.  Track separately whether x is a max-degree vertex.  Goal: find out
whether the 'singleton part' config arises at all, and whether requiring x max-degree
is what forbids it.
"""
import itertools, sys
def turan(n,r):
    if r<=0: return 0
    q,s=divmod(n,r); return (n*n-(s*(q+1)**2+(r-s)*q**2))//2
def kpsav(n,r): return (n//r-1) if 2*r+1<=n else 2
def sig2(bl):
    s=sum(bl); return (s*s-sum(b*b for b in bl))//2
def chi_le(adj,verts,k):
    verts=list(verts); m=len(verts); color={}
    def bt(i):
        if i==m: return True
        v=verts[i]; used={color[u] for u in verts[:i] if u in adj[v]}
        for c in range(k):
            if c not in used:
                color[v]=c
                if bt(i+1): return True
                del color[v]
        return False
    return bt(0)
def all_proper(adj,verts,k):
    verts=list(verts); m=len(verts); color={}
    def bt(i):
        if i==m: yield dict(color); return
        v=verts[i]; used={color[u] for u in verts[:i] if u in adj[v]}
        for c in range(k):
            if c not in used:
                color[v]=c; yield from bt(i+1); del color[v]
    yield from bt(0)

def run(n,r):
    edges=list(itertools.combinations(range(n),2)); E=len(edges)
    ksub=list(itertools.combinations(range(n),r+1))
    cnt={'any_sing':0,'any_empty':0,'max_sing':0,'max_empty':0,'nGnr':0}
    ex_any=[]; ex_max=[]
    for bits in range(1<<E):
        adj=[set() for _ in range(n)]; ne=0
        for i,(a,b) in enumerate(edges):
            if (bits>>i)&1: adj[a].add(b); adj[b].add(a); ne+=1
        if any(all(b in adj[a] for a,b in itertools.combinations(S,2)) for S in ksub): continue
        if chi_le(adj,range(n),r): continue
        cnt['nGnr']+=1
        deg=[len(adj[v]) for v in range(n)]; Delta=max(deg)
        for x in range(n):
            d=deg[x]; c=n-d
            if c<2: continue
            D=sorted(adj[x])
            for col in all_proper(adj,D,r-1):
                parts=[0]*(r-1)
                for v in D: parts[col[v]]+=1
                mn=min(parts)
                if mn>1: continue
                ismax=(deg[x]==Delta)
                blocks=parts+[c]
                if mn==0:
                    cnt['any_empty']+=1
                    if ismax: cnt['max_empty']+=1
                else:
                    cnt['any_sing']+=1
                    if ismax: cnt['max_sing']+=1
                    if len(ex_any)<4: ex_any.append((ne,sorted(parts),c,deg[x],Delta,ismax))
                    if ismax and len(ex_max)<4: ex_max.append((ne,sorted(parts),c,deg[x],Delta))
    print(f"n={n} r={r}: |G_(n,r)|={cnt['nGnr']}")
    print(f"   ANY-x  singleton configs: {cnt['any_sing']}   empty configs: {cnt['any_empty']}")
    print(f"   MAX-deg-x singleton configs: {cnt['max_sing']}   empty configs: {cnt['max_empty']}")
    if ex_any: print("   ANY-x singleton examples (e,parts,c,deg_x,Delta,ismax):", ex_any)
    if ex_max: print("   MAX-x singleton examples (e,parts,c,deg_x,Delta):", ex_max)
    sys.stdout.flush()

for (n,r) in [(6,3),(7,3),(7,4),(6,2),(7,2)]:
    run(n,r)
