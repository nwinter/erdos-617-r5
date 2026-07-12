"""
(A) Lemma 5 optimality at (5,21): among all sequences n=(n1<=...<=n5), sum=20, n4>=2 [cond (3)],
    e(G(n)) = sig2(n)+sig1(n)-ns-nt+1 (ns,nt two smallest parts >1).  Find the maximisers.
(B) For each maximiser, build all |A| variants, check K6-free, alpha<=4, e=173, count non-iso,
    and confirm the complement has AB21 (A=K5-e, B=K4, 4 cross).
"""
import itertools
def parts_seq(total,k):
    # nondecreasing k-tuples summing to total, each>=1
    def rec(t,k,lo):
        if k==1:
            if t>=lo: yield (t,)
            return
        for f in range(lo,t//k+1):
            for r in rec(t-f,k-1,f): yield (f,)+r
    yield from rec(total,k,1)
def sig2(seq):
    s=sum(seq); return (s*s-sum(a*a for a in seq))//2
def eG(seq):
    # ns,nt = two smallest parts that are >1
    big=[a for a in seq if a>1]
    if len(big)<2: return None  # (3) needs n_{r-1}>=2 => >=2 parts>1
    ns,nt=sorted(big)[:2]
    return sig2(seq)+sum(seq)-ns-nt+1

print("=== (A) Lemma 5 at (5,21): sequences sum=20, 5 parts, >=2 parts>1 ===")
best=-1; args=[]
for seq in parts_seq(20,5):
    if sum(1 for a in seq if a>1)<2: continue
    e=eG(seq)
    if e>best: best=e; args=[seq]
    elif e==best: args.append(seq)
print(f"max e(G(seq)) = {best};  #maximising sequences = {len(args)}")
print("  maximisers:", args)

# ---- (B) build G((4,4,4,4,4)) variants and check ----
def build(seq, sizeA):
    # parts N1..N5 as consecutive blocks; x = last vertex
    n=sum(seq)+1; parts=[]; idx=0
    for sz in seq:
        parts.append(list(range(idx,idx+sz))); idx+=sz
    x=n-1
    big_idx=[i for i,a in enumerate(seq) if a>1]
    s,t=sorted(big_idx, key=lambda i: seq[i])[:2]  # two smallest parts>1
    S=[i for i in range(len(seq)) if i not in (s,t)]
    Ns=parts[s]; y=parts[t][0]; Astar=Ns[:sizeA]
    adj=[[False]*n for _ in range(n)]
    def se(a,b,v): adj[a][b]=v; adj[b][a]=v
    # complete multipartite on N1..N5
    partof={}
    for i,p in enumerate(parts):
        for v in p: partof[v]=i
    for a in range(n-1):
        for b in range(a+1,n-1):
            if partof[a]!=partof[b]: se(a,b,True)
    # x connected to union_{i in S} Ni  u  ({y} u Astar)
    conn=set(y for i in S for y in parts[i]) | {y} | set(Astar)
    for v in conn: se(x,v,True)
    # remove edges between y and Astar
    for a in Astar: se(y,a,False)
    return n,adj
def has_clique(adj,n,k):
    for S in itertools.combinations(range(n),k):
        if all(adj[a][b] for a,b in itertools.combinations(S,2)): return True
    return False
def alpha_le(adj,n,m):
    for S in itertools.combinations(range(n),m+1):
        if all(not adj[a][b] for a,b in itertools.combinations(S,2)): return False
    return True
def ecount(adj,n):
    return sum(1 for a in range(n) for b in range(a+1,n) if adj[a][b])
def cert(adj,n):
    # crude iso invariant: sorted degree seq + sorted (deg, sorted-nbr-degs)
    deg=[sum(adj[v]) for v in range(n)]
    sig=tuple(sorted((deg[v],tuple(sorted(deg[u] for u in range(n) if adj[v][u]))) for v in range(n)))
    return sig

print("\n=== (B) G((4,4,4,4,4)) variants |A| in 1..3 ===")
certs={}
for sizeA in [1,2,3]:
    n,adj=build((4,4,4,4,4),sizeA)
    k6=not has_clique(adj,n,6); a4=alpha_le(adj,n,4); e=ecount(adj,n)
    degx=sum(adj[n-1])
    c=cert(adj,n); certs[sizeA]=c
    print(f" |A|={sizeA}: K6-free={k6} alpha<=4={a4} e={e} deg(x)={degx}")
print(" pairwise non-isomorphic (distinct certs):", len(set(certs.values()))==3, "  #distinct certs =", len(set(certs.values())))
