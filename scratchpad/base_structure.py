"""Verify the structural determination claims for both base cases, to script the Lean proof."""
from itertools import combinations

N = 9
def base9A2_adj(a,b):
    if a==b: return False
    if a==8: return b in (0,1,4)
    if b==8: return a in (0,1,4)
    return ((a//4)!=(b//4)) and not ((a==4 and b in(0,1)) or (b==4 and a in(0,1)))
def base9A1_adj(a,b):
    if a==b: return False
    if a==8: return b in (0,4)
    if b==8: return a in (0,4)
    return ((a//4)!=(b//4)) and not ((a==4 and b==0) or (b==4 and a==0))

def mk(fn): return [[fn(a,b) for b in range(N)] for a in range(N)]
def deg(M,v): return sum(M[v])
def nbrs(M,v): return [u for u in range(N) if M[v][u]]

def analyze(name, M):
    print(f"\n===== {name} =====")
    degs = {v: deg(M,v) for v in range(N)}
    print("degrees:", degs)
    mind = min(degs.values())
    lowverts = [v for v in range(N) if degs[v]==mind]
    print(f"min degree = {mind}, at vertices {lowverts}")
    if mind == 2:
        a = lowverts[0]
        Na = nbrs(M,a); p,q = Na
        print(f"[2,4^8] apex a={a}, N(a)={{{p},{q}}}, p~q? {M[p][q]}")
        W = [w for w in range(N) if w!=a and w!=p and w!=q]
        print(f"W (6 verts) = {W}")
        eW = sum(1 for u,v in combinations(W,2) if M[u][v])
        print(f"edges within W = {eW} (should be 9 = K33)")
        # bipartition of W by adjacency
        # check W is K33: every vertex has W-degree 3
        for w in W:
            dW = sum(1 for u in W if M[w][u])
            print(f"  W-deg({w}) = {dW}, ~p? {M[w][p]}, ~q? {M[w][q]}")
    else:  # [3,3,4^7]
        s,t = lowverts
        print(f"[3,3,4^7] deg-3 verts s={s},t={t}, s~t? {M[s][t]}")
        print(f"  N(s)={nbrs(M,s)}, N(t)={nbrs(M,t)}")
        # common neighbors
        common = set(nbrs(M,s)) & set(nbrs(M,t))
        print(f"  common nbrs of s,t: {sorted(common)}")
        # Delete closed nbhd of s: N[s]
        Ns = set(nbrs(M,s)) | {s}
        R = [v for v in range(N) if v not in Ns]
        print(f"  N[s]={sorted(Ns)}, R=V\\N[s] = {R} ({len(R)} verts)")
        eR = sum(1 for u,v in combinations(R,2) if M[u][v])
        print(f"  edges within R = {eR}")
        # Try: two independent 4-sets partition
        # find all independent 4-sets
        ind4 = [S for S in combinations(range(N),4) if all(not M[a][b] for a,b in combinations(S,2))]
        print(f"  # independent 4-sets = {len(ind4)}")
        # find disjoint pairs covering 8 vertices
        for i in range(len(ind4)):
            for j in range(i+1,len(ind4)):
                if not (set(ind4[i]) & set(ind4[j])):
                    apex = (set(range(N)) - set(ind4[i]) - set(ind4[j]))
                    print(f"    disjoint ind4 pair: {ind4[i]} | {ind4[j]}, apex={sorted(apex)}")

analyze("base9A1 [2,4^8]", mk(base9A1_adj))
analyze("base9A2 [3,3,4^7]", mk(base9A2_adj))
