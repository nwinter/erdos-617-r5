from itertools import combinations
# Reuse design_lock construction; F = complement of G((4,4,4,4,4)) = the colour class F_i.
def build_G(Astar, y=4):
    parts = [list(range(4*i, 4*i+4)) for i in range(5)]
    N1,N2,N3,N4,N5 = parts; x=20
    part_of={}; 
    for i,p in enumerate(parts):
        for v in p: part_of[v]=i
    part_of[x]=5
    adj=[[False]*21 for _ in range(21)]
    def se(a,b,v=True): adj[a][b]=v; adj[b][a]=v
    for a in range(20):
        for b in range(a+1,20):
            if part_of[a]!=part_of[b]: se(a,b,True)
    for v in set(N3)|set(N4)|set(N5)|{y}|set(Astar): se(x,v,True)
    for a in Astar: se(y,a,False)
    return adj
def complement(adj):
    n=len(adj); F=[[False]*n for _ in range(n)]
    for a in range(n):
        for b in range(n):
            if a!=b: F[a][b]= not adj[a][b]
    return F
def e_in(F,S):
    return sum(1 for a,b in combinations(S,2) if F[a][b])

print("Verify equality21 encoding on F_i = complement(G((4,4,4,4,4))):")
for sizeA in [1,2,3]:
    Astar=list(range(sizeA)); y=4
    J=build_G(Astar,y); F=complement(J)
    # candidate A = N2 u {x} = {4,5,6,7,20}, B = N1 = {0,1,2,3}
    A=[4,5,6,7,20]; B=[0,1,2,3]
    eA=e_in(F,A); eB=e_in(F,B); eAB=e_in(F,A+B); cross=eAB-eA-eB
    # count non-edges within A (should be exactly 1 = the xy pair)
    nonA=[(a,b) for a,b in combinations(A,2) if not F[a][b]]
    # B is F-clique?
    Bclique = (eB==6)
    print(f" |A*|={sizeA}: e_F(A)={eA} (want 9, one nonedge {nonA}), "
          f"e_F(B)={eB} (want 6, K4={Bclique}), cross={cross} (want 4), e_F(A∪B)={eAB} (want 19)")
    ok = (eA==9 and len(nonA)==1 and eB==6 and cross==4 and eAB==19)
    print(f"    => equality21 conclusion satisfied: {ok}")
