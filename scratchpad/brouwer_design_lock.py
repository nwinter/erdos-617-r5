from itertools import combinations

def build_G(Astar, y=4):
    # KP construction G(n) for n=(4,4,4,4,4), n=21. Parts N1..N5 each size 4, plus x=20.
    parts = [list(range(4*i, 4*i+4)) for i in range(5)]  # N1..N5
    N1, N2, N3, N4, N5 = parts
    x = 20
    part_of = {}
    for i,p in enumerate(parts):
        for v in p: part_of[v] = i
    part_of[x] = 5  # x its own
    adj = [[False]*21 for _ in range(21)]
    def setedge(a,b,val=True):
        adj[a][b]=val; adj[b][a]=val
    # complete 5-partite: edge between different parts (only among 0..19)
    for a in range(20):
        for b in range(a+1,20):
            if part_of[a]!=part_of[b]:
                setedge(a,b,True)
    # add x adjacent to N3 u N4 u N5 u {y} u Astar
    xadj = set(N3)|set(N4)|set(N5)|{y}|set(Astar)
    for v in xadj:
        setedge(x,v,True)
    # remove edges between y and Astar
    for a in Astar:
        setedge(y,a,False)
    return adj

def num_edges(adj):
    n=len(adj); return sum(1 for a in range(n) for b in range(a+1,n) if adj[a][b])

def has_indep(adj, k):
    n=len(adj)
    for S in combinations(range(n), k):
        if all(not adj[a][b] for a,b in combinations(S,2)):
            return S
    return None

def has_clique(adj, k):
    n=len(adj)
    for S in combinations(range(n), k):
        if all(adj[a][b] for a,b in combinations(S,2)):
            return S
    return None

print("=== Design-lock: G((4,4,4,4,4)) extremal construction, n=21 ===")
for sizeA in [1,2,3]:
    Astar = list(range(sizeA))  # subset of N1={0,1,2,3}
    adj = build_G(Astar, y=4)
    e = num_edges(adj)
    indep5 = has_indep(adj,5)   # alpha >=5 ?
    clq6 = has_clique(adj,6)    # K6 ?
    print(f"|A*|={sizeA}: e={e}, K6-free={clq6 is None}, alpha<=4 = {indep5 is None}"
          + (f"  [indep5={indep5}]" if indep5 else "")
          + (f"  [K6={clq6}]" if clq6 else ""))
