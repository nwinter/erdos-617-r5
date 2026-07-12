import itertools, sys
def analyze(n, r):
    edges = list(itertools.combinations(range(n), 2)); E = len(edges)
    ksub = list(itertools.combinations(range(n), r+1))
    def chi_le(adjset, verts, k):
        verts=list(verts); m=len(verts); color={}
        def bt(i):
            if i==m: return True
            v=verts[i]; used={color[u] for u in verts[:i] if u in adjset[v]}
            for c in range(k):
                if c not in used:
                    color[v]=c
                    if bt(i+1): return True
                    del color[v]
            return False
        return bt(0)
    best=-1; best_graphs=[]
    for bits in range(1<<E):
        adjset=[set() for _ in range(n)]; ne=0
        for i,(a,b) in enumerate(edges):
            if (bits>>i)&1: adjset[a].add(b); adjset[b].add(a); ne+=1
        if any(all(b in adjset[a] for a,b in itertools.combinations(S,2)) for S in ksub): continue
        if chi_le(adjset, range(n), r): continue
        if ne>best: best=ne; best_graphs=[adjset]
        elif ne==best: best_graphs.append(adjset)
    if best<0: print(f"n={n} r={r}: EMPTY"); return
    # For each max G: does there EXIST a vertex w whose non-neighbours M(w)=V\N[w] are independent
    # AND removing one z in M(w) gives chi(G-z)<=r?  Also: is M(w) independent for the MIN-deg w?
    exists_indep_w=0; mindeg_M_indep=0; colour_scheme_works=0; total=0
    for adjset in best_graphs:
        total+=1
        deg=[len(adjset[v]) for v in range(n)]
        # scheme: exists w such that M(w)=nonnbrs are independent, and chi(G[N(w)])<=r-1
        found=False
        for w in range(n):
            M=[v for v in range(n) if v!=w and v not in adjset[w]]
            Mindep = all(b not in adjset[a] for a,b in itertools.combinations(M,2))
            if Mindep:
                # colour {w}∪M one colour; need N(w) to be (r-1)-colourable
                Nw=[v for v in adjset[w]]
                if chi_le(adjset, Nw, r-1):
                    found=True; break
        if found: colour_scheme_works+=1
        w0=min(range(n),key=lambda v:deg[v])
        M0=[v for v in range(n) if v!=w0 and v not in adjset[w0]]
        if all(b not in adjset[a] for a,b in itertools.combinations(M0,2)): mindeg_M_indep+=1
    print(f"n={n} r={r}: #max={total}; SCHEME (exists w: nonnbrs indep AND G[N(w)] is (r-1)-col): "
          f"{colour_scheme_works}/{total}; min-deg-w nonnbrs independent: {mindeg_M_indep}/{total}")
    sys.stdout.flush()
analyze(6,3); analyze(7,3)
