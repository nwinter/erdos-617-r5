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
    def bipartite(adjset, verts):
        return chi_le(adjset, verts, 2)
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
    # For each max G and EACH max-degree vertex x, check: is G[C] bipartite, C = V \ N[x]?
    # Also restrict to Case B: G[N(x)] is (r-1)-colourable.
    total=0; gc_bip_all_x=0; gc_bip_some_x=0; caseB_count=0; caseB_gc_bip=0
    for adjset in best_graphs:
        total+=1
        deg=[len(adjset[v]) for v in range(n)]
        Delta=max(deg)
        maxdeg_verts=[v for v in range(n) if deg[v]==Delta]
        all_bip=True; some_bip=False
        for x in maxdeg_verts:
            Nx=adjset[x]; C=[v for v in range(n) if v!=x and v not in Nx]  # non-neighbours of x (C\{x}); x is isolated in G[C]
            is_bip = bipartite(adjset, C)
            if is_bip: some_bip=True
            else: all_bip=False
            # Case B: G[N(x)] (r-1)-colourable
            if chi_le(adjset, list(Nx), r-1):
                caseB_count+=1
                if is_bip: caseB_gc_bip+=1
        if all_bip: gc_bip_all_x+=1
        if some_bip: gc_bip_some_x+=1
    print(f"n={n} r={r}: #max={total} | G[C] bipartite for ALL max-deg x: {gc_bip_all_x}/{total}; "
          f"for SOME max-deg x: {gc_bip_some_x}/{total} | (x,CaseB) pairs: {caseB_count}, of which G[C] bipartite: {caseB_gc_bip}")
    sys.stdout.flush()
analyze(6,3); analyze(7,3); analyze(7,4)
