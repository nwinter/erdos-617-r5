import itertools, sys

def analyze(n, r):
    edges = list(itertools.combinations(range(n), 2)); E = len(edges)
    ksub = list(itertools.combinations(range(n), r+1))
    def chi_le(adjset, verts, k):
        verts = list(verts); m = len(verts); color = {}
        def bt(i):
            if i == m: return True
            v = verts[i]; used = {color[u] for u in verts[:i] if u in adjset[v]}
            for c in range(k):
                if c not in used:
                    color[v] = c
                    if bt(i+1): return True
                    del color[v]
            return False
        return bt(0)
    best = -1; best_graphs = []
    for bits in range(1 << E):
        adjset = [set() for _ in range(n)]; ne = 0
        for i,(a,b) in enumerate(edges):
            if (bits >> i) & 1:
                adjset[a].add(b); adjset[b].add(a); ne += 1
        if any(all(b in adjset[a] for a,b in itertools.combinations(S,2)) for S in ksub): continue
        if chi_le(adjset, range(n), r): continue
        if ne > best: best = ne; best_graphs = [adjset]
        elif ne == best: best_graphs.append(adjset)
    if best < 0: print(f"n={n} r={r}: EMPTY"); return
    # for each max graph: does removing a MIN-DEGREE vertex's non-neighbour work? does a min-degree vertex z work?
    all_exists = True; mindeg_nonnbr_works = 0; total=0
    for adjset in best_graphs:
        total += 1
        deg = [len(adjset[v]) for v in range(n)]
        exists = any(chi_le(adjset, [v for v in range(n) if v!=z], r) for z in range(n))
        all_exists = all_exists and exists
        # heuristic: pick w = min-degree vertex; z = a non-neighbour of w; does chi(G-z)<=r?
        w = min(range(n), key=lambda v: deg[v])
        nonnbrs = [z for z in range(n) if z!=w and z not in adjset[w]]
        hit = any(chi_le(adjset, [v for v in range(n) if v!=z], r) for z in nonnbrs)
        if hit or not nonnbrs: mindeg_nonnbr_works += 1
    print(f"n={n} r={r}: pr={best}, #max={total}, ALL have z with chi(G-z)<=r: {all_exists}, "
          f"min-deg-vertex's non-nbr works: {mindeg_nonnbr_works}/{total}")
    sys.stdout.flush()

analyze(6,3); analyze(7,3); analyze(7,4)
