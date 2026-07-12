import itertools, sys

def run(n, r):
    edges = list(itertools.combinations(range(n), 2))
    E = len(edges)
    # precompute k-subsets for clique test (K_{r+1})
    ksub = list(itertools.combinations(range(n), r+1))
    def chi_le(adjset, verts, k):
        verts = list(verts); m = len(verts)
        # backtracking k-colouring
        color = {}
        order = verts
        def bt(i):
            if i == m: return True
            v = order[i]
            used = set()
            for u in order[:i]:
                if u in adjset[v]:
                    used.add(color[u])
            for c in range(k):
                if c not in used:
                    color[v] = c
                    if bt(i+1): return True
                    del color[v]
            return False
        return bt(0)
    best = -1; best_graphs = []
    for bits in range(1 << E):
        adjset = [set() for _ in range(n)]
        ne = 0
        for i,(a,b) in enumerate(edges):
            if (bits >> i) & 1:
                adjset[a].add(b); adjset[b].add(a); ne += 1
        # K_{r+1}-free?
        kfree = True
        for S in ksub:
            if all(b in adjset[a] for a,b in itertools.combinations(S,2)):
                kfree = False; break
        if not kfree: continue
        # NOT r-colourable?
        if chi_le(adjset, range(n), r): continue
        if ne > best:
            best = ne; best_graphs = [adjset]
        elif ne == best:
            best_graphs.append(adjset)
    if best < 0:
        print(f"n={n} r={r}: G(n,r) EMPTY"); return
    allz = True; details=[]
    for adjset in best_graphs:
        found = any(chi_le(adjset, [v for v in range(n) if v!=z], r) for z in range(n))
        if not found: allz = False
        details.append(found)
    print(f"n={n} r={r}: pr={best} edges, #maxgraphs={len(best_graphs)}, "
          f"ALL have some z with chi(G-z)<=r: {allz}  ({details[:8]}{'...' if len(details)>8 else ''})")

for (n,r) in [(6,3),(7,3),(8,3)]:
    run(n,r)
    sys.stdout.flush()
