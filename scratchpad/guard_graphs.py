"""
Enumerate ALL G in G_{n,r} (K_{r+1}-free, chi>r) and examine every 'guard' config:
a max-degree vertex x, a proper (r-1)-colouring kappa of D=N(x), c=n-|D|>=2, and
some kappa-part of size <=1.  For each such config record whether the candidate
proof routes work:
  * main_ineq route:  e(G) <= sig2(blocks) - 2      (blocks = part sizes ++ [c])
  * Lemma-3 route:    exists z with chi(G - z) <= r   (max-DEGREE only, NOT max-size)
We separate EMPTY-part (min part =0) and SINGLETON (min part =1) configs.
Sanity: e(G) + kpSaving(n,r) <= t_r(n) must always hold (the theorem).
"""
import itertools, sys

def turan(n, r):
    if r <= 0: return 0
    q, s = divmod(n, r); return (n*n - (s*(q+1)**2 + (r-s)*q**2))//2
def kpsav(n, r): return (n//r - 1) if 2*r+1 <= n else 2
def sig2(bl):
    s = sum(bl); return (s*s - sum(b*b for b in bl))//2

def chi_le(adj, verts, k):
    verts = list(verts); m = len(verts); color = {}
    def bt(i):
        if i == m: return True
        v = verts[i]; used = {color[u] for u in verts[:i] if u in adj[v]}
        for c in range(k):
            if c not in used:
                color[v] = c
                if bt(i+1): return True
                del color[v]
        return False
    return bt(0)

def all_proper_colorings(adj, verts, k):
    """yield every proper k-colouring (as dict) of induced graph on verts."""
    verts = list(verts); m = len(verts); color = {}
    def bt(i):
        if i == m:
            yield dict(color); return
        v = verts[i]; used = {color[u] for u in verts[:i] if u in adj[v]}
        for c in range(k):
            if c not in used:
                color[v] = c
                yield from bt(i+1)
                del color[v]
    yield from bt(0)

def run(n, r, verbose=False):
    edges = list(itertools.combinations(range(n), 2)); E = len(edges)
    ksub = list(itertools.combinations(range(n), r+1))
    stats = {'nGnr':0, 'empty_cfg':0, 'sing_cfg':0,
             'sing_mainineq_ok':0, 'sing_mainineq_bad':0,
             'sing_lemma3_ok':0, 'sing_lemma3_bad':0,
             'empty_mainineq_ok':0, 'empty_mainineq_bad':0,
             'empty_lemma3_ok':0, 'empty_lemma3_bad':0,
             'sanity_bad':0}
    sing_bad_examples=[]; empty_bad_examples=[]
    for bits in range(1 << E):
        adj = [set() for _ in range(n)]; ne = 0
        for i,(a,b) in enumerate(edges):
            if (bits>>i)&1: adj[a].add(b); adj[b].add(a); ne+=1
        # K_{r+1}-free
        if any(all(b in adj[a] for a,b in itertools.combinations(S,2)) for S in ksub): continue
        # not r-colourable
        if chi_le(adj, range(n), r): continue
        stats['nGnr'] += 1
        deg = [len(adj[v]) for v in range(n)]; Delta = max(deg)
        tr = turan(n,r); sav = kpsav(n,r)
        if ne + sav > tr: stats['sanity_bad'] += 1  # must never happen
        # exists z with chi(G-z)<=r ?
        lemma3 = any(chi_le(adj, [v for v in range(n) if v!=z], r) for z in range(n))
        seen_cfg = set()  # dedupe (multiset of part sizes, c) per graph to limit noise
        for x in range(n):
            if deg[x] != Delta: continue
            D = sorted(adj[x]); d = len(D); c = n - d
            if c < 2: continue
            # induced graph on D must be (r-1)-partite; enumerate proper (r-1)-colourings
            for col in all_proper_colorings(adj, D, r-1):
                parts = [0]*(r-1)
                for v in D: parts[col[v]] += 1
                mn = min(parts)
                if mn > 1: continue  # not a guard config
                blocks = parts + [c]
                key = (tuple(sorted(parts)), c, min(parts))
                if key in seen_cfg: continue
                seen_cfg.add(key)
                s2 = sig2(blocks)
                mainineq_ok = (ne <= s2 - 2)
                if mn == 0:
                    stats['empty_cfg'] += 1
                    stats['empty_mainineq_ok' if mainineq_ok else 'empty_mainineq_bad'] += 1
                    stats['empty_lemma3_ok' if lemma3 else 'empty_lemma3_bad'] += 1
                    if not lemma3 and len(empty_bad_examples)<5:
                        empty_bad_examples.append((ne,blocks,bits))
                else:  # mn == 1 singleton
                    stats['sing_cfg'] += 1
                    stats['sing_mainineq_ok' if mainineq_ok else 'sing_mainineq_bad'] += 1
                    stats['sing_lemma3_ok' if lemma3 else 'sing_lemma3_bad'] += 1
                    if not mainineq_ok and len(sing_bad_examples)<8:
                        sing_bad_examples.append((ne,s2,blocks,c,lemma3,bits))
    print(f"--- n={n} r={r}: |G_(n,r)|={stats['nGnr']}, t_r={turan(n,r)}, kpSaving={kpsav(n,r)}, p_r={turan(n,r)-kpsav(n,r)}")
    print(f"    sanity violations (e+sav>t_r): {stats['sanity_bad']}")
    print(f"    EMPTY-part configs: {stats['empty_cfg']}  | e<=sig2-2: ok={stats['empty_mainineq_ok']} bad={stats['empty_mainineq_bad']}  | exists z chi(G-z)<=r: ok={stats['empty_lemma3_ok']} bad={stats['empty_lemma3_bad']}")
    print(f"    SINGLETON  configs: {stats['sing_cfg']}  | e<=sig2-2: ok={stats['sing_mainineq_ok']} bad={stats['sing_mainineq_bad']}  | exists z chi(G-z)<=r: ok={stats['sing_lemma3_ok']} bad={stats['sing_lemma3_bad']}")
    if sing_bad_examples:
        print("    SINGLETON e>sig2-2 examples (e, sig2, blocks, c, lemma3ok, bits):")
        for ex in sing_bad_examples: print("       ", ex)
    if empty_bad_examples:
        print("    EMPTY lemma3-FAIL examples (e, blocks, bits):")
        for ex in empty_bad_examples: print("       ", ex)
    sys.stdout.flush()
    return stats

if __name__ == "__main__":
    for (n,r) in [(6,3),(7,3),(7,4)]:
        run(n,r)
