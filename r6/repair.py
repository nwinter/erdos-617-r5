#!/usr/bin/env python3
"""Repair a near-miss candidate: kill all K_6 (make omega<=5) by edge edits while
keeping alpha<=5, then check cap-16. Fast because few K_6 to fix."""
import json, sys, random
from itertools import combinations
N=31; FULL=(1<<N)-1
def fc(adj,k,cand=None,chosen=0):
    if cand is None: cand=FULL
    if bin(chosen).count("1")==k: return chosen
    c=cand
    while c:
        v=(c&-c).bit_length()-1; c&=c-1
        if chosen&~adj[v]: continue
        r=fc(adj,k,cand&adj[v]&~((1<<(v+1))-1),chosen|(1<<v))
        if r is not None: return r
    return None
def indep(adj,k):
    comp=[(~adj[v])&FULL&~(1<<v) for v in range(N)]; return fc(comp,k)
def cap_bad(adj,cap=16):
    for A in combinations(range(N),7):
        m=0
        for v in A: m|=1<<v
        if sum(bin(adj[v]&m).count("1") for v in A)//2>cap: return A
    return None
def bm(A): return [sum(int(A[v][u])<<u for u in range(N)) for v in range(N)]
def edges(adj): return sum(bin(a).count("1") for a in adj)//2

def repair(path, seed=0):
    random.seed(seed)
    adj=bm(json.load(open(path))["adj"])
    print(f"  start edges={edges(adj)}, cap-16 initially: {'OK' if cap_bad(adj) is None else 'FAIL'}")
    # kill K_6's: remove an edge in each K_6 that does NOT create an independent 6-set
    for _ in range(2000):
        c6=fc(adj,6)
        if c6 is None: break
        vs=[v for v in range(N) if c6>>v&1]; random.shuffle(vs)
        done=False
        for a in vs:
            for b in vs:
                if a<b and adj[a]>>b&1:
                    adj[a]&=~(1<<b); adj[b]&=~(1<<a)
                    if indep(adj,6) is None: done=True; break
                    adj[a]|=1<<b; adj[b]|=1<<a
            if done: break
        if not done:
            # must add an edge elsewhere to allow K_6 removal: pick the indep-6 that blocks
            # remove edge and repair alpha by adding an edge in the created indep set
            a,b=vs[0],vs[1]; adj[a]&=~(1<<b); adj[b]&=~(1<<a)
            i6=indep(adj,6)
            if i6 is not None:
                iv=[v for v in range(N) if i6>>v&1]; x,y=random.sample(iv,2); adj[x]|=1<<y; adj[y]|=1<<x
    if fc(adj,6) is not None: return None,"still has K_6"
    if indep(adj,6) is not None: return None,"alpha broke"
    # fix cap-16 by removing densest edges in bad 7-sets (keeping alpha)
    for _ in range(500):
        cb=cap_bad(adj)
        if cb is None: break
        # remove an edge in the bad 7-set that keeps alpha<=5
        vs=list(cb); fixed=False
        for a in vs:
            for b in vs:
                if a<b and adj[a]>>b&1:
                    adj[a]&=~(1<<b); adj[b]&=~(1<<a)
                    if indep(adj,6) is None and fc(adj,6) is None: fixed=True; break
                    adj[a]|=1<<b; adj[b]|=1<<a
            if fixed: break
        if not fixed: return None,"cap stuck"
    ok = indep(adj,6) is None and fc(adj,6) is None and cap_bad(adj) is None
    return (adj if ok else None), ("OK" if ok else "final invalid")

if __name__=="__main__":
    path=sys.argv[1] if len(sys.argv)>1 else "data/r6/candidates/class0_n31_m104.json"
    for seed in range(8):
        adj,st=repair(path,seed)
        if adj is not None:
            e=edges(adj)
            print(f"seed {seed}: REPAIRED -> K_6-free, alpha<=5, cap-16, edges={e}")
            json.dump({"n":N,"edges":e,"note":"repaired from "+path.split('/')[-1]+" to be K_6-free",
                       "degrees":sorted(bin(a).count('1') for a in adj),
                       "adj":[[adj[i]>>j&1 for j in range(N)] for i in range(N)]},
                      open(f"data/r6/candidates/class0_n31_K6free_E{e}.json","w"))
            print(f"  wrote data/r6/candidates/class0_n31_K6free_E{e}.json"); break
        else:
            print(f"seed {seed}: {st}")
