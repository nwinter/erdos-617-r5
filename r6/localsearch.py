#!/usr/bin/env python3
"""Min-edge local search for a K_6-free alpha<=5 cap-16 graph on 31 vtcs.
Repair moves: remove an edge; if that creates independent 6-sets, add edges to
kill them (avoiding new K_6 / cap-16 violation). Keeps net edges trending down."""
import sys, json, random
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
def has_k6(adj): return fc(adj,6) is not None
def cap_bad_one(adj,cap=16):
    # find one bad 7-set quickly by checking around dense vertices; fallback full
    for A in combinations(range(N),7):
        m=0
        for v in A: m|=1<<v
        if sum(bin(adj[v]&m).count("1") for v in A)//2>cap: return A
    return None
def edges(adj): return sum(bin(a).count("1") for a in adj)//2
def adde(adj,a,b): adj[a]|=1<<b; adj[b]|=1<<a
def rme(adj,a,b): adj[a]&=~(1<<b); adj[b]&=~(1<<a)

def valid(adj):
    return indep(adj,6) is None and not has_k6(adj) and cap_bad_one(adj) is None

def run(seed, iters=4000):
    random.seed(seed)
    # start: 5 K_5 (25 vtcs) + 6 extra, then repair to valid
    adj=[0]*N
    for i in range(5):
        B=list(range(5*i,5*i+5))
        for a,b in combinations(B,2): adde(adj,a,b)
    # connect extras 25..30 densely-ish to reduce independence, then repair
    extra=list(range(25,31))
    for a,b in combinations(extra,2):
        if random.random()<0.6: adde(adj,a,b)
    for x in extra:
        for _ in range(4):
            y=random.randrange(25); adde(adj,x,y)
    # repair to validity: while invalid, fix
    for _ in range(3000):
        i6=indep(adj,6)
        if i6 is not None:
            vs=[v for v in range(N) if i6>>v&1]; a,b=random.sample(vs,2); adde(adj,a,b); continue
        if has_k6(adj):
            c6=fc(adj,6); vs=[v for v in range(N) if c6>>v&1]; a,b=random.sample(vs,2); rme(adj,a,b); continue
        cb=cap_bad_one(adj)
        if cb is not None:
            # remove a densest edge in the bad 7-set
            m=0
            for v in cb: m|=1<<v
            best=None
            for a,b in combinations(cb,2):
                if adj[a]>>b&1: best=(a,b); break
            if best: rme(adj,*best); continue
        break
    if not valid(adj): return None
    # minimize: try removing edges + repair, keep if net lower
    best_e=edges(adj); best=[a for a in adj]
    for it in range(iters):
        a=random.randrange(N)
        nb=[u for u in range(N) if adj[a]>>u&1]
        if not nb: continue
        b=random.choice(nb); rme(adj,a,b)
        # repair only alpha (removal can't create K6/cap)
        ok=True
        for _ in range(6):
            i6=indep(adj,6)
            if i6 is None: break
            vs=[v for v in range(N) if i6>>v&1]; x,y=random.sample(vs,2)
            if not(adj[x]>>y&1): adde(adj,x,y)
        else:
            ok=False
        if ok and valid(adj):
            if edges(adj)<best_e:
                best_e=edges(adj); best=[a for a in adj]
        else:
            adj=[a for a in best]  # revert to best
    return best,best_e

if __name__=="__main__":
    seed=int(sys.argv[1]) if len(sys.argv)>1 else 1
    res=run(seed)
    if res is None: print(f"seed {seed}: repair failed"); sys.exit()
    adj,e=res
    print(f"seed {seed}: best valid edges={e}, degrees={sorted(bin(a).count('1') for a in adj)}")
    if valid(adj):
        json.dump({"n":N,"edges":e,"degrees":sorted(bin(a).count('1') for a in adj),
                   "adj":[[adj[i]>>j&1 for j in range(N)] for i in range(N)]},
                  open(f"data/r6/candidates/class0_n31_ls_s{seed}_E{e}.json","w"))
        print(f"  VERIFIED, wrote data/r6/candidates/class0_n31_ls_s{seed}_E{e}.json")
