#!/usr/bin/env python3
"""WalkSAT-style search for alpha<=5 AND omega<=5 (K_6-free) on 31 vtcs, starting
from a hunt candidate. Only fast single-witness clique checks in the loop; cap-16
checked/repaired ONCE at the end. Edge count allowed to float in [98,124]."""
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
def k6(adj): return fc(adj,6)
def indep6(adj):
    comp=[(~adj[v])&FULL&~(1<<v) for v in range(N)]; return fc(comp,6)
def edges(adj): return sum(bin(a).count("1") for a in adj)//2
def bm(A): return [sum(int(A[v][u])<<u for u in range(N)) for v in range(N)]
def cap_bad(adj,cap=16):
    for A in combinations(range(N),7):
        m=0
        for v in A: m|=1<<v
        if sum(bin(adj[v]&m).count("1") for v in A)//2>cap: return A
    return None

def walk(adj, iters=200000, emax=124, seed=0):
    random.seed(seed)
    for it in range(iters):
        c=k6(adj); i=indep6(adj)
        if c is None and i is None:
            return adj
        e=edges(adj)
        # choose which violation to fix (random if both)
        fix_k6 = (i is None) or (c is not None and (e>=emax or random.random()<0.5))
        if fix_k6 and c is not None:
            vs=[v for v in range(N) if c>>v&1]
            a,b=random.sample(vs,2)          # remove a clique edge
            if adj[a]>>b&1: adj[a]&=~(1<<b); adj[b]&=~(1<<a)
        elif i is not None:
            vs=[v for v in range(N) if i>>v&1]
            a,b=random.sample(vs,2)          # add an indep-set edge
            adj[a]|=1<<b; adj[b]|=1<<a
        # occasional random walk to escape
        if random.random()<0.02:
            a=random.randrange(N); b=random.randrange(N)
            if a!=b:
                if adj[a]>>b&1: adj[a]&=~(1<<b); adj[b]&=~(1<<a)
                else: adj[a]|=1<<b; adj[b]|=1<<a
    return None

if __name__=="__main__":
    path=sys.argv[1] if len(sys.argv)>1 else "data/r6/candidates/class0_n31_m104.json"
    start=bm(json.load(open(path))["adj"])
    for seed in range(20):
        adj=[a for a in start]
        res=walk(adj,seed=seed)
        if res is not None:
            e=edges(res)
            print(f"seed {seed}: alpha<=5 AND K_6-free reached, edges={e}. checking cap-16...", flush=True)
            cb=cap_bad(res)
            if cb is None:
                print(f"  cap-16 OK! VALID K_6-free class-0, edges={e}")
                json.dump({"n":N,"edges":e,"note":"K_6-free, from walk on "+path.split('/')[-1],
                           "degrees":sorted(bin(a).count('1') for a in res),
                           "adj":[[res[i]>>j&1 for j in range(N)] for i in range(N)]},
                          open(f"data/r6/candidates/class0_n31_K6free_E{e}.json","w"))
                print(f"  wrote class0_n31_K6free_E{e}.json"); break
            else:
                print(f"  cap-16 fails on {cb}; continuing", flush=True)
        else:
            print(f"seed {seed}: no valid graph (iters exhausted)", flush=True)
