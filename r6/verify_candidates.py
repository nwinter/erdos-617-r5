#!/usr/bin/env python3
"""Load hunt candidates and BRUTE-FORCE verify alpha<=5, omega<=5 (K_6-free), cap-16."""
import json, sys, glob
from itertools import combinations
N=31; FULL=(1<<N)-1
def bm(A): return [sum(int(A[v][u])<<u for u in range(N)) for v in range(N)]
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
def check(path):
    d=json.load(open(path))
    if d.get("n")!=31 or "adj" not in d: return None
    adj=bm(d["adj"]); e=sum(bin(a).count("1") for a in adj)//2
    a6=indep(adj,6); k6=fc(adj,6)
    a_ok = a6 is None; w_ok = k6 is None
    # cap only if alpha/omega ok (else already invalid) -- but check anyway if small
    cap = cap_bad(adj) if (a_ok and w_ok) else "skip"
    return e, a_ok, w_ok, cap, (a6,k6)

targets = ["class0_n31_m104","class0_n31_m118","g31min_s2","g31min_s7",
           "base5k6_s1","base5k6_s3"]
for t in targets:
    p=f"data/r6/candidates/{t}.json"
    try:
        r=check(p)
    except FileNotFoundError:
        print(f"{t}: (missing)"); continue
    if r is None: print(f"{t}: not n=31/adj"); continue
    e,a_ok,w_ok,cap,(a6,k6)=r
    cs = "OK" if cap is None else ("skip" if cap=="skip" else f"FAIL 7set")
    print(f"{t}: edges={e}  alpha<=5:{'OK' if a_ok else 'FAIL'}  "
          f"K6-free:{'OK' if w_ok else 'FAIL'}  cap-16:{cs}  "
          f"=> {'*** VALID+COMPLETABLE-SHAPE ***' if (a_ok and w_ok and cap is None) else 'not usable'}")
    if not w_ok:
        print(f"     K_6 present: {[v for v in range(N) if k6>>v&1]}")
    if not a_ok:
        print(f"     indep-6: {[v for v in range(N) if a6>>v&1]}")
