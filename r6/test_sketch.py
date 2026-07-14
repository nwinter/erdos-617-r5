#!/usr/bin/env python3
"""Concretely test the team-lead's 5xK_6 + apex v sketch for class-0."""
from itertools import combinations
N=31; FULL=(1<<N)-1
def find_clique(adj,k,cand=None,chosen=0):
    if cand is None: cand=FULL
    if bin(chosen).count("1")==k: return chosen
    c=cand
    while c:
        v=(c&-c).bit_length()-1; c&=c-1
        if chosen&~adj[v]: continue
        r=find_clique(adj,k,cand&adj[v]&~((1<<(v+1))-1),chosen|(1<<v))
        if r is not None: return r
    return None
def indep(adj,k):
    comp=[(~adj[v])&FULL&~(1<<v) for v in range(N)]; return find_clique(comp,k)
def count_k6(adj):
    # count via all 6-subsets (C(31,6) ~736k) - just report if any and rough count of disjoint
    cnt=0
    for A in combinations(range(N),6):
        if all(adj[a]>>b&1 for a,b in combinations(A,2)): cnt+=1
        if cnt>=6: return ">=6"
    return cnt

# Build 5 K_6 on vertices 0..29, apex v=30
adj=[0]*N
blocks=[list(range(6*i,6*i+6)) for i in range(5)]
for B in blocks:
    for a,b in combinations(B,2): adj[a]|=1<<b; adj[b]|=1<<a
# apex v=30: to try to kill independent 6-sets, connect v to one vertex per block
#  (cap-16 allows deg into each K_6 <=1 anyway)
for i,B in enumerate(blocks): adj[30]|=1<<B[0]; adj[B[0]]|=1<<30
e=sum(bin(a).count("1") for a in adj)//2
print(f"5xK_6 + apex(1 per block): edges={e}")
i6=indep(adj,6)
print(f"  alpha<=5? {'YES' if i6 is None else 'NO, indep-6: '+str([v for v in range(N) if i6>>v&1])}")
c6=find_clique(adj,6)
print(f"  omega<=5 (K_6-free)? {'YES' if c6 is None else 'NO -- contains K_6 (each block is one)'}")
print(f"  => the 5 blocks ARE five disjoint K_6's; omega=6, VIOLATES the forced K_6-free property.")
print(f"  Even before completion, this class-0 is excluded by the section-5 obstruction (margin 36).")
# also: is alpha<=5 even reachable? apex non-adjacent to 5 block-reps {B[1..5]} gives indep 6-set:
print(f"  Also alpha: apex v is non-adjacent to 25 vertices; picking 1 per block avoiding B[0] + ... ")
