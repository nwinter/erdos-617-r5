"""
For every optimal (5,21) sequence and every valid |A|, build G(seq,A); test
K6-free / alpha<=4 / e=173; test AB21 on the complement F (real search for A=K5-e,
B=K4, disjoint, 19 edges); emit canonical graph6 (via nauty labelg) for exact iso count.
"""
import itertools, subprocess, sys
LABELG="/opt/homebrew/bin/labelg"

def build(seq, sizeA):
    n=sum(seq)+1; parts=[]; idx=0
    for sz in seq: parts.append(list(range(idx,idx+sz))); idx+=sz
    x=n-1
    big=[i for i,a in enumerate(seq) if a>1]
    s,t=sorted(big,key=lambda i:seq[i])[:2]
    S=[i for i in range(len(seq)) if i not in (s,t)]
    Ns=parts[s]; y=parts[t][0]; Astar=Ns[:sizeA]
    adj=[[False]*n for _ in range(n)]
    def se(a,b,v): adj[a][b]=v; adj[b][a]=v
    partof={}
    for i,p in enumerate(parts):
        for v in p: partof[v]=i
    for a in range(n-1):
        for b in range(a+1,n-1):
            if partof[a]!=partof[b]: se(a,b,True)
    conn=set(v for i in S for v in parts[i])|{y}|set(Astar)
    for v in conn: se(x,v,True)
    for a in Astar: se(y,a,False)
    return n,adj,seq[s]  # return |Ns| too

def compl(adj,n): return [[(a!=b and not adj[a][b]) for b in range(n)] for a in range(n)]
def ecnt(adj,n): return sum(adj[a][b] for a in range(n) for b in range(a+1,n))
def hasK(adj,n,k):
    return any(all(adj[a][b] for a,b in itertools.combinations(S,2)) for S in itertools.combinations(range(n),k))
def alpha_le(adj,n,m):
    return not any(all(not adj[a][b] for a,b in itertools.combinations(S,2)) for S in itertools.combinations(range(n),m+1))
def g6(adj,n):
    bits=[]
    for j in range(1,n):
        for i in range(j): bits.append(1 if adj[i][j] else 0)
    out=chr(n+63)
    for i in range(0,len(bits),6):
        b=0
        for k in range(6):
            b=(b<<1)|(bits[i+k] if i+k<len(bits) else 0)
        out+=chr(b+63)
    return out
def canon(adj,n):
    s=g6(adj,n)
    r=subprocess.run([LABELG],input=s+"\n",capture_output=True,text=True)
    return r.stdout.strip()

def AB21(F,n):
    # A: 5-set inducing K5 minus exactly one edge; B: 4-set inducing K4; disjoint; e_F(A u B)=19
    K4s=[set(S) for S in itertools.combinations(range(n),4)
         if all(F[a][b] for a,b in itertools.combinations(S,2))]
    K5e=[set(S) for S in itertools.combinations(range(n),5)
         if sum(1 for a,b in itertools.combinations(S,2) if not F[a][b])==1
         and sum(1 for a,b in itertools.combinations(S,2) if F[a][b])==9]
    for A in K5e:
        for B in K4s:
            if A & B: continue
            U=A|B
            e=sum(1 for a,b in itertools.combinations(sorted(U),2) if F[a][b])
            if e==19: return True
    return False

seqs=[(3,3,4,5,5),(3,4,4,4,5),(4,4,4,4,4)]
canons_all=set(); canons_ab21=set()
print(f"{'seq':<14}{'|A|':<5}{'K6free':<8}{'a<=4':<7}{'e':<5}{'AB21':<7}canon")
for seq in seqs:
    for sizeA in range(1, max(a for a in seq)):  # A proper nonempty subset of N_s (size seq[s])
        n,adj,Ns_size=build(seq,sizeA)
        if sizeA>=Ns_size: continue  # A must be proper subset of N_s
        k6=not hasK(adj,n,6); a4=alpha_le(adj,n,4); e=ecnt(adj,n)
        F=compl(adj,n); ab=AB21(F,n)
        cn=canon(adj,n)
        if a4 and k6 and e==173:
            canons_all.add(cn)
            if ab: canons_ab21.add(cn)
        print(f"{str(seq):<14}{sizeA:<5}{str(k6):<8}{str(a4):<7}{e:<5}{str(ab):<7}{cn[:18]}")
print()
print(f"# distinct iso classes among EXTREMAL (K6free,a<=4,e=173) constructions: {len(canons_all)}")
print(f"# of those with AB21: {len(canons_ab21)}")
print(f"ALL extremal constructions have AB21: {canons_all==canons_ab21 and len(canons_all)>0}")
if canons_all-canons_ab21:
    print("!!! EXTREMAL WITHOUT AB21 (would falsify exists_AB21_iso):")
    for c in canons_all-canons_ab21: print("   ",c)
