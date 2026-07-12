"""
FAST robustness check at larger n (no chi(G-z)).  For every G in G_{n,r} and every
MAX-DEGREE x with a proper (r-1)-colouring of N(x) having a part <=1 and c>=2, verify:
  (1) c >= 3                                    [the provable structural fact]
  (2) if singleton (min part==1):  e <= sig2(blocks) - ceil((c-1)/2)   [main_ineq consequence]
      if only empty (min part==0): e <= sig2(blocks)                    [main_ineq]
  (3) resulting bound closes:  (that bound) + kpSaving(n,r) <= t_r(n)   [arith S/E]
Also verify main_ineq itself: 2e + Sum_{v in D} defc(v) <= 2 sig2(blocks).
Usage: geng n | python guard_verify10.py n r
"""
import sys, itertools
def parse_graph6(line):
    data=[ord(ch)-63 for ch in line.rstrip()]; n=data[0]; bits=[]
    for b in data[1:]:
        for k in range(5,-1,-1): bits.append((b>>k)&1)
    adj=[set() for _ in range(n)]; idx=0
    for j in range(1,n):
        for i in range(j):
            if idx<len(bits) and bits[idx]: adj[i].add(j); adj[j].add(i)
            idx+=1
    return n,adj
def chi_le(adj,verts,k):
    verts=list(verts); m=len(verts); color={}
    def bt(i):
        if i==m: return True
        v=verts[i]; used={color[u] for u in verts[:i] if u in adj[v]}
        for c in range(k):
            if c not in used:
                color[v]=c
                if bt(i+1): return True
                del color[v]
        return False
    return bt(0)
def all_proper(adj,verts,k):
    verts=list(verts); m=len(verts); color={}
    def bt(i):
        if i==m: yield dict(color); return
        v=verts[i]; used={color[u] for u in verts[:i] if u in adj[v]}
        for c in range(k):
            if c not in used:
                color[v]=c; yield from bt(i+1); del color[v]
    yield from bt(0)
def turan(n,r):
    if r<=0: return 0
    q,s=divmod(n,r); return (n*n-(s*(q+1)**2+(r-s)*q**2))//2
def kpsav(n,r): return (n//r-1) if 2*r+1<=n else 2
def sig2(bl):
    s=sum(bl); return (s*s-sum(b*b for b in bl))//2

def main():
    n=int(sys.argv[1]); r=int(sys.argv[2])
    ksub=list(itertools.combinations(range(n),r+1))
    cfgs=0; c2=0; mainineq_bad=0; bound_bad=0; close_bad=0
    minc=99
    for line in sys.stdin:
        if not line.strip(): continue
        nn,adj=parse_graph6(line)
        if nn!=n: continue
        if any(all(b in adj[a] for a,b in itertools.combinations(S,2)) for S in ksub): continue
        if chi_le(adj,range(n),r): continue
        deg=[len(adj[v]) for v in range(n)]; Delta=max(deg); ne=sum(deg)//2
        seen=set()
        for x in range(n):
            if deg[x]!=Delta: continue
            c=n-deg[x]
            if c<2: continue
            D=sorted(adj[x])
            for col in all_proper(adj,D,r-1):
                parts=[0]*(r-1)
                for v in D: parts[col[v]]+=1
                if min(parts)>1: continue
                key=(x,tuple(col[v] for v in D))
                if key in seen: continue
                seen.add(key)
                cfgs+=1; minc=min(minc,c)
                if c<3: c2+=1
                blocks=parts+[c]; s2=sig2(blocks)
                sumdefc=sum(n-parts[col[v]]-deg[v] for v in D)
                if 2*ne+sumdefc>2*s2: mainineq_bad+=1
                if 1 in parts:
                    ded=(c-1+1)//2
                    if ne>s2-ded: bound_bad+=1
                    if (s2-ded)+kpsav(n,r)>turan(n,r): close_bad+=1
                else:
                    if ne>s2: bound_bad+=1
                    if s2+kpsav(n,r)>turan(n,r): close_bad+=1
    print(f"== n={n} r={r}: max-deg guard configs={cfgs}, min c={minc} ==")
    print(f"   c<3 (should be 0): {c2}")
    print(f"   main_ineq (2e+Sumdefc<=2 sig2) violations: {mainineq_bad}")
    print(f"   route-bound (e<= sig2-ded) violations: {bound_bad}")
    print(f"   closing (bound+kpSaving<=t_r) violations: {close_bad}")
main()
