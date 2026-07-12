"""
Read graph6 graphs from stdin (piped from nauty `geng n`), one iso-rep each, and
test the guard config with x = MAX-DEGREE vertex.  Reports whether ANY graph in
G_{n,r} admits (x max-degree, D=N(x) (r-1)-partite, c>=2, some part <=1).
Usage:  geng n | python guard_geng.py n r
"""
import sys, itertools

def parse_graph6(line):
    line = line.rstrip()
    data = [ord(ch)-63 for ch in line]
    n = data[0]
    bits = []
    for b in data[1:]:
        for k in range(5,-1,-1):
            bits.append((b>>k)&1)
    adj=[set() for _ in range(n)]
    idx=0
    for j in range(1,n):
        for i in range(j):
            if idx < len(bits) and bits[idx]: adj[i].add(j); adj[j].add(i)
            idx+=1
    return n, adj

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
    nGnr=0; max_sing=0; max_empty=0; sanity_bad=0
    sing_ex=[]; empty_ex=[]
    lemma3_fail_amongGnr=0
    for line in sys.stdin:
        if not line.strip(): continue
        nn,adj=parse_graph6(line)
        if nn!=n: continue
        if any(all(b in adj[a] for a,b in itertools.combinations(S,2)) for S in ksub): continue
        if chi_le(adj,range(n),r): continue
        nGnr+=1
        deg=[len(adj[v]) for v in range(n)]; Delta=max(deg)
        ne=sum(deg)//2
        if ne+kpsav(n,r)>turan(n,r): sanity_bad+=1
        # exists z chi(G-z)<=r ?
        lem3=any(chi_le(adj,[v for v in range(n) if v!=z],r) for z in range(n))
        if not lem3: lemma3_fail_amongGnr+=1
        for x in range(n):
            if deg[x]!=Delta: continue
            c=n-deg[x]
            if c<2: continue
            D=sorted(adj[x])
            for col in all_proper(adj,D,r-1):
                parts=[0]*(r-1)
                for v in D: parts[col[v]]+=1
                mn=min(parts)
                if mn>1: continue
                blocks=parts+[c]
                if mn==0:
                    max_empty+=1
                    if len(empty_ex)<6: empty_ex.append((line.strip(),ne,sorted(parts),c,lem3))
                else:
                    max_sing+=1
                    if len(sing_ex)<6: sing_ex.append((line.strip(),ne,sorted(parts),c,lem3,sig2(blocks)))
    print(f"n={n} r={r}: |G_(n,r)|(iso)={nGnr}  t_r={turan(n,r)} kpSav={kpsav(n,r)} p_r={turan(n,r)-kpsav(n,r)}")
    print(f"   sanity(e+sav>t_r) violations: {sanity_bad}")
    print(f"   MAX-deg singleton configs: {max_sing}   MAX-deg empty configs: {max_empty}")
    print(f"   #G in G_(n,r) with NO z s.t. chi(G-z)<=r : {lemma3_fail_amongGnr}")
    if sing_ex:
        print("   MAX-deg singleton examples (g6,e,parts,c,exists_z,sig2):")
        for e in sing_ex: print("      ",e)
    if empty_ex:
        print("   MAX-deg empty examples (g6,e,parts,c,exists_z):")
        for e in empty_ex: print("      ",e)

main()
