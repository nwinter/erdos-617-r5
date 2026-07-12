"""
For each MAX-DEGREE singleton/empty config in G_{n,r}, characterise the mechanism:
 - defc(w) for the singleton w, Sum_{v in D} defc(v), and c ; test Sumdefc>=3.
 - find working z (chi(G-z)<=r). Report: does z=w work? does some z in C work?
   For a working z, is C\{z} independent (the EXISTING-code condition)?
   Is there a z with the 'D-colours + one fresh colour, proper off z' colouring
   (equiv: exists z s.t. every edge inside C is incident to z)?
Usage: geng n | python guard_mechanism.py n r
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

def indep(adj,S):
    S=list(S)
    return all(b not in adj[a] for a,b in itertools.combinations(S,2))

def main():
    n=int(sys.argv[1]); r=int(sys.argv[2])
    ksub=list(itertools.combinations(range(n),r+1))
    min_sumdefc=99; min_sumdefc_ex=None
    n_sing=0
    sumdefc_lt3=0
    zw_works=0            # z=w works
    zC_works=0           # some z in C works
    zCstar_works=0       # some z with C\{z} independent AND z makes G-z r-col via D-colouring
    star_condition=0     # exists z in C s.t. every C-edge incident to z (=> existing code works)
    star_fail_but_lem3=0 # existing-code condition fails but chi(G-z)<=r for some z anyway
    examples_starfail=[]
    for line in sys.stdin:
        if not line.strip(): continue
        nn,adj=parse_graph6(line)
        if nn!=n: continue
        if any(all(b in adj[a] for a,b in itertools.combinations(S,2)) for S in ksub): continue
        if chi_le(adj,range(n),r): continue
        deg=[len(adj[v]) for v in range(n)]; Delta=max(deg)
        seen=set()
        for x in range(n):
            if deg[x]!=Delta: continue
            c=n-deg[x]
            if c<2: continue
            D=sorted(adj[x]); Dset=set(D); Cset=set(range(n))-Dset
            for col in all_proper(adj,D,r-1):
                parts=[0]*(r-1); members=[[] for _ in range(r-1)]
                for v in D: parts[col[v]]+=1; members[col[v]].append(v)
                mn=min(parts)
                if mn!=1: continue   # focus on singletons here
                key=(tuple(sorted(parts)),c,x)
                if key in seen: continue
                seen.add(key)
                n_sing+=1
                # the singleton vertex w (a part of size 1)
                i0=parts.index(1); w=members[i0][0]
                defc=lambda v: n - parts[col[v]] - deg[v]
                dw=defc(w); sumdefc=sum(defc(v) for v in D)
                if sumdefc<min_sumdefc: min_sumdefc=sumdefc; min_sumdefc_ex=(line.strip(),c,dw,sumdefc,sorted(parts))
                if sumdefc<3: sumdefc_lt3+=1
                # z = w works?
                if chi_le(adj,[v for v in range(n) if v!=w],r): zw_works+=1
                # some z in C works?
                if any(chi_le(adj,[v for v in range(n) if v!=z],r) for z in Cset): zC_works+=1
                # star condition: exists z in C covering all C-edges
                Cedges=[(a,b) for a,b in itertools.combinations(sorted(Cset),2) if b in adj[a]]
                star_z=[z for z in Cset if all(z in (a,b) for (a,b) in Cedges)]
                if star_z: star_condition+=1
                else:
                    # existing code condition fails; does ANY z give chi(G-z)<=r?
                    if any(chi_le(adj,[v for v in range(n) if v!=z],r) for z in range(n)):
                        star_fail_but_lem3+=1
                        if len(examples_starfail)<6:
                            examples_starfail.append((line.strip(),c,sorted(parts),len(Cedges)))
    print(f"== n={n} r={r}: singleton configs examined={n_sing} ==")
    print(f"  min Sum_defc over singleton configs = {min_sumdefc}  (Sumdefc<3 count={sumdefc_lt3})")
    print(f"     witness (g6,c,defc_w,sumdefc,parts) = {min_sumdefc_ex}")
    print(f"  z=w gives chi(G-w)<=r : {zw_works}/{n_sing}")
    print(f"  some z in C gives chi(G-z)<=r : {zC_works}/{n_sing}")
    print(f"  EXISTING-code condition (exists z in C covering all C-edges): {star_condition}/{n_sing}")
    print(f"  existing-condition FAILS but exists z chi(G-z)<=r : {star_fail_but_lem3}/{n_sing}")
    if examples_starfail:
        print("  star-fail examples (g6,c,parts,#Cedges):")
        for e in examples_starfail: print("    ",e)
main()
