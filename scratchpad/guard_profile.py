"""
Deeper profile of MAX-DEGREE singleton configs, keyed by c.
 - per c: count, min Sum_defc, min defc(w)
 - is the singleton EVER the unique bad part? (bad = every part-vertex has defc>=1)
 - among unique-bad singletons: how many C-misses does w have (|misses(w) cap C|)?
 - the working z in C: is it always a C-nonneighbour of w? report the min |{z in C: chi(G-z)<=r}|.
Also: DROP the max-degree requirement to a WEAKER 'x has max degree among ... ' ? no; keep max.
Usage: geng n | python guard_profile.py n r
"""
import sys, itertools
from collections import defaultdict
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

def main():
    n=int(sys.argv[1]); r=int(sys.argv[2])
    ksub=list(itertools.combinations(range(n),r+1))
    per_c=defaultdict(lambda:{'cnt':0,'minsum':99,'mindw':99,'uniquebad':0,
                              'ub_Cmiss_ge2':0,'minCz':99})
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
                if min(parts)!=1: continue
                key=(x,tuple(col[v] for v in D))
                if key in seen: continue
                seen.add(key)
                defc={v:(n-parts[col[v]]-deg[v]) for v in D}
                # choose the singleton part i0 (a part of size 1)
                i0=parts.index(1); w=members[i0][0]
                dw=defc[w]; sm=sum(defc.values())
                rec=per_c[c]; rec['cnt']+=1
                rec['minsum']=min(rec['minsum'],sm); rec['mindw']=min(rec['mindw'],dw)
                # bad parts
                badparts=[i for i in range(r-1) if all(defc[v]>=1 for v in members[i])]
                if badparts==[i0]:  # singleton unique bad
                    rec['uniquebad']+=1
                    Cmiss=len([u for u in Cset if u not in adj[w]])
                    if Cmiss>=2: rec['ub_Cmiss_ge2']+=1
                # number of deletable z in C
                nz=sum(1 for z in Cset if chi_le(adj,[v for v in range(n) if v!=z],r))
                rec['minCz']=min(rec['minCz'],nz)
    print(f"== n={n} r={r} singleton-config profile by c ==")
    for c in sorted(per_c):
        r_=per_c[c]
        print(f"  c={c}: cnt={r_['cnt']} minSumDefc={r_['minsum']} min_defc(w)={r_['mindw']} "
              f"uniqueBadSingleton={r_['uniquebad']} (of those |Cmiss(w)|>=2: {r_['ub_Cmiss_ge2']}) "
              f"min#deletable-z-in-C={r_['minCz']}")
main()
