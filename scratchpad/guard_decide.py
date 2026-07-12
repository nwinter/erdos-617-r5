"""
Decisive aggregation over G_{n,r} (iso-reps from geng), for MAX-DEGREE x guard configs.
For every (graph, x max-deg, proper (r-1)-colouring of N(x) with a part <=1, c>=2):
  - Lemma-3 route works?    exists z with chi(G-z)<=r        (max-DEGREE only)
  - main_ineq route works?  e(G) <= sig2(blocks) - 2
Separately split singleton (min part=1) vs empty (min part=0).
Report, over ALL such configs, how many FAIL each route, with worst examples.
Usage: geng n | python guard_decide.py n r
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
    C={'sing_cfg':0,'sing_lem3_fail':0,'sing_mi_fail':0,
       'empty_cfg':0,'empty_lem3_fail':0,'empty_mi_fail':0,
       'sing_graphs':0,'sing_graphs_lem3_fail':0}
    sing_lem3_fail_ex=[]; sing_mi_fail_ex=[]; empty_mi_fail_ex=[]
    for line in sys.stdin:
        if not line.strip(): continue
        nn,adj=parse_graph6(line)
        if nn!=n: continue
        if any(all(b in adj[a] for a,b in itertools.combinations(S,2)) for S in ksub): continue
        if chi_le(adj,range(n),r): continue
        deg=[len(adj[v]) for v in range(n)]; Delta=max(deg); ne=sum(deg)//2
        lem3=any(chi_le(adj,[v for v in range(n) if v!=z],r) for z in range(n))
        graph_has_sing=False; graph_sing_lem3fail=False
        seen=set()
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
                key=(tuple(sorted(parts)),c)
                if key in seen: continue
                seen.add(key)
                blocks=parts+[c]; s2=sig2(blocks)
                mi_ok=(ne<=s2-2)
                if mn==1:
                    C['sing_cfg']+=1; graph_has_sing=True
                    if not lem3:
                        C['sing_lem3_fail']+=1; graph_sing_lem3fail=True
                        if len(sing_lem3_fail_ex)<8: sing_lem3_fail_ex.append((line.strip(),ne,sorted(parts),c,s2))
                    if not mi_ok:
                        C['sing_mi_fail']+=1
                        if len(sing_mi_fail_ex)<8: sing_mi_fail_ex.append((line.strip(),ne,sorted(parts),c,s2,lem3))
                else:
                    C['empty_cfg']+=1
                    if not lem3: C['empty_lem3_fail']+=1
                    if not mi_ok:
                        C['empty_mi_fail']+=1
                        if len(empty_mi_fail_ex)<8: empty_mi_fail_ex.append((line.strip(),ne,sorted(parts),c,s2,lem3))
        if graph_has_sing:
            C['sing_graphs']+=1
            if graph_sing_lem3fail: C['sing_graphs_lem3_fail']+=1
    print(f"== n={n} r={r}  t_r={turan(n,r)} kpSav={kpsav(n,r)} p_r={turan(n,r)-kpsav(n,r)} ==")
    print(f"  SINGLETON configs={C['sing_cfg']}  Lemma3-route FAIL={C['sing_lem3_fail']}  mainineq(e<=sig2-2) FAIL={C['sing_mi_fail']}")
    print(f"  singleton-config GRAPHS={C['sing_graphs']}  of which NO valid z (Lemma3 fails)={C['sing_graphs_lem3_fail']}")
    print(f"  EMPTY configs={C['empty_cfg']}  Lemma3-route FAIL={C['empty_lem3_fail']}  mainineq FAIL={C['empty_mi_fail']}")
    if sing_lem3_fail_ex:
        print("  *** SINGLETON configs where Lemma3 route FAILS (g6,e,parts,c,sig2):")
        for e in sing_lem3_fail_ex: print("     ",e)
    if sing_mi_fail_ex:
        print("  SINGLETON configs where e>sig2-2 (g6,e,parts,c,sig2,lem3):")
        for e in sing_mi_fail_ex: print("     ",e)
    if empty_mi_fail_ex:
        print("  EMPTY configs where e>sig2 (should study) (g6,e,parts,c,sig2,lem3):")
        for e in empty_mi_fail_ex: print("     ",e)
main()
