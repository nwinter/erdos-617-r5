"""Is s~t forced? Generate all triangle-free 9v e=17 graphs with degree sequence exactly
[3,3,4^7] and the two degree-3 vertices NON-adjacent; check their independence number.
If all have alpha>=5, s~t is forced by (tri-free + degseq + alpha<=4). Inspect the ind-5-set
to design the Lean contradiction."""
import subprocess
from itertools import combinations
N=9
def parse(line):
    d=[ord(c)-63 for c in line.strip()]; n=d[0]; bits=[]
    for b in d[1:]:
        for k in range(5,-1,-1): bits.append((b>>k)&1)
    adj=[[False]*n for _ in range(n)]; idx=0
    for j in range(1,n):
        for i in range(j):
            if idx<len(bits) and bits[idx]: adj[i][j]=adj[j][i]=True
            idx+=1
    return adj
def alpha_and_witness(a):
    for k in range(N,4,-1):
        for S in combinations(range(N),k):
            if all(not a[x][y] for x,y in combinations(S,2)):
                return k,S
    return 4,None

out=subprocess.run(["/opt/homebrew/bin/geng","-t","9","17:17"],capture_output=True,text=True)
tot=0; ok_degseq=0; nonadj=0; alpha_ge5=0; alpha_le4_cases=[]
witnesses=[]
for l in out.stdout.split():
    a=parse(l); tot+=1
    deg=[sum(a[v]) for v in range(N)]
    if sorted(deg)!=[3,3,4,4,4,4,4,4,4]: continue
    ok_degseq+=1
    d3=[v for v in range(N) if deg[v]==3]
    if a[d3[0]][d3[1]]:  # adjacent - skip, we want nonadjacent
        continue
    nonadj+=1
    al,wit=alpha_and_witness(a)
    if al>=5:
        alpha_ge5+=1
        # describe the witness relative to s,t
        s,t=d3
        wset=set(wit)
        witnesses.append((wit, s in wset, t in wset, len(wset)))
    else:
        alpha_le4_cases.append(l)
print(f"total tri-free 9v-17e: {tot}")
print(f"with degseq [3,3,4^7]: {ok_degseq}")
print(f"...and the two deg-3 vertices NON-adjacent: {nonadj}")
print(f"...of those, alpha>=5 (so excluded by alpha<=4): {alpha_ge5}")
print(f"...alpha<=4 (would be counterexamples to 's~t forced'): {len(alpha_le4_cases)}")
print("sample ind-5-set witnesses (set, contains_s, contains_t, size):")
for w in witnesses[:8]:
    print("  ", w)
