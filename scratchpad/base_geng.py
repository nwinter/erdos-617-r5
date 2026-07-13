"""Use nauty geng to enumerate triangle-free 9-vertex 17-edge graphs, filter alpha<=4,
confirm exactly 2 iso classes and that they equal base9A2/base9A1."""
import subprocess, sys
from itertools import combinations, permutations

N = 9

def parse_graph6(line):
    line = line.strip()
    data = [ord(c)-63 for c in line]
    n = data[0]
    bits = []
    for byte in data[1:]:
        for k in range(5,-1,-1):
            bits.append((byte>>k)&1)
    adj = [[False]*n for _ in range(n)]
    idx = 0
    for j in range(1,n):
        for i in range(j):
            if idx < len(bits) and bits[idx]:
                adj[i][j]=adj[j][i]=True
            idx += 1
    return adj

def alpha_le4(adj):
    for S in combinations(range(N),5):
        if all(not adj[a][b] for a,b in combinations(S,2)):
            return False
    return True

def canon(adj):
    best=None
    for perm in permutations(range(N)):
        bits=0; idx=0
        for a in range(N):
            for b in range(a+1,N):
                if adj[perm[a]][perm[b]]: bits|=(1<<idx)
                idx+=1
        if best is None or bits<best: best=bits
    return best

# geng -t: triangle-free; 9 vertices; 17:17 edges
out = subprocess.run(["/opt/homebrew/bin/geng","-t","9","17:17"],
                     capture_output=True, text=True)
lines = [l for l in out.stdout.splitlines() if l.strip()]
print(f"geng produced {len(lines)} triangle-free 9v-17e graphs (up to iso)")

good = []
for l in lines:
    adj = parse_graph6(l)
    if alpha_le4(adj):
        good.append(adj)
print(f"of which alpha<=4: {len(good)}")

# witnesses
def base9A2_adj(a,b):
    if a==b: return False
    if a==8: return b in (0,1,4)
    if b==8: return a in (0,1,4)
    return ((a//4)!=(b//4)) and not ((a==4 and b in(0,1)) or (b==4 and a in(0,1)))
def base9A1_adj(a,b):
    if a==b: return False
    if a==8: return b in (0,4)
    if b==8: return a in (0,4)
    return ((a//4)!=(b//4)) and not ((a==4 and b==0) or (b==4 and a==0))
w2=[[base9A2_adj(a,b) for b in range(N)] for a in range(N)]
w1=[[base9A1_adj(a,b) for b in range(N)] for a in range(N)]
c2,c1=canon(w2),canon(w1)
classes = set(canon(a) for a in good)
print(f"distinct iso classes among good graphs: {len(classes)}")
print(f"canon(base9A2)={c2}, canon(base9A1)={c1}")
print(f"classes == {{base9A2, base9A1}} : {classes == {c1,c2}}")
# degree sequences
for a in good:
    ds = sorted(sum(row) for row in a)
    print("  degseq:", ds)
