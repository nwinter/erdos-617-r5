"""Determine the [3,3,4^7] structure GIVEN s~t. Enumerate all triangle-free, alpha<=4 graphs on
Fin 9 with degseq [3,3,4^7], the two deg-3 vertices s,t ADJACENT, and confirm the unique structure:
  N(t) = {s, sp1, sp2},  N(s) = {t, y1, y2},  spokes/ys deg 4,
  zs = rest (3 verts, deg 4),
  N0 = spokes ∪ ys (independent 4-set), N1 = {s} ∪ zs (independent 4-set),
  cross edges: t~s, t~spokes, s~ys, spokes~zs (complete 2x3), ys~zs (complete 2x3);
  NON-edges: t~ys, t~zs, s~spokes, s~zs, spokes~ys, zs~zs.
Also probe which hypotheses force the 4 crux facts (spokes≁ys, zs indep, spokes~zs, ys~zs)."""
from itertools import combinations

N = 9
S, T = 7, 8  # s=7, t=8, ADJACENT

def alpha_le4(adj):
    for St in combinations(range(N), 5):
        if all(not adj[x][y] for x, y in combinations(St, 2)):
            return False
    return True

def trifree(adj):
    for a, b, c in combinations(range(N), 3):
        if adj[a][b] and adj[b][c] and adj[a][c]:
            return False
    return True

# Fix N(s), N(t): s~t. N(s) = {t, y1, y2} with ys among 0..2; N(t) = {s, sp1, sp2} spokes among 3..5.
# Remaining vertex is z-pool {0..6}\(ys∪spokes) plus we let backtracking pick internal edges.
# To be exhaustive up to the s,t-neighbourhood labelling, fix ys={0,1}, spokes={2,3}; zs={4,5,6}.
YS = [0, 1]
SP = [2, 3]
ZS = [4, 5, 6]

def build():
    base = [[False] * N for _ in range(N)]
    def add(u, v):
        base[u][v] = base[v][u] = True
    add(S, T)
    for y in YS: add(S, y)
    for sp in SP: add(T, sp)
    return base

editable = [(i, j) for i in range(7) for j in range(i + 1, 7)]
# remove pairs already forced or forbidden? We'll just skip ones already set and let degree guard handle.

def enumerate_all():
    base = build()
    target = {v: (3 if v in (S, T) else 4) for v in range(N)}
    sols = []
    adj = [row[:] for row in base]
    deg = [sum(row) for row in adj]
    # editable pairs among 0..6 that are NOT already set (S,T edges are to 7,8 so none among 0..6 set)
    edits = [(i, j) for (i, j) in editable if not adj[i][j]]
    def ok_trifree(i, j):
        return not any(adj[i][c] and adj[j][c] for c in range(N) if c != i and c != j)
    def bt(idx):
        if idx == len(edits):
            if all(deg[v] == target[v] for v in range(N)) and alpha_le4(adj):
                sols.append([row[:] for row in adj])
            return
        i, j = edits[idx]
        bt(idx + 1)
        if deg[i] < target[i] and deg[j] < target[j] and ok_trifree(i, j):
            adj[i][j] = adj[j][i] = True; deg[i] += 1; deg[j] += 1
            bt(idx + 1)
            adj[i][j] = adj[j][i] = False; deg[i] -= 1; deg[j] -= 1
    bt(0)
    return sols

sols = enumerate_all()
print(f"# completions (s~t, ys={YS}, spokes={SP}, zs={ZS}, tri-free, degseq, alpha<=4): {len(sols)}")

def classify(adj):
    """Check the target structure holds."""
    def A(u, v): return adj[u][v]
    checks = {
        "N0 indep (spokes,ys mutual non-adj)": all(not A(u, v) for u, v in combinations(SP + YS, 2)),
        "N1 indep ({s}∪zs)": all(not A(u, v) for u, v in combinations([S] + ZS, 2)),
        "spokes~zs complete": all(A(sp, z) for sp in SP for z in ZS),
        "ys~zs complete": all(A(y, z) for y in YS for z in ZS),
        "s~ys": all(A(S, y) for y in YS),
        "s≁spokes": all(not A(S, sp) for sp in SP),
        "s≁zs": all(not A(S, z) for z in ZS),
        "t~spokes": all(A(T, sp) for sp in SP),
        "t≁ys": all(not A(T, y) for y in YS),
        "t≁zs": all(not A(T, z) for z in ZS),
    }
    return checks

allpass = True
for adj in sols:
    ch = classify(adj)
    if not all(ch.values()):
        allpass = False
        print("STRUCTURE MISMATCH:", {k: v for k, v in ch.items() if not v})
print(f"all {len(sols)} completions match target structure: {allpass}")

# Probe: drop alpha, keep tri-free+degseq+s~t. How many completions, and do the crux facts still hold?
def enumerate_no_alpha():
    base = build()
    target = {v: (3 if v in (S, T) else 4) for v in range(N)}
    sols = []
    adj = [row[:] for row in base]
    deg = [sum(row) for row in adj]
    edits = [(i, j) for (i, j) in editable if not adj[i][j]]
    def ok_trifree(i, j):
        return not any(adj[i][c] and adj[j][c] for c in range(N) if c != i and c != j)
    def bt(idx):
        if idx == len(edits):
            if all(deg[v] == target[v] for v in range(N)):
                sols.append([row[:] for row in adj])
            return
        i, j = edits[idx]
        bt(idx + 1)
        if deg[i] < target[i] and deg[j] < target[j] and ok_trifree(i, j):
            adj[i][j] = adj[j][i] = True; deg[i] += 1; deg[j] += 1
            bt(idx + 1)
            adj[i][j] = adj[j][i] = False; deg[i] -= 1; deg[j] -= 1
    bt(0)
    return sols

nо = enumerate_no_alpha()
print(f"\n# completions WITHOUT alpha<=4 (tri-free+degseq+s~t): {len(nо)}")
bad = [adj for adj in nо if not all(classify(adj).values())]
print(f"  of which violate target structure: {len(bad)} (=> alpha IS needed to force structure)")
if bad:
    a = bad[0]
    # show E_sy for a violator
    Esy = sum(1 for sp in SP for y in YS if a[sp][y])
    print(f"  example violator: E_sy (spoke-y edges) = {Esy}; its alpha-5 indep set exists")
