"""Design the [3,3,4^7] local determination. Verify: (A) the two deg-3 vertices are adjacent,
and whether forcing them non-adjacent (+tri-free+alpha<=4) caps e below 17; (B) the rooted
structure at a deg-3 vertex t with N(t)={h,s1,s2}, h the other deg-3 vertex."""
from itertools import combinations
N=9
def base9A2_adj(a,b):
    if a==b: return False
    if a==8: return b in (0,1,4)
    if b==8: return a in (0,1,4)
    return ((a//4)!=(b//4)) and not ((a==4 and b in(0,1)) or (b==4 and a in(0,1)))
M=[[base9A2_adj(a,b) for b in range(N)] for a in range(N)]
deg=[sum(M[v]) for v in range(N)]
print("degrees:",deg)
d3=[v for v in range(N) if deg[v]==3]
print("deg-3 verts:",d3, "adjacent?",M[d3[0]][d3[1]])
for t in d3:
    Nt=[u for u in range(N) if M[t][u]]
    print(f" t={t}: N(t)={Nt}, their degrees={[deg[u] for u in Nt]}")
    # hub = the deg-3 member; spokes = deg-4 members
    hub=[u for u in Nt if deg[u]==3]; spokes=[u for u in Nt if deg[u]==4]
    print(f"   hub(deg3 in N(t))={hub}, spokes(deg4)={spokes}")

# (A) Max edges of a triangle-free alpha<=4 graph on 9 vertices with TWO non-adjacent deg-3 vertices?
# Enumerate via geng-like: reuse brute over triangle-free 9v graphs is heavy; instead search
# all triangle-free alpha<=4 graphs with e in 15..17 having 2 nonadjacent vertices of degree exactly 3.
# Simpler: rely on geng externally. Here, test the specific claim on base9A2 only + reason.

# (B) Verify the rooted determination logic on base9A2 for each deg-3 root t:
print("\n--- rooted determination check ---")
for t in d3:
    Nt=set(u for u in range(N) if M[t][u])
    hub=[u for u in Nt if deg[u]==3][0]
    spokes=[u for u in Nt if deg[u]==4]
    Wp=[u for u in range(N) if u!=t and u not in Nt]  # 5 vertices
    print(f"t={t}: hub h={hub}, spokes={spokes}, W'={Wp}")
    # each w in W' : adjacency to N(t)
    for w in Wp:
        adjNt=[u for u in Nt if M[w][u]]
        print(f"   w={w} (deg{deg[w]}): adj to N(t) at {adjNt}  (adj hub? {M[w][hub]})")
    # claim: N1 = {h} + (W' vertices adjacent to both spokes?), N0 = spokes + (W' adjacent to h)
    # In base9A2: N0={0,1,2,3}(spokes 0,1 + 2,3), N1={4,5,6,7}(hub 4 + 5,6,7)
    # W' vertices: which are on hub's side (N1) vs spoke's side (N0)?
    N1side=[w for w in Wp if M[w][spokes[0]]]  # adjacent to a spoke => opposite side => N1
    N0side=[w for w in Wp if M[w][hub]]        # adjacent to hub => opposite => N0
    print(f"   W' adj to spoke0 (=>N1 side): {N1side}; W' adj to hub (=>N0 side): {N0side}")
