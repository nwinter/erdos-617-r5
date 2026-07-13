"""D2 descent verification: the cone/bound argument FORCES c=|C|=4 at every level.

At level (r,n): J is K_{r+1}-free, alpha<=4, e = p_r(n) = t_r(n) - floor(n/r) + 1 (the KP max),
non-r-partite. Take a max-degree vertex x; D1 gives the cone C=V\\N(x) independent, D-C complete,
|C|=c in {1,..,4} (since d>=ceil(2e/n) forces c<=4, and x in C forces c>=1), and
  e(J) = e(J[D]) + d*c,   d = n-c,   J[D] on d verts is K_r-free, alpha<=4.
We claim only c=4 is consistent: for c in {1,2,3}, e(J[D]) either exceeds the plain Turan bound
t_{r-1}(d) = ex(d,K_r) (K_r-free) OR exceeds the non-(r-1)-partite KP bound while alpha<=4 forbids
(r-1)-partite (which would force alpha>=ceil(d/(r-1))>=5). And for c=4, e(J[D]) = p_{r-1}(d) exactly
(J[D] is the next extremal graph), continuing the descent.  Verify (5,21)->(4,17)->(3,13)->(2,9)."""
from math import comb, floor, ceil

def turan_parts(n, r):
    q, s = divmod(n, r)
    return [q + 1] * s + [q] * (r - s)

def t(n, r):  # ex(n, K_{r+1}) = e(Turan graph T_r(n))
    if r <= 0:
        return 0
    parts = turan_parts(n, r)
    return comb(n, 2) - sum(comb(p, 2) for p in parts)

def p(n, r):  # KP maximum p_r(n) = t_r(n) - floor(n/r) + 1 (main regime n>=2r+1)
    return t(n, r) - (n // r) + 1

def analyze(r, n, alpha=4):
    e = p(n, r)
    print(f"\n=== level (r={r}, n={n}): extremal e = p_{r}({n}) = {e},  "
          f"t_{r}({n})={t(n,r)}, floor(n/r)={n//r} ===")
    # d = ceil(2e/n) lower bound on max degree; c = n - d
    dmin = ceil(2 * e / n)
    print(f"    max-degree >= ceil(2e/n) = ceil({2*e}/{n}) = {dmin}  =>  c = n-d <= {n - dmin}")
    survivors = []
    for c in range(1, n - dmin + 1):
        d = n - c
        eD = e - d * c  # edges of J[D]
        # J[D] is K_r-free on d vertices with alpha<=4.
        turan_bound = t(d, r - 1)          # ex(d, K_r): plain Turan
        # alpha<=4 forbids (r-1)-partite iff (r-1)*4 < d, i.e. any (r-1)-coloring has a class >4
        forces_nonpartite = (r - 1) * alpha < d
        kp_bound = p(d, r - 1) if d >= 2 * (r - 1) + 1 else turan_bound - 1  # non-(r-1)-partite max
        # the operative upper bound on e(J[D]):
        if forces_nonpartite:
            ub = min(turan_bound, kp_bound)  # must be non-partite AND K_r-free
            why = f"non-partite(KP)={kp_bound}"
        else:
            ub = turan_bound
            why = f"Turan={turan_bound}"
        ok = eD <= ub
        tag = "OK" if ok else "IMPOSSIBLE (eD>ub)"
        extremal = (eD == p(d, r - 1)) if d >= 2*(r-1)+1 else None
        print(f"    c={c}, d={d}: e(J[D])={eD}, K_{r}-free bound: {why}={ub}, alpha forces "
              f"non-partite={forces_nonpartite}  => {tag}"
              + (f"  [eD == p_{r-1}({d})={p(d,r-1)}: {extremal}]" if extremal is not None else ""))
        if ok:
            survivors.append((c, d, eD))
    print(f"    SURVIVORS: {survivors}")
    return survivors

for (r, n) in [(5, 21), (4, 17), (3, 13)]:
    analyze(r, n)

print("\n=== base level (2,9): triangle-free, non-bipartite, alpha<=4, e=17 ===")
print(f"    p_2(9) = {p(9,2)}, t_2(9)={t(9,2)}  (the C5-blowup / KP r=2 construction; handled as base)")
print("\nCONCLUSION: at (5,21),(4,17),(3,13) the ONLY surviving c is 4, and e(J[D]) hits p_{r-1}(d)")
print("exactly -> J[D] is the next extremal graph -> descent 21->17->13->9 forced. QED numerically.")
