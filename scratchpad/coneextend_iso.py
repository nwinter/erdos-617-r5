"""D3 numeric pre-check (runner 20): explicit iso kpG ≅ coneExtend^3 base9A2 and
kpG1 ≅ coneExtend^3 base9A1.

Lean design: descent peels three independent 4-sets, each joined completely to
everything below (a cone). Canonical `coneExtend G : Fin (m+4)` puts G on the low
positions 0..m-1 and 4 new independent vertices on m..m+3, joined to all of 0..m-1.
Iterating from the 9-vertex base:
  coneExtend^3 base9  : Fin 21,
    0..8   = base9   (N0={0,1,2,3}, N1={4,5,6,7}, apex 8),
    9..12  = cone C3  (joined to 0..8),
    13..16 = cone C2  (joined to 0..12),
    17..20 = cone C1  (joined to 0..16).
The three cone 4-sets are pairwise complete + independent within = K_{4,4,4},
all joined to base9  => coneExtend^3 base9 = K_{4,4,4} * base9  exactly.

Explicit iso sigma : kpG-vertex -> coneExtend-position:
    sigma(v) = v            if v < 8      (base N0,N1)
             = 8            if v == 20    (base apex)
             = v + 1        if 8 <= v <= 19  (the three parts N2,N3,N4 -> cones)
This verifies EXACTLY the Lean native_decide obligation:
    forall a b,  kpG.Adj a b  <->  (coneExtend^3 base9A2).Adj (sigma a) (sigma b).
"""
from itertools import combinations


# ---- base graphs (mirror EqualityProof.lean base9A2Rel / base9A1Rel) ----
def base9A2Rel(a, b):
    if a == b:
        return False
    if a == 8:
        return b in (0, 1, 4)
    if b == 8:
        return a in (0, 1, 4)
    return (a // 4 != b // 4) and not (
        (a == 4 and b in (0, 1)) or (b == 4 and a in (0, 1)))


def base9A1Rel(a, b):
    if a == b:
        return False
    if a == 8:
        return b in (0, 4)
    if b == 8:
        return a in (0, 4)
    return (a // 4 != b // 4) and not ((a == 4 and b == 0) or (b == 4 and a == 0))


# ---- kpG / kpG1 (mirror KPConstruction.lean kpRel / kpRel1) ----
def kpRel(a, b):
    if a == b:
        return False
    if a < 20 and b < 20:
        return (a // 4 != b // 4) and not (
            (a == 4 and b in (0, 1)) or (b == 4 and a in (0, 1)))
    o = b if a == 20 else a
    return o in (0, 1, 4) or (8 <= o < 20)


def kpRel1(a, b):
    if a == b:
        return False
    if a < 20 and b < 20:
        return (a // 4 != b // 4) and not ((a == 4 and b == 0) or (b == 4 and a == 0))
    o = b if a == 20 else a
    return o in (0, 4) or (8 <= o < 20)


# ---- coneExtend: G on Fin m -> Fin (m+4) ----
def cone_extend(adj, m):
    n = m + 4
    def new_adj(u, v):
        if u == v:
            return False
        lu, lv = u < m, v < m
        if lu and lv:
            return adj(u, v)
        # at least one high vertex
        if (not lu) and (not lv):
            return False          # both high: independent
        return True               # one low, one high: joined
    return new_adj, n


def iterate_cone(base_rel, m0, times):
    adj, m = base_rel, m0
    for _ in range(times):
        adj, m = cone_extend(adj, m)
    return adj, m


# sigma : kpG-vertex -> coneExtend^3 position
def sigma(v):
    if v < 8:
        return v
    if v == 20:
        return 8
    return v + 1   # 8..19 -> 9..20


def check(name, kprel, baserel):
    target, n = iterate_cone(baserel, 9, 3)
    assert n == 21
    # sigma is a bijection
    img = sorted(sigma(v) for v in range(21))
    assert img == list(range(21)), f"sigma not a bijection: {img}"
    # adjacency preserved
    bad = []
    for a in range(21):
        for b in range(21):
            if kprel(a, b) != target(sigma(a), sigma(b)):
                bad.append((a, b))
    # edge count of target (sanity: should be 173)
    E = sum(1 for a in range(21) for b in range(a + 1, 21) if target(a, b))
    print(f"{name}: coneExtend^3 base edges = {E} (want 173); "
          f"iso mismatches = {len(bad)} (want 0)")
    if bad:
        print("   first mismatches:", bad[:10])
    return not bad and E == 173


ok2 = check("kpG  ~ coneExtend^3 base9A2", kpRel, base9A2Rel)
ok1 = check("kpG1 ~ coneExtend^3 base9A1", kpRel1, base9A1Rel)

# Also confirm the base slices really are base9A2/base9A1 under the identity+apex map:
#   kpG base = {0..7, 20} with 20->8 identity else; check adjacency vs base9A2.
def base_map(v):   # kpG base vertex -> base9 position
    return 8 if v == 20 else v
def check_base(name, kprel, baserel):
    base_vs = list(range(8)) + [20]
    bad = [(a, b) for a in base_vs for b in base_vs
           if kprel(a, b) != baserel(base_map(a), base_map(b))]
    print(f"{name} base-slice matches: {not bad} (mismatches {len(bad)})")
    return not bad
check_base("kpG", kpRel, base9A2Rel)
check_base("kpG1", kpRel1, base9A1Rel)

print("\nALL D3 numeric checks pass:", ok2 and ok1)
