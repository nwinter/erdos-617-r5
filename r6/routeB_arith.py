#!/usr/bin/env python3
"""Route B (external candidate's gap-graph pincer) arithmetic, parameterised by r.
Calibrates on r=5 (K_26) reproducing candidate-proof.md exactly, then transposes to
r=6 (K_37).  Attribution: structure follows review_queue/external-candidate-B/
candidate-proof.md (SURVIVES-reviewed).  Every number here is computed, not asserted.
"""
from math import comb, floor
from itertools import combinations


def turan(n, parts):
    """t_parts(n): edges of the balanced complete multipartite (Turan) graph."""
    if parts <= 0:
        return 0
    q, s = divmod(n, parts)
    return comb(n, 2) - (s * comb(q + 1, 2) + (parts - s) * comb(q, 2))


def L(m, t):
    """L_t(m) = min edges of an m-vertex graph with alpha<=t = C(m,2)-t_t(m)
    = sum of C(size_i,2) over t as-equal-as-possible cliques (complementary Turan)."""
    return comb(m, 2) - turan(m, t)


def core_numbers(r):
    n = r * r + 1
    E = comb(n, 2)
    emax = E // r                                    # minority colour edge bound
    alpha_force = E - turan(n, r - 1)                # e(G) if alpha<=r-1 (complement K_r-free)
    cap = comb(r + 1, 2) - (r - 1)                   # (r+1)-set max own-colour edges
    Ri_max = r - 1                                   # |R_i|<=r-1 (R_i u {q_i} = K_{r+1} forbidden)
    W = n - r                                        # |W| after removing an independent r-set Q
    # baseline P: r groups of <=(r-1) cover <= r(r-1) < W  => P >= W+1
    cover = r * (r - 1)
    P_base = W + 1 if cover < W else None
    P_upper = emax - L(W, r)                         # e(W) >= L_r(W)
    return dict(n=n, E=E, emax=emax, alpha_force=alpha_force, cap=cap,
                Ri_max=Ri_max, W=W, cover=cover, P_base=P_base, P_upper=P_upper)


def stability(r, forbid_boundary=None):
    """Section-7 analogue.  Returns the (sigma,c) table with max P(A+x), and the
    regular-case boundary.  BN finds an (r-1)-clique A (H-clique) once e(H)>t_{r-1}(n)."""
    n = r * r + 1
    E = comb(n, 2)
    emax = E // r
    eH = E - emax                                    # e(H) >= this (H = complement, K_{r+1}-free)
    tH_max = turan(n, r)                             # H is K_{r+1}-free => e(H) <= t_r(n)
    bn_threshold = turan(n, r - 1)                   # BN needs e(H) > t_{r-1}(n)
    # regular case: H k-regular, e(H)=n*k/2 in [eH, tH_max], k even (n odd)
    reg_k = [k for k in range(0, n) if (n * k) % 2 == 0 and eH <= n * k // 2 <= tH_max]
    reg_eH = [n * k // 2 for k in reg_k]
    # G regular degree = n-1-k
    reg_G = [(n - 1 - k, r * (n - 1 - k)) for k in reg_k]  # (deg, boundary=r*deg)
    # BN degree-sum bound (in H): > 2*(r-1)*eH/n  -- check if it lands exactly on integer
    bn_ds = 2 * (r - 1) * eH / n
    bn_ds_strict = floor(bn_ds) + 1 if bn_ds == int(bn_ds) else floor(bn_ds) + 1
    # sigma = (r-1)(n-1) - sum_H d(a) ; sum_H d(a) >= bn_ds_strict
    sigma_max = (r - 1) * (n - 1) - bn_ds_strict
    # c >= (sum_H d) - (r-2)*n = ((r-1)(n-1)-sigma) - (r-2)n = 32-sigma style
    def c_lb(sigma):
        return (r - 1) * (n - 1) - sigma - (r - 2) * n
    c_max = r                                         # C is a G-clique; omega(G)<=r (K_{r+1} capped)
    # sigma range: c_lb(sigma) <= c_max => sigma >= (r-1)(n-1)-(r-2)n - c_max
    sigma_min = (r - 1) * (n - 1) - (r - 2) * n - c_max
    rows = []
    for sigma in range(sigma_min, sigma_max + 1):
        clo = max(1, c_lb(sigma))
        for c in range(clo, c_max + 1):
            D = n - (r - 1) - c
            LD = L(D, r)
            budget = emax - sigma - comb(c, 2) - LD   # max e(C,D)
            if budget < 0:
                continue
            maxP = sigma + c - 1 + (budget // c)
            rows.append(dict(sigma=sigma, c=c, D=D, LD=LD, maxeCD=budget, maxP=maxP))
    return dict(eH=eH, tH_max=tH_max, bn_threshold=bn_threshold, bn_ds=bn_ds,
                bn_ds_strict=bn_ds_strict, sigma_min=sigma_min, sigma_max=sigma_max,
                c_max=c_max, reg_k=reg_k, reg_eH=reg_eH, reg_G=reg_G, rows=rows)


def partitions(m, maxpart=None):
    """all partitions of m into positive parts (each <= maxpart if given)."""
    if maxpart is None:
        maxpart = m
    res = []
    def rec(rem, mx, cur):
        if rem == 0:
            res.append(tuple(cur)); return
        for p in range(min(rem, mx), 0, -1):
            cur.append(p); rec(rem - p, p, cur); cur.pop()
    rec(m, maxpart, [])
    return res


def signatures(r):
    """Count exact-P* signatures: excess=r-1 exceptional patterns x ordinary group
    size multisets (r groups, each in [0,r-1], summing to W-k)."""
    n = r * r + 1
    W = n - r
    Pstar = r * r
    excess = Pstar - W                                # = r-1
    exc_patterns = partitions(excess)                 # exceptional excess -> degree = 1+part, <= r
    sigs = []
    for pat in exc_patterns:
        degs = tuple(sorted((1 + p for p in pat), reverse=True))
        if any(d > r for d in degs):                  # exceptional Q-degree <= r
            continue
        k = len(pat)                                   # number of exceptionals
        ordinary = W - k
        # ordinary group sizes: r groups, each in [0, r-1], summing to `ordinary`
        # enumerate as sorted multisets (partitions of `ordinary` into <=r parts each <=r-1,
        # padded with zeros to length r)
        seen = set()
        for gp in partitions(ordinary, maxpart=r - 1):
            if len(gp) <= r:
                seen.add(tuple(sorted(gp + (0,) * (r - len(gp)), reverse=True)))
        for gsz in seen:
            sigs.append((degs, gsz))
    return dict(Pstar=Pstar, excess=excess, exc_patterns=exc_patterns,
                n_exc_patterns=len(exc_patterns), signatures=sigs, n_sigs=len(sigs))


def report(r, verbose=True):
    print("=" * 72)
    print(f"  ROUTE B at r={r}   (K_{r*r+1}, minority-colour gap graph)")
    print("=" * 72)
    cn = core_numbers(r)
    print(f"  n={cn['n']}  C(n,2)={cn['E']}  e(G)<=emax=floor(E/r)={cn['emax']}")
    print(f"  alpha=r={r} FORCED: alpha<=r-1 needs e>=E-t_{r-1}(n)={cn['alpha_force']} > emax={cn['emax']}"
          f"  ({'OK' if cn['alpha_force'] > cn['emax'] else '*** FAILS ***'})")
    print(f"  cap (max own-colour in (r+1)-set) = {cn['cap']};  |R_i| <= {cn['Ri_max']}")
    print(f"  |W|=n-r={cn['W']};  r groups of <=({r-1}) cover <= {cn['cover']} < |W| => P_baseline={cn['P_base']}")
    print(f"  e(W) >= L_{r}({cn['W']})={L(cn['W'],r)} => P_upper <= emax - that = {cn['P_upper']}")
    st = stability(r)
    print(f"\n  --- Section 7 stability ---")
    print(f"  e(H) >= E-emax = {st['eH']};  H K_{r+1}-free so e(H) <= t_{r}(n)={st['tH_max']}")
    print(f"  BN threshold t_{r-1}(n) = {st['bn_threshold']}; e(H) > it? {st['eH'] > st['bn_threshold']}")
    print(f"  BN degree-sum bound 2(r-1)e(H)/n = {st['bn_ds']}  "
          f"(integer? {st['bn_ds']==int(st['bn_ds'])} -> STRICT gives >= {st['bn_ds_strict']})")
    print(f"  => sigma <= (r-1)(n-1) - {st['bn_ds_strict']} = {st['sigma_max']};  sigma >= {st['sigma_min']}")
    print(f"  regular case: G-degree,boundary options = {st['reg_G']}  (e(H)={st['reg_eH']})")
    print(f"  {'sigma':>5} {'c':>3} {'|D|':>4} {'L_r(|D|)':>8} {'max e(C,D)':>10} {'max P(A+x)':>10}")
    for row in st['rows']:
        print(f"  {row['sigma']:>5} {row['c']:>3} {row['D']:>4} {row['LD']:>8} {row['maxeCD']:>10} {row['maxP']:>10}")
    sg = signatures(r)
    print(f"\n  --- Section 8 signatures at P*=r^2={sg['Pstar']} ---")
    print(f"  excess = P* - |W| = {sg['excess']} (= r-1);  below-cases to eliminate: "
          f"P={cn['P_base']}..{sg['Pstar']-1}  = {sg['Pstar']-cn['P_base']} cases (= r-2)")
    print(f"  exceptional patterns (partitions of {sg['excess']}): {sg['n_exc_patterns']} = p(r-1)")
    print(f"  TOTAL signatures (exc pattern x ordinary group multiset): {sg['n_sigs']}")
    if verbose:
        for degs, gsz in sg['signatures']:
            print(f"      exc-degs {degs}  ordinary-groups {gsz}")


if __name__ == "__main__":
    report(5)
    print()
    report(6)
