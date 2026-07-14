#!/usr/bin/env python3
"""Route B case-explosion + SAT-core sizing, r=5 vs r=6.
(1) Section-7 hand-exclusion burden (rows with maxP > P* that must be excluded like
    the candidate's 7.1-7.3).  (2) Section-6 below-elimination signature counts.
    (3) Section-9/10 per-signature SAT-core sizes and cap-clause estimates.
    (4) defect-lemma orbit-count estimate."""
from math import comb
from routeB_arith import core_numbers, stability, signatures, partitions, L


def sec7_burden(r):
    st = stability(r)
    Pstar = r * r
    rows = st['rows']
    self_excl = [row for row in rows if row['maxP'] <= Pstar]      # give boundary<=P* directly
    hand_excl = [row for row in rows if row['maxP'] > Pstar]       # need 7.x-style exclusion
    levels = sorted(set(row['maxP'] for row in rows))
    return dict(Pstar=Pstar, n_rows=len(rows), n_self=len(self_excl),
                n_hand=len(hand_excl), maxP_levels=levels,
                hand_rows=[(r_['sigma'], r_['c'], r_['maxP']) for r_ in hand_excl],
                sigma_range=(st['sigma_min'], st['sigma_max']))


def below_signatures(r):
    """For each below-P value (excess 1..r-2), count signatures = partitions of the
    excess x ordinary-group multisets (same rule as at P*)."""
    n = r * r + 1
    W = n - r
    out = []
    total = 0
    for excess in range(1, r - 1):                 # P = W+1+... => excess 1..r-2
        P = W + excess
        cnt = 0
        for pat in partitions(excess):
            degs = tuple(sorted((1 + p for p in pat), reverse=True))
            if any(d > r for d in degs):
                continue
            k = len(pat)
            ordinary = W - k
            seen = set()
            for gp in partitions(ordinary, maxpart=r - 1):
                if len(gp) <= r:
                    seen.add(tuple(sorted(gp + (0,) * (r - len(gp)), reverse=True)))
            cnt += len(seen)
        out.append((P, excess, cnt))
        total += cnt
    return out, total


def core_sizes(r):
    """For each P*=r^2 signature, the reduced SAT core = Q + deficient groups + X
    (large groups peeled by completion lemma).  deficient = group size < r-1."""
    sg = signatures(r)
    res = []
    for degs, gsz in sg['signatures']:
        deficient = [s for s in gsz if 0 < s < r - 1]
        X = len(degs)                               # exceptional vertices
        core = r + sum(deficient) + X               # Q(r) + deficient + X
        full = r * r + 1                             # full structure = K_n
        res.append(dict(degs=degs, gsz=gsz, n_def=len(deficient),
                        def_sizes=deficient, X=X, core=core, full=full,
                        cap_core=comb(core, r + 1), cap_full=comb(full, r + 1)))
    return res


def defect_orbits(r):
    """All-degree-2 signatures: exceptions X (all Q-degree 2) with masks = 2-subsets of
    Q(r) excluding the pair of the two large indices... generalise: masks avoid pairs
    lying wholly in the LARGE index set.  Count labelled mask-assignments |masks|^|X|."""
    sg = signatures(r)
    out = []
    for degs, gsz in sg['signatures']:
        if set(degs) != {2}:
            continue
        X = len(degs)
        large_idx = sum(1 for s in gsz if s == r - 1)     # groups at full capacity = "large"
        defic_idx = r - large_idx
        # a degree-2 exception meets a deficient index (large-neighbour lemma); its mask
        # is a 2-subset of Q with at least one deficient index. count such masks:
        masks = comb(r, 2) - comb(large_idx, 2)
        out.append(dict(gsz=gsz, X=X, large=large_idx, defic=defic_idx,
                        masks=masks, labelled=masks ** X))
    return out


def report(r):
    print("=" * 72)
    print(f"  ROUTE B case-explosion, r={r}")
    print("=" * 72)
    b = sec7_burden(r)
    print(f"  Section 7: P*={b['Pstar']}, sigma in {b['sigma_range']}, {b['n_rows']} table rows.")
    print(f"    maxP levels present: {b['maxP_levels']}  (P* +/- ...)")
    print(f"    rows that self-give boundary<=P* (no work): {b['n_self']}")
    print(f"    rows needing 7.x-style hand-exclusion (maxP>P*): {b['n_hand']}")
    print(f"      -> {b['hand_rows']}")
    bs, tot = below_signatures(r)
    print(f"  Section 6 below-elimination (P below P*): {len(bs)} P-values, signatures each:")
    for P, ex, cnt in bs:
        print(f"    P={P} (excess {ex}): {cnt} signatures")
    print(f"    TOTAL below-signatures to hand-eliminate: {tot}")
    print(f"  Section 8 signatures AT P*: {signatures(r)['n_sigs']}")
    cs = core_sizes(r)
    print(f"  Section 9/10 SAT-core sizes per P* signature (reduced core = Q+deficient+X):")
    print(f"    full-structure SAT = {r*r+1} vtcs, cap-clauses ~ C({r*r+1},{r+1}) = {comb(r*r+1,r+1):,}")
    maxcore = max(c['core'] for c in cs)
    print(f"    reduced cores range {min(c['core'] for c in cs)}..{maxcore} vtcs;"
          f" worst cap-clauses ~ C({maxcore},{r+1}) = {comb(maxcore, r+1):,}")
    for c in cs:
        tag = "" if c['n_def'] else "  (no deficient: all-large, core=Q+X trivial)"
        print(f"      {c['degs']}  groups {c['gsz']}  def={c['def_sizes']} X={c['X']}"
              f"  core={c['core']}  capcl~{c['cap_core']:,}{tag}")
    do = defect_orbits(r)
    print(f"  defect-lemma (all-degree-2 signatures) labelled mask-assignments:")
    for d in do:
        print(f"      groups {d['gsz']}: {d['defic']} deficient idx, {d['masks']} masks, "
              f"X={d['X']} -> {d['masks']}^{d['X']} = {d['labelled']:,} labelled (orbits fewer)")


if __name__ == "__main__":
    import sys
    sys.path.insert(0, "r6")
    report(5)
    print()
    report(6)
