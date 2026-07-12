"""
Verify the EXACT doubled-form statements of Lemma A (singleton_arith) and
Lemma B (empty_arith) that the Lean proof will transcribe, and probe the
0-part monotonicity step M0.

Lemma A: blocks has an entry = 1, last entry = c >= 3, sum = n, length = r
         => 2*sig2 + 2*kpSaving n r <= 2*t_r(n) + (c-1)
Lemma B: blocks has an entry = 0, last entry = c >= 3, sum = n, length = r
         => 2*sig2 + 2*kpSaving n r <= 2*t_r(n)

The OTHER (r-2) blocks are ARBITRARY naturals >= 0 (the guard branch only knows
ONE part is <=1). So we must allow arbitrary 0s and 1s among the middle parts.

M0 (the 0-part lift, if needed by the recursion):
    kpSaving n r + t_{r-1}(n) <= kpSaving n (r-1) + t_r(n)
"""
import itertools

def turan(n, r):
    if r <= 0: return 0
    q, s = divmod(n, r)
    sq = s*(q+1)**2 + (r-s)*q**2
    return (n*n - sq)//2

def kpsav(n, r):
    return (n//r - 1) if 2*r+1 <= n else 2

def sig2(blocks):
    s = sum(blocks)
    return (s*s - sum(b*b for b in blocks))//2

def compositions(total, k, lo=0):
    if k == 0:
        if total == 0: yield ()
        return
    if k == 1:
        if total >= lo: yield (total,)
        return
    for first in range(lo, total - lo*(k-1) + 1):
        for rest in compositions(total-first, k-1, lo):
            yield (first,)+rest

# ---- Lemma A (doubled), middle parts ARBITRARY >=0, one of them ==1 ----
# We arrange blocks = (r-1 D-parts) + [c]; require min over D-parts scenario:
# at least one D-part == 1. Middle parts >= 0 arbitrary.
print("="*72)
print("LEMMA A (doubled): 2*sig2 + 2*kpsav <= 2*t_r + (c-1)")
print("  blocks = D-parts(r-1, each>=0, at least one ==1) + [c], c>=3")
print("="*72)
for require_nr3 in (True, False):
    viol=0; total=0; worst=None; wex=None
    for r in range(2, 8):
        for n in range(3, 19):
            if require_nr3 and n < r+3: continue
            if n < r-1: continue
            for c in range(3, n+1):
                dsum = n - c
                if dsum < 0: continue
                # r-1 D-parts summing to dsum, each >=0, at least one ==1
                if r-1 == 0:
                    continue
                for dparts in compositions(dsum, r-1, 0):
                    if 1 not in dparts: continue
                    blocks = list(dparts)+[c]
                    total += 1
                    lhs = 2*sig2(blocks) + 2*kpsav(n,r)
                    rhs = 2*turan(n,r) + (c-1)
                    slack = rhs - lhs
                    if lhs > rhs:
                        viol += 1
                        if viol<=8: print(f"  VIOL r={r} n={n} blocks={blocks}: {lhs} > {rhs}")
                    if worst is None or slack<worst[0]:
                        worst=(slack,r,n,tuple(blocks))
    tag = "n>=r+3" if require_nr3 else "ALL n>=3"
    print(f"  [{tag}] checked {total}, violations {viol}; tightest slack {worst}")

# ---- Lemma B (doubled), middle parts ARBITRARY >=0, one of them ==0 ----
print("="*72)
print("LEMMA B (doubled): 2*sig2 + 2*kpsav <= 2*t_r")
print("  blocks = D-parts(r-1, each>=0, at least one ==0) + [c], c>=3")
print("="*72)
for require_nr3 in (True, False):
    viol=0; total=0; worst=None
    for r in range(2, 8):
        for n in range(3, 19):
            if require_nr3 and n < r+3: continue
            if n < r-1: continue
            for c in range(3, n+1):
                dsum = n - c
                if dsum < 0: continue
                if r-1 == 0: continue
                for dparts in compositions(dsum, r-1, 0):
                    if 0 not in dparts: continue
                    blocks = list(dparts)+[c]
                    total += 1
                    lhs = 2*sig2(blocks) + 2*kpsav(n,r)
                    rhs = 2*turan(n,r)
                    slack = rhs - lhs
                    if lhs > rhs:
                        viol += 1
                        if viol<=8: print(f"  VIOL r={r} n={n} blocks={blocks}: {lhs} > {rhs}")
                    if worst is None or slack<worst[0]:
                        worst=(slack,r,n,tuple(blocks))
    tag = "n>=r+3" if require_nr3 else "ALL n>=3"
    print(f"  [{tag}] checked {total}, violations {viol}; tightest slack {worst}")

# ---- M0: the 0-part lift ----
print("="*72)
print("M0 (0-part lift): kpsav n r + t_{r-1}(n) <= kpsav n (r-1) + t_r(n)")
print("  needed to remove a 0 block (length r -> r-1). Test for r>=3.")
print("="*72)
for require_nr3 in (True, False):
    viol=0; total=0; worst=None
    for r in range(3, 12):
        for n in range(3, 40):
            if require_nr3 and n < r+3: continue
            total += 1
            lhs = kpsav(n,r) + turan(n,r-1)
            rhs = kpsav(n,r-1) + turan(n,r)
            slack = rhs-lhs
            if lhs>rhs:
                viol+=1
                if viol<=8: print(f"  VIOL r={r} n={n}: {lhs} > {rhs} (ksav_r={kpsav(n,r)} t_{r-1}={turan(n,r-1)} ksav_{r-1}={kpsav(n,r-1)} t_r={turan(n,r)})")
            if worst is None or slack<worst[0]:
                worst=(slack,r,n)
    tag = "n>=r+3" if require_nr3 else "ALL n>=3"
    print(f"  [{tag}] checked {total}, violations {viol}; tightest slack {worst}")

# ---- Base cases ----
print("="*72)
print("BASE-A: [1,c], r=2, n=1+c:  2*c + 2*kpsav(1+c,2) <= 2*t_2(1+c) + (c-1)")
print("BASE-B: [0,c], r=2, n=c:    2*0 + 2*kpsav(c,2)   <= 2*t_2(c)")
print("="*72)
va=0; vb=0
for c in range(3, 60):
    # A
    n=1+c
    if 2*c + 2*kpsav(n,2) > 2*turan(n,2)+(c-1):
        va+=1; print(f"  BASE-A VIOL c={c}")
    # B
    n=c
    if 2*0 + 2*kpsav(n,2) > 2*turan(n,2):
        vb+=1; print(f"  BASE-B VIOL c={c}")
print(f"  BASE-A violations {va}, BASE-B violations {vb} (c in [3,60))")
