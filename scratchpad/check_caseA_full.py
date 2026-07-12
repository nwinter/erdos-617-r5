from math import comb
def t(n,r):
    if r==0: return comb(n,2)
    q,rem = divmod(n,r)
    within = rem*comb(q+1,2) + (r-rem)*comb(q,2)
    return comb(n,2) - within
def sav(n,r):
    return (n//r - 1) if n >= 2*r+1 else 2
# FULL range of the Lean statement: 2<=r, 0<d<n. No n>=r+3, no d>=r+1.
bad=[]; tight=[]
for r in range(2,9):
    for n in range(1, 60):
        for d in range(1, n):  # 0<d<n
            lhs = t(d,r-1) + d*(n-d) + sav(n,r)
            rhs = t(n,r) + sav(d,r-1)
            if lhs > rhs:
                bad.append((r,n,d,lhs,rhs, lhs-rhs))
            if lhs == rhs:
                tight.append((r,n,d))
print("checked r=2..8, n up to 59, d in [1,n-1] (FULL Lean hypothesis range)")
print("violations:", len(bad))
for b in bad[:40]: print("  FAIL", b)
print("tight (equality) count:", len(tight))
# show some tight cases across r
from collections import defaultdict
byr=defaultdict(list)
for (r,n,d) in tight: byr[r].append((n,d))
for r in sorted(byr): print(f"  r={r}: {len(byr[r])} tight, e.g. {byr[r][:6]}")
