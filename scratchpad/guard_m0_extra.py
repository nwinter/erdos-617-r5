def turan(n, r):
    if r <= 0: return 0
    q, s = divmod(n, r)
    sq = s*(q+1)**2 + (r-s)*q**2
    return (n*n - sq)//2
def kpsav(n, r):
    return (n//r - 1) if 2*r+1 <= n else 2

# M0 extended: kpsav n (r+1) + t_r(n) <= kpsav n r + t_{r+1}(n), r>=2, n>=3
v=0; worst=None
for r in range(2, 40):
    for n in range(3, 400):
        lhs = kpsav(n,r+1) + turan(n,r)
        rhs = kpsav(n,r) + turan(n,r+1)
        if lhs>rhs:
            v+=1
            if v<=10: print(f"M0 VIOL r={r} n={n}: {lhs}>{rhs}")
        s=rhs-lhs
        if worst is None or s<worst[0]: worst=(s,r,n)
print(f"M0 extended: violations {v}; tightest {worst}")

# Strict-Turan helper: t_r(n) <= t_r(n-1) + (n-2), for n >= 2r+1 (parts>=2)
v=0; worst=None
for r in range(2, 40):
    for n in range(2*r+1, 400):
        lhs = turan(n,r)
        rhs = turan(n-1,r) + (n-2)
        if lhs>rhs:
            v+=1
            if v<=10: print(f"ADDV VIOL r={r} n={n}: {lhs}>{rhs} (t_r(n)={turan(n,r)} t_r(n-1)={turan(n-1,r)})")
        s=rhs-lhs
        if worst is None or s<worst[0]: worst=(s,r,n)
print(f"add-vertex t_r(n)<=t_r(n-1)+(n-2) for n>=2r+1: violations {v}; tightest {worst}")

# Also: the exact hard-case sufficient bound used: t_{r+1}(n) >= t_r(n)+1 for n>=2r+1
v=0
for r in range(2,40):
    for n in range(2*r+1, 400):
        if turan(n,r+1) < turan(n,r)+1: 
            v+=1
            if v<=10: print(f"STRICT VIOL r={r} n={n}")
print(f"t_{{r+1}}(n) >= t_r(n)+1 for n>=2r+1: violations {v}")
