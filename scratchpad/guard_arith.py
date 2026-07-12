"""
Arithmetic tests for the `some-part <= 1` guard in kp_caseB_impl.

Notation: r >= 2, n >= r+3. blocks = (r-1 D-parts) + (c) : r blocks summing to n.
  t_r(n)  = Turan edge count (balanced complete r-partite)
  kpSaving(n,r) = (n//r - 1) if 2r+1<=n else 2
  sig2(blocks) = sum_{i<j} b_i b_j  (= e(complete multipartite), <= t_r(n))

The two routes we want to justify:
 (Empty)     some D-part = 0  =>  e(G) <= t_{r-1}(n)          [main_ineq, sig2 drops a 0 block]
             need:  t_{r-1}(n) + kpSaving(n,r) <= t_r(n)
 (Singleton) some D-part = 1 (={w}), c>=2, all parts >=1
             deg(w) <= Delta = d, so defc(w) = n-1-deg(w) >= n-1-d = c-1
             main_ineq: 2 e(G) + sum defc <= 2 sig2(blocks), sum defc >= defc(w) >= c-1
             => e(G) <= sig2(blocks) - ceil((c-1)/2)
             need:  sig2(blocks) - ceil((c-1)/2) + kpSaving(n,r) <= t_r(n)
                    for EVERY block vector with a singleton D-part and c>=2.
  Also test the cruder singleton bounds to see which is the weakest that still holds:
             (S1)  sig2(blocks) - 1  + kpSaving <= t_r   (just "singleton is bad", Sum defc>=1)
             (S2)  sig2(blocks) - 2  + kpSaving <= t_r   (defc(w)>=2 subcase)
"""
import itertools, math

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

def compositions(n, k, lo=0):
    """all k-tuples of ints >= lo summing to n (ordered)."""
    if k == 1:
        if n >= lo: yield (n,)
        return
    for first in range(lo, n - lo*(k-1) + 1):
        for rest in compositions(n-first, k-1, lo):
            yield (first,)+rest

# ---------- Claim 1: empty-part route arithmetic ----------
print("="*70)
print("CLAIM 1 (empty part):  t_{r-1}(n) + kpSaving(n,r) <= t_r(n),  n>=r+3")
print("="*70)
viol1 = 0; total1 = 0
worst1 = None
for r in range(2, 12):
    for n in range(r+3, 60):
        total1 += 1
        lhs = turan(n, r-1) + kpsav(n, r)
        rhs = turan(n, r)
        slack = rhs - lhs
        if lhs > rhs:
            viol1 += 1
            if viol1 <= 10: print(f"  VIOL r={r} n={n}: t_{r-1}={turan(n,r-1)} +kpsav={kpsav(n,r)} = {lhs} > t_r={rhs}")
        if worst1 is None or slack < worst1[0]:
            worst1 = (slack, r, n)
print(f"  checked {total1}, violations {viol1}; tightest slack = {worst1}")

# ---------- Claim S / S1 / S2: singleton-part route arithmetic ----------
print("="*70)
print("SINGLETON routes: blocks = (r-1 D-parts, c),  min D-part = 1, c>=2")
print(" (Smain) sig2 - ceil((c-1)/2) + kpSaving <= t_r   [main_ineq, defc(w)>=c-1]")
print(" (S1)    sig2 - 1              + kpSaving <= t_r   [singleton bad]")
print(" (S2)    sig2 - 2              + kpSaving <= t_r")
print("="*70)
for (name, ded) in [("Smain", None), ("S1", 1), ("S2", 2)]:
    viol = 0; total = 0; worst = None; example = None
    for r in range(2, 9):
        for n in range(r+3, 26):
            # D-parts: r-1 of them, each >=1, one =1 (singleton). c = last block >=2.
            for c in range(2, n-(r-2)+1 if r>=2 else n+1):
                dsum = n - c
                if dsum < (r-1):  # each D-part >=1
                    continue
                # enumerate D-part vectors of length r-1, each >=1, min==1
                for dparts in compositions(dsum, r-1, 1):
                    if min(dparts) != 1:
                        continue
                    blocks = list(dparts) + [c]
                    s2 = sig2(blocks)
                    if name == "Smain":
                        deduction = (c-1+1)//2  # ceil((c-1)/2)
                    else:
                        deduction = ded
                    total += 1
                    lhs = s2 - deduction + kpsav(n, r)
                    rhs = turan(n, r)
                    slack = rhs - lhs
                    if lhs > rhs:
                        viol += 1
                        if viol <= 6:
                            print(f"  {name} VIOL r={r} n={n} blocks={blocks}: "
                                  f"sig2={s2} -ded{deduction} +sav{kpsav(n,r)} = {lhs} > t_r={rhs}")
                    if worst is None or slack < worst[0]:
                        worst = (slack, r, n, tuple(blocks))
    print(f"[{name}] checked {total}, violations {viol}; tightest slack = {worst}")
