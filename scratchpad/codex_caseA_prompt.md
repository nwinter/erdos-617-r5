# Task: finish the 4 `sorry`s in `caseA_slack` (Lean 4 + Mathlib)

File: `/Users/winter/research/erdos-617/lean617_f7/Lean617/ScratchCaseA.lean`

It currently COMPILES with 4 `sorry`s (one per `split_ifs` branch) inside `caseA_slack`.
Compile check command (run from `/Users/winter/research/erdos-617/lean617_f7`):
  `lake env lean Lean617/ScratchCaseA.lean`
It must end with only the `declaration uses sorry` warning (or none once done). DO NOT
edit `two_mul_turan` (proven) or anything above `caseA_slack`. Only replace the 4 `sorry`s.

## Context: what each branch's goal is

Before the `split_ifs`, the goal was reduced (via `two_mul_turan`, the division-free
Turán identity `2*t_r(n) = (n/r)*(n+n%r)*(r-1) + (n%r)*(n%r-1)`) to a pure ℕ polynomial
inequality. Local hypotheses in scope in EVERY branch:
  q = n/r, s = n%r, qp = d/(r-1), sp = d%(r-1)   (via `set`)
  hn  : n = r*q + s
  hslt: s < r
  hd  : d = (r-1)*qp + sp
  hsplt: sp < r - 1
  hr  : 2 ≤ r,  hd0 : 0 < d,  hdn : d < n
  hts : #(turanGraph d (r-1)).edgeFinset + d*(n-d) ≤ #(turanGraph n r).edgeFinset  (turan_step)

The 4 branches (from `split_ifs with h1 h2 h2` on savn = kpSaving n r, savd = kpSaving d (r-1)):
  B1 [h1: 2*r+1 ≤ n]      [h2: 2*(r-1)+1 ≤ d]   savn = q-1, savd = qp-1
  B2 [h1: 2*r+1 ≤ n]      [¬h2: ¬ 2*(r-1)+1 ≤ d] savn = q-1, savd = 2
  B3 [¬h1: ¬ 2*r+1 ≤ n]   [h2: 2*(r-1)+1 ≤ d]   savn = 2,   savd = qp-1
  B4 [¬h1]                [¬h2]                  savn = 2,   savd = 2

Each branch goal (schematically, all ℕ, `#` = edge card already replaced by the poly):
  (qp*d + qp*sp)*(r-1-1) + sp*(sp-1) + 2*(d*(n-d)) + 2*savn
    ≤ q*(n+s)*(r-1) + s*(s-1) + 2*savd

## The mathematical certificate (all VERIFIED numerically, 0 violations, r=2..11)

Define B := 2*(t_r(n) - t_{r-1}(d) - d*(n-d)) ≥ 0 (this is `hts` doubled). One proves
`2*(RHS) - 2*(LHS)` i.e. the doubled goal reduces to `B ≥ 2*(savn - savd)`. Over ℤ, the
KEY IDENTITY (verified in sympy) is:
  B = Q*(r*(r-1)*Q + 2*(r-1)*s - 2*r*sp) + (s-sp)*(s-sp-1),   where Q := q - qp.

Regime facts:
- B4 (savn=savd=2): `2*(savn-savd)=0`; goal is exactly `hts` doubled ⇒ `omega`-close using hts.
- B3 (n small, d main): forces n=2r, d=2r-1 (since d<n≤2r and d≥2r-1). Then need B ≥ 2*(2-(qp-1))=6-2qp.
  Just `nlinarith`/`omega` after substituting; small/tight — may need the identity.
- B2 (n main, d small): savd=2. Need B ≥ 2*(q-1-2) = 2q-6. Hard only if q≥4.
- B1 (MM, savn=q-1, savd=qp-1): need B ≥ 2Q = 2(q-qp). Using the identity:
    B - 2Q = Q*(r*(r-1)*Q + 2*(r-1)*s - 2*r*sp - 2) + (s-sp)*(s-sp-1).
    * If Q ≤ 0: B ≥ 0 ≥ 2Q, done via hts (turan_step) + omega — no identity needed.
    * If Q ≥ 2: bracket `r(r-1)Q + 2(r-1)s - 2r*sp - 2 ≥ 2r-2 > 0` (since sp ≤ r-2),
      so Q*bracket ≥ 0, plus (s-sp)(s-sp-1) ≥ 0 (consecutive ints).
    * If Q = 1: reduces to `(s-sp)² + (2r-3)s - (2r-1)sp + r²-r-2 ≥ 0`. Since it is DECREASING
      in sp and sp ≤ r-2, min at sp=r-2 where it equals `s*(s+1) ≥ 0`. Certificate hints:
      `sq_nonneg ((s:ℤ)-sp)`, `mul_nonneg (s≥0) (s+1≥0)`, and `(r-2-sp) ≥ 0`.

## Recommended Lean approach

Work over ℤ. Suggested per-branch skeleton:
1. Add cast helpers near the top of `caseA_slack` (before `split_ifs`):
     have cast_pred : ∀ a : ℕ, ((a*(a-1) : ℕ) : ℤ) = (a:ℤ)*((a:ℤ)-1) := by
       intro a; cases a with | zero => simp | succ k => push_cast; ring
2. In each branch: `subst hn hd` is NOT possible (n,d are let-bound by earlier context) —
   instead keep hn, hd as equations. `zify [hdn.le]` the goal, then rewrite the two
   `↑(s*(s-1))`, `↑(sp*(sp-1))` occurrences with `cast_pred s`, `cast_pred sp` (may need
   `push_cast` first to expose them; guard `r-1-1`, `r-1` via `Nat.cast_sub`).
   Then `nlinarith [hn, hd, hslt, hsplt, <the certificate hints above>, sq_nonneg (...),
   mul_nonneg ...]`. For Q-sign split in B1, do `rcases le_or_lt (qp) q` (Q≥0) etc. or
   `rcases lt_trichotomy q qp` and handle.
3. B4: likely `omega`-provable directly from `hts` (double it). Try `omega` first (with the
   two_mul_turan-substituted terms it may need nlinarith; if so, the savn=savd=2 makes the
   savings cancel so `nlinarith [hts-derived]`).

Prefer robust tactics; it's fine to `rcases` on Q sign and regime sub-cases. Keep each branch
self-contained. Verify the whole file compiles clean at the end. Report the final proof text
of the 4 branches.
