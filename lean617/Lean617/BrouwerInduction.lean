/-
F6 discharge (WIP scaffold) — the Kang–Pikhurko / Brouwer upper-bound induction.

This file is the SKELETON of `kp_upper` (KP Theorem 4 upper bound, both regimes),
by strong induction on `r`, built on the sorry-free foundations in
`BrouwerDischarge.lean` (`turan_step`, `symmG_edgeCount_eq`). The **Case A** branch
(H[D] not (r−1)-partite ⇒ IH) is fully assembled modulo two clearly-named sorries:
  * `exists_induced_on_nbhd` — transport of `G[Γx]` to `Fin d` (comap kit);
  * `caseA_slack` — the arithmetic slack, NUMERICALLY VERIFIED true for all
    `d ∈ [1,n−1]`, `r = 2..6` (scratchpad/check_caseA_slack.py). Closed-form/floor
    proof, or `decide` over the bounded `n ≤ 21` descent.
Case B is now `kp_caseB_impl` (good/bad dichotomy, takes the `(r−1)`-colouring `κ`
directly), wired into `kp_upper` via `colorable_restrict_of_comap` + the small-`n`
emptiness lemma `gnr_colorable_small` (gives `hn : r+3 ≤ n`). The remaining sorries are:
  * `kp_lemma3` — the `K_{r+1}`-counting core (sub-lemma F, HARD);
  * `kp_caseB_impl`'s `some-part ≤ 1` guard (needs the max-size-`G` reduction);
  * `equality21` — the (5,21) KP equality classification.

See FORMAL.md F6 "DISCHARGE ROADMAP" for the full plan.
Research project: Mathlib style linters disabled.
-/
import Lean617.BrouwerDischarge

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.multiGoal false
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 2000000

open Finset SimpleGraph
open scoped Classical

namespace Erdos617

/-- The KP/Brouwer saving off the Turán maximum: `⌊n/r⌋ − 1` in the main regime
`n ≥ 2r+1`, and `2` in the small regime `r+3 ≤ n ≤ 2r` (KP Theorem 1). -/
def kpSaving (n r : ℕ) : ℕ := if 2 * r + 1 ≤ n then n / r - 1 else 2

/-- In the main regime `n ≥ 2r+1`, `kpSaving n r = ⌊n/r⌋ − 1`. -/
theorem kpSaving_of_main {n r : ℕ} (h : 2 * r + 1 ≤ n) : kpSaving n r = n / r - 1 := by
  rw [kpSaving, if_pos h]

/-- Division-free Turán identity: `2·t_r(n) = (n/r)·(n + n%r)·(r−1) + (n%r)·(n%r−1)`. -/
theorem two_mul_turan (n r : ℕ) (hr : 1 ≤ r) :
    2 * (turanGraph n r).edgeFinset.card
      = (n / r) * (n + n % r) * (r - 1) + (n % r) * (n % r - 1) := by
  rw [card_edgeFinset_turanGraph]
  set s := n % r with hs
  set q := n / r with hq
  have hrpos : 0 < r := hr
  have hnrq : n = r * q + s := by rw [hq, hs]; exact (Nat.div_add_mod n r).symm
  have hsle : s ≤ n := by omega
  have hsq : n ^ 2 - s ^ 2 = r * q * (n + s) := by
    rw [Nat.sq_sub_sq]
    have hns : n - s = r * q := by omega
    rw [hns]; ring
  set M := q * (n + s) * (r - 1) with hM
  have hMr : (n ^ 2 - s ^ 2) * (r - 1) = r * M := by rw [hsq, hM]; ring
  have h2M : 2 ∣ M := by
    have hnss : n + s = r * q + 2 * s := by omega
    have hev : 2 ∣ (n + s) * (r - 1) := by
      rw [hnss]
      have h1 : 2 ∣ r * (r - 1) := (Nat.even_mul_pred_self r).two_dvd
      have h2 : (r * q + 2 * s) * (r - 1) = q * (r * (r - 1)) + 2 * (s * (r - 1)) := by ring
      rw [h2]
      exact Nat.dvd_add (Dvd.dvd.mul_left h1 q) (Dvd.dvd.mul_right (dvd_refl 2) _)
    have hMeq : M = q * ((n + s) * (r - 1)) := by rw [hM]; ring
    rw [hMeq]; exact Dvd.dvd.mul_left hev q
  have hdiv : (n ^ 2 - s ^ 2) * (r - 1) / (2 * r) = M / 2 := by
    rw [hMr, mul_comm 2 r, Nat.mul_div_mul_left _ _ hrpos]
  have hchoo : s.choose 2 = s * (s - 1) / 2 := Nat.choose_two_right s
  rw [hdiv, hchoo, Nat.mul_add, Nat.mul_div_cancel' h2M,
    Nat.mul_div_cancel' (Nat.even_mul_pred_self s).two_dvd]

/-! ## The arithmetic slack (Case A)

`caseA_slack` is the closed-form inequality that lets the `(r−1)`-level IH bound
compose with the Turán recursion (`turan_step`). Verified numerically true for all
`d ∈ [1,n−1]`, `2 ≤ r ≤ 6`; the `r = 5` descent only needs `n ≤ 21`. -/

/-- **Case-A arithmetic slack** (SORRY — verified true numerically for all
`d ∈ [1,n−1]`, `2 ≤ r ≤ 6`; scratchpad/check_caseA_slack.py). For `2 ≤ r`, `0 < d`,
`d < n`: `t_{r−1}(d) + d·(n−d) + kpSaving n r ≤ t_r(n) + kpSaving d (r−1)`.

PROOF RECIPE (the division-by-`r` is the only obstacle; here is the clean route):
1. Prove the **division-free** Turán identity (reusable; also for `equality21`):
     `2 * (turanGraph n r).edgeFinset.card = (n/r)*(n + n%r)*(r−1) + (n%r)*(n%r − 1)`.
   Derivation from `card_edgeFinset_turanGraph` (`t = (n²−(n%r)²)(r−1)/(2r) + C(n%r,2)`):
   with `q=n/r, s=n%r`: `n−s = r*q` (Nat.div_add_mod), `n²−s²=(n−s)(n+s)=r*q*(n+s)`
   (`Nat.sq_sub_sq`), so `(n²−s²)(r−1)/(2r) = q*(n+s)*(r−1)/2` (`Nat.mul_div_mul_left`,
   cancel `r`); `2*C(s,2)=s*(s−1)` (`Nat.choose_two_right`+`Nat.div_mul_cancel`, `2∣s(s−1)`);
   clear the `/2` via evenness `2 ∣ q*(n+s)*(r−1)` (expand `n+s=rq+2s` ⇒
   `q²r(r−1)+2qs(r−1)`, both even; `Nat.even_mul_pred_self`). Verified: 176/102/90 at
   (21,5)/(16,5)/(15,5).
2. `rw` this identity (and its `(d, r−1)` instance) after `×2`-ing the goal
   (`Nat.mul_le_mul_left` / omega-scale), unfold `kpSaving` (both branches via
   `split_ifs`), and substitute `n = r*(n/r)+n%r`, `d = (r−1)*(d/(r−1))+d%(r−1)` with
   `n%r < r`, `d%(r−1) < r−1`. The result is a degree-2 polynomial inequality in the
   atoms `{n/r, n%r, d/(r−1), d%(r−1), r}` — close with `nlinarith` (likely needs SOS
   hints on the products) or, since the `r=5` uses have `n ≤ 21`, restructure `kp_upper`
   to `n ≤ 21 ∧ r ≤ 5` and `interval_cases … <;> decide` (bounded fallback). -/
theorem caseA_slack {n r d : ℕ} (hr : 2 ≤ r) (hd0 : 0 < d) (hdn : d < n) :
    (turanGraph d (r - 1)).edgeFinset.card + d * (n - d) + kpSaving n r
      ≤ (turanGraph n r).edgeFinset.card + kpSaving d (r - 1) := by
  -- turan_step at level r-1: t_{r-1}(d) + d(n-d) ≤ t_r(n)
  have hts : (turanGraph d (r-1)).edgeFinset.card + d * (n - d)
      ≤ (turanGraph n r).edgeFinset.card := by
    have h := turan_step (n := n) (r := r - 1) (d := d) (by omega) (by omega)
    rwa [Nat.sub_add_cancel (show 1 ≤ r by omega)] at h
  suffices h2 : 2 * ((turanGraph d (r-1)).edgeFinset.card + d * (n - d) + kpSaving n r)
      ≤ 2 * ((turanGraph n r).edgeFinset.card + kpSaving d (r - 1)) by omega
  have hTn := two_mul_turan n r (by omega)
  have hTd := two_mul_turan d (r - 1) (by omega)
  simp only [Nat.mul_add]
  rw [hTd, hTn]
  -- goal now polynomial in n/r, n%r, d/(r-1), d%(r-1)
  set q := n / r with hqdef
  set s := n % r with hsdef
  set qp := d / (r - 1) with hqpdef
  set sp := d % (r - 1) with hspdef
  have hn : n = r * q + s := by rw [hqdef, hsdef]; exact (Nat.div_add_mod n r).symm
  have hslt : s < r := hsdef ▸ Nat.mod_lt n (by omega)
  have hd : d = (r - 1) * qp + sp := by rw [hqpdef, hspdef]; exact (Nat.div_add_mod d (r - 1)).symm
  have hsplt : sp < r - 1 := hspdef ▸ Nat.mod_lt d (by omega)
  simp only [kpSaving]
  split_ifs with h1 h2 h2
  · rw [← hqdef, ← hqpdef]
    have hbase : qp * (d + sp) * (r - 1 - 1) + sp * (sp - 1) +
        2 * (d * (n - d)) ≤ q * (n + s) * (r - 1) + s * (s - 1) := by
      omega
    by_cases hqqp : q ≤ qp
    · omega
    have hq1 : 0 < q := by rw [hqdef]; exact Nat.div_pos (by omega) (by omega)
    have hqp1 : 0 < qp := by rw [hqpdef]; exact Nat.div_pos (by omega) (by omega)
    have cast_pred : ∀ a : ℕ, (a : ℤ) * ((a - 1 : ℕ) : ℤ) = (a : ℤ) * ((a : ℤ) - 1) := by
      intro a
      cases a with
      | zero => simp
      | succ k => push_cast; ring
    zify [hdn.le, show (1:ℕ) ≤ r by omega, show (1:ℕ) ≤ r - 1 by omega,
      show (1:ℕ) ≤ q by omega, show (1:ℕ) ≤ qp by omega]
    rw [cast_pred s, cast_pred sp]
    push_cast
    have hnZ : (n : ℤ) = (r : ℤ) * q + s := by exact_mod_cast hn
    have hdZ : (d : ℤ) = ((r : ℤ) - 1) * qp + sp := by
      have h1r : (1 : ℕ) ≤ r := by omega
      rw [hd]; push_cast [Nat.cast_sub h1r]; ring
    have hcon : 0 ≤ ((s : ℤ) - sp) * ((s : ℤ) - sp - 1) := by
      by_cases h : (sp : ℤ) < s
      · nlinarith [mul_nonneg (show (0:ℤ) ≤ (s:ℤ) - sp by linarith)
          (show (0:ℤ) ≤ (s:ℤ) - sp - 1 by linarith)]
      · push_neg at h
        nlinarith [mul_nonneg (show (0:ℤ) ≤ (sp:ℤ) - s by linarith)
          (show (0:ℤ) ≤ (sp:ℤ) - s + 1 by linarith)]
    by_cases hQ : q = qp + 1
    · -- Q = 1: K + Δ(Δ−1) = s(s+1) + (r−2−sp)(2s+r+1−sp)
      have hQZ : (q : ℤ) = qp + 1 := by exact_mod_cast hQ
      have e1 : 0 ≤ (s : ℤ) * (s + 1) := by positivity
      have e2 : 0 ≤ ((r : ℤ) - 2 - sp) * (2 * (s : ℤ) + r + 1 - sp) :=
        mul_nonneg (by omega) (by omega)
      rw [hnZ, hdZ, hQZ]
      nlinarith [e1, e2]
    · have hqgap : (qp : ℤ) + 2 ≤ q := by omega
      have hbr : 0 ≤ (r : ℤ) * ((r : ℤ) - 1) * ((q : ℤ) - qp) +
          2 * ((r : ℤ) - 1) * s - 2 * (r : ℤ) * sp - 2 := by
        nlinarith [mul_nonneg (mul_nonneg (show (0:ℤ) ≤ (r:ℤ) by omega)
            (show (0:ℤ) ≤ (r:ℤ) - 1 by omega)) (show (0:ℤ) ≤ (q:ℤ) - qp - 2 by omega),
          mul_nonneg (show (0:ℤ) ≤ 2*(r:ℤ) by omega) (show (0:ℤ) ≤ (r:ℤ) - 2 - sp by omega),
          mul_nonneg (show (0:ℤ) ≤ (r:ℤ) - 1 by omega) (show (0:ℤ) ≤ (s:ℤ) by positivity)]
      have hprod : 0 ≤ ((q : ℤ) - qp) *
          ((r : ℤ) * ((r : ℤ) - 1) * ((q : ℤ) - qp) +
            2 * ((r : ℤ) - 1) * s - 2 * (r : ℤ) * sp - 2) :=
        mul_nonneg (by omega) hbr
      rw [hnZ, hdZ]
      nlinarith [hprod, hcon]
  · rw [← hqdef]
    have hbase : qp * (d + sp) * (r - 1 - 1) + sp * (sp - 1) +
        2 * (d * (n - d)) ≤ q * (n + s) * (r - 1) + s * (s - 1) := by
      omega
    by_cases hqsmall : q ≤ 3
    · omega
    have hq1 : 0 < q := by rw [hqdef]; exact Nat.div_pos (by omega) (by omega)
    have cast_pred : ∀ a : ℕ, (a : ℤ) * ((a - 1 : ℕ) : ℤ) = (a : ℤ) * ((a : ℤ) - 1) := by
      intro a
      cases a with
      | zero => simp
      | succ k => push_cast; ring
    zify [hdn.le, show (1:ℕ) ≤ r by omega, show (1:ℕ) ≤ r - 1 by omega,
      show (1:ℕ) ≤ q by omega]
    rw [cast_pred s, cast_pred sp]
    push_cast
    have hnZ : (n : ℤ) = (r : ℤ) * q + s := by exact_mod_cast hn
    have hdZ : (d : ℤ) = ((r : ℤ) - 1) * qp + sp := by
      have h1r : (1 : ℕ) ≤ r := by omega
      rw [hd]; push_cast [Nat.cast_sub h1r]; ring
    have hqple : (qp : ℤ) ≤ 2 := by
      by_contra h
      have hprod : 0 ≤ ((r : ℤ) - 1) * ((qp : ℤ) - 3) :=
        mul_nonneg (by omega) (by omega)
      nlinarith
    have hcon : 0 ≤ ((s : ℤ) - sp) * ((s : ℤ) - sp - 1) := by
      by_cases h : (sp : ℤ) < s
      · nlinarith [mul_nonneg (show (0:ℤ) ≤ (s:ℤ) - sp by linarith)
          (show (0:ℤ) ≤ (s:ℤ) - sp - 1 by linarith)]
      · push_neg at h
        nlinarith [mul_nonneg (show (0:ℤ) ≤ (sp:ℤ) - s by linarith)
          (show (0:ℤ) ≤ (sp:ℤ) - s + 1 by linarith)]
    have hqgap : (qp : ℤ) + 2 ≤ q := by omega
    have hbr : 0 ≤ (r : ℤ) * ((r : ℤ) - 1) * ((q : ℤ) - qp) +
        2 * ((r : ℤ) - 1) * s - 2 * (r : ℤ) * sp - 2 := by
      nlinarith [mul_nonneg (mul_nonneg (show (0:ℤ) ≤ (r:ℤ) by omega)
          (show (0:ℤ) ≤ (r:ℤ) - 1 by omega)) (show (0:ℤ) ≤ (q:ℤ) - qp - 2 by omega),
        mul_nonneg (show (0:ℤ) ≤ 2*(r:ℤ) by omega) (show (0:ℤ) ≤ (r:ℤ) - 2 - sp by omega),
        mul_nonneg (show (0:ℤ) ≤ (r:ℤ) - 1 by omega) (show (0:ℤ) ≤ (s:ℤ) by positivity)]
    have hprod : 0 ≤ ((q : ℤ) - qp) *
        ((r : ℤ) * ((r : ℤ) - 1) * ((q : ℤ) - qp) +
          2 * ((r : ℤ) - 1) * s - 2 * (r : ℤ) * sp - 2) :=
      mul_nonneg (by omega) hbr
    rw [hnZ, hdZ]
    nlinarith [hprod, hcon, hqple]
  · rw [← hqpdef]
    have hbase : qp * (d + sp) * (r - 1 - 1) + sp * (sp - 1) +
        2 * (d * (n - d)) ≤ q * (n + s) * (r - 1) + s * (s - 1) := by
      omega
    by_cases hqpbig : 3 ≤ qp
    · omega
    have hnval : n = 2 * r := by omega
    have hdval : d = 2 * r - 1 := by omega
    have hqple : qp ≤ 2 := by omega
    have hqpge : 2 ≤ qp := by
      by_contra h
      have hqple' : qp ≤ 1 := by omega
      have hp : (r - 1) * qp ≤ (r - 1) * 1 := Nat.mul_le_mul_left _ hqple'
      omega
    have hqpval : qp = 2 := le_antisymm hqple hqpge
    have hspval : sp = 1 := by
      have h := hd; rw [hqpval, hdval] at h; omega
    have hsval : s = 0 := by rw [hsdef, hnval]; exact Nat.mul_mod_left 2 r
    have hqval : q = 2 := by
      have h0 := hn; rw [hnval, hsval, add_zero] at h0
      exact Nat.eq_of_mul_eq_mul_left (show 0 < r by omega) (by omega)
    rw [hqval, hsval, hqpval, hspval, hnval, hdval]
    simp only [Nat.sub_self, Nat.zero_mul, Nat.mul_zero, Nat.add_zero,
      Nat.zero_add, show (0:ℕ) - 1 = 0 from rfl, show (1:ℕ) - 1 = 0 from rfl]
    zify [show (1:ℕ) ≤ r by omega, show (1:ℕ) ≤ r - 1 by omega,
      show (1:ℕ) ≤ 2 * r by omega, show (2 * r - 1 : ℕ) ≤ 2 * r by omega]
    nlinarith [sq_nonneg (r:ℤ)]
  · omega

/-! ## Arithmetic backbone I: the two-bad-parts bound (`two_bad_aux`)

For `r` part-sizes each `≥ 2` summing to `n`, `σ₂(parts) − min(parts) + kpSaving n r
≤ t_r(n)`. This is what the Case-B "two bad parts" branch (`e(G) ≤ σ₂(d) − d₁`)
feeds into. Proof: induction peeling the max part (head of a descending-sorted list);
each step is EXACTLY `caseA_slack` (the `kpSaving (n−max, r−1)` cancels), base `r = 1`
uses `t_1 = 0`. Numerically verified 0 violations (scratchpad/check_kp_caseB_arith.py,
two_bad_route.py). -/

/-- σ₂ of a list of part-sizes, head-recursively: `σ₂(a::L) = a·(Σ L) + σ₂(L)`. -/
def sig2 : List ℕ → ℕ
  | [] => 0
  | a :: L => a * L.sum + sig2 L

@[simp] theorem sig2_nil : sig2 [] = 0 := rfl
@[simp] theorem sig2_cons (a : ℕ) (L : List ℕ) : sig2 (a :: L) = a * L.sum + sig2 L := rfl

/-- **two_bad backbone (sorted form).** For a descending-sorted list `L` of part-sizes,
each `≥ 2`, with actual minimum `m` (`m ∈ L`, a lower bound), we have
`σ₂(L) + kpSaving (ΣL) |L| ≤ t_{|L|}(ΣL) + m`. Peels the head (= max, by sortedness);
the step is exactly `caseA_slack`. -/
theorem two_bad_aux : ∀ (L : List ℕ), List.Pairwise (· ≥ ·) L → (∀ x ∈ L, 2 ≤ x) →
    ∀ m, m ∈ L → (∀ x ∈ L, m ≤ x) →
    sig2 L + kpSaving L.sum L.length
      ≤ (turanGraph L.sum L.length).edgeFinset.card + m := by
  intro L
  induction L with
  | nil => intro _ _ m hm _; simp at hm
  | cons a L IH =>
    intro hsort hge2 m hm hmle
    have ha2 : 2 ≤ a := hge2 a (by simp)
    cases L with
    | nil =>
      -- base: L = [a], r = 1, sum = a, t_1(a) = 0
      have hma : m = a := by simpa using hm
      have h2 := two_mul_turan a 1 (le_refl 1)
      simp only [Nat.div_one, Nat.mod_one, Nat.sub_self, Nat.mul_zero, Nat.zero_mul,
        Nat.add_zero] at h2
      simp only [sig2_cons, sig2_nil, List.sum_cons, List.sum_nil, List.length_cons,
        List.length_nil, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
      simp only [kpSaving]
      split_ifs <;> omega
    | cons b L' =>
      obtain ⟨hheadmax, hsortL⟩ := List.pairwise_cons.mp hsort
      have hge2L : ∀ x ∈ b :: L', 2 ≤ x := fun x hx => hge2 x (List.mem_cons_of_mem a hx)
      have hmleL : ∀ x ∈ b :: L', m ≤ x := fun x hx => hmle x (List.mem_cons_of_mem a hx)
      -- m ∈ (b :: L'): the min survives peeling the max head
      have hmL : m ∈ b :: L' := by
        rcases List.mem_cons.mp hm with hma | h
        · have hbL : b ∈ b :: L' := List.mem_cons_self
          have hba := hheadmax b hbL
          have hmb := hmleL b hbL
          have hbm : b = m := by omega
          rw [← hbm]; exact hbL
        · exact h
      have hLpos : 0 < (b :: L').sum := by
        have hb2 : 2 ≤ b := hge2L b List.mem_cons_self
        have hble : b ≤ (b :: L').sum :=
          List.single_le_sum (fun _ _ => Nat.zero_le _) b List.mem_cons_self
        omega
      have hIH := IH hsortL hge2L m hmL hmleL
      -- caseA_slack with n = a + (b::L').sum, r = (b::L').length + 1, d = (b::L').sum
      have hslack := caseA_slack (n := a + (b :: L').sum) (r := (b :: L').length + 1)
        (d := (b :: L').sum) (by rw [List.length_cons]; omega) hLpos (by omega)
      -- normalise the two subtractions so atoms match hIH / goal
      rw [(by omega : (a + (b :: L').sum) - (b :: L').sum = a),
          (by omega : (b :: L').length + 1 - 1 = (b :: L').length)] at hslack
      -- peel exactly one cons in the goal (keep `(b::L').sum`, `(b::L').length` intact)
      have hsum : (a :: b :: L').sum = a + (b :: L').sum := List.sum_cons
      have hlen : (a :: b :: L').length = (b :: L').length + 1 := List.length_cons ..
      rw [hsum, hlen, sig2_cons, Nat.mul_comm a (b :: L').sum]
      omega

/-! ## Bridges from the sorted-list `two_bad_aux` to caller-friendly forms

`two_mul_sig2` (σ₂ from sum & sum-of-squares) ⇒ `sig2` is permutation-invariant
(`sig2_perm`) ⇒ `two_bad_list` (UNSORTED list, sorts internally via `mergeSort`) and
`two_bad_finset` (`Fin r → ℕ` indexed). The Case-B good/bad sub-lemmas (C, E) build the
part-size list `(d₁,…,d_{r−1},c)` in whatever order and hand it to these. -/

/-- **`two_mul_sig2`.** `sig2` is determined by sum and sum-of-squares:
`2·σ₂(L) + Σ aᵢ² = (Σ L)²`. -/
theorem two_mul_sig2 : ∀ (L : List ℕ), 2 * sig2 L + (L.map (· ^ 2)).sum = L.sum ^ 2 := by
  intro L
  induction L with
  | nil => simp
  | cons a L IH =>
    simp only [sig2_cons, List.map_cons, List.sum_cons]
    rw [show (a + L.sum) ^ 2 = a ^ 2 + 2 * a * L.sum + L.sum ^ 2 from by ring, ← IH]
    ring

/-- `sig2` is permutation-invariant (via `two_mul_sig2`). -/
theorem sig2_perm {L₁ L₂ : List ℕ} (h : L₁.Perm L₂) : sig2 L₁ = sig2 L₂ := by
  have e1 := two_mul_sig2 L₁
  have e2 := two_mul_sig2 L₂
  have hs : L₁.sum = L₂.sum := h.sum_eq
  have hsq : (L₁.map (· ^ 2)).sum = (L₂.map (· ^ 2)).sum := (h.map _).sum_eq
  rw [hs, hsq] at e1
  omega

/-- **`two_bad_list`.** Unsorted-list form of `two_bad_aux`: sorts internally via
`mergeSort`, so the caller need not pre-sort the part-sizes. -/
theorem two_bad_list (L : List ℕ) (h2 : ∀ x ∈ L, 2 ≤ x)
    (m : ℕ) (hm : m ∈ L) (hmle : ∀ x ∈ L, m ≤ x) :
    sig2 L + kpSaving L.sum L.length
      ≤ (turanGraph L.sum L.length).edgeFinset.card + m := by
  have hperm : (L.mergeSort (· ≥ ·)).Perm L := List.mergeSort_perm L _
  have hsorted : List.Pairwise (· ≥ ·) (L.mergeSort (· ≥ ·)) :=
    List.pairwise_mergeSort' (· ≥ ·) L
  have h2' : ∀ x ∈ L.mergeSort (· ≥ ·), 2 ≤ x := fun x hx => h2 x (hperm.mem_iff.mp hx)
  have hm' : m ∈ L.mergeSort (· ≥ ·) := hperm.mem_iff.mpr hm
  have hmle' : ∀ x ∈ L.mergeSort (· ≥ ·), m ≤ x := fun x hx => hmle x (hperm.mem_iff.mp hx)
  have hres := two_bad_aux (L.mergeSort (· ≥ ·)) hsorted h2' m hm' hmle'
  rw [hperm.sum_eq, hperm.length_eq, sig2_perm hperm] at hres
  exact hres

/-- **`two_bad_finset`.** `Fin r → ℕ` (indexed) form: parts `p i ≥ 2`, `i₀` an argmin.
`σ₂(p) + kpSaving (Σp) r ≤ t_r(Σp) + p i₀` (i.e. `σ₂(p) − p i₀ + kpSaving ≤ t_r`);
`σ₂(p) = sig2 (ofFn p) = Σ_{i<j} p i · p j`. -/
theorem two_bad_finset {r : ℕ} (p : Fin r → ℕ) (h2 : ∀ i, 2 ≤ p i)
    (i₀ : Fin r) (hmin : ∀ i, p i₀ ≤ p i) :
    sig2 (List.ofFn p) + kpSaving (∑ i, p i) r
      ≤ (turanGraph (∑ i, p i) r).edgeFinset.card + p i₀ := by
  have hsum : (List.ofFn p).sum = ∑ i, p i := List.sum_ofFn
  have hlen : (List.ofFn p).length = r := by simp
  have h2' : ∀ x ∈ List.ofFn p, 2 ≤ x := by
    intro x hx; rw [List.mem_ofFn] at hx; obtain ⟨i, rfl⟩ := hx; exact h2 i
  have hm' : p i₀ ∈ List.ofFn p := by rw [List.mem_ofFn]; exact ⟨i₀, rfl⟩
  have hmle' : ∀ x ∈ List.ofFn p, p i₀ ≤ x := by
    intro x hx; rw [List.mem_ofFn] at hx; obtain ⟨i, rfl⟩ := hx; exact hmin i
  have hres := two_bad_list (List.ofFn p) h2' (p i₀) hm' hmle'
  rw [hsum, hlen] at hres
  exact hres

/-! ## Arithmetic backbone II: the construction bound (`constr_le`)

For the KP construction sequence `seq = (1^l, n₁..n_{r-l})` (`n = Σseq + 1`,
`n_s ≤ n_t` the two smallest parts `≥ 2`), `e(G(seq)) + kpSaving n r ≤ t_r(n)`,
where `e(G(seq)) = σ₂(seq) + σ₁(seq) − n_s − n_t + 1`. This is what KP Lemma 3's
output feeds into. Stated with `n_s, n_t` at the front and the rest `L` each `= 1`
or `≥ n_t`; proof identical in spirit to `two_bad_aux` — peel `L` (each step exactly
`caseA_slack`), `n_s, n_t` ride along, base `r = 2` (`constr_base`). Numerically
verified 0 violations (scratchpad/lemma3_route.py route (C)). -/

/-- **constr backbone (base, 2 parts).** For `ns, nt ≥ 2`, `ns ≤ nt`,
`ns·nt + (ns+nt+1) + kpSaving (ns+nt+1) 2 ≤ t_2(ns+nt+1) + ns + nt`. -/
theorem constr_base (ns nt : ℕ) (hns2 : 2 ≤ ns) (hnst : ns ≤ nt) :
    ns * nt + (ns + nt + 1) + kpSaving (ns + nt + 1) 2
      ≤ (turanGraph (ns + nt + 1) 2).edgeFinset.card + ns + nt := by
  have hkp : kpSaving (ns + nt + 1) 2 = (ns + nt + 1) / 2 - 1 := kpSaving_of_main (by omega)
  rw [hkp]
  suffices h : ns * nt + (ns + nt + 1) / 2 ≤ (turanGraph (ns + nt + 1) 2).edgeFinset.card by omega
  have hT := two_mul_turan (ns + nt + 1) 2 (by omega)
  simp only [show (2:ℕ) - 1 = 1 from rfl, Nat.mul_one] at hT
  set Q := (ns + nt + 1) / 2 with hQ
  have hdm : 2 * Q + (ns + nt + 1) % 2 = ns + nt + 1 := Nat.div_add_mod (ns + nt + 1) 2
  rcases (show (ns + nt + 1) % 2 = 0 ∨ (ns + nt + 1) % 2 = 1 by omega) with h0 | h1
  · rw [h0] at hT hdm
    simp only [Nat.add_zero, Nat.zero_mul] at hT hdm
    zify at hT hdm ⊢
    nlinarith [hT, hdm, mul_nonneg (show (0:ℤ) ≤ (Q:ℤ) - ns by omega)
      (show (0:ℤ) ≤ (Q:ℤ) - ns - 1 by omega)]
  · rw [h1] at hT hdm
    simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero] at hT hdm
    zify at hT hdm ⊢
    nlinarith [hT, hdm, sq_nonneg ((Q:ℤ) - ns)]

/-- **construction bound (`constr_le`, sorted form).** Any two parts `ns ≤ nt`
(each `≥ 2`) fixed at the front; the remaining parts `L` are each `≥ 1`. Then
`σ₂(ns::nt::L) + (Σ+1) + kpSaving (Σ+1) r ≤ t_r(Σ+1) + ns + nt`, i.e.
`e(G(seq)) + kpSaving n r ≤ t_r(n)` (`e(G(seq)) = σ₂(seq)+σ₁(seq)−n_s−n_t+1`, KP (4)).
Peels `L` (each peel exactly `caseA_slack`); `ns, nt` ride along untouched.
Base = `constr_base`. (The proof only needs each `L`-part `≥ 1`; taking `ns, nt` the two
smallest parts gives the tightest — construction-exact — instance, but ANY two `≥2` parts
work, which is what lets `lemma3_arith` pull the two smallest-`m` parts to the front.) -/
theorem constr_le (ns nt : ℕ) (hns2 : 2 ≤ ns) (hnst : ns ≤ nt) :
    ∀ (L : List ℕ), (∀ x ∈ L, 1 ≤ x) →
    sig2 (ns :: nt :: L) + ((ns :: nt :: L).sum + 1)
        + kpSaving ((ns :: nt :: L).sum + 1) (ns :: nt :: L).length
      ≤ (turanGraph ((ns :: nt :: L).sum + 1) (ns :: nt :: L).length).edgeFinset.card
        + ns + nt := by
  intro L
  induction L with
  | nil =>
    intro _
    have hb := constr_base ns nt hns2 hnst
    simpa using hb
  | cons a L' IH =>
    intro hmem
    have hIH := IH (fun x hx => hmem x (List.mem_cons_of_mem a hx))
    have ha1 : 1 ≤ a := hmem a List.mem_cons_self
    have hspos : 0 < (ns :: nt :: L').sum + 1 := by omega
    -- caseA_slack at the literal N and d (so its turanGraph terms match hIH / goal)
    have hslack := caseA_slack (n := (ns :: nt :: a :: L').sum + 1)
      (r := (ns :: nt :: a :: L').length) (d := (ns :: nt :: L').sum + 1)
      (by simp only [List.length_cons]; omega) hspos
      (by simp only [List.sum_cons]; omega)
    -- normalise SECOND args only (safe: turanGraph's Fin type depends on 1st arg only)
    rw [(by simp only [List.length_cons]; omega :
          (ns :: nt :: a :: L').length - 1 = (ns :: nt :: L').length),
        (by simp only [List.sum_cons]; omega :
          ((ns :: nt :: a :: L').sum + 1) - ((ns :: nt :: L').sum + 1) = a)] at hslack
    -- σ₂ peel + bridge a·(Σ rest) with (Σ rest + 1)·a
    have hsig : sig2 (ns :: nt :: a :: L')
        = sig2 (ns :: nt :: L') + a * (ns :: nt :: L').sum := by
      simp only [sig2_cons, List.sum_cons]; ring
    have hmul : a * (ns :: nt :: L').sum + a = ((ns :: nt :: L').sum + 1) * a := by ring
    have hNn' : (ns :: nt :: a :: L').sum + 1 = ((ns :: nt :: L').sum + 1) + a := by
      simp only [List.sum_cons]; ring
    rw [hsig]
    omega

/-! ## Arithmetic backbone II′: `lemma3_arith` (the direct Lemma-3 feed)

The pre-optimisation KP Lemma-3 bound (6), fed the `Mᵢ` sizes DIRECTLY (no optimisation
step (6)→construction, no `e(G(seq))`). Follows from `constr_le` (pull the two smallest-`m`
big classes to the front — sorted by size, `constr_le` now accepts ANY two `≥2` parts) plus
`(mₐ−1)(m_b−1) ≥ 0` and `Σ_L m ≤ Σ_L n`. Verified 0 violations over 4.1M cases
(scratchpad/check_kp_caseB_arith.py, `lemma3_arith`). -/

/-- `Σ(snd) ≤ Σ(fst)` over a list of pairs with each `snd ≤ fst` (`mᵢ ≤ nᵢ`). -/
theorem snd_sum_le_fst_sum : ∀ (M : List (ℕ × ℕ)), (∀ p ∈ M, p.2 ≤ p.1) →
    (M.map Prod.snd).sum ≤ (M.map Prod.fst).sum := by
  intro M
  induction M with
  | nil => intro _; simp
  | cons p M' IH =>
    intro hM
    simp only [List.map_cons, List.sum_cons]
    have h1 := hM p List.mem_cons_self
    have h2 := IH (fun q hq => hM q (List.mem_cons_of_mem p hq))
    omega

/-- **`lemma3_arith` (KP Lemma 3 pre-optimisation bound).** Parts `= 1^l` (singleton
colour classes) ++ the big classes; the two big classes `(na,ma),(nb,mb)` carrying the two
smallest `Mᵢ`-sizes are pulled to the front (sorted by size, `na ≤ nb`; `−ma·mb` is the
paper's (6) term), the rest `L` as `(nᵢ,mᵢ)` pairs with `2 ≤ nᵢ`, `1 ≤ mᵢ ≤ nᵢ`. Then
`σ₂(1^l,nvec) − m₁m₂ + l + Σmᵢ + kpSaving n r ≤ t_r(n)` (as `… + Σmᵢ + kpSaving ≤ t_r + m₁m₂`
to stay in ℕ). Feeds the `Mᵢ` sizes DIRECTLY — no optimisation, no `e(G(seq))`.
Proof: `constr_le` (`na,nb` at front) + `(ma−1)(mb−1) ≥ 0` + `Σ_L m ≤ Σ_L n`. -/
theorem lemma3_arith (l na nb ma mb : ℕ)
    (hna : 2 ≤ na) (hnab : na ≤ nb) (hma : 1 ≤ ma) (hmb : 1 ≤ mb)
    (hman : ma ≤ na) (hmbn : mb ≤ nb)
    (L : List (ℕ × ℕ)) (hL : ∀ p ∈ L, 2 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.2 ≤ p.1) :
    sig2 (na :: nb :: (List.replicate l 1 ++ L.map Prod.fst)) + l
        + (ma + mb + (L.map Prod.snd).sum)
        + kpSaving ((na :: nb :: (List.replicate l 1 ++ L.map Prod.fst)).sum + 1)
                   (na :: nb :: (List.replicate l 1 ++ L.map Prod.fst)).length
      ≤ (turanGraph ((na :: nb :: (List.replicate l 1 ++ L.map Prod.fst)).sum + 1)
                    (na :: nb :: (List.replicate l 1 ++ L.map Prod.fst)).length).edgeFinset.card
        + ma * mb := by
  have hrest1 : ∀ x ∈ (List.replicate l 1 ++ L.map Prod.fst), 1 ≤ x := by
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with h | h
    · rw [List.mem_replicate] at h; omega
    · rw [List.mem_map] at h; obtain ⟨p, hp, rfl⟩ := h
      have := (hL p hp).1; omega
  have hcl := constr_le na nb hna hnab
    (List.replicate l 1 ++ L.map Prod.fst) hrest1
  have hsum : (na :: nb :: (List.replicate l 1 ++ L.map Prod.fst)).sum
      = na + nb + l + (L.map Prod.fst).sum := by
    simp [List.sum_cons, List.sum_append, List.sum_replicate, Nat.add_assoc]
  have hNfm : (L.map Prod.snd).sum ≤ (L.map Prod.fst).sum :=
    snd_sum_le_fst_sum L (fun p hp => (hL p hp).2.2)
  have hprod : ma + mb ≤ ma * mb + 1 := by
    rcases Nat.exists_eq_add_of_le hma with ⟨a, rfl⟩
    rcases Nat.exists_eq_add_of_le hmb with ⟨b, rfl⟩
    nlinarith [Nat.zero_le (a * b)]
  omega

/-! ## Transport of the neighbourhood-induced subgraph

`G[Γx]` relabelled onto `Fin d` (`d = |Γx|`), preserving edge count and (from
`no_clique_r_in_nbhd`) `K_r`-freeness. The `(r−1)`-colourability of this transport
is the Case A/B discriminant. -/

/-- The induced subgraph on `Γx`, relabelled to `Fin |Γx|`: preserves the edge
count and (via `no_clique_r_in_nbhd`) is `K_r`-free. -/
theorem exists_induced_on_nbhd {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n) {r : ℕ}
    (hr : 1 ≤ r) (hCF : G.CliqueFree (r + 1)) :
    ∃ X : SimpleGraph (Fin (G.neighborFinset x).card),
      edgeCountIn X Finset.univ = edgeCountIn G (G.neighborFinset x) ∧ X.CliqueFree r := by
  obtain ⟨f, hf⟩ := exists_embedding_image_eq (G.neighborFinset x) rfl
  refine ⟨G.comap f, ?_, ?_⟩
  · rw [edgeCountIn_comap G f Finset.univ, hf]
  intro K hK
  obtain ⟨hclq, hcard⟩ := hK
  have hSsub : K.image f ⊆ G.neighborFinset x := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨a, _, rfl⟩ := hy
    have hmem : f a ∈ Finset.univ.image f := Finset.mem_image_of_mem f (Finset.mem_univ a)
    rwa [hf] at hmem
  have hSclq : G.IsClique ↑(K.image f) := by
    intro u hu v hv huv
    rw [Finset.mem_coe, Finset.mem_image] at hu hv
    obtain ⟨a, ha, rfl⟩ := hu
    obtain ⟨b, hb, rfl⟩ := hv
    have hab : a ≠ b := fun h => huv (by rw [h])
    have hcc := hclq (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab
    rwa [SimpleGraph.comap_adj] at hcc
  have hScard : (K.image f).card = r := by
    rw [Finset.card_image_of_injective _ f.injective, hcard]
  have hle := no_clique_r_in_nbhd hCF (K.image f) hSsub hSclq
  omega

/-- **Sub-lemma A (partition transport, F6o).** If `G.comap f` is `k`-colourable
(`f : Fin d ↪ Fin n`), then `G` restricted to the image of `f` has a proper `k`-colouring
`κ : Fin n → ℕ` (colours `< k`). The parts `Dᵢ = (image f).filter (κ · = i)` are then
independent in `G` (same colour ⇒ non-adjacent, the contrapositive of the second clause).
`ℕ`-valued to dodge `Fin k` emptiness when `d = 0`. This is the Case-B discriminant's
usable output: `X.Colorable (r−1)` with `X = G.comap f` (from `exists_induced_on_nbhd`'s
embedding) gives the `(r−1)`-partition `D = ⊍ Dᵢ` of `Γx`. -/
theorem colorable_restrict_of_comap {n d k : ℕ} (G : SimpleGraph (Fin n)) (f : Fin d ↪ Fin n)
    (h : (G.comap f).Colorable k) :
    ∃ κ : Fin n → ℕ, (∀ u ∈ Finset.univ.image f, κ u < k) ∧
      (∀ u ∈ Finset.univ.image f, ∀ v ∈ Finset.univ.image f, G.Adj u v → κ u ≠ κ v) := by
  obtain ⟨φ⟩ := h
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    exact ⟨fun _ => 0, fun u hu => absurd hu (by simp), fun u hu => absurd hu (by simp)⟩
  · haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    refine ⟨fun v => (φ (Function.invFun f v)).val, ?_, ?_⟩
    · intro u _; exact (φ _).isLt
    · intro u hu v hv hadj
      rw [Finset.mem_image] at hu hv
      obtain ⟨a, _, rfl⟩ := hu
      obtain ⟨b, _, rfl⟩ := hv
      show (φ (Function.invFun f (f a))).val ≠ (φ (Function.invFun f (f b))).val
      rw [Function.leftInverse_invFun f.injective a, Function.leftInverse_invFun f.injective b]
      have hne : φ a ≠ φ b := φ.valid (by rw [SimpleGraph.comap_adj]; exact hadj)
      exact fun heq => hne (Fin.val_injective heq)

/-! ## The MAIN degree inequality (F6p) — workhorse for the good/bad split

`2·e(G) + Σ_{v∈D} defc(v) ≤ 2·σ₂(blocks)` where `blocks = (d₀,…,d_{q−1}, c)` are the
`(r−1)` colour-part sizes plus `c = |C| = n−d`, and `defc(v) = n − |D_{κv}| − d_G(v)` is
`v`'s deficiency outside its own part. The ONLY inequality used is the max-degree bound on
`C` (`Σ_{v∈C} d_G(v) ≤ c·d`); everything else is exact. The good/bad analysis lower-bounds
`Σ defc` (≥ 2·min-block from ≥2 bad parts) and closes via `two_bad_list`. -/

/-- Sum of squares of a list (recursive; `= Σ aᵢ²`). -/
def sqsum : List ℕ → ℕ
  | [] => 0
  | a :: L => a * a + sqsum L

@[simp] theorem sqsum_nil : sqsum [] = 0 := rfl
@[simp] theorem sqsum_cons (a : ℕ) (L : List ℕ) : sqsum (a :: L) = a * a + sqsum L := rfl

/-- Bridge to the `(·^2)`-map form used by `two_mul_sig2`. -/
theorem sqsum_eq_pow (L : List ℕ) : sqsum L = (L.map (· ^ 2)).sum := by
  induction L with
  | nil => simp
  | cons a L IH => simp only [sqsum_cons, List.map_cons, List.sum_cons, IH, pow_two]

/-- `sqsum` of `ofFn f` is `∑ i, f i * f i`. -/
theorem sqsum_ofFn {q : ℕ} (f : Fin q → ℕ) : sqsum (List.ofFn f) = ∑ i, f i * f i := by
  rw [sqsum_eq_pow, List.map_ofFn, List.sum_ofFn]; simp [pow_two]

/-- `sqsum` splits over append. -/
theorem sqsum_append (L L' : List ℕ) : sqsum (L ++ L') = sqsum L + sqsum L' := by
  induction L with
  | nil => simp
  | cons a L IH => simp only [List.cons_append, sqsum_cons, IH]; ring

section MainIneq
variable {n : ℕ}

/-- **Max-degree bound (INEQ-1).** With `x` of max degree, `D = Γx`, `C = univ∖D`,
`d = |D|`, `c = |C|`: `2·e(G) ≤ (∑_{v∈D} d_G(v)) + c·d`. Only inequality used: every
`C`-vertex has degree `≤ d_G(x) = d`. -/
theorem two_edge_le_sum_degree_add (G : SimpleGraph (Fin n)) (x : Fin n)
    (hmax : ∀ y, G.degree y ≤ G.degree x) :
    2 * edgeCountIn G Finset.univ
      ≤ (∑ v ∈ G.neighborFinset x, G.degree v)
        + (n - (G.neighborFinset x).card) * (G.neighborFinset x).card := by
  set D := G.neighborFinset x with hD
  set d := D.card with hd
  have hdeg_x : G.degree x = d := by rw [hd, hD, G.card_neighborFinset_eq_degree]
  have htwice : 2 * edgeCountIn G Finset.univ = ∑ v, G.degree v := by
    rw [edgeCountIn_univ_eq_card_edgeFinset, ← G.sum_degrees_eq_twice_card_edges]
  rw [htwice]
  have hsplit : ∑ v, G.degree v
      = (∑ v ∈ D, G.degree v) + (∑ v ∈ Finset.univ \ D, G.degree v) := by
    rw [← Finset.sum_add_sum_compl D (fun v => G.degree v), Finset.compl_eq_univ_sdiff]
  rw [hsplit]
  have hCcard : (Finset.univ \ D).card = n - d := by
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin]
  have hCbound : (∑ v ∈ Finset.univ \ D, G.degree v) ≤ (n - d) * d := by
    calc (∑ v ∈ Finset.univ \ D, G.degree v)
        ≤ ∑ _v ∈ Finset.univ \ D, d := by
          apply Finset.sum_le_sum
          intro v _
          rw [← hdeg_x]; exact hmax v
      _ = (n - d) * d := by rw [Finset.sum_const, hCcard, smul_eq_mul]
  omega

/-- For `v ∈ D`, if `v`'s colour part `Dᵢ = {u∈D : κu = κv}` is `G`-independent,
then `d_G(v) ≤ n − |Dᵢ|` (all of `v`'s neighbours avoid `Dᵢ`). -/
theorem degree_le_of_part (G : SimpleGraph (Fin n)) {q : ℕ} (κ : Fin n → Fin q)
    (D : Finset (Fin n)) (hDindep : ∀ i : Fin q, ∀ u ∈ D.filter (κ · = i),
      ∀ w ∈ D.filter (κ · = i), ¬ G.Adj u w)
    {v : Fin n} (hv : v ∈ D) :
    G.degree v ≤ n - (D.filter (κ · = κ v)).card := by
  set Di := D.filter (κ · = κ v) with hDi
  have hvDi : v ∈ Di := by rw [hDi, Finset.mem_filter]; exact ⟨hv, rfl⟩
  have hnb : G.neighborFinset v ⊆ Finset.univ \ Di := by
    intro w hw
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hwDi
    rw [SimpleGraph.mem_neighborFinset] at hw
    exact hDindep (κ v) w hwDi v hvDi (hw.symm)
  calc G.degree v = (G.neighborFinset v).card := (G.card_neighborFinset_eq_degree v).symm
    _ ≤ (Finset.univ \ Di).card := Finset.card_le_card hnb
    _ = n - Di.card := by
        rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin]

/-- **The MAIN degree inequality.** With `x` of max degree, `D = Γx`, `κ` a proper
`Fin q`-colouring of `G[D]` (partition `Dᵢ = {u∈D : κu=i}`), and blocks
`(d₀,…,d_{q−1}, c)` (`c = |C| = n−d`): `2·e(G) + Σ_{v∈D} defc(v) ≤ 2·σ₂(blocks)`,
where `defc(v) = n − |D_{κv}| − d_G(v)` is `v`'s deficiency outside its part. -/
theorem main_ineq (G : SimpleGraph (Fin n)) (x : Fin n) {q : ℕ}
    (hmax : ∀ y, G.degree y ≤ G.degree x) (κ : Fin n → Fin q)
    (hDindep : ∀ i : Fin q, ∀ u ∈ (G.neighborFinset x).filter (κ · = i),
      ∀ w ∈ (G.neighborFinset x).filter (κ · = i), ¬ G.Adj u w) :
    2 * edgeCountIn G Finset.univ
        + (∑ v ∈ G.neighborFinset x,
            (n - ((G.neighborFinset x).filter (κ · = κ v)).card - G.degree v))
      ≤ 2 * sig2 ((List.ofFn fun i : Fin q => ((G.neighborFinset x).filter (κ · = i)).card)
          ++ [n - (G.neighborFinset x).card]) := by
  set D := G.neighborFinset x with hD
  set d := D.card with hd
  set c := n - d with hc
  set psz : Fin q → ℕ := fun i => (D.filter (κ · = i)).card with hpsz
  set blocks := (List.ofFn psz) ++ [c] with hblocks
  have hdn : d ≤ n := by
    rw [hd, hD]
    calc (G.neighborFinset x).card ≤ (Finset.univ : Finset (Fin n)).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = n := by rw [Finset.card_univ, Fintype.card_fin]
  have hpart_card : ∑ i, psz i = d := by
    rw [hpsz, hd]
    exact (Finset.card_eq_sum_card_fiberwise (fun v _ => Finset.mem_univ (κ v))).symm
  have hblock_sum : blocks.sum = n := by
    rw [hblocks, List.sum_append, List.sum_ofFn, List.sum_cons, List.sum_nil, hpart_card]
    omega
  have hsqblocks : sqsum blocks = (∑ i, psz i * psz i) + c * c := by
    rw [hblocks, sqsum_append, sqsum_ofFn]
    simp [sqsum]
  have hsig : 2 * sig2 blocks + sqsum blocks = n ^ 2 := by
    have h := two_mul_sig2 blocks
    rw [← sqsum_eq_pow, hblock_sum] at h; exact h
  have hfiber : (∑ v ∈ D, psz (κ v)) = ∑ i, psz i * psz i := by
    rw [← Finset.sum_fiberwise D κ (fun v => psz (κ v))]
    apply Finset.sum_congr rfl
    intro i _
    have hcong : ∀ v ∈ D.filter (κ · = i), psz (κ v) = psz i := by
      intro v hv; rw [(Finset.mem_filter.mp hv).2]
    rw [Finset.sum_congr rfl hcong, Finset.sum_const, smul_eq_mul]
  have hsumid : (∑ v ∈ D, G.degree v) + (∑ v ∈ D, psz (κ v))
      + (∑ v ∈ D, (n - psz (κ v) - G.degree v)) = d * n := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    rw [show d * n = ∑ _v ∈ D, n by rw [Finset.sum_const, hd, smul_eq_mul]]
    apply Finset.sum_congr rfl
    intro v hv
    have hle : G.degree v ≤ n - psz (κ v) := degree_le_of_part G κ D hDindep hv
    have hle2 : psz (κ v) ≤ n :=
      le_trans (Finset.card_le_card (Finset.filter_subset _ _)) hdn
    omega
  have hineq1 := two_edge_le_sum_degree_add G x hmax
  rw [← hD, ← hd, ← hc] at hineq1
  rw [hfiber] at hsumid
  have hcd : c + d = n := by rw [hc]; omega
  nlinarith [hsig, hsqblocks, hsumid, hineq1, hcd, hfiber]

end MainIneq

/-- A nonempty list of naturals has a minimum element (in the list, ≤ all). -/
theorem list_has_min (L : List ℕ) (h : L ≠ []) : ∃ m ∈ L, ∀ y ∈ L, m ≤ y := by
  have hne : L.toFinset.Nonempty := by rw [List.toFinset_nonempty_iff]; exact h
  refine ⟨L.toFinset.min' hne, List.mem_toFinset.mp (L.toFinset.min'_mem hne), ?_⟩
  intro y hy
  exact L.toFinset.min'_le y (List.mem_toFinset.mpr hy)

section CaseBClose
variable {n r : ℕ}

/-- **Case-B closer (F6q).** Given the `(r−1)`-partition `κ`, all parts `≥ 2`, `c ≥ 2`,
and a block-minimum `m` (a block, `≤` every block), together with `Σ defc ≥ 2m`, the goal
`e(G) + kpSaving ≤ t_r` follows from `main_ineq` + `two_bad_list`. The good/bad analysis
supplies `m` (`= min block`) and `Σ defc ≥ 2m` (from ≥ 2 bad parts, or one bad part with
every vertex missing ≥ 2). -/
theorem caseB_close (hr : 2 ≤ r) (G : SimpleGraph (Fin n)) (x : Fin n)
    (hmax : ∀ y, G.degree y ≤ G.degree x) (κ : Fin n → Fin (r - 1))
    (hDindep : ∀ i : Fin (r - 1), ∀ u ∈ (G.neighborFinset x).filter (κ · = i),
      ∀ w ∈ (G.neighborFinset x).filter (κ · = i), ¬ G.Adj u w)
    (h2part : ∀ i : Fin (r - 1), 2 ≤ ((G.neighborFinset x).filter (κ · = i)).card)
    (hc2 : 2 ≤ n - (G.neighborFinset x).card)
    (m : ℕ)
    (hmle_part : ∀ i : Fin (r - 1), m ≤ ((G.neighborFinset x).filter (κ · = i)).card)
    (hmle_c : m ≤ n - (G.neighborFinset x).card)
    (hm_mem : (∃ i : Fin (r - 1), ((G.neighborFinset x).filter (κ · = i)).card = m)
              ∨ n - (G.neighborFinset x).card = m)
    (hdef : 2 * m ≤ ∑ v ∈ G.neighborFinset x,
              (n - ((G.neighborFinset x).filter (κ · = κ v)).card - G.degree v)) :
    edgeCountIn G Finset.univ + kpSaving n r ≤ (turanGraph n r).edgeFinset.card := by
  have hmain := main_ineq G x hmax κ hDindep
  set D := G.neighborFinset x with hD
  set L := (List.ofFn fun i : Fin (r - 1) => (D.filter (κ · = i)).card) ++ [n - D.card] with hL
  have hDn : D.card ≤ n := by
    calc D.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = n := by rw [Finset.card_univ, Fintype.card_fin]
  have hlen : L.length = r := by
    rw [hL, List.length_append, List.length_ofFn, List.length_singleton]; omega
  have hsum : L.sum = n := by
    rw [hL, List.sum_append, List.sum_ofFn, List.sum_cons, List.sum_nil]
    have hpc : ∑ i, (D.filter (κ · = i)).card = D.card :=
      (Finset.card_eq_sum_card_fiberwise (fun v _ => Finset.mem_univ (κ v))).symm
    rw [hpc]; exact Nat.add_sub_cancel' hDn
  have h2blocks : ∀ y ∈ L, 2 ≤ y := by
    intro y hy; rw [hL, List.mem_append] at hy
    rcases hy with h | h
    · rw [List.mem_ofFn] at h; obtain ⟨i, rfl⟩ := h; exact h2part i
    · rw [List.mem_singleton] at h; rw [h]; exact hc2
  have hmmem : m ∈ L := by
    rcases hm_mem with ⟨i, hi⟩ | hi
    · rw [hL, List.mem_append]; left; rw [List.mem_ofFn]; exact ⟨i, hi⟩
    · rw [hL, List.mem_append]; right; rw [List.mem_singleton]; exact hi.symm
  have hmle : ∀ y ∈ L, m ≤ y := by
    intro y hy; rw [hL, List.mem_append] at hy
    rcases hy with h | h
    · rw [List.mem_ofFn] at h; obtain ⟨i, rfl⟩ := h; exact hmle_part i
    · rw [List.mem_singleton] at h; rw [h]; exact hmle_c
  have htb := two_bad_list L h2blocks m hmmem hmle
  rw [hsum, hlen] at htb
  omega

end CaseBClose


section CaseBGoodBad
variable {n r : ℕ}

/-- **K_{r+1} from a clique + a cross edge.** An `(r−1)`-clique `K` (in `G`), plus two
vertices `a ≠ b` outside `K` each adjacent to all of `K` and to each other, spans `K_{r+1}`
— contradicting `K_{r+1}`-freeness. -/
theorem no_Kr_plus_edge (G : SimpleGraph (Fin n)) (hr : 1 ≤ r)
    (hCF : G.CliqueFree (r + 1))
    (K : Finset (Fin n)) (hKclq : G.IsClique ↑K) (hKcard : K.card = r - 1)
    (a b : Fin n) (ha : a ∉ K) (hb : b ∉ K) (hab : a ≠ b)
    (haK : ∀ w ∈ K, G.Adj a w) (hbK : ∀ w ∈ K, G.Adj b w) (hadjab : G.Adj a b) :
    False := by
  have hbK' : b ∉ K := hb
  have hcard : (insert a (insert b K)).card = r + 1 := by
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert]; push_neg; exact ⟨hab, ha⟩),
      Finset.card_insert_of_notMem hbK', hKcard]
    omega
  have hclq : G.IsClique ↑(insert a (insert b K)) := by
    intro u hu v hv huv
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hu hv
    rcases hu with rfl | rfl | hu <;> rcases hv with rfl | rfl | hv
    · exact absurd rfl huv
    · exact hadjab
    · exact haK v hv
    · exact hadjab.symm
    · exact absurd rfl huv
    · exact hbK v hv
    · exact (haK u hu).symm
    · exact (hbK u hu).symm
    · exact hKclq (Finset.mem_coe.mpr hu) (Finset.mem_coe.mpr hv) huv
  exact hCF (insert a (insert b K)) ⟨hclq, hcard⟩

/-- **r-colouring when `C` is independent.** If `C = univ∖Γx` is `G`-independent, then the
`(r−1)`-partition `κ` of `Γx` plus a fresh colour on `C` is a proper `r`-colouring of `G`. -/
theorem colorable_of_C_indep (hr : 2 ≤ r) (G : SimpleGraph (Fin n)) (x : Fin n)
    (κ : Fin n → Fin (r - 1))
    (hproper : ∀ u ∈ G.neighborFinset x, ∀ v ∈ G.neighborFinset x, G.Adj u v → κ u ≠ κ v)
    (hCindep : ∀ u, u ∉ G.neighborFinset x → ∀ v, v ∉ G.neighborFinset x → ¬ G.Adj u v) :
    G.Colorable r := by
  set D := G.neighborFinset x with hD
  refine ⟨SimpleGraph.Coloring.mk
    (fun v => if v ∈ D then (⟨(κ v).val, by omega⟩ : Fin r) else (⟨r - 1, by omega⟩ : Fin r)) ?_⟩
  intro u v hadj
  simp only []
  by_cases hu : u ∈ D <;> by_cases hv : v ∈ D
  · rw [if_pos hu, if_pos hv]
    intro heq
    rw [Fin.mk.injEq] at heq
    exact hproper u hu v hv hadj (Fin.ext heq)
  · rw [if_pos hu, if_neg hv]
    intro heq
    rw [Fin.mk.injEq] at heq
    have h1 : (κ u).val < r - 1 := (κ u).isLt
    omega
  · rw [if_neg hu, if_pos hv]
    intro heq
    rw [Fin.mk.injEq] at heq
    have h1 : (κ v).val < r - 1 := (κ v).isLt
    omega
  · exact absurd hadj (hCindep u hu v hv)

/-- **Good-witness adjacency.** A part vertex `y ∈ Dᵢ` with full degree `n − |Dᵢ|`
(deficiency 0) is adjacent in `G` to every vertex outside `Dᵢ`. -/
theorem good_witness_adj (G : SimpleGraph (Fin n)) (x : Fin n) {q : ℕ} (κ : Fin n → Fin q)
    (hDindep : ∀ i : Fin q, ∀ u ∈ (G.neighborFinset x).filter (κ · = i),
      ∀ w ∈ (G.neighborFinset x).filter (κ · = i), ¬ G.Adj u w)
    (i : Fin q) (y : Fin n) (hy : y ∈ (G.neighborFinset x).filter (κ · = i))
    (hdeg : G.degree y = n - ((G.neighborFinset x).filter (κ · = i)).card)
    (w : Fin n) (hw : w ∉ (G.neighborFinset x).filter (κ · = i)) :
    G.Adj y w := by
  set Di := (G.neighborFinset x).filter (κ · = i) with hDi
  have hsub : G.neighborFinset y ⊆ Finset.univ \ Di := by
    intro z hz
    rw [Finset.mem_sdiff]; refine ⟨Finset.mem_univ _, ?_⟩
    intro hzi
    rw [SimpleGraph.mem_neighborFinset] at hz
    exact hDindep i z hzi y hy hz.symm
  have hcardeq : (G.neighborFinset y).card = (Finset.univ \ Di).card := by
    rw [G.card_neighborFinset_eq_degree, hdeg, ← Finset.compl_eq_univ_sdiff, Finset.card_compl,
      Fintype.card_fin]
  have heq : G.neighborFinset y = Finset.univ \ Di :=
    Finset.eq_of_subset_of_card_le hsub (le_of_eq hcardeq.symm)
  have hwin : w ∈ G.neighborFinset y := by rw [heq, Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, hw⟩
  rwa [SimpleGraph.mem_neighborFinset] at hwin

/-! ## KP Lemma 3, inequality (5): the transversal-counting core (sub-lemma F STEP 6)

`Σ_{i<j} ē_ij ≥ m₁ m₂` (`missing_edges_ge`), abstracted away from the graph: `M i` are the
`Mᵢ` sets, `Adj` the adjacency, `hbad` the `K_{r+1}`-freeness consequence (no
rainbow-clique transversal). This is "the single hardest step" of Lemma 3; the remaining
STEPs 1–5,7 (class extraction, `Y`-clique, `Mᵢ≠∅`, `l≤r−2`, edge accounting, feeding
`lemma3_arith`) are the structural bookkeeping around it. -/

/-- **Fiber bound.** The transversals `t ∈ ∏ Mₕ` with `t i = u`, `t j = v` number at most
`∏_{h ≠ i,j} |M h|` (the other coordinates are free; coords `i,j` are pinned). -/
theorem fiber_card_le {n k : ℕ} (M : Fin k → Finset (Fin n)) {i j : Fin k} (hij : i ≠ j)
    (u v : Fin n) :
    ((Fintype.piFinset M).filter (fun t => t i = u ∧ t j = v)).card
      ≤ ∏ h ∈ (Finset.univ.erase i).erase j, (M h).card := by
  classical
  set M' : Fin k → Finset (Fin n) :=
    fun h => if h = i then {u} else if h = j then {v} else M h with hM'
  have hsub : (Fintype.piFinset M).filter (fun t => t i = u ∧ t j = v) ⊆ Fintype.piFinset M' := by
    intro t ht
    rw [Finset.mem_filter, Fintype.mem_piFinset] at ht
    obtain ⟨hmem, hti, htj⟩ := ht
    rw [Fintype.mem_piFinset]
    intro h
    rw [hM']
    by_cases hi : h = i
    · subst hi; simp [hti]
    · by_cases hj : h = j
      · subst hj; simp [hi, htj]
      · simp [hi, hj]; exact hmem h
  have hM'i : (M' i).card = 1 := by rw [hM']; simp
  have hM'j : (M' j).card = 1 := by rw [hM']; simp [Ne.symm hij]
  have hM'h : ∀ h ∈ (Finset.univ.erase i).erase j, (M' h).card = (M h).card := by
    intro h hh
    rw [Finset.mem_erase, Finset.mem_erase] at hh
    rw [hM']; simp [hh.1, hh.2.1]
  calc ((Fintype.piFinset M).filter (fun t => t i = u ∧ t j = v)).card
      ≤ (Fintype.piFinset M').card := Finset.card_le_card hsub
    _ = ∏ h, (M' h).card := Fintype.card_piFinset M'
    _ = ∏ h ∈ (Finset.univ.erase i).erase j, (M h).card := by
        rw [← Finset.mul_prod_erase Finset.univ (fun h => (M' h).card) (Finset.mem_univ i)]
        rw [← Finset.mul_prod_erase (Finset.univ.erase i) (fun h => (M' h).card)
          (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)]
        rw [hM'i, hM'j, one_mul, one_mul]
        exact Finset.prod_congr rfl hM'h

/-- **(5) — transversal covering.** `∏ mᵢ ≤ Σ_{i<j} ē_ij · ∏_{h≠i,j} mₕ`. Every
transversal (one vertex per class) plus the clique `Y` would be `K_{r+1}` unless some
chosen pair is non-adjacent, so every transversal is "covered" by a missing `Mᵢ–Mⱼ`
edge; the fiber over each missing edge has `≤ ∏_{h≠i,j} mₕ` transversals. -/
theorem prod_le_sum_bad {n k : ℕ} (M : Fin k → Finset (Fin n))
    (Adj : Fin n → Fin n → Prop)
    (hbad : ∀ t ∈ Fintype.piFinset M, ∃ i j, i < j ∧ ¬ Adj (t i) (t j)) :
    (∏ i, (M i).card)
      ≤ ∑ p ∈ (Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2)),
          ((M p.1 ×ˢ M p.2).filter (fun uv => ¬ Adj uv.1 uv.2)).card
            * ∏ h ∈ (Finset.univ.erase p.1).erase p.2, (M h).card := by
  classical
  set P := Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2) with hP
  set BP : Fin k × Fin k → Finset (Fin n × Fin n) :=
    fun p => (M p.1 ×ˢ M p.2).filter (fun uv => ¬ Adj uv.1 uv.2) with hBP
  set fib : (Fin k × Fin k) → (Fin n × Fin n) → Finset (Fin k → Fin n) :=
    fun p uv => (Fintype.piFinset M).filter (fun t => t p.1 = uv.1 ∧ t p.2 = uv.2) with hfib
  have hcover : Fintype.piFinset M ⊆ P.biUnion (fun p => (BP p).biUnion (fun uv => fib p uv)) := by
    intro t ht
    obtain ⟨i, j, hij, hnadj⟩ := hbad t ht
    rw [Finset.mem_biUnion]
    refine ⟨(i, j), by rw [hP, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hij⟩, ?_⟩
    rw [Finset.mem_biUnion]
    rw [Fintype.mem_piFinset] at ht
    refine ⟨(t i, t j), ?_, by rw [hfib, Finset.mem_filter]; exact ⟨Fintype.mem_piFinset.mpr ht, rfl, rfl⟩⟩
    rw [hBP, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨ht i, ht j⟩, hnadj⟩
  calc (∏ i, (M i).card) = (Fintype.piFinset M).card := (Fintype.card_piFinset M).symm
    _ ≤ (P.biUnion (fun p => (BP p).biUnion (fun uv => fib p uv))).card :=
        Finset.card_le_card hcover
    _ ≤ ∑ p ∈ P, ((BP p).biUnion (fun uv => fib p uv)).card := Finset.card_biUnion_le
    _ ≤ ∑ p ∈ P, ∑ uv ∈ BP p, (fib p uv).card :=
        Finset.sum_le_sum (fun p _ => Finset.card_biUnion_le)
    _ ≤ ∑ p ∈ P, ∑ _uv ∈ BP p, ∏ h ∈ (Finset.univ.erase p.1).erase p.2, (M h).card :=
        Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun uv _ => by
          have hne : p.1 ≠ p.2 := by
            rw [hP, Finset.mem_filter] at hp; exact ne_of_lt hp.2
          exact fiber_card_le M hne uv.1 uv.2))
    _ = ∑ p ∈ P, ((M p.1 ×ˢ M p.2).filter (fun uv => ¬ Adj uv.1 uv.2)).card
          * ∏ h ∈ (Finset.univ.erase p.1).erase p.2, (M h).card := by
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.sum_const, smul_eq_mul, hBP]

/-- **KP Lemma 3, inequality (5).** With the two smallest classes `M ia, M ib`
(`|M ia| ≤ |M i|` all `i`; `|M ib| ≤ |M i|` for `i ≠ ia`), the total number of missing
`Mᵢ–Mⱼ` edges is at least `|M ia|·|M ib| = m₁ m₂`. From `prod_le_sum_bad` by cancelling
the common product `∏_{h≠ia,ib} mₕ`. -/
theorem missing_edges_ge {n k : ℕ} (M : Fin k → Finset (Fin n))
    (hMne : ∀ i, (M i).Nonempty)
    (Adj : Fin n → Fin n → Prop)
    (hbad : ∀ t ∈ Fintype.piFinset M, ∃ i j, i < j ∧ ¬ Adj (t i) (t j))
    (ia ib : Fin k) (hiab : ia ≠ ib)
    (hmin_a : ∀ i, (M ia).card ≤ (M i).card)
    (hmin_b : ∀ i, i ≠ ia → (M ib).card ≤ (M i).card) :
    (M ia).card * (M ib).card
      ≤ ∑ p ∈ (Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2)),
          ((M p.1 ×ˢ M p.2).filter (fun uv => ¬ Adj uv.1 uv.2)).card := by
  classical
  set m : Fin k → ℕ := fun h => (M h).card with hm
  set P := Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2) with hP
  have hmpos : ∀ h, 0 < m h := fun h => Finset.card_pos.mpr (hMne h)
  set Q := ∏ h ∈ (Finset.univ.erase ia).erase ib, m h with hQ
  have hQpos : 0 < Q := Finset.prod_pos (fun h _ => hmpos h)
  have habpos : 0 < m ia * m ib := Nat.mul_pos (hmpos ia) (hmpos ib)
  have hall : (∏ i, m i) = m ia * m ib * Q := by
    rw [← Finset.mul_prod_erase Finset.univ m (Finset.mem_univ ia),
        ← Finset.mul_prod_erase (Finset.univ.erase ia) m
          (Finset.mem_erase.mpr ⟨Ne.symm hiab, Finset.mem_univ ib⟩), hQ]
    ring
  have hpp : ∀ p ∈ P, m ia * m ib ≤ m p.1 * m p.2 := by
    intro p hp
    rw [hP, Finset.mem_filter] at hp
    have hp12 : p.1 ≠ p.2 := ne_of_lt hp.2
    by_cases h1 : p.1 = ia
    · have h2 : p.2 ≠ ia := by rw [h1] at hp12; exact fun h => hp12 h.symm
      rw [h1]; exact Nat.mul_le_mul_left _ (hmin_b p.2 h2)
    · by_cases h2 : p.2 = ia
      · rw [h2, Nat.mul_comm (m p.1)]; exact Nat.mul_le_mul_left _ (hmin_b p.1 h1)
      · exact Nat.mul_le_mul (le_trans (hmin_a ib) (hmin_b p.1 h1)) (hmin_b p.2 h2)
  have hpQ : ∀ p ∈ P, (∏ h ∈ (Finset.univ.erase p.1).erase p.2, m h) ≤ Q := by
    intro p hp
    have hp12 : p.1 ≠ p.2 := by rw [hP, Finset.mem_filter] at hp; exact ne_of_lt hp.2
    have hall_p : (∏ i, m i)
        = m p.1 * m p.2 * (∏ h ∈ (Finset.univ.erase p.1).erase p.2, m h) := by
      rw [← Finset.mul_prod_erase Finset.univ m (Finset.mem_univ p.1),
          ← Finset.mul_prod_erase (Finset.univ.erase p.1) m
            (Finset.mem_erase.mpr ⟨Ne.symm hp12, Finset.mem_univ p.2⟩)]
      ring
    have hkey : m ia * m ib * (∏ h ∈ (Finset.univ.erase p.1).erase p.2, m h)
        ≤ m ia * m ib * Q := by
      calc m ia * m ib * (∏ h ∈ (Finset.univ.erase p.1).erase p.2, m h)
          ≤ m p.1 * m p.2 * (∏ h ∈ (Finset.univ.erase p.1).erase p.2, m h) :=
            Nat.mul_le_mul_right _ (hpp p hp)
        _ = ∏ i, m i := hall_p.symm
        _ = m ia * m ib * Q := hall
    exact Nat.le_of_mul_le_mul_left hkey habpos
  have hchain : m ia * m ib * Q
      ≤ (∑ p ∈ P, ((M p.1 ×ˢ M p.2).filter (fun uv => ¬ Adj uv.1 uv.2)).card) * Q := by
    calc m ia * m ib * Q = ∏ i, m i := hall.symm
      _ ≤ ∑ p ∈ P, ((M p.1 ×ˢ M p.2).filter (fun uv => ¬ Adj uv.1 uv.2)).card
            * ∏ h ∈ (Finset.univ.erase p.1).erase p.2, m h := prod_le_sum_bad M Adj hbad
      _ ≤ ∑ p ∈ P, ((M p.1 ×ˢ M p.2).filter (fun uv => ¬ Adj uv.1 uv.2)).card * Q :=
          Finset.sum_le_sum (fun p hp => Nat.mul_le_mul_left _ (hpQ p hp))
      _ = (∑ p ∈ P, ((M p.1 ×ˢ M p.2).filter (fun uv => ¬ Adj uv.1 uv.2)).card) * Q := by
          rw [Finset.sum_mul]
  exact Nat.le_of_mul_le_mul_right hchain hQpos

/-- **The `hbad` bridge (STEP 6 input).** If `Y` is a `G`-clique of size `l+1`, the classes
`M i` (`k` of them) are pairwise disjoint and disjoint from `Y`, every `Mᵢ`-vertex is
`G`-adjacent to all of `Y`, and `k + l + 1 = r + 1`, then `G.CliqueFree (r+1)` forces: every
transversal picks a non-adjacent pair (else `Y ∪ image t` is a `K_{r+1}`). Supplies
`missing_edges_ge`'s `hbad`. -/
theorem transversal_has_bad_pair {n r k l : ℕ} (G : SimpleGraph (Fin n))
    (hCF : G.CliqueFree (r + 1))
    (Y : Finset (Fin n)) (hYclq : G.IsClique ↑Y) (hYcard : Y.card = l + 1)
    (hklr : k + l + 1 = r + 1)
    (M : Fin k → Finset (Fin n))
    (hMdisj : ∀ i j, i ≠ j → Disjoint (M i) (M j))
    (hMY : ∀ i, ∀ u ∈ M i, u ∉ Y)
    (hMadj : ∀ i, ∀ u ∈ M i, ∀ y ∈ Y, G.Adj u y) :
    ∀ t ∈ Fintype.piFinset M, ∃ i j, i < j ∧ ¬ G.Adj (t i) (t j) := by
  intro t ht
  rw [Fintype.mem_piFinset] at ht
  by_contra hcon
  push_neg at hcon
  have htinj : Function.Injective t := by
    intro i j hij
    by_contra hne
    have h1 : t i ∈ M j := hij ▸ ht j
    exact Finset.disjoint_left.mp (hMdisj i j hne) (ht i) h1
  set S := Y ∪ (Finset.univ.image t) with hS
  have hdisjYt : Disjoint Y (Finset.univ.image t) := by
    rw [Finset.disjoint_left]
    intro y hyY hyt
    rw [Finset.mem_image] at hyt
    obtain ⟨i, _, rfl⟩ := hyt
    exact hMY i (t i) (ht i) hyY
  have himgcard : (Finset.univ.image t).card = k := by
    rw [Finset.card_image_of_injective _ htinj, Finset.card_univ, Fintype.card_fin]
  have hScard : S.card = r + 1 := by
    rw [hS, Finset.card_union_of_disjoint hdisjYt, hYcard, himgcard]; omega
  have hSclq : G.IsClique ↑S := by
    intro a ha b hb hab
    rw [Finset.mem_coe, hS, Finset.mem_union, Finset.mem_image] at ha hb
    rcases ha with haY | ⟨i, _, rfl⟩ <;> rcases hb with hbY | ⟨j, _, rfl⟩
    · exact hYclq (Finset.mem_coe.mpr haY) (Finset.mem_coe.mpr hbY) hab
    · exact (hMadj j (t j) (ht j) a haY).symm
    · exact hMadj i (t i) (ht i) b hbY
    · have hijne : i ≠ j := fun h => hab (by rw [h])
      rcases lt_or_gt_of_ne hijne with hlt | hgt
      · exact hcon i j hlt
      · exact (hcon j i hgt).symm
  exact hCF S ⟨hSclq, hScard⟩

set_option maxHeartbeats 4000000 in

theorem sqsum_replicate_one (l : ℕ) : sqsum (List.replicate l 1) = l := by
  induction l with
  | zero => simp [sqsum]
  | succ m ih => rw [List.replicate_succ, sqsum_cons, ih]; ring

theorem sum_replicate_one (l : ℕ) : (List.replicate l (1 : ℕ)).sum = l := by
  induction l with
  | zero => simp
  | succ m ih => rw [List.replicate_succ, List.sum_cons, ih]; omega

/-- Recolour `z` with colour `c` (no `z`-neighbour has colour `c`), keeping `κ'` off `z`. -/
theorem recolor_z {n r : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n) (κ' : Fin n → Fin r)
    (hproper' : ∀ u v, u ≠ z → v ≠ z → G.Adj u v → κ' u ≠ κ' v)
    (c : Fin r) (hc : ∀ w, w ≠ z → G.Adj z w → κ' w ≠ c) : G.Colorable r := by
  refine ⟨SimpleGraph.Coloring.mk (fun v => if v = z then c else κ' v) ?_⟩
  intro u v hadj
  have huv : u ≠ v := G.ne_of_adj hadj
  simp only []
  by_cases hu : u = z
  · rw [if_pos hu]
    by_cases hv : v = z
    · exact absurd (hu.trans hv.symm) huv
    · rw [if_neg hv]; exact fun h => hc v hv (hu ▸ hadj) h.symm
  · rw [if_neg hu]
    by_cases hv : v = z
    · rw [if_pos hv]; exact hc u hu (hv ▸ hadj).symm
    · rw [if_neg hv]; exact hproper' u v hu hv hadj

/-- Merge recolour: recolour `b → i` and `z → j` (`i ≠ j`), keeping `κ'` elsewhere. -/
theorem recolor_zb {n r : ℕ} (G : SimpleGraph (Fin n)) (z b : Fin n) (κ' : Fin n → Fin r)
    (hproper' : ∀ u v, u ≠ z → v ≠ z → G.Adj u v → κ' u ≠ κ' v)
    (i j : Fin r) (hij : i ≠ j) (hbz : b ≠ z)
    (hbi : ∀ w, w ≠ b → w ≠ z → G.Adj b w → κ' w ≠ i)
    (hzj : ∀ w, w ≠ b → w ≠ z → G.Adj z w → κ' w ≠ j) : G.Colorable r := by
  refine ⟨SimpleGraph.Coloring.mk (fun v => if v = b then i else if v = z then j else κ' v) ?_⟩
  intro u v hadj
  have huv : u ≠ v := G.ne_of_adj hadj
  simp only []
  by_cases hub : u = b
  · rw [if_pos hub]
    by_cases hvb : v = b
    · exact absurd (hub.trans hvb.symm) huv
    · rw [if_neg hvb]
      by_cases hvz : v = z
      · rw [if_pos hvz]; exact hij
      · rw [if_neg hvz]; exact fun h => hbi v hvb hvz (hub ▸ hadj) h.symm
  · rw [if_neg hub]
    by_cases huz : u = z
    · rw [if_pos huz]
      by_cases hvb : v = b
      · rw [if_pos hvb]; exact fun h => hij h.symm
      · rw [if_neg hvb]
        by_cases hvz : v = z
        · exact absurd (huz.trans hvz.symm) huv
        · rw [if_neg hvz]; exact fun h => hzj v hvb hvz (huz ▸ hadj) h.symm
    · rw [if_neg huz]
      by_cases hvb : v = b
      · rw [if_pos hvb]; exact hbi u hub huz (hvb ▸ hadj).symm
      · rw [if_neg hvb]
        by_cases hvz : v = z
        · rw [if_pos hvz]; exact hzj u hub huz (hvz ▸ hadj).symm
        · rw [if_neg hvz]; exact hproper' u v huz hvz hadj

/-- STEP 7 finish: from the STEP 5+6 counting output (`hcount`), the class data over
`Fin k` (`k` big classes, `l` singletons, `l+k=r`), and the two smallest-`m` indices
`ia,ib`, conclude Lemma 3's bound. Pulls `ia,ib` to the front and applies `lemma3_arith`. -/
theorem kp_lemma3_finish {r n l k : ℕ} (hr : 2 ≤ r) (hk : 2 ≤ k) (hlk : l + k = r)
    (nn mm : Fin k → ℕ) (hnn : ∀ a, 2 ≤ nn a) (hmm1 : ∀ a, 1 ≤ mm a) (hmmn : ∀ a, mm a ≤ nn a)
    (ia ib : Fin k) (hiab : ia ≠ ib)
    (hn : n = 1 + l + ∑ a, nn a)
    (E : ℕ)
    (hcount : E + mm ia * mm ib ≤ sig2 (List.replicate l 1 ++ List.ofFn nn) + l + ∑ a, mm a) :
    E + kpSaving n r ≤ (turanGraph n r).edgeFinset.card := by
  classical
  set T : Finset (Fin k) := (univ.erase ia).erase ib with hT
  have hib_erase : ib ∈ univ.erase ia := Finset.mem_erase.mpr ⟨hiab.symm, Finset.mem_univ _⟩
  -- sum splits over Fin k = {ia, ib} ⊔ T
  have hsum_nn : ∑ a, nn a = nn ia + nn ib + ∑ a ∈ T, nn a := by
    rw [hT, ← Finset.add_sum_erase univ nn (Finset.mem_univ ia),
        ← Finset.add_sum_erase (univ.erase ia) nn hib_erase]; ring
  have hsum_mm : ∑ a, mm a = mm ia + mm ib + ∑ a ∈ T, mm a := by
    rw [hT, ← Finset.add_sum_erase univ mm (Finset.mem_univ ia),
        ← Finset.add_sum_erase (univ.erase ia) mm hib_erase]; ring
  have hsum_sq : ∑ a, nn a * nn a
      = nn ia * nn ia + nn ib * nn ib + ∑ a ∈ T, nn a * nn a := by
    have key : (∑ a, nn a * nn a) = nn ia * nn ia + ∑ a ∈ univ.erase ia, nn a * nn a :=
      (Finset.add_sum_erase univ (fun a => nn a * nn a) (Finset.mem_univ ia)).symm
    have key2 : (∑ a ∈ univ.erase ia, nn a * nn a)
        = nn ib * nn ib + ∑ a ∈ T, nn a * nn a := by
      rw [hT]; exact (Finset.add_sum_erase (univ.erase ia) (fun a => nn a * nn a) hib_erase).symm
    rw [key, key2, add_assoc]
  have hTcard : T.card = k - 2 := by
    rw [hT, Finset.card_erase_of_mem hib_erase, Finset.card_erase_of_mem (Finset.mem_univ ia),
      Finset.card_univ, Fintype.card_fin]; omega
  -- residual list L of (nn, mm) pairs over T
  set L : List (ℕ × ℕ) := T.toList.map (fun a => (nn a, mm a)) with hL
  have hLfst : (L.map Prod.fst).sum = ∑ a ∈ T, nn a := by
    rw [hL, List.map_map, Finset.sum_map_toList]; exact Finset.sum_congr rfl (fun a _ => rfl)
  have hLsnd : (L.map Prod.snd).sum = ∑ a ∈ T, mm a := by
    rw [hL, List.map_map, Finset.sum_map_toList]; exact Finset.sum_congr rfl (fun a _ => rfl)
  have hLfst_sq : sqsum (L.map Prod.fst) = ∑ a ∈ T, nn a * nn a := by
    rw [hL, List.map_map, sqsum_eq_pow, List.map_map, Finset.sum_map_toList]
    simp only [Function.comp, pow_two]
  have hLlen : L.length = k - 2 := by rw [hL, List.length_map, Finset.length_toList, hTcard]
  have hLmem : ∀ p ∈ L, 2 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.2 ≤ p.1 := by
    intro p hp
    rw [hL, List.mem_map] at hp
    obtain ⟨a, _, rfl⟩ := hp
    exact ⟨hnn a, hmm1 a, hmmn a⟩
  -- sig2 identity via (sum, sqsum): both lists have equal sum & sqsum
  have hsig2_eq : ∀ na nb : ℕ, na + nb = nn ia + nn ib →
      na * na + nb * nb = nn ia * nn ia + nn ib * nn ib →
      sig2 (List.replicate l 1 ++ List.ofFn nn)
        = sig2 (na :: nb :: (List.replicate l 1 ++ L.map Prod.fst)) := by
    intro na nb hsum hsq
    have e1 := two_mul_sig2 (List.replicate l 1 ++ List.ofFn nn)
    have e2 := two_mul_sig2 (na :: nb :: (List.replicate l 1 ++ L.map Prod.fst))
    rw [← sqsum_eq_pow] at e1 e2
    have hsA : (List.replicate l 1 ++ List.ofFn nn).sum = l + ∑ a, nn a := by
      rw [List.sum_append, sum_replicate_one, List.sum_ofFn]
    have hsB : (na :: nb :: (List.replicate l 1 ++ L.map Prod.fst)).sum
        = na + nb + l + ∑ a ∈ T, nn a := by
      rw [List.sum_cons, List.sum_cons, List.sum_append, sum_replicate_one, hLfst]; ring
    have hqA : sqsum (List.replicate l 1 ++ List.ofFn nn) = l + ∑ a, nn a * nn a := by
      rw [sqsum_append, sqsum_replicate_one, sqsum_ofFn]
    have hqB : sqsum (na :: nb :: (List.replicate l 1 ++ L.map Prod.fst))
        = na * na + nb * nb + l + ∑ a ∈ T, nn a * nn a := by
      rw [sqsum_cons, sqsum_cons, sqsum_append, sqsum_replicate_one, hLfst_sq]; ring
    rw [hsA, hqA] at e1
    rw [hsB, hqB] at e2
    have hsumeq : na + nb + l + ∑ a ∈ T, nn a = l + ∑ a, nn a := by rw [hsum_nn]; omega
    have hsqeq : na * na + nb * nb + l + ∑ a ∈ T, nn a * nn a = l + ∑ a, nn a * nn a := by
      rw [hsum_sq]; omega
    rw [hsumeq, hsqeq] at e2
    omega
  -- case on which of nn ia, nn ib is the smaller size (lemma3_arith needs na ≤ nb)
  rcases le_total (nn ia) (nn ib) with hord | hord
  · have hsig := hsig2_eq (nn ia) (nn ib) rfl rfl
    have harith := lemma3_arith l (nn ia) (nn ib) (mm ia) (mm ib)
      (hnn ia) hord (hmm1 ia) (hmm1 ib) (hmmn ia) (hmmn ib) L hLmem
    have hsumlist : (nn ia :: nn ib :: (List.replicate l 1 ++ L.map Prod.fst)).sum + 1 = n := by
      rw [List.sum_cons, List.sum_cons, List.sum_append, sum_replicate_one, hLfst]; omega
    have hlenlist : (nn ia :: nn ib :: (List.replicate l 1 ++ L.map Prod.fst)).length = r := by
      rw [List.length_cons, List.length_cons, List.length_append, List.length_replicate,
        List.length_map, hLlen]; omega
    rw [← hsumlist, ← hlenlist]
    omega
  · have hsig := hsig2_eq (nn ib) (nn ia) (by omega) (by ring)
    have harith := lemma3_arith l (nn ib) (nn ia) (mm ib) (mm ia)
      (hnn ib) hord (hmm1 ib) (hmm1 ia) (hmmn ib) (hmmn ia) L hLmem
    have hsumlist : (nn ib :: nn ia :: (List.replicate l 1 ++ L.map Prod.fst)).sum + 1 = n := by
      rw [List.sum_cons, List.sum_cons, List.sum_append, sum_replicate_one, hLfst]; omega
    have hlenlist : (nn ib :: nn ia :: (List.replicate l 1 ++ L.map Prod.fst)).length = r := by
      rw [List.length_cons, List.length_cons, List.length_append, List.length_replicate,
        List.length_map, hLlen]; omega
    have hcomm : mm ib * mm ia = mm ia * mm ib := Nat.mul_comm _ _
    rw [← hsumlist, ← hlenlist]
    omega

/-- Symmetric double sum splits as diagonal + twice the strict-upper part. -/
theorem sum_sym {k : ℕ} (g : Fin k → Fin k → ℕ) (hsymm : ∀ a b, g a b = g b a) :
    (∑ a, ∑ b, g a b)
      = (∑ a, g a a)
        + 2 * ∑ p ∈ univ.filter (fun p : Fin k × Fin k => p.1 < p.2), g p.1 p.2 := by
  classical
  set P := univ.filter (fun p : Fin k × Fin k => p.1 < p.2) with hP
  set Q := univ.filter (fun p : Fin k × Fin k => p.2 < p.1) with hQ
  -- ∑ over the whole product = ∑_P + ∑_{¬<}
  have hprod : (∑ a, ∑ b, g a b) = ∑ p ∈ (univ : Finset (Fin k × Fin k)), g p.1 p.2 := by
    rw [← Finset.univ_product_univ, Finset.sum_product']
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset (Fin k × Fin k))
    (fun p => p.1 < p.2) (fun p => g p.1 p.2)
  -- ∑_{¬<} = ∑_diag + ∑_Q
  have hge : (univ.filter (fun p : Fin k × Fin k => ¬ p.1 < p.2))
      = univ.filter (fun p : Fin k × Fin k => p.1 = p.2) ∪ Q := by
    rw [hQ]; ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    omega
  have hdisj_dQ : Disjoint (univ.filter (fun p : Fin k × Fin k => p.1 = p.2)) Q := by
    rw [hQ, Finset.disjoint_filter]; intro p _ heq; omega
  have hsum_ge : (∑ p ∈ univ.filter (fun p : Fin k × Fin k => ¬ p.1 < p.2), g p.1 p.2)
      = (∑ p ∈ univ.filter (fun p : Fin k × Fin k => p.1 = p.2), g p.1 p.2)
        + ∑ p ∈ Q, g p.1 p.2 := by
    rw [hge, Finset.sum_union hdisj_dQ]
  -- diagonal = ∑_a g a a
  have hdiag : (∑ p ∈ univ.filter (fun p : Fin k × Fin k => p.1 = p.2), g p.1 p.2)
      = ∑ a, g a a := by
    apply Finset.sum_nbij' (fun p => p.1) (fun a => (a, a))
    · intro p _; exact Finset.mem_univ _
    · intro a _; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, rfl⟩
    · intro p hp; rw [Finset.mem_filter] at hp; exact Prod.ext_iff.mpr ⟨rfl, hp.2⟩
    · intro a _; rfl
    · intro p hp; rw [Finset.mem_filter] at hp; simp only [hp.2]
  -- Q reindexes to P via swap
  have hQP : (∑ p ∈ Q, g p.1 p.2) = ∑ p ∈ P, g p.1 p.2 := by
    rw [hQ, hP]
    apply Finset.sum_nbij' (fun p => (p.2, p.1)) (fun p => (p.2, p.1))
    · intro p hp; rw [Finset.mem_filter] at hp ⊢; exact ⟨Finset.mem_univ _, hp.2⟩
    · intro p hp; rw [Finset.mem_filter] at hp ⊢; exact ⟨Finset.mem_univ _, hp.2⟩
    · intro p _; rfl
    · intro p _; rfl
    · intro p _; exact hsymm p.1 p.2
  rw [hprod, ← hsplit, hsum_ge, hdiag, hQP]; ring



/-- `crossE` is symmetric. -/
theorem crossE_comm {s : ℕ} (G : SimpleGraph (Fin s)) (A B : Finset (Fin s)) :
    crossE G A B = crossE G B A := by
  rw [crossE_eq_product, crossE_eq_product]
  apply Finset.card_nbij' (fun p => (p.2, p.1)) (fun p => (p.2, p.1))
  · intro p hp; simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, G.symm hp.2⟩
  · intro p hp; simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, G.symm hp.2⟩
  · intro p _; rfl
  · intro p _; rfl

set_option maxHeartbeats 4000000 in
/-- **D1: e(⋃Nₐ) = Σ_{a<b} crossE(Nₐ,N_b)** for pairwise-disjoint independent `N`. -/
theorem edgeCountIn_bigs {n k : ℕ} (G : SimpleGraph (Fin n)) (N : Fin k → Finset (Fin n))
    (hdisj : ∀ a b, a ≠ b → Disjoint (N a) (N b))
    (hindep : ∀ a, ∀ u ∈ N a, ∀ w ∈ N a, ¬ G.Adj u w) :
    edgeCountIn G ((univ : Finset (Fin k)).biUnion N)
      = ∑ p ∈ univ.filter (fun p : Fin k × Fin k => p.1 < p.2), crossE G (N p.1) (N p.2) := by
  have hdisj' : ∀ i ∈ (univ : Finset (Fin k)), ∀ j ∈ (univ : Finset (Fin k)), i ≠ j →
      Disjoint (N i) (N j) := fun i _ j _ h => hdisj i j h
  have hcs := crossE_self G ((univ : Finset (Fin k)).biUnion N)
  have hdd : crossE G ((univ : Finset (Fin k)).biUnion N) ((univ : Finset (Fin k)).biUnion N)
      = ∑ a, ∑ b, crossE G (N a) (N b) := by
    rw [crossE_biUnion_right G _ univ N hdisj']
    apply Finset.sum_congr rfl; intro b _
    rw [crossE_comm G _ (N b), crossE_biUnion_right G (N b) univ N hdisj']
  have hss := sum_sym (fun a b => crossE G (N a) (N b)) (fun a b => crossE_comm G (N a) (N b))
  have hdiag0 : (∑ a, crossE G (N a) (N a)) = 0 := by
    apply Finset.sum_eq_zero; intro a _
    simp [crossE_self, edgeCountIn_eq_zero_of_indep G (N a) (fun u hu w hw => hindep a u hu w hw)]
  have h2 : 2 * edgeCountIn G ((univ : Finset (Fin k)).biUnion N)
      = 2 * ∑ p ∈ univ.filter (fun p : Fin k × Fin k => p.1 < p.2), crossE G (N p.1) (N p.2) := by
    rw [← hcs, hdd, hss, hdiag0]; ring
  omega



set_option maxHeartbeats 4000000 in
/-- **STEP 5 (the edge-count).** With `V = Y ⊔ Bigs`, `Bigs = ⋃Nₐ`, `M a ⊆ N a` all-adjacent
to `Y`, the KP edge-accounting: `e(G) + Σ_{a<b} ē_ij ≤ σ₂(1^l,nvec) + l + Σ mₐ`. -/
theorem kp_lemma3_count {n k l : ℕ} (G : SimpleGraph (Fin n))
    (N : Fin k → Finset (Fin n)) (Y : Finset (Fin n)) (M : Fin k → Finset (Fin n))
    (hMN : ∀ a, M a ⊆ N a)
    (hNdisj : ∀ a b, a ≠ b → Disjoint (N a) (N b))
    (hNindep : ∀ a, ∀ u ∈ N a, ∀ w ∈ N a, ¬ G.Adj u w)
    (hpart : (univ : Finset (Fin n)) = Y ∪ (univ : Finset (Fin k)).biUnion N)
    (hYBdisj : Disjoint Y ((univ : Finset (Fin k)).biUnion N))
    (hYcard : Y.card = l + 1)
    (hMadj : ∀ a, ∀ u ∈ M a, ∀ y ∈ Y, G.Adj u y)
    (hNMmiss : ∀ a, ∀ u ∈ N a, u ∉ M a → (Y.filter (fun y => G.Adj u y)).card ≤ l) :
    edgeCountIn G univ
      + (∑ p ∈ univ.filter (fun p : Fin k × Fin k => p.1 < p.2),
          ((M p.1 ×ˢ M p.2).filter (fun uv => ¬ G.Adj uv.1 uv.2)).card)
      ≤ sig2 (List.replicate l 1 ++ List.ofFn (fun a => (N a).card)) + l + ∑ a, (M a).card := by
  classical
  set Bigs := (univ : Finset (Fin k)).biUnion N with hBigs
  set P := univ.filter (fun p : Fin k × Fin k => p.1 < p.2) with hP
  -- (A) partition edge count
  have hA : edgeCountIn G univ = edgeCountIn G Y + edgeCountIn G Bigs + crossE G Y Bigs := by
    rw [hpart, edgeCountIn_disjoint_union G hYBdisj]
  -- (B) e(Y) ≤ C(l+1,2)
  have hB : edgeCountIn G Y ≤ (l + 1).choose 2 := by
    have := edgeCountIn_le_choose_two G Y; rwa [hYcard] at this
  -- (C) crossE(Y,Bigs) ≤ Σ_a (|M a| + l·|N a|)
  have hCsplit : crossE G Y Bigs = ∑ a, crossE G (N a) Y := by
    rw [hBigs, crossE_biUnion_right G Y univ N (fun i _ j _ h => hNdisj i j h)]
    apply Finset.sum_congr rfl; intro a _; exact crossE_comm G Y (N a)
  have hCa : ∀ a, crossE G (N a) Y ≤ (M a).card + l * (N a).card := by
    intro a
    unfold crossE
    rw [← Finset.sum_filter_add_sum_filter_not (N a) (fun u => u ∈ M a)]
    have h1 : (∑ u ∈ (N a).filter (fun u => u ∈ M a), (Y.filter (fun y => G.Adj u y)).card)
        ≤ (M a).card * (l + 1) := by
      calc (∑ u ∈ (N a).filter (fun u => u ∈ M a), (Y.filter (fun y => G.Adj u y)).card)
          ≤ ∑ _u ∈ (N a).filter (fun u => u ∈ M a), (l + 1) := by
            apply Finset.sum_le_sum; intro u _
            rw [← hYcard]; exact Finset.card_filter_le _ _
        _ = ((N a).filter (fun u => u ∈ M a)).card * (l + 1) := by rw [Finset.sum_const, smul_eq_mul]
        _ = (M a).card * (l + 1) := by
            rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (hMN a)]
    have h2 : (∑ u ∈ (N a).filter (fun u => ¬ u ∈ M a), (Y.filter (fun y => G.Adj u y)).card)
        ≤ ((N a).filter (fun u => ¬ u ∈ M a)).card * l := by
      calc (∑ u ∈ (N a).filter (fun u => ¬ u ∈ M a), (Y.filter (fun y => G.Adj u y)).card)
          ≤ ∑ _u ∈ (N a).filter (fun u => ¬ u ∈ M a), l := by
            apply Finset.sum_le_sum; intro u hu
            rw [Finset.mem_filter] at hu; exact hNMmiss a u hu.1 hu.2
        _ = ((N a).filter (fun u => ¬ u ∈ M a)).card * l := by rw [Finset.sum_const, smul_eq_mul]
    have hcardsplit : ((N a).filter (fun u => u ∈ M a)).card
        + ((N a).filter (fun u => ¬ u ∈ M a)).card = (N a).card :=
      Finset.filter_card_add_filter_neg_card_eq_card _
    have hMcard : ((N a).filter (fun u => u ∈ M a)).card = (M a).card := by
      rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (hMN a)]
    have hMle : (M a).card ≤ (N a).card := Finset.card_le_card (hMN a)
    calc (∑ u ∈ (N a).filter (fun u => u ∈ M a), (Y.filter (fun y => G.Adj u y)).card)
          + (∑ u ∈ (N a).filter (fun u => ¬ u ∈ M a), (Y.filter (fun y => G.Adj u y)).card)
        ≤ (M a).card * (l + 1) + ((N a).filter (fun u => ¬ u ∈ M a)).card * l :=
          add_le_add h1 h2
      _ ≤ (M a).card + l * (N a).card := by nlinarith [hcardsplit, hMcard, hMle]
  have hC : crossE G Y Bigs ≤ (∑ a, (M a).card) + l * ∑ a, (N a).card := by
    rw [hCsplit]
    calc (∑ a, crossE G (N a) Y) ≤ ∑ a, ((M a).card + l * (N a).card) := Finset.sum_le_sum (fun a _ => hCa a)
      _ = (∑ a, (M a).card) + l * ∑ a, (N a).card := by rw [Finset.sum_add_distrib, Finset.mul_sum]
  -- (D) e(Bigs) + Σ_P miss ≤ σ₂(nvec)
  have hD2 : ∀ p ∈ P, crossE G (N p.1) (N p.2)
      + ((M p.1 ×ˢ M p.2).filter (fun uv => ¬ G.Adj uv.1 uv.2)).card
      ≤ (N p.1).card * (N p.2).card := by
    intro p _
    rw [crossE_eq_product]
    have hsub : (M p.1 ×ˢ M p.2).filter (fun uv => ¬ G.Adj uv.1 uv.2)
        ⊆ (N p.1 ×ˢ N p.2).filter (fun uv => ¬ G.Adj uv.1 uv.2) := by
      intro uv huv; rw [Finset.mem_filter, Finset.mem_product] at huv ⊢
      exact ⟨⟨hMN p.1 huv.1.1, hMN p.2 huv.1.2⟩, huv.2⟩
    have hle := Finset.card_le_card hsub
    have hcard := Finset.filter_card_add_filter_neg_card_eq_card
      (s := N p.1 ×ˢ N p.2) (p := fun uv => G.Adj uv.1 uv.2)
    rw [Finset.card_product] at hcard
    have hnegeq : (N p.1 ×ˢ N p.2).filter (fun uv => ¬ (fun uv => G.Adj uv.1 uv.2) uv)
        = (N p.1 ×ˢ N p.2).filter (fun uv => ¬ G.Adj uv.1 uv.2) := rfl
    rw [hnegeq] at hcard
    omega
  have hD3 : (∑ p ∈ P, (N p.1).card * (N p.2).card)
      = sig2 (List.ofFn (fun a => (N a).card)) := by
    have hss := sum_sym (fun a b => (N a).card * (N b).card) (fun a b => Nat.mul_comm _ _)
    simp only [] at hss
    rw [← hP] at hss
    have hsq := two_mul_sig2 (List.ofFn (fun a => (N a).card))
    rw [← sqsum_eq_pow, sqsum_ofFn, List.sum_ofFn] at hsq
    have hfull : (∑ a, ∑ b, (N a).card * (N b).card) = (∑ a, (N a).card) ^ 2 := by
      rw [pow_two, Finset.sum_mul_sum]
    rw [hfull] at hss
    omega
  have hD : edgeCountIn G Bigs
      + (∑ p ∈ P, ((M p.1 ×ˢ M p.2).filter (fun uv => ¬ G.Adj uv.1 uv.2)).card)
      ≤ sig2 (List.ofFn (fun a => (N a).card)) := by
    rw [hBigs, edgeCountIn_bigs G N hNdisj hNindep, ← hP, ← hD3, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hD2
  -- (E) combine via the arithmetic identity (no ℕ subtraction)
  have hident2 : sig2 (List.replicate l 1 ++ List.ofFn (fun a => (N a).card)) + l
      = (l + 1).choose 2 + l * (∑ a, (N a).card) + sig2 (List.ofFn (fun a => (N a).card)) := by
    have e1 := two_mul_sig2 (List.replicate l 1 ++ List.ofFn (fun a => (N a).card))
    have e2 := two_mul_sig2 (List.ofFn (fun a => (N a).card))
    rw [← sqsum_eq_pow, sqsum_append, sqsum_replicate_one, sqsum_ofFn, List.sum_append,
      sum_replicate_one, List.sum_ofFn] at e1
    rw [← sqsum_eq_pow, sqsum_ofFn, List.sum_ofFn] at e2
    have hexp : (l + ∑ a, (N a).card) ^ 2
        = l ^ 2 + 2 * (l * ∑ a, (N a).card) + (∑ a, (N a).card) ^ 2 := by ring
    rw [hexp] at e1
    have hdvd : 2 ∣ (l + 1) * l := by rw [mul_comm]; exact (Nat.even_mul_succ_self l).two_dvd
    have hchoose2 : 2 * (l + 1).choose 2 = l ^ 2 + l := by
      rw [Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_div_cancel' hdvd]; ring
    omega
  -- assemble
  rw [hA]
  omega

set_option maxHeartbeats 4000000 in
/-- **KP Lemma 3.** `G ∈ Gₙ,ᵣ` with `G−z` `r`-colourable (proper off `z`) ⇒
`e(G) + kpSaving ≤ t_r`. STEPs 1 (classes), 2 (Y clique), 3 (Mᵢ≠∅), 4 (k≥2), 6
(transversal counting), 7 (`lemma3_arith`) are sorry-free; STEP 5 (the edge-count
`e(G) + Σ ēᵢⱼ ≤ σ₂(1^l,nvec) + l + Σmᵢ`) was the last local gap, since discharged — `kp_lemma3` is sorry-free. -/
theorem kp_lemma3 {r n : ℕ} (hr : 2 ≤ r) (G : SimpleGraph (Fin n)) (hn : r + 3 ≤ n)
    (hCF : G.CliqueFree (r + 1)) (hchi : ¬ G.Colorable r)
    (z : Fin n) (κ' : Fin n → Fin r)
    (hproper' : ∀ u v, u ≠ z → v ≠ z → G.Adj u v → κ' u ≠ κ' v) :
    edgeCountIn G Finset.univ + kpSaving n r ≤ (turanGraph n r).edgeFinset.card := by
  classical
  -- STEP 1: colour classes of G−z
  set C : Fin r → Finset (Fin n) := fun i => (univ.erase z).filter (fun v => κ' v = i) with hCdef
  have hCmem : ∀ i v, v ∈ C i ↔ v ≠ z ∧ κ' v = i := by
    intro i v; rw [hCdef]
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
  have hCz : ∀ i, z ∉ C i := by intro i h; exact (hCmem i z).mp h |>.1 rfl
  have hCindep : ∀ i, ∀ u ∈ C i, ∀ w ∈ C i, ¬ G.Adj u w := by
    intro i u hu w hw hadj
    obtain ⟨huz, hui⟩ := (hCmem i u).mp hu
    obtain ⟨hwz, hwi⟩ := (hCmem i w).mp hw
    exact hproper' u w huz hwz hadj (hui.trans hwi.symm)
  have hCdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j) := by
    intro i j hij; rw [Finset.disjoint_left]; intro v hvi hvj
    exact hij (((hCmem i v).mp hvi).2.symm.trans ((hCmem j v).mp hvj).2)
  have hCnonempty : ∀ i, (C i).Nonempty := by
    intro i
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    apply hchi
    refine ⟨SimpleGraph.Coloring.mk (fun v => if v = z then i else κ' v) ?_⟩
    intro u v hadj
    simp only []
    have huv : u ≠ v := G.ne_of_adj hadj
    by_cases hu : u = z <;> by_cases hv : v = z
    · exact absurd (hu.trans hv.symm) huv
    · rw [if_pos hu, if_neg hv]; intro heq
      have : v ∈ C i := (hCmem i v).mpr ⟨hv, heq.symm⟩
      rw [hemp] at this; exact absurd this (Finset.notMem_empty v)
    · rw [if_neg hu, if_pos hv]; intro heq
      have : u ∈ C i := (hCmem i u).mpr ⟨hu, heq⟩
      rw [hemp] at this; exact absurd this (Finset.notMem_empty u)
    · rw [if_neg hu, if_neg hv]; exact hproper' u v hu hv hadj
  have hC1 : ∀ i, 1 ≤ (C i).card := fun i => Finset.card_pos.mpr (hCnonempty i)
  -- big / singleton split
  set Big : Finset (Fin r) := univ.filter (fun i => 2 ≤ (C i).card) with hBigdef
  set Sing : Finset (Fin r) := univ.filter (fun i => ¬ 2 ≤ (C i).card) with hSingdef
  set k : ℕ := Big.card with hkdef
  set l : ℕ := Sing.card with hldef
  have hlk : l + k = r := by
    have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin r)))
      (fun i => 2 ≤ (C i).card)
    rw [Finset.card_univ, Fintype.card_fin] at h
    rw [hldef, hkdef, hSingdef, hBigdef]; omega
  have hSing1 : ∀ i ∈ Sing, (C i).card = 1 := by
    intro i hi; rw [hSingdef, Finset.mem_filter] at hi
    have := hC1 i; omega
  -- reindex Big to Fin k
  set bigEmb : Fin k ↪o Fin r := Big.orderEmbOfFin hkdef.symm with hbigEmb
  have hbigmem : ∀ a, bigEmb a ∈ Big := fun a => Finset.orderEmbOfFin_mem Big hkdef.symm a
  have hbigimg : univ.image bigEmb = Big := Finset.image_orderEmbOfFin_univ Big hkdef.symm
  have hbiginj : Function.Injective bigEmb := bigEmb.injective
  set N : Fin k → Finset (Fin n) := fun a => C (bigEmb a) with hNdef
  set Y : Finset (Fin n) := insert z (Sing.biUnion C) with hYdef
  set M : Fin k → Finset (Fin n) := fun a => (N a).filter (fun u => ∀ y ∈ Y, G.Adj u y) with hMdef
  have hnn2 : ∀ a, 2 ≤ (N a).card := by
    intro a; have := hbigmem a; rw [hBigdef, Finset.mem_filter] at this; exact this.2
  have hmmn : ∀ a, (M a).card ≤ (N a).card := fun a => Finset.card_le_card (Finset.filter_subset _ _)
  have hMsubN : ∀ a, M a ⊆ N a := fun a => Finset.filter_subset _ _
  have hNbig : ∀ a, bigEmb a ∈ Big := hbigmem
  -- membership: N a ⊆ erase z
  have hNz : ∀ a, ∀ u ∈ N a, u ≠ z := by
    intro a u hu; rw [hNdef] at hu; exact ((hCmem _ u).mp hu).1
  have hMY : ∀ a, ∀ u ∈ M a, u ∉ Y := by
    intro a u hu
    have huN : u ∈ N a := hMsubN a hu
    have huz : u ≠ z := hNz a u huN
    rw [hYdef, Finset.mem_insert]; push_neg; refine ⟨huz, ?_⟩
    intro hus
    rw [Finset.mem_biUnion] at hus
    obtain ⟨j, hjS, huj⟩ := hus
    have hjB : bigEmb a ∈ Big := hbigmem a
    by_cases hje : j = bigEmb a
    · rw [hSingdef, Finset.mem_filter] at hjS
      rw [hBigdef, Finset.mem_filter] at hjB
      rw [hje] at hjS; exact hjS.2 hjB.2
    · rw [hNdef] at huN
      exact (Finset.disjoint_left.mp (hCdisj j (bigEmb a) hje) huj) huN
  have hMadj : ∀ a, ∀ u ∈ M a, ∀ y ∈ Y, G.Adj u y := by
    intro a u hu y hy; rw [hMdef, Finset.mem_filter] at hu; exact hu.2 y hy
  have hMdisj : ∀ a b, a ≠ b → Disjoint (M a) (M b) := by
    intro a b hab
    have hne : bigEmb a ≠ bigEmb b := fun h => hab (hbiginj h)
    exact (hCdisj (bigEmb a) (bigEmb b) hne).mono (hMsubN a) (hMsubN b)
  have hmm1 : ∀ a, 1 ≤ (M a).card := by
    intro a
    rw [Nat.one_le_iff_ne_zero]
    intro hcard0
    rw [Finset.card_eq_zero] at hcard0
    apply hchi
    have hf0 : ∀ u ∈ N a, ∃ y, y ∈ Y ∧ ¬ G.Adj u y := by
      intro u hu
      by_contra hcon; push_neg at hcon
      have hmem : u ∈ M a := by rw [hMdef, Finset.mem_filter]; exact ⟨hu, hcon⟩
      rw [hcard0] at hmem; exact absurd hmem (Finset.notMem_empty u)
    choose! f hfY hfna using hf0
    have hYNa : ∀ w ∈ Y, w ∉ N a := by
      intro w hw hwNa
      rw [hYdef, Finset.mem_insert] at hw
      rcases hw with hwz | hw
      · exact hNz a w hwNa hwz
      · obtain ⟨j, hjS, hwj⟩ := Finset.mem_biUnion.mp hw
        by_cases hj : j = bigEmb a
        · rw [hSingdef, Finset.mem_filter] at hjS
          have hb := hbigmem a; rw [hBigdef, Finset.mem_filter] at hb
          rw [hj] at hjS; exact hjS.2 hb.2
        · rw [hNdef] at hwNa; exact (Finset.disjoint_left.mp (hCdisj j (bigEmb a) hj) hwj) hwNa
    have hkbig : ∀ w, w ≠ z → κ' w = bigEmb a → w ∈ N a := by
      intro w hw hk; rw [hNdef]; exact (hCmem (bigEmb a) w).mpr ⟨hw, hk⟩
    have hsingcol : ∀ w, w ∈ Y → w ≠ z → w ∈ C (κ' w) ∧ (C (κ' w)).card = 1 := by
      intro w hw hwz
      rw [hYdef, Finset.mem_insert] at hw
      rcases hw with h | h
      · exact absurd h hwz
      · obtain ⟨j, hjS, hwj⟩ := Finset.mem_biUnion.mp h
        have hjeq : κ' w = j := ((hCmem j w).mp hwj).2
        rw [hjeq]; exact ⟨hwj, hSing1 j hjS⟩
    refine ⟨SimpleGraph.Coloring.mk (fun v => if v ∈ N a
      then (if f v = z then bigEmb a else κ' (f v))
      else (if v = z then bigEmb a else κ' v)) ?_⟩
    intro u v hadj
    have huv : u ≠ v := G.ne_of_adj hadj
    simp only []
    by_cases hu : u ∈ N a <;> by_cases hv : v ∈ N a
    · rw [if_pos hu, if_pos hv]; exact absurd hadj (hCindep (bigEmb a) u hu v hv)
    · rw [if_pos hu, if_neg hv]
      intro heq
      have hfuY : f u ∈ Y := hfY u hu
      have hfuna : ¬ G.Adj u (f u) := hfna u hu
      have hfuNa : f u ∉ N a := hYNa (f u) hfuY
      by_cases hfz : f u = z
      · rw [if_pos hfz] at heq
        by_cases hvz : v = z
        · rw [hvz] at hadj; rw [hfz] at hfuna; exact hfuna hadj
        · rw [if_neg hvz] at heq; exact hv (hkbig v hvz heq.symm)
      · rw [if_neg hfz] at heq
        by_cases hvz : v = z
        · rw [if_pos hvz] at heq; exact hfuNa (hkbig (f u) hfz heq)
        · rw [if_neg hvz] at heq
          obtain ⟨hfuc, hcard1⟩ := hsingcol (f u) hfuY hfz
          have hvc : v ∈ C (κ' (f u)) := (hCmem (κ' (f u)) v).mpr ⟨hvz, heq.symm⟩
          obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard1
          rw [hw, Finset.mem_singleton] at hfuc hvc
          rw [hvc, ← hfuc] at hadj; exact hfuna hadj
    · rw [if_neg hu, if_pos hv]
      intro heq
      have hfvY : f v ∈ Y := hfY v hv
      have hfvna : ¬ G.Adj v (f v) := hfna v hv
      have hfvNa : f v ∉ N a := hYNa (f v) hfvY
      by_cases hfz : f v = z
      · rw [if_pos hfz] at heq
        by_cases huz : u = z
        · rw [huz] at hadj; rw [hfz] at hfvna; exact hfvna hadj.symm
        · rw [if_neg huz] at heq; exact hu (hkbig u huz heq)
      · rw [if_neg hfz] at heq
        by_cases huz : u = z
        · rw [if_pos huz] at heq; exact hfvNa (hkbig (f v) hfz heq.symm)
        · rw [if_neg huz] at heq
          obtain ⟨hfvc, hcard1⟩ := hsingcol (f v) hfvY hfz
          have huc : u ∈ C (κ' (f v)) := (hCmem (κ' (f v)) u).mpr ⟨huz, heq⟩
          obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard1
          rw [hw, Finset.mem_singleton] at hfvc huc
          rw [huc, ← hfvc] at hadj; exact hfvna hadj.symm
    · rw [if_neg hu, if_neg hv]
      intro heq
      by_cases huz : u = z
      · rw [if_pos huz] at heq
        by_cases hvz : v = z
        · exact huv (huz.trans hvz.symm)
        · rw [if_neg hvz] at heq; exact hv (hkbig v hvz heq.symm)
      · rw [if_neg huz] at heq
        by_cases hvz : v = z
        · rw [if_pos hvz] at heq; exact hu (hkbig u huz heq)
        · rw [if_neg hvz] at heq; exact hproper' u v huz hvz hadj heq
  have hMne : ∀ a, (M a).Nonempty := fun a => Finset.card_pos.mp (hmm1 a)
  -- counting bridges
  have hSingSum : ∑ i ∈ Sing, (C i).card = Sing.card := by
    rw [Finset.sum_congr rfl (fun i hi => hSing1 i hi), ← Finset.card_eq_sum_ones]
  have hBigSum : ∑ i ∈ Big, (C i).card = ∑ a, (N a).card := by
    rw [← hbigimg, Finset.sum_image (fun a _ b _ h => hbiginj h)]
  have hYcard : Y.card = l + 1 := by
    have hznotin : z ∉ Sing.biUnion C := by
      rw [Finset.mem_biUnion]; rintro ⟨i, _, hi⟩; exact hCz i hi
    rw [hYdef, Finset.card_insert_of_notMem hznotin,
      Finset.card_biUnion (fun i _ j _ hij => hCdisj i j hij), hSingSum]
  have hYclq : G.IsClique ↑Y := by
    intro a ha b hb hab
    rw [Finset.mem_coe, hYdef, Finset.mem_insert] at ha hb
    by_contra hnadj
    apply hchi
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact absurd rfl hab
      · obtain ⟨i, hiS, hbi⟩ := Finset.mem_biUnion.mp hb
        obtain ⟨w, hCiw⟩ := Finset.card_eq_one.mp (hSing1 i hiS)
        have hbw : b = w := by rw [hCiw] at hbi; exact Finset.mem_singleton.mp hbi
        refine recolor_z G a κ' hproper' i (fun v hvz hadjzv hveqi => ?_)
        have hvCi : v ∈ C i := (hCmem i v).mpr ⟨hvz, hveqi⟩
        rw [hCiw, Finset.mem_singleton] at hvCi
        apply hnadj; rw [hvCi, ← hbw] at hadjzv; exact hadjzv
    · rcases hb with rfl | hb
      · obtain ⟨i, hiS, hai⟩ := Finset.mem_biUnion.mp ha
        obtain ⟨w, hCiw⟩ := Finset.card_eq_one.mp (hSing1 i hiS)
        have haw : a = w := by rw [hCiw] at hai; exact Finset.mem_singleton.mp hai
        refine recolor_z G b κ' hproper' i (fun v hvz hadjzv hveqi => ?_)
        have hvCi : v ∈ C i := (hCmem i v).mpr ⟨hvz, hveqi⟩
        rw [hCiw, Finset.mem_singleton] at hvCi
        apply hnadj; rw [hvCi, ← haw] at hadjzv; exact hadjzv.symm
      · obtain ⟨i, hiS, hai⟩ := Finset.mem_biUnion.mp ha
        obtain ⟨j, hjS, hbj⟩ := Finset.mem_biUnion.mp hb
        obtain ⟨wa, hCiwa⟩ := Finset.card_eq_one.mp (hSing1 i hiS)
        obtain ⟨wb, hCjwb⟩ := Finset.card_eq_one.mp (hSing1 j hjS)
        have hawa : a = wa := by rw [hCiwa] at hai; exact Finset.mem_singleton.mp hai
        have hbwb : b = wb := by rw [hCjwb] at hbj; exact Finset.mem_singleton.mp hbj
        have hij : i ≠ j := by
          intro h; subst h; apply hab
          rw [hCiwa] at hai hbj
          rw [Finset.mem_singleton.mp hai, Finset.mem_singleton.mp hbj]
        have hbz : b ≠ z := by intro h; exact hCz j (h ▸ hbj)
        refine recolor_zb G z b κ' hproper' i j hij hbz (fun w hwb hwz hadjbw hwi => ?_)
          (fun w hwb hwz hadjzw hwj => ?_)
        · have hwCi : w ∈ C i := (hCmem i w).mpr ⟨hwz, hwi⟩
          rw [hCiwa, Finset.mem_singleton] at hwCi
          apply hnadj; rw [hwCi, ← hawa] at hadjbw; exact hadjbw.symm
        · have hwCj : w ∈ C j := (hCmem j w).mpr ⟨hwz, hwj⟩
          rw [hCjwb, Finset.mem_singleton] at hwCj
          apply hwb; rw [hwCj, ← hbwb]
  have hn_eq : n = 1 + l + ∑ a, (N a).card := by
    have herasez : (univ.erase z).card = n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ z), Finset.card_univ, Fintype.card_fin]
    have hcover : univ.erase z = (univ : Finset (Fin r)).biUnion C := by
      ext v
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
      constructor
      · intro hv; exact ⟨κ' v, (hCmem (κ' v) v).mpr ⟨hv, rfl⟩⟩
      · rintro ⟨i, hi⟩; exact ((hCmem i v).mp hi).1
    have hcard_eq : (univ.erase z).card = ∑ i, (C i).card := by
      rw [hcover, Finset.card_biUnion (fun i _ j _ hij => hCdisj i j hij)]
    have hsplit : ∑ i, (C i).card = ∑ a, (N a).card + l := by
      have hp := Finset.sum_filter_add_sum_filter_not univ
        (fun i => 2 ≤ (C i).card) (fun i => (C i).card)
      rw [← hBigdef, ← hSingdef, hBigSum, hSingSum] at hp
      omega
    have hall : ∑ a, (N a).card + l = n - 1 := by rw [← hsplit, ← hcard_eq]; exact herasez
    omega
  -- STEP 4: k ≥ 2 (else l = r ⇒ n = r+1, or l = r−1 ⇒ Y∪{u} = K_{r+1})
  have hk : 2 ≤ k := by
    by_contra hk2
    push_neg at hk2
    interval_cases k
    · simp only [Finset.univ_eq_empty, Finset.sum_empty] at hn_eq
      omega
    · obtain ⟨u, hu⟩ := hMne 0
      have huY : u ∉ Y := hMY 0 u hu
      have huadj : ∀ y ∈ Y, G.Adj u y := hMadj 0 u hu
      apply hCF (insert u Y)
      refine ⟨?_, ?_⟩
      · intro a ha b hb hab
        rw [Finset.mem_coe, Finset.mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact absurd rfl hab
        · exact huadj b hb
        · exact (huadj a ha).symm
        · exact hYclq (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab
      · rw [Finset.card_insert_of_notMem huY, hYcard]; omega
  have hkpos : 0 < k := by omega
  -- two smallest-m indices
  haveI : Nonempty (Fin k) := ⟨⟨0, hkpos⟩⟩
  obtain ⟨ia, -, hia_min⟩ := Finset.exists_min_image univ (fun a => (M a).card)
    ⟨⟨0, hkpos⟩, Finset.mem_univ _⟩
  have herasene : (univ.erase ia).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]; omega
  obtain ⟨ib, hibmem, hib_min⟩ := Finset.exists_min_image (univ.erase ia) (fun a => (M a).card) herasene
  have hiab : ia ≠ ib := fun h => (Finset.mem_erase.mp hibmem).1 h.symm
  have hmin_a : ∀ i, (M ia).card ≤ (M i).card := fun i => hia_min i (Finset.mem_univ _)
  have hmin_b : ∀ i, i ≠ ia → (M ib).card ≤ (M i).card :=
    fun i hi => hib_min i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩)
  -- STEP 6: hbad + missing_edges_ge
  have hbad := transversal_has_bad_pair G hCF Y hYclq hYcard (by omega : k + l + 1 = r + 1)
    M hMdisj hMY hMadj
  have hstep6 := missing_edges_ge M hMne G.Adj hbad ia ib hiab hmin_a hmin_b
  -- STEP 5: counting
  have hstep5 : edgeCountIn G univ
      + (∑ p ∈ univ.filter (fun p : Fin k × Fin k => p.1 < p.2),
          ((M p.1 ×ˢ M p.2).filter (fun uv => ¬ G.Adj uv.1 uv.2)).card)
      ≤ sig2 (List.replicate l 1 ++ List.ofFn (fun a => (N a).card)) + l + ∑ a, (M a).card :=
    by
      have hNdisj : ∀ a b, a ≠ b → Disjoint (N a) (N b) :=
        fun a b hab => hCdisj (bigEmb a) (bigEmb b) (fun h => hab (hbiginj h))
      have hNindep : ∀ a, ∀ u ∈ N a, ∀ w ∈ N a, ¬ G.Adj u w := by
        intro a u hu w hw; rw [hNdef] at hu hw; exact hCindep (bigEmb a) u hu w hw
      have hpart : (univ : Finset (Fin n)) = Y ∪ (univ : Finset (Fin k)).biUnion N := by
        ext v
        simp only [Finset.mem_univ, true_iff, Finset.mem_union, hYdef, Finset.mem_insert,
          Finset.mem_biUnion, Finset.mem_univ, true_and]
        by_cases hvz : v = z
        · exact Or.inl (Or.inl hvz)
        · have hvC : v ∈ C (κ' v) := (hCmem (κ' v) v).mpr ⟨hvz, rfl⟩
          by_cases hbig : 2 ≤ (C (κ' v)).card
          · have hmem : κ' v ∈ Big := by
              rw [hBigdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hbig⟩
            rw [← hbigimg, Finset.mem_image] at hmem
            obtain ⟨a, _, ha⟩ := hmem
            exact Or.inr ⟨a, by show v ∈ C (bigEmb a); rw [ha]; exact hvC⟩
          · have hmem : κ' v ∈ Sing := by
              rw [hSingdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hbig⟩
            exact Or.inl (Or.inr ⟨κ' v, hmem, hvC⟩)
      have hYBdisj : Disjoint Y ((univ : Finset (Fin k)).biUnion N) := by
        rw [Finset.disjoint_left]
        intro v hvY hvB
        rw [Finset.mem_biUnion] at hvB
        obtain ⟨a, _, hva⟩ := hvB
        rw [hNdef] at hva
        have hvz : v ≠ z := ((hCmem _ v).mp hva).1
        have hvk : κ' v = bigEmb a := ((hCmem _ v).mp hva).2
        rw [hYdef, Finset.mem_insert] at hvY
        rcases hvY with h | h
        · exact hvz h
        · rw [Finset.mem_biUnion] at h
          obtain ⟨j, hjS, hvj⟩ := h
          have hjk : κ' v = j := ((hCmem j v).mp hvj).2
          rw [hSingdef, Finset.mem_filter] at hjS
          have hbm := hbigmem a; rw [hBigdef, Finset.mem_filter] at hbm
          have hjeq : j = bigEmb a := by rw [← hjk, hvk]
          rw [hjeq] at hjS; exact hjS.2 hbm.2
      have hNMmiss : ∀ a, ∀ u ∈ N a, u ∉ M a → (Y.filter (fun y => G.Adj u y)).card ≤ l := by
        intro a u hu hnM
        have hex : ∃ y ∈ Y, ¬ G.Adj u y := by
          by_contra hcon; push_neg at hcon
          exact hnM (Finset.mem_filter.mpr ⟨hu, hcon⟩)
        obtain ⟨y0, hy0Y, hy0⟩ := hex
        have hsub : Y.filter (fun y => G.Adj u y) ⊆ Y.erase y0 := by
          intro y hy; rw [Finset.mem_filter] at hy; rw [Finset.mem_erase]
          exact ⟨fun h => hy0 (h ▸ hy.2), hy.1⟩
        calc (Y.filter (fun y => G.Adj u y)).card ≤ (Y.erase y0).card := Finset.card_le_card hsub
          _ = Y.card - 1 := Finset.card_erase_of_mem hy0Y
          _ = l := by rw [hYcard, Nat.add_sub_cancel]
      exact kp_lemma3_count G N Y M hMsubN hNdisj hNindep hpart hYBdisj hYcard hMadj hNMmiss
  have hcount : edgeCountIn G univ + (M ia).card * (M ib).card
      ≤ sig2 (List.replicate l 1 ++ List.ofFn (fun a => (N a).card)) + l + ∑ a, (M a).card := by
    omega
  exact kp_lemma3_finish hr hk hlk (fun a => (N a).card) (fun a => (M a).card)
    hnn2 hmm1 hmmn ia ib hiab hn_eq (edgeCountIn G univ) hcount


/-! ## Singleton/empty guard arithmetic (Route MI) — closes the `some-part ≤ 1`
branch of `kp_caseB_impl` from `main_ineq` + `c ≥ 3`, no max-size needed. -/

/-- Turán is monotone in the number of parts: `t_r(n) ≤ t_{r+1}(n)`.
Immediate from `turan_step` at `d = n` (the `d*(n-d)` term vanishes). -/
theorem turan_le_succ (n r : ℕ) (hr : 0 < r) :
    (turanGraph n r).edgeFinset.card ≤ (turanGraph n (r + 1)).edgeFinset.card := by
  have h := turan_step (n := n) (r := r) (d := n) hr (le_refl n)
  simpa using h

/-- Adding one vertex to a balanced `r`-partite Turán graph adds at most `n-2` edges,
provided every part already has ≥ 2 vertices (`2r+1 ≤ n`). Division-form via `two_mul_turan`. -/
theorem turan_addvertex (n r : ℕ) (hr : 2 ≤ r) (hn : 2 * r + 1 ≤ n) :
    (turanGraph n r).edgeFinset.card ≤ (turanGraph (n - 1) r).edgeFinset.card + (n - 2) := by
  suffices h2 : 2 * (turanGraph n r).edgeFinset.card
      ≤ 2 * ((turanGraph (n - 1) r).edgeFinset.card + (n - 2)) by omega
  have hTn := two_mul_turan n r (by omega)
  have hTn1 := two_mul_turan (n - 1) r (by omega)
  rw [Nat.mul_add, hTn, hTn1]
  set q := n / r with hq
  set s := n % r with hs
  have hn_eq : n = r * q + s := by rw [hq, hs]; exact (Nat.div_add_mod n r).symm
  have hslt : s < r := hs ▸ Nat.mod_lt n (by omega)
  have hq2 : 2 ≤ q := by
    rw [hq]; exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hrq : 4 ≤ r * q := Nat.mul_le_mul hr hq2
  -- (n-1)/r and (n-1)%r depend on whether s = 0
  by_cases hsz : s = 0
  · -- s = 0: n = r*q, n-1 = r*(q-1) + (r-1)
    have hmulsub : r * (q - 1) = r * q - r := by rw [Nat.mul_sub, Nat.mul_one]
    have key : n - 1 = r * (q - 1) + (r - 1) := by omega
    have hq1 : (n - 1) / r = q - 1 := by
      rw [key, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
    have hr1 : (n - 1) % r = r - 1 := by
      rw [key, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    rw [hq1, hr1, hsz]
    have hnrq : n = r * q := by omega
    rw [hnrq]
    zify [show (1:ℕ) ≤ r by omega, show (1:ℕ) ≤ r - 1 by omega, show (1:ℕ) ≤ q by omega,
      show (1:ℕ) ≤ r * q by omega, show (2:ℕ) ≤ r * q by omega]
    nlinarith [show (2:ℤ) ≤ (q:ℤ) by exact_mod_cast hq2]
  · -- s ≥ 1: n-1 = r*q + (s-1), so (n-1)/r = q, (n-1)%r = s-1
    have key : n - 1 = r * q + (s - 1) := by omega
    have hq1 : (n - 1) / r = q := by
      rw [key, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
    have hr1 : (n - 1) % r = s - 1 := by
      rw [key, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    rw [hq1, hr1]
    rcases Nat.lt_or_ge s 2 with hs1 | hs2
    · -- s = 1: the s*(s-1) and (s-1)*((s-1)-1) terms vanish
      have hs1' : s = 1 := by omega
      rw [hs1']
      simp only [Nat.sub_self, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.zero_mul]
      zify [show (1:ℕ) ≤ r by omega, show (1:ℕ) ≤ n by omega, show (2:ℕ) ≤ n by omega]
      have hnZ : (n : ℤ) = r * q + 1 := by rw [hn_eq, hs1']; push_cast; ring
      nlinarith [show (2:ℤ) ≤ (q:ℤ) by exact_mod_cast hq2, hnZ]
    · -- s ≥ 2
      have hnZ : (n : ℤ) = r * q + s := by rw [hn_eq]; push_cast; ring
      zify [show (1:ℕ) ≤ r by omega, show (1:ℕ) ≤ s by omega, show (2:ℕ) ≤ s by omega,
        show (1:ℕ) ≤ s - 1 by omega, show (1:ℕ) ≤ n by omega, show (2:ℕ) ≤ n by omega]
      rw [hnZ]
      nlinarith [show (2:ℤ) ≤ (q:ℤ) by exact_mod_cast hq2]

/-- **M0 (the 0-part lift).** Lifting the part-count by one at fixed `n`:
`kpSaving n (r+1) + t_r(n) ≤ kpSaving n r + t_{r+1}(n)`. Used to remove an empty
block in the singleton/empty guard recursion. -/
theorem m0_lift (n r : ℕ) (hr : 2 ≤ r) :
    2 * kpSaving n (r + 1) + 2 * (turanGraph n r).edgeFinset.card
      ≤ 2 * kpSaving n r + 2 * (turanGraph n (r + 1)).edgeFinset.card := by
  have hmono : (turanGraph n r).edgeFinset.card ≤ (turanGraph n (r + 1)).edgeFinset.card :=
    turan_le_succ n r (by omega)
  simp only [kpSaving]
  split_ifs with h1 h2 h2
  · -- (T,T) both main
    have hdiv : n / (r + 1) ≤ n / r := Nat.div_le_div_left (by omega) (by omega)
    omega
  · -- (T,F) r+1 main, r small: 2r+3 ≤ n but ¬ 2r+1 ≤ n, contradiction
    omega
  · -- (F,T) r+1 small (n ≤ 2r+2), r main (2r+1 ≤ n): the hard case
    have hn2r : 2 ≤ n / r := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    have hstep := turan_step (n := n) (r := r) (d := n - 1) (by omega) (by omega)
    have haddv := turan_addvertex n r (by omega) (by omega)
    -- turan_step: t_r(n-1) + (n-1)*(n-(n-1)) ≤ t_{r+1}(n); (n-(n-1)) = 1
    rw [show n - (n - 1) = 1 by omega, Nat.mul_one] at hstep
    omega
  · -- (F,F) both small
    omega

/-- **Base case for the singleton/empty guard arithmetic** (`[s, c]`, `r = 2`).
`2·(s·c) + 2·kpSaving (s+c) 2 ≤ 2·t_2(s+c) + s·(c−1)` for `s ≤ 1`, `c ≥ 3`. -/
theorem baseAB (s c : ℕ) (hs : s ≤ 1) (hc : 3 ≤ c) :
    2 * (s * c) + 2 * kpSaving (s + c) 2
      ≤ 2 * (turanGraph (s + c) 2).edgeFinset.card + s * (c - 1) := by
  -- helper: `2·kpSaving m 2 ≤ 2·t_2(m) + (m·(m%2 has been handled))` machinery via two_mul_turan
  have turandbl : ∀ m : ℕ, 3 ≤ m →
      2 * (turanGraph m 2).edgeFinset.card = m / 2 * (m + m % 2) := by
    intro m hm
    have hT := two_mul_turan m 2 (by omega)
    simp only [show (2:ℕ) - 1 = 1 from rfl, Nat.mul_one] at hT
    have hterm0 : m % 2 * (m % 2 - 1) = 0 := by
      rcases (show m % 2 = 0 ∨ m % 2 = 1 from by omega) with h | h <;> rw [h]
    rw [hterm0, Nat.add_zero] at hT; exact hT
  interval_cases s
  · -- s = 0: goal 2·kpSaving c 2 ≤ 2·t_2(c)
    rw [turandbl (0 + c) (by omega)]
    simp only [Nat.zero_add, Nat.zero_mul, Nat.mul_zero, Nat.add_zero]
    have hdm : 2 * (c / 2) + c % 2 = c := Nat.div_add_mod c 2
    have hmod : c % 2 < 2 := Nat.mod_lt c (by omega)
    simp only [kpSaving]
    split_ifs with hmain
    · have hQ2 : 2 ≤ c / 2 := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
      have h2 : c / 2 * 2 ≤ c / 2 * (c + c % 2) := Nat.mul_le_mul (le_refl _) (by omega)
      omega
    · have hc4 : c ≤ 4 := by omega
      interval_cases c <;> omega
  · -- s = 1: goal 2·c + 2·kpSaving (1+c) 2 ≤ 2·t_2(1+c) + (c-1)
    rw [turandbl (1 + c) (by omega)]
    simp only [Nat.one_mul, Nat.mul_one]
    have hdm : 2 * ((1 + c) / 2) + (1 + c) % 2 = 1 + c := Nat.div_add_mod (1 + c) 2
    have hmod : (1 + c) % 2 < 2 := Nat.mod_lt (1 + c) (by omega)
    simp only [kpSaving]
    split_ifs with hmain
    · have hQ2 : 2 ≤ (1 + c) / 2 := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
      have h3 : (1 + c) / 2 * 4 ≤ (1 + c) / 2 * ((1 + c) + (1 + c) % 2) :=
        Nat.mul_le_mul (le_refl _) (by omega)
      omega
    · have hc4 : c ≤ 3 := by omega
      interval_cases c <;> omega

/-- **Singleton/empty guard arithmetic (peel form).** For any middle list `L`
(parts ≥ 0), special part `s ≤ 1`, and last part `c ≥ 3`:
`2·σ₂(s::c::L) + 2·kpSaving n r ≤ 2·t_r(n) + s·(c−1)` where `n = (s::c::L).sum`,
`r = (s::c::L).length`. Peels the head of `L`: a `0` head via `m0_lift`, a positive
head via `caseA_slack` (the `s,c` tail rides along; base `[s,c]` via `baseAB`). -/
theorem sig2AB_core (s c : ℕ) (hs : s ≤ 1) (hc : 3 ≤ c) : ∀ (L : List ℕ),
    2 * sig2 (s :: c :: L) + 2 * kpSaving (s :: c :: L).sum (s :: c :: L).length
      ≤ 2 * (turanGraph (s :: c :: L).sum (s :: c :: L).length).edgeFinset.card + s * (c - 1) := by
  intro L
  induction L with
  | nil =>
    simp only [sig2_cons, sig2_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
    have hb := baseAB s c hs hc
    convert hb using 3 <;> ring
  | cons a L' IH =>
    by_cases ha : a = 0
    · -- a = 0: remove the empty block via m0_lift
      subst ha
      have hsig0 : sig2 (s :: c :: 0 :: L') = sig2 (s :: c :: L') := by
        simp only [sig2_cons, List.sum_cons]; ring
      have hsum0 : (s :: c :: 0 :: L').sum = (s :: c :: L').sum := by
        simp only [List.sum_cons]; ring
      have hlen0 : (s :: c :: 0 :: L').length = (s :: c :: L').length + 1 := by
        simp only [List.length_cons]
      have hm0 := m0_lift ((s :: c :: L').sum) ((s :: c :: L').length)
        (by simp only [List.length_cons]; omega)
      rw [hsig0, hsum0, hlen0]
      omega
    · -- a ≥ 1: peel via caseA_slack
      have ha1 : 1 ≤ a := by omega
      have hdpos : 0 < (s :: c :: L').sum := by simp only [List.sum_cons]; omega
      have hslack := caseA_slack (n := (s :: c :: a :: L').sum)
        (r := (s :: c :: a :: L').length) (d := (s :: c :: L').sum)
        (by simp only [List.length_cons]; omega) hdpos
        (by simp only [List.sum_cons]; omega)
      rw [(by simp only [List.length_cons]; omega :
            (s :: c :: a :: L').length - 1 = (s :: c :: L').length),
          (by simp only [List.sum_cons]; omega :
            (s :: c :: a :: L').sum - (s :: c :: L').sum = a)] at hslack
      have hsig : sig2 (s :: c :: a :: L') = sig2 (s :: c :: L') + a * (s :: c :: L').sum := by
        simp only [sig2_cons, List.sum_cons]; ring
      have hmul : (s :: c :: L').sum * a = a * (s :: c :: L').sum := by ring
      rw [hsig]
      omega

/-- **Some-part-≤1 guard closure (Route MI).** In Case B with `x` of max degree, the
`(r−1)`-colouring `κ` of `G[Γx]`, and a colour class `D_{i0}` of size `≤ 1`, the KP bound
`e(G) + kpSaving n r ≤ t_r(n)` holds. Closes by `main_ineq` once `c ≥ 3`, then the
singleton/empty arithmetic `sig2AB_core`. -/
theorem guard_somepart_closure {n r : ℕ} (hr : 2 ≤ r) (G : SimpleGraph (Fin n)) (x : Fin n)
    (hCF : G.CliqueFree (r + 1)) (hchi : ¬ G.Colorable r)
    (hmax : ∀ y, G.degree y ≤ G.degree x)
    (κ : Fin n → Fin (r - 1))
    (hproper : ∀ u ∈ G.neighborFinset x, ∀ v ∈ G.neighborFinset x, G.Adj u v → κ u ≠ κ v)
    (hDindep : ∀ i : Fin (r - 1), ∀ u ∈ (G.neighborFinset x).filter (κ · = i),
      ∀ w ∈ (G.neighborFinset x).filter (κ · = i), ¬ G.Adj u w)
    (hcguard : 2 ≤ n - (G.neighborFinset x).card)
    (i0 : Fin (r - 1)) (hi0 : ((G.neighborFinset x).filter (κ · = i0)).card < 2) :
    edgeCountIn G Finset.univ + kpSaving n r ≤ (turanGraph n r).edgeFinset.card := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  set D := G.neighborFinset x with hD
  set c := n - D.card with hc
  have hDn : D.card ≤ n := by
    rw [hD]; calc (G.neighborFinset x).card ≤ (Finset.univ : Finset (Fin n)).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = n := by rw [Finset.card_univ, Fintype.card_fin]
  -- (0) c ≥ 3
  have hc3 : 3 ≤ c := by
    by_contra hlt
    apply hchi
    apply colorable_of_C_indep hr G x κ hproper
    intro u hu v hv hadj
    have hux : u ≠ x := by
      intro h; apply hv; rw [SimpleGraph.mem_neighborFinset]; rw [h] at hadj; exact hadj
    have hvx : v ≠ x := by
      intro h; apply hu; rw [SimpleGraph.mem_neighborFinset]; rw [h] at hadj; exact hadj.symm
    have hxD : x ∉ D := by rw [hD]; simp [SimpleGraph.mem_neighborFinset]
    have hsub : ({x, u, v} : Finset (Fin n)) ⊆ Finset.univ \ D := by
      intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_sdiff]; refine ⟨Finset.mem_univ _, ?_⟩
      rcases hw with rfl | rfl | rfl; exacts [hxD, hu, hv]
    have hcard3 : ({x, u, v} : Finset (Fin n)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by
            simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
            exact ⟨hux.symm, hvx.symm⟩),
          Finset.card_insert_of_notMem (by
            simp only [Finset.mem_singleton]; exact G.ne_of_adj hadj),
          Finset.card_singleton]
    have h3le : 3 ≤ (Finset.univ \ D).card := hcard3 ▸ Finset.card_le_card hsub
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin] at h3le
    omega
  -- (1) main_ineq
  have hmain := main_ineq G x hmax κ hDindep
  rw [← hD] at hmain
  set p : Fin (m + 2 - 1) → ℕ := fun i => (D.filter (κ · = i)).card with hp
  -- blocks = ofFn p ++ [c]; matched to  (p i0) :: c :: L  via sum & sqsum equality
  set L : List ℕ := List.ofFn (fun j : Fin m => p (i0.succAbove j)) with hL
  have hsplit_sum : ∑ i, p i = p i0 + ∑ j : Fin m, p (i0.succAbove j) :=
    Fin.sum_univ_succAbove p i0
  have hsplit_sq : ∑ i, p i * p i
      = p i0 * p i0 + ∑ j : Fin m, p (i0.succAbove j) * p (i0.succAbove j) :=
    Fin.sum_univ_succAbove (fun i => p i * p i) i0
  have hLsum : L.sum = ∑ j : Fin m, p (i0.succAbove j) := by rw [hL, List.sum_ofFn]
  have hLsq : sqsum L = ∑ j : Fin m, p (i0.succAbove j) * p (i0.succAbove j) := by
    rw [hL, sqsum_ofFn]
  -- sum & sqsum of blocks vs  (p i0 :: c :: L)
  have hblk_sum : (List.ofFn p ++ [c]).sum = (p i0 :: c :: L).sum := by
    simp only [List.sum_append, List.sum_ofFn, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [hLsum, hsplit_sum]; ring
  have hblk_sq : sqsum (List.ofFn p ++ [c]) = sqsum (p i0 :: c :: L) := by
    simp only [sqsum_append, sqsum_ofFn, sqsum_cons, sqsum_nil, Nat.add_zero]
    rw [hLsq, hsplit_sq]; ring
  have hsigeq : sig2 (List.ofFn p ++ [c]) = sig2 (p i0 :: c :: L) := by
    have e1 := two_mul_sig2 (List.ofFn p ++ [c])
    have e2 := two_mul_sig2 (p i0 :: c :: L)
    rw [← sqsum_eq_pow] at e1 e2
    rw [hblk_sum, hblk_sq] at e1
    omega
  -- lengths & total sum
  have hpsum : ∑ i, p i = D.card := by
    rw [hp]; exact (Finset.card_eq_sum_card_fiberwise (fun v _ => Finset.mem_univ (κ v))).symm
  have hLlen : L.length = m := by rw [hL, List.length_ofFn]
  have hsumn : (p i0 :: c :: L).sum = n := by
    rw [← hblk_sum]
    simp only [List.sum_append, List.sum_ofFn, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [hpsum, hc]; omega
  have hlenr : (p i0 :: c :: L).length = m + 2 := by
    simp only [List.length_cons, hLlen]
  -- (2) the singleton/empty arithmetic
  have hsle : p i0 ≤ 1 := by rw [hp]; exact Nat.lt_succ_iff.mp hi0
  have hAB := sig2AB_core (p i0) c hsle hc3 L
  rw [hsumn, hlenr] at hAB
  -- (2') deficiency lower bound  p i0 * (c-1) ≤ Σ defc   (unifies singleton & empty)
  have hdeflb : p i0 * (c - 1)
      ≤ ∑ v ∈ D, (n - (D.filter (κ · = κ v)).card - G.degree v) := by
    rcases Nat.eq_zero_or_pos (p i0) with h0 | hpos
    · rw [h0]; simp
    · -- p i0 = 1: singleton {w}
      have hpeq : p i0 = (D.filter (κ · = i0)).card := rfl
      have hpi1 : p i0 = 1 := by omega
      have hcard1 : (D.filter (κ · = i0)).card = 1 := by rw [← hpeq]; exact hpi1
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard1
      have hwmem : w ∈ D.filter (κ · = i0) := by rw [hw]; exact Finset.mem_singleton_self w
      have hwD : w ∈ D := (Finset.mem_filter.mp hwmem).1
      have hwi0 : κ w = i0 := (Finset.mem_filter.mp hwmem).2
      have hdegw : G.degree w ≤ D.card := by
        rw [hD, G.card_neighborFinset_eq_degree]; exact hmax w
      have hfilw : (D.filter (κ · = κ w)).card = 1 := by rw [hwi0]; exact hcard1
      have hdefw : c - 1 ≤ n - (D.filter (κ · = κ w)).card - G.degree w := by
        rw [hfilw]; omega
      calc p i0 * (c - 1) = c - 1 := by rw [hpi1, Nat.one_mul]
        _ ≤ n - (D.filter (κ · = κ w)).card - G.degree w := hdefw
        _ ≤ ∑ v ∈ D, (n - (D.filter (κ · = κ v)).card - G.degree v) :=
            Finset.single_le_sum
              (f := fun v => n - (D.filter (κ · = κ v)).card - G.degree v)
              (fun i _ => Nat.zero_le _) hwD
  -- combine: 2e + Σdefc ≤ 2·sig2 blocks = 2·sig2(pi0::c::L) ≤ 2·t + (p i0)(c-1)
  rw [hsigeq] at hmain
  omega


/-- **Sub-lemma B–E core.** Case B of KP Thm 4 with the `(r−1)`-colouring `κ` supplied
directly. Good/bad dichotomy: ≥2 bad parts or one all-≥2-miss bad part ⇒ `caseB_close`;
all good ⇒ `Kr+1`/`χ≤r` contra; unique bad with a `1`-miss vertex, or a small part ⇒
`kp_lemma3`. -/
theorem kp_caseB_impl (hr : 2 ≤ r) (G : SimpleGraph (Fin n)) (x : Fin n) (hn : r + 3 ≤ n)
    (hCF : G.CliqueFree (r + 1)) (hchi : ¬ G.Colorable r)
    (hmax : ∀ y, G.degree y ≤ G.degree x)
    (κ : Fin n → Fin (r - 1))
    (hproper : ∀ u ∈ G.neighborFinset x, ∀ v ∈ G.neighborFinset x, G.Adj u v → κ u ≠ κ v) :
    edgeCountIn G Finset.univ + kpSaving n r ≤ (turanGraph n r).edgeFinset.card := by
  set D := G.neighborFinset x with hD
  have hDindep : ∀ i : Fin (r - 1), ∀ u ∈ D.filter (κ · = i),
      ∀ w ∈ D.filter (κ · = i), ¬ G.Adj u w := by
    intro i u hu w hw hadj
    obtain ⟨huD, hui⟩ := Finset.mem_filter.mp hu
    obtain ⟨hwD, hwi⟩ := Finset.mem_filter.mp hw
    exact hproper u huD w hwD hadj (hui.trans hwi.symm)
  -- deficiency of `v`: number of non-neighbours outside its own part
  set defc : Fin n → ℕ := fun v => n - (D.filter (κ · = κ v)).card - G.degree v with hdefc
  by_cases hcguard : 2 ≤ n - D.card
  · -- c ≥ 2
    by_cases hpartguard : ∀ i : Fin (r - 1), 2 ≤ (D.filter (κ · = i)).card
    · -- all parts ≥ 2 and c ≥ 2: good/bad
      -- minimum block m
      obtain ⟨m, hmmem, hmle⟩ := list_has_min
        ((List.ofFn fun i : Fin (r - 1) => (D.filter (κ · = i)).card) ++ [n - D.card])
        (by simp)
      have hmle_part : ∀ i : Fin (r - 1), m ≤ (D.filter (κ · = i)).card := by
        intro i; apply hmle; rw [List.mem_append]; left; rw [List.mem_ofFn]; exact ⟨i, rfl⟩
      have hmle_c : m ≤ n - D.card := by
        apply hmle; rw [List.mem_append]; right; exact List.mem_singleton.mpr rfl
      have hm_mem_form : (∃ i : Fin (r - 1), (D.filter (κ · = i)).card = m) ∨ n - D.card = m := by
        rw [List.mem_append] at hmmem
        rcases hmmem with h | h
        · rw [List.mem_ofFn] at h; obtain ⟨i, hi⟩ := h; exact Or.inl ⟨i, hi⟩
        · exact Or.inr (List.mem_singleton.mp h).symm
      -- Σ over any part of `defc`
      have hpartsum : ∀ (i : Fin (r - 1)), (∀ v ∈ D.filter (κ · = i), 1 ≤ defc v) →
          (D.filter (κ · = i)).card ≤ ∑ v ∈ D.filter (κ · = i), defc v := by
        intro i hbad
        calc (D.filter (κ · = i)).card = ∑ _v ∈ D.filter (κ · = i), 1 := by
              rw [Finset.sum_const, smul_eq_mul, mul_one]
          _ ≤ _ := Finset.sum_le_sum (fun v hv => hbad v hv)
      have hpartsub : ∀ i : Fin (r - 1),
          ∑ v ∈ D.filter (κ · = i), defc v ≤ ∑ v ∈ D, defc v :=
        fun i => Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      -- good/bad count
      by_cases hallgood : ∀ i : Fin (r - 1), ∃ v ∈ D.filter (κ · = i), defc v = 0
      · -- all good ⇒ contra (Kr+1 if C has an edge, else χ ≤ r)
        exfalso
        choose y hy hdefy using hallgood
        have hydeg : ∀ i, G.degree (y i) = n - (D.filter (κ · = i)).card := by
          intro i
          have hyi : κ (y i) = i := (Finset.mem_filter.mp (hy i)).2
          have h0 : n - (D.filter (κ · = i)).card - G.degree (y i) = 0 := by
            have hh := hdefy i; simp only [hdefc] at hh; rw [hyi] at hh; exact hh
          have hle : G.degree (y i) ≤ n - (D.filter (κ · = i)).card := by
            have := degree_le_of_part G κ D hDindep (Finset.mem_filter.mp (hy i)).1
            rwa [hyi] at this
          omega
        have hyadj : ∀ (i : Fin (r - 1)) (w : Fin n), w ∉ D.filter (κ · = i) → G.Adj (y i) w :=
          fun i w hw => good_witness_adj G x κ hDindep i (y i) (hy i) (hydeg i) w hw
        have hyinj : Function.Injective y := by
          intro i j hij
          have hyi : κ (y i) = i := (Finset.mem_filter.mp (hy i)).2
          have hyj : κ (y j) = j := (Finset.mem_filter.mp (hy j)).2
          rw [← hyi, hij, hyj]
        have hnotDi : ∀ (i j : Fin (r - 1)), i ≠ j → y j ∉ D.filter (κ · = i) := by
          intro i j hij hmem
          apply hij
          rw [← (Finset.mem_filter.mp hmem).2]; exact (Finset.mem_filter.mp (hy j)).2
        set K := Finset.univ.image y with hK
        have hKcard : K.card = r - 1 := by
          rw [hK, Finset.card_image_of_injective _ hyinj, Finset.card_univ, Fintype.card_fin]
        have hKclq : G.IsClique ↑K := by
          intro a ha b hb hab
          rw [Finset.mem_coe, hK, Finset.mem_image] at ha hb
          obtain ⟨i, _, rfl⟩ := ha
          obtain ⟨j, _, rfl⟩ := hb
          exact hyadj i (y j) (hnotDi i j (fun h => hab (by rw [h])))
        by_cases hCedge : ∃ a b, a ∉ D ∧ b ∉ D ∧ G.Adj a b
        · obtain ⟨a, b, haD, hbD, hadjab⟩ := hCedge
          have haK : a ∉ K := by
            rw [hK, Finset.mem_image]; rintro ⟨i, _, rfl⟩; exact haD (Finset.mem_filter.mp (hy i)).1
          have hbK : b ∉ K := by
            rw [hK, Finset.mem_image]; rintro ⟨i, _, rfl⟩; exact hbD (Finset.mem_filter.mp (hy i)).1
          have haKadj : ∀ w ∈ K, G.Adj a w := by
            intro w hw; rw [hK, Finset.mem_image] at hw; obtain ⟨i, _, rfl⟩ := hw
            exact (hyadj i a (fun hh => haD (Finset.mem_filter.mp hh).1)).symm
          have hbKadj : ∀ w ∈ K, G.Adj b w := by
            intro w hw; rw [hK, Finset.mem_image] at hw; obtain ⟨i, _, rfl⟩ := hw
            exact (hyadj i b (fun hh => hbD (Finset.mem_filter.mp hh).1)).symm
          exact no_Kr_plus_edge G (by omega) hCF K hKclq hKcard a b haK hbK
            (G.ne_of_adj hadjab) haKadj hbKadj hadjab
        · apply hchi
          apply colorable_of_C_indep hr G x κ hproper
          intro u hu v hv hadj
          exact hCedge ⟨u, v, hu, hv, hadj⟩
      · -- ∃ bad part
        push_neg at hallgood
        obtain ⟨i0, hi0bad0⟩ := hallgood
        -- i0 bad: every v in part i0 has defc ≥ 1
        have hi0bad : ∀ v ∈ D.filter (κ · = i0), 1 ≤ defc v := by
          intro v hv
          have := hi0bad0 v hv
          omega
        have htwopart : ∀ (i j : Fin (r - 1)), i ≠ j →
            (∀ v ∈ D.filter (κ · = i), 1 ≤ defc v) → (∀ v ∈ D.filter (κ · = j), 1 ≤ defc v) →
            (D.filter (κ · = i)).card + (D.filter (κ · = j)).card ≤ ∑ v ∈ D, defc v := by
          intro i j hij hbi hbj
          have hdisj : Disjoint (D.filter (κ · = i)) (D.filter (κ · = j)) := by
            rw [Finset.disjoint_left]; intro v hvi hvj
            exact hij ((Finset.mem_filter.mp hvi).2.symm.trans (Finset.mem_filter.mp hvj).2)
          have hsub : D.filter (κ · = i) ∪ D.filter (κ · = j) ⊆ D := by
            intro v hv; rw [Finset.mem_union] at hv
            rcases hv with h | h <;> exact (Finset.mem_filter.mp h).1
          calc (D.filter (κ · = i)).card + (D.filter (κ · = j)).card
              ≤ (∑ v ∈ D.filter (κ · = i), defc v) + (∑ v ∈ D.filter (κ · = j), defc v) :=
                Nat.add_le_add (hpartsum i hbi) (hpartsum j hbj)
            _ = ∑ v ∈ D.filter (κ · = i) ∪ D.filter (κ · = j), defc v := (Finset.sum_union hdisj).symm
            _ ≤ ∑ v ∈ D, defc v := Finset.sum_le_sum_of_subset hsub
        by_cases hsecond : ∃ j : Fin (r - 1), j ≠ i0 ∧ ∀ v ∈ D.filter (κ · = j), 1 ≤ defc v
        · -- two bad parts ⇒ caseB_close
          obtain ⟨j, hji0, hjbad⟩ := hsecond
          apply caseB_close hr G x hmax κ hDindep hpartguard hcguard m hmle_part hmle_c hm_mem_form
          change 2 * m ≤ ∑ v ∈ D, defc v
          have h1 := htwopart i0 j (Ne.symm hji0) hi0bad hjbad
          have hmi0 := hmle_part i0
          have hmj := hmle_part j
          omega
        · -- i0 unique bad
          by_cases hall2 : ∀ v ∈ D.filter (κ · = i0), 2 ≤ defc v
          · -- every vertex of i0 misses ≥ 2 ⇒ caseB_close
            apply caseB_close hr G x hmax κ hDindep hpartguard hcguard m hmle_part hmle_c hm_mem_form
            change 2 * m ≤ ∑ v ∈ D, defc v
            have h1 : 2 * (D.filter (κ · = i0)).card ≤ ∑ v ∈ D.filter (κ · = i0), defc v := by
              calc 2 * (D.filter (κ · = i0)).card = ∑ _v ∈ D.filter (κ · = i0), 2 := by
                    rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
                _ ≤ _ := Finset.sum_le_sum (fun v hv => hall2 v hv)
            have h2 := hpartsub i0
            have hmi0 := hmle_part i0
            omega
          · -- ∃ v ∈ i0 with defc = 1 ⇒ unique-bad ⇒ Lemma 3
            push Not at hsecond hall2
            obtain ⟨v1, hv1mem, hv1lt⟩ := hall2
            have hv1i0 : κ v1 = i0 := (Finset.mem_filter.mp hv1mem).2
            have hv1D : v1 ∈ D := (Finset.mem_filter.mp hv1mem).1
            have hdsle : (D.filter (κ · = i0)).card ≤ n := by
              calc (D.filter (κ · = i0)).card ≤ (Finset.univ : Finset (Fin n)).card :=
                    Finset.card_le_card (Finset.subset_univ _)
                _ = n := by rw [Finset.card_univ, Fintype.card_fin]
            have hv1le : G.degree v1 ≤ n - (D.filter (κ · = i0)).card := by
              have := degree_le_of_part G κ D hDindep hv1D; rwa [hv1i0] at this
            have hv1def1 : n - (D.filter (κ · = i0)).card - G.degree v1 = 1 := by
              have hb := hi0bad v1 hv1mem
              have he : defc v1 = n - (D.filter (κ · = i0)).card - G.degree v1 := by
                simp only [hdefc]; rw [hv1i0]
              rw [he] at hb hv1lt; omega
            -- W = the single non-neighbour of v1 outside its part
            set W := (Finset.univ \ D.filter (κ · = i0)) \ G.neighborFinset v1 with hW
            have hΓsub : G.neighborFinset v1 ⊆ Finset.univ \ D.filter (κ · = i0) := by
              intro w hw; rw [Finset.mem_sdiff]; refine ⟨Finset.mem_univ _, ?_⟩
              intro hwi0; rw [SimpleGraph.mem_neighborFinset] at hw
              exact hDindep i0 w hwi0 v1 hv1mem hw.symm
            have hWcard : W.card = 1 := by
              rw [hW, Finset.card_sdiff_of_subset hΓsub, G.card_neighborFinset_eq_degree,
                ← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin]
              omega
            obtain ⟨z, hzeq⟩ := Finset.card_eq_one.mp hWcard
            have hznotDi0 : z ∉ D.filter (κ · = i0) := by
              have : z ∈ W := by rw [hzeq]; exact Finset.mem_singleton_self z
              rw [hW, Finset.mem_sdiff, Finset.mem_sdiff] at this; exact this.1.2
            have hv1adj : ∀ w, w ∉ D.filter (κ · = i0) → w ≠ z → G.Adj v1 w := by
              intro w hwi0 hwz
              have hwuniv : w ∈ Finset.univ \ D.filter (κ · = i0) := by
                rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, hwi0⟩
              have hnotW : w ∉ W := by rw [hzeq, Finset.mem_singleton]; exact hwz
              rw [hW, Finset.mem_sdiff, not_and, not_not] at hnotW
              have := hnotW hwuniv; rwa [SimpleGraph.mem_neighborFinset] at this
            -- good witnesses for j ≠ i0
            have hgoodj : ∀ j : Fin (r - 1), j ≠ i0 →
                ∃ y, y ∈ D.filter (κ · = j) ∧ G.degree y = n - (D.filter (κ · = j)).card := by
              intro j hj
              obtain ⟨y, hymem, hydef⟩ := hsecond j hj
              refine ⟨y, hymem, ?_⟩
              have hyj : κ y = j := (Finset.mem_filter.mp hymem).2
              have he : defc y = n - (D.filter (κ · = j)).card - G.degree y := by
                simp only [hdefc]; rw [hyj]
              rw [he] at hydef
              have hle := degree_le_of_part G κ D hDindep (Finset.mem_filter.mp hymem).1
              rw [hyj] at hle; omega
            -- witness map: wit i0 = v1, wit j = good witness of D_j (j ≠ i0)
            set wit : Fin (r - 1) → Fin n :=
              fun j => if h : j = i0 then v1 else (hgoodj j h).choose with hwit
            have hwit_mem : ∀ j, wit j ∈ D.filter (κ · = j) := by
              intro j; rw [hwit]; by_cases h : j = i0
              · subst h; simp only [dif_pos]; exact hv1mem
              · simp only [dif_neg h]; exact (hgoodj j h).choose_spec.1
            have hwit_good : ∀ j, j ≠ i0 → ∀ w, w ∉ D.filter (κ · = j) → G.Adj (wit j) w := by
              intro j hj w hw
              have hwitj : wit j = (hgoodj j hj).choose := by simp only [hwit, dif_neg hj]
              have hdeg : G.degree (wit j) = n - (D.filter (κ · = j)).card := by
                rw [hwitj]; exact (hgoodj j hj).choose_spec.2
              exact good_witness_adj G x κ hDindep j (wit j) (hwit_mem j) hdeg w hw
            have hwit_i0 : wit i0 = v1 := by rw [hwit]; simp only [dif_pos]
            have hwitκ : ∀ j, κ (wit j) = j := fun j => (Finset.mem_filter.mp (hwit_mem j)).2
            have hwit_inj : Function.Injective wit := by
              intro i j hij
              have hh := hwitκ i; rw [hij, hwitκ j] at hh; exact hh.symm
            have hwit_notDi : ∀ (i j : Fin (r - 1)), i ≠ j → wit j ∉ D.filter (κ · = i) := by
              intro i j hij hmem; apply hij
              rw [← (Finset.mem_filter.mp hmem).2]; exact (hwitκ j)
            set K := Finset.univ.image wit with hK
            have hKcard : K.card = r - 1 := by
              rw [hK, Finset.card_image_of_injective _ hwit_inj, Finset.card_univ, Fintype.card_fin]
            have hKclq : G.IsClique ↑K := by
              intro a ha b hb hab
              rw [Finset.mem_coe, hK, Finset.mem_image] at ha hb
              obtain ⟨i, _, rfl⟩ := ha; obtain ⟨j, _, rfl⟩ := hb
              have hij : i ≠ j := fun h => hab (by rw [h])
              by_cases hi : i = i0
              · have hj0 : j ≠ i0 := fun h => hij (hi.trans h.symm)
                exact (hwit_good j hj0 (wit i) (hwit_notDi j i (fun h => hij h.symm))).symm
              · exact hwit_good i hi (wit j) (hwit_notDi i j hij)
            -- v1's unique miss z ∉ Γ(v1)
            have hzv1 : ¬ G.Adj v1 z := by
              have hzW : z ∈ W := by rw [hzeq]; exact Finset.mem_singleton_self z
              rw [hW, Finset.mem_sdiff, Finset.mem_sdiff] at hzW
              intro hh; exact hzW.2 (by rw [SimpleGraph.mem_neighborFinset]; exact hh)
            -- every K-vertex is adjacent to every vertex outside D except possibly z
            have hKadj : ∀ a ∈ K, ∀ w, w ∉ D → w ≠ z → G.Adj a w := by
              intro a ha w hwD hwz
              rw [hK, Finset.mem_image] at ha; obtain ⟨j, _, rfl⟩ := ha
              by_cases hj : j = i0
              · rw [hj, hwit_i0]
                exact hv1adj w (fun hh => hwD (Finset.mem_filter.mp hh).1) hwz
              · exact hwit_good j hj w (fun hh => hwD (Finset.mem_filter.mp hh).1)
            have hnotinK : ∀ a, a ∉ D → a ∉ K := by
              intro a haD hh; rw [hK, Finset.mem_image] at hh
              obtain ⟨j, _, rfl⟩ := hh; exact haD (Finset.mem_filter.mp (hwit_mem j)).1
            by_cases hzD : z ∈ D
            · -- z ∈ D ⇒ K adjacent to all C ⇒ Kr+1 (C-edge) or χ ≤ r (contra)
              exfalso
              by_cases hCedge : ∃ a b, a ∉ D ∧ b ∉ D ∧ G.Adj a b
              · obtain ⟨a, b, haD, hbD, hadjab⟩ := hCedge
                have haz : a ≠ z := fun h => haD (h ▸ hzD)
                have hbz : b ≠ z := fun h => hbD (h ▸ hzD)
                exact no_Kr_plus_edge G (by omega) hCF K hKclq hKcard a b (hnotinK a haD)
                  (hnotinK b hbD) (G.ne_of_adj hadjab)
                  (fun w hw => (hKadj w hw a haD haz).symm)
                  (fun w hw => (hKadj w hw b hbD hbz).symm) hadjab
              · apply hchi
                apply colorable_of_C_indep hr G x κ hproper
                intro u hu v hv hadj
                exact hCedge ⟨u, v, hu, hv, hadj⟩
            · -- z ∉ D ⇒ z ∈ C. K adjacent to C∖{z} ⇒ Kr+1 (edge in C∖{z}) or Lemma 3
              by_cases hCzedge : ∃ a b, a ∉ D ∧ a ≠ z ∧ b ∉ D ∧ b ≠ z ∧ G.Adj a b
              · exfalso
                obtain ⟨a, b, haD, haz, hbD, hbz, hadjab⟩ := hCzedge
                exact no_Kr_plus_edge G (by omega) hCF K hKclq hKcard a b (hnotinK a haD)
                  (hnotinK b hbD) (G.ne_of_adj hadjab)
                  (fun w hw => (hKadj w hw a haD haz).symm)
                  (fun w hw => (hKadj w hw b hbD hbz).symm) hadjab
              · -- C∖{z} independent ⇒ G−z is r-colourable ⇒ Lemma 3
                apply kp_lemma3 hr G hn hCF hchi z
                  (fun w => if w ∈ D then (⟨(κ w).val, by omega⟩ : Fin r) else (⟨r - 1, by omega⟩ : Fin r))
                intro u v huz hvz hadj
                split_ifs with hu hv hv
                · intro heq; rw [Fin.mk.injEq] at heq
                  exact hproper u hu v hv hadj (Fin.ext heq)
                · intro heq; rw [Fin.mk.injEq] at heq
                  have h1 : (κ u).val < r - 1 := (κ u).isLt; omega
                · intro heq; rw [Fin.mk.injEq] at heq
                  have h1 : (κ v).val < r - 1 := (κ v).isLt; omega
                · exact absurd ⟨u, v, hu, huz, hv, hvz, hadj⟩ hCzedge
    · -- some part ≤ 1 ⇒ guard closes via main_ineq + c ≥ 3 (Route MI, no max-size)
      push_neg at hpartguard
      obtain ⟨i0, hi0⟩ := hpartguard
      exact guard_somepart_closure hr G x hCF hchi hmax κ hproper hDindep hcguard i0 hi0
  · -- c ≤ 1 ⇒ colourable ⇒ contra
    exfalso
    apply hchi
    apply colorable_of_C_indep hr G x κ hproper
    intro u hu v hv hadj
    have huv : u ≠ v := G.ne_of_adj hadj
    have hsub : ({u, v} : Finset (Fin n)) ⊆ Finset.univ \ D := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_sdiff]
      exact ⟨Finset.mem_univ _, by rcases hw with rfl | rfl; exacts [hu, hv]⟩
    have h2 : 2 ≤ (Finset.univ \ D).card := by
      calc 2 = ({u, v} : Finset (Fin n)).card := (Finset.card_pair huv).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hCcard : (Finset.univ \ D).card = n - D.card := by
      rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin]
    omega

end CaseBGoodBad

/-! ## Small-`n` emptiness: `Gₙ,ᵣ = ∅` for `n ≤ r+2` (KP side condition)

Gives `hn : r+3 ≤ n` at every Case-B entry (from `¬G.Colorable r`). Foundations:
`colorable_of_proper_on` (colour a special set with `k` colours + inject the rest),
`colorable_of_indep`, `exists_nonedge`. The `n = r+2` case is the star/two-disjoint-
non-edges argument (a complement-empty or star complement forces a `K_{r+1}`). -/

/-- **Colour a special set + inject the rest.** If `c₀` properly colours the pairs
inside `T` with `k` colours, then `G` is `(k + (n − |T|))`-colourable: keep `c₀` on `T`
(colours `< k`), give every vertex outside `T` its own fresh colour `≥ k`. -/
theorem colorable_of_proper_on {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n))
    {k : ℕ} (c₀ : Fin n → Fin k)
    (hproper : ∀ u ∈ T, ∀ v ∈ T, G.Adj u v → c₀ u ≠ c₀ v) :
    G.Colorable (k + (n - T.card)) := by
  classical
  set m := n - T.card with hm
  have hcard : (Tᶜ : Finset (Fin n)).card = m := by
    rw [hm, Finset.card_compl, Fintype.card_fin]
  let e : (Tᶜ : Finset (Fin n)) ≃ Fin m := Finset.equivFinOfCardEq hcard
  refine ⟨SimpleGraph.Coloring.mk (fun v =>
      if h : v ∈ T then Fin.castAdd m (c₀ v)
      else Fin.natAdd k (e ⟨v, Finset.mem_compl.mpr h⟩)) ?_⟩
  intro u v hadj
  have huv : u ≠ v := G.ne_of_adj hadj
  by_cases hu : u ∈ T <;> by_cases hv : v ∈ T
  · simp only [dif_pos hu, dif_pos hv]
    intro heq
    have hval := congrArg Fin.val heq
    simp only [Fin.coe_castAdd] at hval
    exact hproper u hu v hv hadj (Fin.val_injective hval)
  · simp only [dif_pos hu, dif_neg hv]
    intro heq
    have hval := congrArg Fin.val heq
    simp only [Fin.coe_castAdd, Fin.coe_natAdd] at hval
    have := (c₀ u).isLt
    omega
  · simp only [dif_neg hu, dif_pos hv]
    intro heq
    have hval := congrArg Fin.val heq
    simp only [Fin.coe_castAdd, Fin.coe_natAdd] at hval
    have := (c₀ v).isLt
    omega
  · simp only [dif_neg hu, dif_neg hv]
    intro heq
    have h2 : (⟨u, Finset.mem_compl.mpr hu⟩ : (Tᶜ : Finset (Fin n)))
        = ⟨v, Finset.mem_compl.mpr hv⟩ := by
      apply e.injective
      have hval := congrArg Fin.val heq
      simp only [Fin.coe_natAdd] at hval
      exact Fin.val_injective (by omega)
    exact huv (Subtype.ext_iff.mp h2)

/-- **Merge one independent set.** An independent `T` gives `Colorable (1 + (n − |T|))`. -/
theorem colorable_of_indep {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n))
    (hindep : ∀ u ∈ T, ∀ v ∈ T, ¬ G.Adj u v) :
    G.Colorable (1 + (n - T.card)) := by
  apply colorable_of_proper_on G T (k := 1) (fun _ => 0)
  intro u hu v hv hadj
  exact absurd hadj (hindep u hu v hv)

/-- A `K_k`-free graph on `Fin m` with `k ≤ m` has a non-edge. -/
theorem exists_nonedge {m k : ℕ} (hk : k ≤ m) (G : SimpleGraph (Fin m))
    (hCF : G.CliqueFree k) : ∃ a b : Fin m, a ≠ b ∧ ¬ G.Adj a b := by
  by_contra h
  push_neg at h
  obtain ⟨s, _, hs⟩ : ∃ t ⊆ (Finset.univ : Finset (Fin m)), t.card = k :=
    Finset.exists_subset_card_eq (by rw [Finset.card_univ, Fintype.card_fin]; exact hk)
  exact hCF s ⟨fun a _ b _ hab => h a b hab, hs⟩

/-- **`Gₙ,ᵣ = ∅` for `n ≤ r+2`.** A `K_{r+1}`-free graph on `≤ r+2` vertices is
`r`-colourable. (Contrapositive: `¬Colorable r ⇒ r+3 ≤ n`.) -/
theorem gnr_colorable_small {n r : ℕ} (hr : 1 ≤ r) (hn : n ≤ r + 2)
    (G : SimpleGraph (Fin n)) (hCF : G.CliqueFree (r + 1)) : G.Colorable r := by
  classical
  rcases Nat.lt_or_ge n (r + 1) with hlt | hge
  · have hcol := G.colorable_of_fintype
    rw [Fintype.card_fin] at hcol
    exact hcol.mono (by omega)
  · obtain ⟨a, b, hab, hnab⟩ := exists_nonedge (k := r + 1) (by omega) G hCF
    rcases Nat.lt_or_ge n (r + 2) with hlt2 | hge2
    · have hind : ∀ u ∈ ({a, b} : Finset (Fin n)), ∀ v ∈ ({a, b} : Finset (Fin n)),
          ¬ G.Adj u v := by
        intro u hu v hv hadj
        have huv := G.ne_of_adj hadj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
        rcases hu with hu | hu <;> rcases hv with hv | hv <;> subst u <;> subst v
        · exact huv rfl
        · exact hnab hadj
        · exact hnab hadj.symm
        · exact huv rfl
      have hcol := colorable_of_indep G {a, b} hind
      rw [Finset.card_pair hab] at hcol
      exact hcol.mono (by omega)
    · have hn2 : n = r + 2 := by omega
      by_cases htriple : ∃ c d f : Fin n, c ≠ d ∧ c ≠ f ∧ d ≠ f ∧
          ¬ G.Adj c d ∧ ¬ G.Adj c f ∧ ¬ G.Adj d f
      · obtain ⟨c, d, f, hcd, hcf, hdf, hncd, hncf, hndf⟩ := htriple
        have hind : ∀ u ∈ ({c, d, f} : Finset (Fin n)), ∀ v ∈ ({c, d, f} : Finset (Fin n)),
            ¬ G.Adj u v := by
          intro u hu v hv hadj
          have huv := G.ne_of_adj hadj
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
          rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv <;> subst u <;> subst v <;>
            first
            | exact huv rfl
            | exact hncd hadj | exact hncd hadj.symm
            | exact hncf hadj | exact hncf hadj.symm
            | exact hndf hadj | exact hndf hadj.symm
        have hcol := colorable_of_indep G {c, d, f} hind
        have hTcard : ({c, d, f} : Finset (Fin n)).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [hcd, hcf]),
            Finset.card_insert_of_notMem (by simp [hdf]), Finset.card_singleton]
        rw [hTcard] at hcol
        exact hcol.mono (by omega)
      · by_cases h2disj : ∃ c d f g : Fin n, c ≠ d ∧ f ≠ g ∧ c ≠ f ∧ c ≠ g ∧ d ≠ f ∧ d ≠ g ∧
            ¬ G.Adj c d ∧ ¬ G.Adj f g
        · obtain ⟨c, d, f, g, hcd, hfg, hcf, hcg, hdf, hdg, hncd, hnfg⟩ := h2disj
          have hcol := colorable_of_proper_on G {c, d, f, g}
            (k := 2) (fun v => if v = c ∨ v = d then 0 else 1) ?_
          · have hTcard : ({c, d, f, g} : Finset (Fin n)).card = 4 := by
              rw [Finset.card_insert_of_notMem (by simp [hcd, hcf, hcg]),
                Finset.card_insert_of_notMem (by simp [hdf, hdg]),
                Finset.card_insert_of_notMem (by simp [hfg]), Finset.card_singleton]
            rw [hTcard] at hcol
            have h4n : 4 ≤ n := by
              have hle := Finset.card_le_univ ({c, d, f, g} : Finset (Fin n))
              rw [hTcard, Fintype.card_fin] at hle; exact hle
            exact hcol.mono (by omega)
          · intro u hu v hv hadj
            have huv := G.ne_of_adj hadj
            simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
            by_cases hucd : u = c ∨ u = d <;> by_cases hvcd : v = c ∨ v = d
            · exfalso
              rcases hucd with hu' | hu' <;> rcases hvcd with hv' | hv' <;>
                subst u <;> subst v
              · exact huv rfl
              · exact hncd hadj
              · exact hncd hadj.symm
              · exact huv rfl
            · simp only [if_pos hucd, if_neg hvcd]; decide
            · simp only [if_neg hucd, if_pos hvcd]; decide
            · exfalso
              have huf : u = f ∨ u = g := by tauto
              have hvf : v = f ∨ v = g := by tauto
              rcases huf with hu' | hu' <;> rcases hvf with hv' | hv' <;>
                subst u <;> subst v
              · exact huv rfl
              · exact hnfg hadj
              · exact hnfg hadj.symm
              · exact huv rfl
        · exfalso
          push_neg at htriple h2disj
          by_cases hA : ∀ p q : Fin n, p ≠ a → q ≠ a → p ≠ q → G.Adj p q
          · apply hCF (Finset.univ.erase a)
            refine ⟨fun p hp q hq hpq => hA p q (Finset.mem_erase.mp hp).1
              (Finset.mem_erase.mp hq).1 hpq, ?_⟩
            rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
              Fintype.card_fin]; omega
          · push_neg at hA
            obtain ⟨c, d, hca, hda, hcd, hncd⟩ := hA
            have hbcd : b = c ∨ b = d := by
              by_contra hb
              push_neg at hb
              exact hncd (h2disj a b c d hab hcd (Ne.symm hca) (Ne.symm hda) hb.1 hb.2 hnab)
            obtain ⟨w, hwb, hwa, hnbw⟩ : ∃ w, w ≠ b ∧ w ≠ a ∧ ¬ G.Adj b w := by
              rcases hbcd with hbc | hbd
              · exact ⟨d, by rw [hbc]; exact Ne.symm hcd, hda, by rw [hbc]; exact hncd⟩
              · exact ⟨c, by rw [hbd]; exact hcd, hca, by rw [hbd]; exact fun h => hncd h.symm⟩
            have hadjaw : G.Adj a w :=
              htriple b a w (Ne.symm hab) (Ne.symm hwb) (Ne.symm hwa)
                (fun h => hnab h.symm) hnbw
            apply hCF (Finset.univ.erase b)
            refine ⟨fun p hp q hq hpq => ?_, ?_⟩
            · have hpb : p ≠ b := (Finset.mem_erase.mp hp).1
              have hqb : q ≠ b := (Finset.mem_erase.mp hq).1
              by_contra hnpq
              have hapq : p = a ∨ q = a := by
                by_contra hap
                push_neg at hap
                exact hnpq (h2disj a b p q hab hpq (Ne.symm hap.1) (Ne.symm hap.2)
                  (Ne.symm hpb) (Ne.symm hqb) hnab)
              have hwpq : p = w ∨ q = w := by
                by_contra hwp
                push_neg at hwp
                exact hnpq (h2disj b w p q (Ne.symm hwb) hpq (Ne.symm hpb) (Ne.symm hqb)
                  (Ne.symm hwp.1) (Ne.symm hwp.2) hnbw)
              rcases hapq with hpa | hqa
              · rcases hwpq with hpw | hqw
                · exact hwa (by rw [← hpa, hpw])
                · subst hpa; subst hqw; exact hnpq hadjaw
              · rcases hwpq with hpw | hqw
                · subst hqa; subst hpw; exact hnpq hadjaw.symm
                · exact hwa (by rw [← hqa, hqw])
            · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
                Fintype.card_fin]; omega

/-! ## The main induction -/

/-- **KP/Brouwer upper bound** (both regimes), by strong induction on `r`.
`K_{r+1}`-free + non-`r`-colourable ⇒ `e(G) + kpSaving n r ≤ t_r(n)`. -/
theorem kp_upper : ∀ r : ℕ, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    G.CliqueFree (r + 1) → ¬ G.Colorable r →
    edgeCountIn G Finset.univ + kpSaving n r ≤ (turanGraph n r).edgeFinset.card := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r IH =>
    intro n G hCF hchi
    -- base cases r ∈ {0,1} are vacuous (hypotheses contradictory)
    rcases Nat.lt_or_ge r 2 with hrsmall | hr2
    · -- base cases: hypotheses contradictory (Gₙ,ᵣ = ∅ for r ≤ 1)
      exfalso
      interval_cases r
      · exact hchi (colorable_zero_iff.mpr (cliqueFree_one.mp hCF))   -- r=0
      · exact hchi (colorable_one_iff.mpr (cliqueFree_two.mp hCF))    -- r=1
    · -- main body, r ≥ 2
      -- `n > 0` (else G is colourable, contradicting hchi)
      have hn : 0 < n := by
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h; exact absurd (Colorable.of_isEmpty r) hchi
        · exact h
      haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      -- max-degree vertex x
      obtain ⟨x, hxmax⟩ := G.exists_maximal_degree_vertex
      have hmax : ∀ y, G.degree y ≤ G.degree x := fun y => hxmax ▸ G.degree_le_maxDegree y
      -- `d = |Γx| ≤ n − 1` (as `x ∉ Γx`)
      have hdn : (G.neighborFinset x).card ≤ n - 1 := by
        have hsub : G.neighborFinset x ⊆ Finset.univ.erase x := by
          intro y hy
          rw [Finset.mem_erase]
          exact ⟨(G.ne_of_adj ((G.mem_neighborFinset x y).mp hy)).symm, Finset.mem_univ _⟩
        calc (G.neighborFinset x).card ≤ (Finset.univ.erase x).card := Finset.card_le_card hsub
          _ = n - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
                              Fintype.card_fin]
      -- e(G) ≤ e(H) = e(G[Γx]) + d·(n−d)
      have hGH : edgeCountIn G Finset.univ ≤ edgeCountIn (symmG G x) Finset.univ :=
        symmG_edgeCount_ge hmax
      have hHsplit : edgeCountIn (symmG G x) Finset.univ
          = edgeCountIn G (G.neighborFinset x)
            + (G.neighborFinset x).card * (n - (G.neighborFinset x).card) :=
        symmG_edgeCount_eq G x
      -- transport `G[Γx] = H[Γx]` to `Fin |Γx|`; case split on its (r−1)-colourability
      -- expose the embedding `f : Fin |Γx| ↪ Fin n` (image = Γx) so Case B can recover `κ`
      obtain ⟨f, hf⟩ := exists_embedding_image_eq (G.neighborFinset x) rfl
      set X := G.comap f with hXdef
      have hXcount : edgeCountIn X Finset.univ = edgeCountIn G (G.neighborFinset x) := by
        rw [hXdef, edgeCountIn_comap G f Finset.univ, hf]
      have hXCF : X.CliqueFree r := by
        intro K hK
        rw [hXdef] at hK
        obtain ⟨hclq, hcard⟩ := hK
        have hSsub : K.image f ⊆ G.neighborFinset x := by
          intro y hy
          rw [Finset.mem_image] at hy
          obtain ⟨a, _, rfl⟩ := hy
          have hmem : f a ∈ Finset.univ.image f := Finset.mem_image_of_mem f (Finset.mem_univ a)
          rwa [hf] at hmem
        have hSclq : G.IsClique ↑(K.image f) := by
          intro u hu v hv huv
          rw [Finset.mem_coe, Finset.mem_image] at hu hv
          obtain ⟨a, ha, rfl⟩ := hu
          obtain ⟨b, hb, rfl⟩ := hv
          have hab : a ≠ b := fun h => huv (by rw [h])
          have hcc := hclq (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab
          rwa [SimpleGraph.comap_adj] at hcc
        have hScard : (K.image f).card = r := by
          rw [Finset.card_image_of_injective _ f.injective, hcard]
        have hle := no_clique_r_in_nbhd hCF (K.image f) hSsub hSclq
        omega
      by_cases hXcol : X.Colorable (r - 1)
      · -- Case B (H[Γx] ≅ X is (r−1)-partite): the good/bad dichotomy via `kp_caseB_impl`
        have hn_r3 : r + 3 ≤ n := by
          by_contra hcon
          push_neg at hcon
          exact hchi (gnr_colorable_small (by omega) (by omega) G hCF)
        obtain ⟨κ0, hκ0lt, hκ0proper⟩ := colorable_restrict_of_comap G f (hXdef ▸ hXcol)
        refine kp_caseB_impl hr2 G x hn_r3 hCF hchi hmax
          (fun v => ⟨κ0 v % (r - 1), Nat.mod_lt _ (by omega)⟩) ?_
        intro u hu v hv hadj heq
        rw [← hf] at hu hv
        have hune := hκ0proper u hu v hv hadj
        have hlu := hκ0lt u hu
        have hlv := hκ0lt v hv
        apply hune
        simp only [Fin.mk.injEq] at heq
        rwa [Nat.mod_eq_of_lt hlu, Nat.mod_eq_of_lt hlv] at heq
      · -- Case A: X non-(r−1)-colourable ⇒ IH at level r−1
        -- IH at r−1 (< r): e(X) + kpSaving d (r−1) ≤ t_{r−1}(d)
        have hIH : edgeCountIn X Finset.univ + kpSaving (G.neighborFinset x).card (r - 1)
            ≤ (turanGraph (G.neighborFinset x).card (r - 1)).edgeFinset.card :=
          IH (r - 1) (by omega) (G.neighborFinset x).card X
            (by rw [Nat.sub_add_cancel (show 1 ≤ r by omega)]; exact hXCF) hXcol
        -- d > 0 : else `Fin d` empty ⇒ X colourable, contradicting the Case-A branch
        have hd0 : 0 < (G.neighborFinset x).card := by
          rcases Nat.eq_zero_or_pos (G.neighborFinset x).card with h0 | h0
          · exfalso
            haveI : IsEmpty (Fin (G.neighborFinset x).card) := by rw [h0]; exact inferInstance
            exact hXcol (Colorable.of_isEmpty (r - 1))
          · exact h0
        have hslack := caseA_slack (n := n) (r := r) (d := (G.neighborFinset x).card)
          hr2 hd0 (by omega)
        rw [hXcount] at hIH
        omega

/-! ## Wiring to `BrouwerFacts`: the `saving` field, PROVEN

`kp_upper` specialised to the main regime `n ≥ 2r+1` is exactly the `saving` field, and it is now
sorry-free (`caseA_slack` and `kp_caseB` are discharged above, so `kp_upper` is complete).
`kp_saving` below is that field.

The full `BrouwerFacts` structure is assembled downstream in `Equality21.lean` as `brouwerFacts_of`,
combining this PROVEN `saving` with the single remaining classical hypothesis
`KPEqualityClassification` (the (5,21) KP equality classification) via the verified transport. The
old `brouwerFacts` constant (which left its `equality21` field as an unproved placeholder) is
therefore retired — nothing consumed it, and `brouwerFacts_of` supersedes it. -/

/-- The `saving` field shape (main regime), via `kp_upper`. Sorry-free and axiom-clean: the whole
`BrouwerFacts.saving` obligation is now proven. -/
theorem kp_saving : ∀ {n r : ℕ}, 0 < r → 2 * r + 1 ≤ n → ∀ G : SimpleGraph (Fin n),
    G.CliqueFree (r + 1) → ¬ G.Colorable r →
    edgeCountIn G Finset.univ + (n / r - 1) ≤ (turanGraph n r).edgeFinset.card := by
  intro n r _ h2r G hCF hchi
  have h := kp_upper r n G hCF hchi
  rwa [kpSaving_of_main h2r] at h

end Erdos617

