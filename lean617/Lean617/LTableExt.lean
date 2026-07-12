/-
Erdős Problem 617, r = 5 — shared L-table extension (F7a).

Extends F5's L-table (`Lean617/LTable.lean`, which exports `L13..L19`, `Mfloor`,
`ufloor`, and the per-vertex floor infrastructure, all CONDITIONAL on `PrimFacts`)
with the pieces BOTH the F7 [MH″] and F8 [MM] assemblies consume:

  `turan3_general`   : complement-Turán floor for `α ≤ 3` graphs (`Gᶜ` is `K₄`-free).
  `affineBound_20`   : the per-degree affine bound for the `s = 20` recursion.
  `L20`              : `L(20) = 84`, by the F5 method.
  `Lfloor`           : the unified `α ≤ 3` / `ω ≤ 4` / cap-11 floor for `s ≤ 20`
                       (complement-Turán for `s ≤ 12`, the L-table for `s ∈ [13,20]`).
  `Lfloor_le_of_props` : `Lfloor t ≤ e(Y)` packaged (`t ≤ 20`).

Per the team-lead's ownership decision (2026-07-10): F7 owns this file; F8 consumes
these exact names and deletes its own duplicates. Lands as its own commit ("F7a")
before `MH2Proof.lean` so F8 can rebase onto it.

Research project: Mathlib style linters disabled.
-/
import Lean617.LTable

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.style.multiGoal false
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false

open Finset SimpleGraph
open scoped Classical

namespace Erdos617

/-! ## L-table extension to `s = 20`, the `α ≤ 3` small-`s` floor, and `Lfloor`

The `§4.3` recursion for `H` uses per-vertex floors `L(20 − d)` for `20 − d ∈ [0,20]`.
F5 exported `L13..L19`; we add `L20 = 84` by the same method, plus a complement-Turán
floor for `α ≤ 3` graphs on `s ≤ 12` vertices, and bundle both as `Lfloor`. -/

/-- **Complement-Turán floor for `α ≤ 3`** (analogue of `mantel_general`). For any
`α ≤ 3` graph on `Fin t`, `e(G) ≥ C(t,2) − e(turanGraph t 3)`. (`Gᶜ` is `K₄`-free.) -/
theorem turan3_general {t : ℕ} (G : SimpleGraph (Fin t)) (hα : alphaAtMost G 3) :
    t.choose 2 - (turanGraph t 3).edgeFinset.card ≤ edgeCountIn G Finset.univ := by
  have hcf : Gᶜ.CliqueFree 4 := by
    intro S hS
    have hcard := hS.2
    have hclq := hS.1
    have hindep : IsIndep G S := by
      intro u hu v hv huv
      have hadj := hclq (Finset.mem_coe.mpr hu) (Finset.mem_coe.mpr hv) huv
      rw [SimpleGraph.compl_adj] at hadj
      exact hadj.2
    have := hα S hindep
    omega
  have hT := (isTuranMaximal_turanGraph (n := t) (r := 3) (by norm_num)).2 hcf
  rw [card_edgeFinset_eq_edgeCountIn Gᶜ] at hT
  have hid := edgeCountIn_add_compl G
  omega

/-- Per-degree affine bound for `s = 20` (`twoA = 125, twoB = 15`), checked over the
feasible range `d ∈ [s−11, s−1] = [9,19]` by `decide` (see scratchpad/check_f7_arith.py).
Equality holds at `d = 9`. -/
theorem affineBound_20 (d : ℕ) (hlo : 9 ≤ d) (hhi : d ≤ 19) :
    125 + 20 * d + 2 * ufloor d ≤ 2 * Mfloor (20 - 1 - d) + 2 * d ^ 2 + 15 * d := by
  interval_cases d <;> decide

/-- **L-table, s = 20: `L(20) = 84`.** Same assembly as F5's `L13..L19`. -/
theorem L20 (h : PrimFacts) (X : SimpleGraph (Fin 20)) (hα3 : alphaAtMost X 3)
    (hω : X.CliqueFree 5) (hcap : capAtMost11 X) : 84 ≤ edgeCountIn X Finset.univ := by
  rw [edgeCountIn_univ_eq_card_edgeFinset]
  have hWcard : ∀ v, (complClosedNbhd X v).card = 20 - 1 - X.degree v := complNbhd_card X
  have hM_lb : ∀ v, Mfloor (20 - 1 - X.degree v) ≤ edgeCountIn X (complClosedNbhd X v) := by
    intro v; rw [← hWcard v]; exact Mfloor_le_edgeCountIn_complNbhd h X hα3 hω hcap v
  have hN_ub : ∀ v, edgeCountIn X (X.neighborFinset v) ≤ ufloor (X.degree v) :=
    fun v => edgeCountIn_nbhd_le_ufloor X hω hcap v
  have hAff : ∀ v, 125 + 20 * X.degree v + 2 * ufloor (X.degree v)
      ≤ 2 * Mfloor (20 - 1 - X.degree v) + 2 * (X.degree v) ^ 2 + 15 * X.degree v := by
    intro v
    refine affineBound_20 (X.degree v) ?_ (degree_le_pred X v)
    have := complNbhd_card_le_ten h X hα3 hcap v
    rw [hWcard v] at this
    omega
  have hId := sum_edgeCountIn_compl_nbhd_add_sq_deg X
  have hDeg := X.sum_degrees_eq_twice_card_edges
  have hPM := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hM_lb v)
  have hSN := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hN_ub v)
  have hAffSum := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hAff v)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at hAffSum
  omega

/-- The unified `α ≤ 3`, `ω ≤ 4`, cap-11 edge floor `L(s)` for `s ≤ 20`, as literal
numerals (so `decide` stays fast, mirroring F5's `Mfloor`): `C(s,2) − t₃(s)` for
`s ≤ 12` (complement-Turán, values `0,0,0,0,1,2,3,5,7,9,12,15,18`) and the L-table
values `24..84` for `s ∈ [13,20]`; `0` above (unused). -/
def Lfloor : ℕ → ℕ
  | 0 | 1 | 2 | 3 => 0
  | 4 => 1 | 5 => 2 | 6 => 3 | 7 => 5 | 8 => 7 | 9 => 9 | 10 => 12 | 11 => 15 | 12 => 18
  | 13 => 24 | 14 => 31 | 15 => 38 | 16 => 46 | 17 => 53 | 18 => 62 | 19 => 73 | 20 => 84
  | _ => 0

/-- **The `α ≤ 3` floor, packaged.** For `Y` on `Fin t` (`t ≤ 20`) with `α ≤ 3`,
`ω ≤ 4` (`CliqueFree 5`), cap-11: `Lfloor t ≤ e(Y)`. Complement-Turán for `t ≤ 12`,
the L-table `L13..L20` for `t ∈ [13,20]`. -/
theorem Lfloor_le_of_props (h : PrimFacts) {t : ℕ} (ht : t ≤ 20) (Y : SimpleGraph (Fin t))
    (hα : alphaAtMost Y 3) (hω : Y.CliqueFree 5) (hcap : capAtMost11 Y) :
    Lfloor t ≤ edgeCountIn Y Finset.univ := by
  interval_cases t
  · exact le_trans (by decide) (turan3_general Y hα)
  · exact le_trans (by decide) (turan3_general Y hα)
  · exact le_trans (by decide) (turan3_general Y hα)
  · exact le_trans (by decide) (turan3_general Y hα)
  · exact le_trans (by decide) (turan3_general Y hα)
  · exact le_trans (by decide) (turan3_general Y hα)
  · exact le_trans (by decide) (turan3_general Y hα)
  · exact le_trans (by decide) (turan3_general Y hα)
  · exact le_trans (by decide) (turan3_general Y hα)
  · exact le_trans (by decide) (turan3_general Y hα)
  · exact le_trans (by decide) (turan3_general Y hα)
  · exact le_trans (by decide) (turan3_general Y hα)
  · exact le_trans (by decide) (turan3_general Y hα)
  · exact le_trans (by decide) (L13 h Y hα hω hcap)
  · exact le_trans (by decide) (L14 h Y hα hω hcap)
  · exact le_trans (by decide) (L15 h Y hα hω hcap)
  · exact le_trans (by decide) (L16 h Y hα hω hcap)
  · exact le_trans (by decide) (L17 h Y hα hω hcap)
  · exact le_trans (by decide) (L18 h Y hα hω hcap)
  · exact le_trans (by decide) (L19 h Y hα hω hcap)
  · exact le_trans (by decide) (L20 h Y hα hω hcap)

end Erdos617
