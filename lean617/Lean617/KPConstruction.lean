/-
equality21 PREP (F6h prep) — the KP extremal construction `G((4,4,4,4,4))` on `Fin 21`,
defined concretely, with its reviewer-verified properties (edge count 173, `K₆`-free,
`α ≤ 4`, and the `A/B` structure on the colour class `F = Jᶜ`). These are the facts
`equality21`'s eventual uniqueness proof cites. Standalone file — does NOT touch
`BrouwerInduction.lean` (owned by lean-f6e).

Construction (papers/brouwer-kang-pikhurko.md §2, scratchpad/verify_equality21.py):
parts `Nᵢ = {4i,…,4i+3}` (i=0..4), apex `x = 20`; complete 5-partite on `0..19`;
`x` joined to `N₂∪N₃∪N₄ ∪ {y} ∪ A*` with `y = 4∈N₁`, `A* = {0,1} ⊂ N₀`; the edges
`{y,a}` for `a∈A*` removed. (Indices 0-based; `A*` size 2 is one of the three isomorphic
witnesses, all with `e = 173`.)

Research project: Mathlib style linters disabled.
-/
import Lean617.Statements
import Lean617.Counting
import Lean617.LTable

set_option linter.style.header false
set_option linter.style.longLine false

open Finset SimpleGraph

namespace Erdos617

/-- Adjacency (Bool) of `J = G((4,4,4,4,4))`, `A* = {0,1}`, `y = 4`, apex `x = 20`. -/
def kpRel (a b : Fin 21) : Bool :=
  if a = b then false
  else if a.val < 20 ∧ b.val < 20 then
    -- both non-apex: complete 5-partite (different parts) minus {4,0},{4,1}
    (a.val / 4 ≠ b.val / 4) &&
      !((a.val = 4 && (b.val = 0 || b.val = 1)) || (b.val = 4 && (a.val = 0 || a.val = 1)))
  else
    -- one endpoint is the apex 20: joined to {0,1,4} ∪ {8,…,19}
    let o := if a.val = 20 then b.val else a.val
    (o = 0 || o = 1 || o = 4 || (8 ≤ o && o < 20))

/-- `J = G((4,4,4,4,4))` as a `SimpleGraph (Fin 21)`. -/
def kpG : SimpleGraph (Fin 21) where
  Adj a b := kpRel a b = true
  symm := by
    have h : ∀ a b : Fin 21, kpRel a b = true → kpRel b a = true := by decide
    exact fun a b => h a b
  loopless := by
    have h : ∀ a : Fin 21, ¬ (kpRel a a = true) := by decide
    exact ⟨h⟩

instance kpG_decRel : DecidableRel kpG.Adj := fun a b => decEq (kpRel a b) true

/-- **Edge count 173.** `e(J) = t_5(21) − ⌊21/5⌋ + 1 = 176 − 3 = 173` (KP maximum).
`kpG.degree` is decidable via `kpG_decRel`, so `∑ degrees = 346` by `native_decide`;
the handshake `∑ degrees = 2·e` then pins `e = 173`. -/
theorem kpG_card_edges : kpG.edgeFinset.card = 173 := by
  have hhand := SimpleGraph.sum_degrees_eq_twice_card_edges kpG
  have hd : ∑ v, kpG.degree v = 346 := by native_decide
  omega

theorem kpG_edgeCount : edgeCountIn kpG Finset.univ = 173 := by
  rw [edgeCountIn_univ_eq_card_edgeFinset]
  convert kpG_card_edges using 2
  ext e
  simp [SimpleGraph.mem_edgeFinset]

/-- **`K₆`-free.** `J = G((4,4,4,4,4))` contains no `K₆` (it is `K_{r+1}`-free by the
KP construction; here `r = 5`). -/
theorem kpG_cliqueFree : kpG.CliqueFree 6 := by
  show ∀ t : Finset (Fin 21), ¬ kpG.IsNClique 6 t
  native_decide

/-- **`α ≤ 4`.** Every independent set of `J` has at most 4 vertices. -/
theorem kpG_alpha : alphaAtMost kpG 4 := by
  show ∀ S : Finset (Fin 21), (∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ kpG.Adj u v) → S.card ≤ 4
  native_decide

/-! ## The `A/B` structure on the colour class `F = Jᶜ`

`equality21`'s conclusion, instantiated at `F = Jᶜ`, with `A = {4,5,6,7,20} = N₁ ∪ {x}`,
`B = {0,1,2,3} = N₀`: `F[A] = K₅ − {4,20}` (unique non-edge = the one `J`-edge `x–4`
inside `A`), `F[B] = K₄`, `e_F(A∪B) = 19` (4 cross edges). Cross-checked for all
`|A*| ∈ {1,2,3}` in scratchpad/verify_equality21.py. The `edgeCountIn F (A∪B) = 19`
count is bridged past the noncomputable `edgeCountIn` via `Finset.filter_congr_decidable`
(the `Finset.filter` result is decidability-instance-irrelevant) + `native_decide` on the
computable filter. These are the existence-witness half; `equality21` itself is the ∀-`F`
UNIQUENESS classification, a separate (harder) argument that CITES `kpG_*` above. -/

/-- **`A/B` structure witness.** The colour class `F = Jᶜ` realises `equality21`'s
extremal shape: `A = {4,5,6,7,20} = N₁ ∪ {x}`, `B = {0,1,2,3} = N₀`, with `F[A] = K₅ − {4,20}`
(unique non-edge, the one `J`-edge `x–4` inside `A`), `F[B] = K₄`, and `e_F(A∪B) = 19`.
Exactly the `∃ A B …` conclusion of `BrouwerFacts.equality21` instantiated at `F = kpGᶜ`. -/
theorem kpG_compl_AB_structure :
    ∃ A B : Finset (Fin 21), Disjoint A B ∧ A.card = 5 ∧ B.card = 4 ∧
      (∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ ¬ kpGᶜ.Adj x y ∧
        (∀ u ∈ A, ∀ w ∈ A, u ≠ w →
          (¬ kpGᶜ.Adj u w ↔ (u = x ∧ w = y) ∨ (u = y ∧ w = x)))) ∧
      (∀ u ∈ B, ∀ w ∈ B, u ≠ w → kpGᶜ.Adj u w) ∧
      edgeCountIn kpGᶜ (A ∪ B) = 19 := by
  refine ⟨{4, 5, 6, 7, 20}, {0, 1, 2, 3}, by decide, by decide, by decide,
    ⟨4, by decide, 20, by decide, by decide, by native_decide, by native_decide⟩,
    by native_decide, ?_⟩
  -- edgeCountIn is noncomputable (Classical filter); bridge to the same filter with a
  -- computable instance (filter result is decidability-instance-irrelevant).
  have key : ((({4, 5, 6, 7, 20} : Finset (Fin 21)) ∪ {0, 1, 2, 3}).sym2.filter
      (fun e => e ∈ kpGᶜ.edgeSet)).card = 19 := by native_decide
  unfold edgeCountIn
  convert key using 2
  exact Finset.filter_congr_decidable _ _ _

end Erdos617
