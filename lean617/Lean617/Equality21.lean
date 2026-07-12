/-
equality21 assembly (F6i refactor, relay runner 16). The (5,21) KP equality classification is now a
single hypothesis-only `Prop` — `KPEqualityClassification` (the exact former `exists_AB21_iso`
statement) — with the whole transport VERIFIED sorry-free: `equality21_reduce` (F→J extremal),
`edgeCountIn_iso`, `equality21_transport` (variant-agnostic), `AB21_kpG_compl` (numeric witness).
`equality21_final` derives `BrouwerFacts.equality21` from that hypothesis via the transport, and
`brouwerFacts_of` assembles the full `BrouwerFacts` from the PROVEN Brouwer bound (`kp_saving`,
axiom-clean, BrouwerInduction.lean) + the hypothesis. This file is sorry-free — the former
`exists_AB21_iso` placeholder is retired, its statement preserved as `KPEqualityClassification`.
Research linters off.
-/
import Lean617.Brouwer
import Lean617.KPConstruction
import Lean617.BrouwerInduction

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option maxHeartbeats 2000000

open Finset SimpleGraph
open scoped Classical

namespace Erdos617

/-- **equality21 STEP 1 (reduction to the extremal complement).** A colour class `F` on `Fin 21`
with `α(F)≤5`, `K₅`-free, `e(F)=37` has complement `J=Fᶜ` that is `K₆`-free, `α(J)≤4`, and
attains the Brouwer maximum `e(J)=173`. (Entry to the KP equality classification.) -/
theorem equality21_reduce (F : SimpleGraph (Fin 21)) (hα : alphaAtMost F 5)
    (hK5 : F.CliqueFree 5) (he : edgeCountIn F Finset.univ = 37) :
    Fᶜ.CliqueFree 6 ∧ alphaAtMost Fᶜ 4 ∧ edgeCountIn Fᶜ Finset.univ = 173 := by
  refine ⟨compl_cliqueFree_six_of_alphaAtMost_five F hα,
    alphaAtMost_compl_four_of_cliqueFree_five F hK5, ?_⟩
  have hid := edgeCountIn_add_compl F
  have hc : (21 : ℕ).choose 2 = 210 := by decide
  omega

/-- **`edgeCountIn` under a graph isomorphism.** If `σ : Fin n ≃ Fin n` carries `F` to `H`
(`F.Adj a b ↔ H.Adj (σ a) (σ b)`), then `edgeCountIn F S = edgeCountIn H (S.image σ)`. -/
theorem edgeCountIn_iso {n : ℕ} (F H : SimpleGraph (Fin n)) (σ : Fin n ≃ Fin n)
    (hiso : ∀ a b, F.Adj a b ↔ H.Adj (σ a) (σ b)) (S : Finset (Fin n)) :
    edgeCountIn F S = edgeCountIn H (S.image σ) := by
  classical
  unfold edgeCountIn
  apply Finset.card_bij' (fun e _ => Sym2.map σ e) (fun e _ => Sym2.map σ.symm e)
  · intro e he
    rw [Finset.mem_filter] at he ⊢
    obtain ⟨heS, heF⟩ := he
    refine ⟨?_, ?_⟩
    · -- Sym2.map σ e ∈ (S.image σ).sym2
      induction e using Sym2.ind with
      | _ a b =>
        rw [Finset.mk_mem_sym2_iff] at heS
        rw [Sym2.map_pair_eq, Finset.mk_mem_sym2_iff]
        exact ⟨Finset.mem_image_of_mem σ heS.1, Finset.mem_image_of_mem σ heS.2⟩
    · -- Sym2.map σ e ∈ H.edgeSet
      induction e using Sym2.ind with
      | _ a b =>
        rw [Sym2.map_pair_eq, SimpleGraph.mem_edgeSet]
        rw [SimpleGraph.mem_edgeSet] at heF
        exact (hiso a b).mp heF
  · intro e he
    rw [Finset.mem_filter] at he ⊢
    obtain ⟨heS, heH⟩ := he
    refine ⟨?_, ?_⟩
    · induction e using Sym2.ind with
      | _ a b =>
        rw [Finset.mk_mem_sym2_iff] at heS
        rw [Sym2.map_pair_eq, Finset.mk_mem_sym2_iff]
        obtain ⟨a', ha'S, ha'⟩ := Finset.mem_image.mp heS.1
        obtain ⟨b', hb'S, hb'⟩ := Finset.mem_image.mp heS.2
        refine ⟨?_, ?_⟩
        · rw [← ha', σ.symm_apply_apply]; exact ha'S
        · rw [← hb', σ.symm_apply_apply]; exact hb'S
    · induction e using Sym2.ind with
      | _ a b =>
        rw [Sym2.map_pair_eq, SimpleGraph.mem_edgeSet]
        rw [SimpleGraph.mem_edgeSet] at heH
        rw [hiso]; simpa using heH
  · intro e _; induction e using Sym2.ind with
    | _ a b => simp [Sym2.map_map]
  · intro e _; induction e using Sym2.ind with
    | _ a b => simp [Sym2.map_map]

/-- **The equality21 A/B-structure predicate** on a graph over `Fin 21`. -/
def AB21 (H : SimpleGraph (Fin 21)) : Prop :=
  ∃ A B : Finset (Fin 21), Disjoint A B ∧ A.card = 5 ∧ B.card = 4 ∧
    (∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ ¬ H.Adj x y ∧
      (∀ u ∈ A, ∀ w ∈ A, u ≠ w →
        (¬ H.Adj u w ↔ (u = x ∧ w = y) ∨ (u = y ∧ w = x)))) ∧
    (∀ u ∈ B, ∀ w ∈ B, u ≠ w → H.Adj u w) ∧
    edgeCountIn H (A ∪ B) = 19

/-- **The (5,21) Kang–Pikhurko equality classification**, as a hypothesis-only `Prop`. This is
the exact statement of the former research placeholder `exists_AB21_iso`, and it is the SINGLE classical
input the r = 5 resolution remains conditional on (literature-verified,
papers/brouwer-kang-pikhurko.md; independently numerically validated, FORMAL.md EQUALITY21
analysis). It reads: every extremal colour class `F` (`α(F) ≤ 5`, `K₅`-free, `e(F) = 37`) is
isomorphic to some graph `H` that carries the extremal A/B structure `AB21 H`. From it the
`BrouwerFacts.equality21` field follows by the verified `equality21_transport`; Brouwer's bound
itself (`BrouwerFacts.saving`) is PROVEN separately (`kp_saving`), so this Prop is everything the
final theorem still assumes. -/
def KPEqualityClassification : Prop :=
  ∀ (F : SimpleGraph (Fin 21)), alphaAtMost F 5 → F.CliqueFree 5 →
    edgeCountIn F Finset.univ = 37 →
    ∃ (H : SimpleGraph (Fin 21)) (σ : Fin 21 ≃ Fin 21),
      (∀ a b, F.Adj a b ↔ H.Adj (σ a) (σ b)) ∧ AB21 H

/-- **equality21 TRANSPORT (variant-agnostic).** A graph iso `σ : F ≅ H` transports the A/B
structure from `H` to `F`. This reduces `equality21` to: every extremal colour-class `F` is
isomorphic to SOME `H` with the A/B structure — the KP Thm 4 research core. NB the (5,21) extremal
graph is NOT unique — `G((4,4,4,4,4))` has TWO iso classes (CORRECTED 2026-07-12 by full
nauty canonical-form analysis, FORMAL.md "EQUALITY21 — analysis": `|A*|=1 ≅ |A*|=3`, so the
classes are `|A*|=2` and `|A*|∈{1,3}`); `H` ranges over these 2. `AB21 kpGᶜ`
(= `kpG_compl_AB_structure`) is the `|A*|=2` witness; ONE more construction (`kpG1`,
the `|A*|=1` class) + a `native_decide` completes the witness set. -/
theorem equality21_transport (F H : SimpleGraph (Fin 21)) (σ : Fin 21 ≃ Fin 21)
    (hiso : ∀ a b, F.Adj a b ↔ H.Adj (σ a) (σ b)) (hH : AB21 H) : AB21 F := by
  classical
  obtain ⟨A0, B0, hdisj0, hA0c, hB0c, ⟨x0, hx0, y0, hy0, hxy0, hnadj0, hchar0⟩, hB0clq, hAB0⟩ := hH
  have hmem : ∀ (s : Finset (Fin 21)) u, u ∈ s.image σ.symm ↔ σ u ∈ s := by
    intro s u; rw [Finset.mem_image]
    exact ⟨by rintro ⟨a, ha, rfl⟩; rwa [σ.apply_symm_apply], fun h => ⟨σ u, h, σ.symm_apply_apply u⟩⟩
  have hFiso : ∀ u w, ¬ F.Adj u w ↔ ¬ H.Adj (σ u) (σ w) := fun u w => not_congr (hiso u w)
  unfold AB21
  refine ⟨A0.image σ.symm, B0.image σ.symm, ?_, ?_, ?_,
    ⟨σ.symm x0, (hmem _ _).mpr (by rw [σ.apply_symm_apply]; exact hx0),
     σ.symm y0, (hmem _ _).mpr (by rw [σ.apply_symm_apply]; exact hy0), ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [Finset.disjoint_left]; intro v hvA hvB
    rw [hmem] at hvA hvB; exact Finset.disjoint_left.mp hdisj0 hvA hvB
  · rw [Finset.card_image_of_injective _ σ.symm.injective, hA0c]
  · rw [Finset.card_image_of_injective _ σ.symm.injective, hB0c]
  · exact fun h => hxy0 (σ.symm.injective h)
  · rw [hFiso, σ.apply_symm_apply, σ.apply_symm_apply]; exact hnadj0
  · intro u hu w hw huw
    rw [hmem] at hu hw
    rw [hFiso, hchar0 (σ u) hu (σ w) hw (fun h => huw (σ.injective h))]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨by rw [← h1, σ.symm_apply_apply], by rw [← h2, σ.symm_apply_apply]⟩
      · exact Or.inr ⟨by rw [← h1, σ.symm_apply_apply], by rw [← h2, σ.symm_apply_apply]⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨by rw [h1, σ.apply_symm_apply], by rw [h2, σ.apply_symm_apply]⟩
      · exact Or.inr ⟨by rw [h1, σ.apply_symm_apply], by rw [h2, σ.apply_symm_apply]⟩
  · intro u hu w hw huw
    rw [hmem] at hu hw
    rw [hiso]; exact hB0clq (σ u) hu (σ w) hw (fun h => huw (σ.injective h))
  · rw [← Finset.image_union, edgeCountIn_iso F H σ hiso, Finset.image_image]
    have : (A0 ∪ B0).image (σ ∘ σ.symm) = A0 ∪ B0 := by
      rw [show (σ ∘ σ.symm) = id from funext σ.apply_symm_apply, Finset.image_id]
    rw [this]; exact hAB0

/-- The `kpGᶜ` witness of `AB21` (the `|A*|=2` extremal variant), from the native-decide-backed
`kpG_compl_AB_structure`. -/
theorem AB21_kpG_compl : AB21 kpGᶜ := kpG_compl_AB_structure

/-- **equality21, assembled** = the classification hypothesis (`h : KPEqualityClassification`) ∘
the verified `equality21_transport`. This IS `BrouwerFacts.equality21`'s conclusion (`AB21 F` is
definitionally the inlined `∃ A B …`). Formerly this composed the sorried `exists_AB21_iso`; that
placeholder is retired — its statement is now the hypothesis `KPEqualityClassification`. Since Brouwer's
bound itself is proven (`kp_saving`), this hypothesis is the ONLY classical input threaded to the
final theorem. -/
theorem equality21_final (h : KPEqualityClassification) (F : SimpleGraph (Fin 21))
    (hα : alphaAtMost F 5) (hK5 : F.CliqueFree 5) (he : edgeCountIn F Finset.univ = 37) : AB21 F := by
  obtain ⟨H, σ, hiso, hH⟩ := h F hα hK5 he
  exact equality21_transport F H σ hiso hH

/-- **`BrouwerFacts`, assembled from one classical hypothesis.** The `saving` field is the PROVEN
Brouwer bound `kp_saving` (BrouwerInduction.lean; sorry-free, axiom-clean); the `equality21` field
is `equality21_final h` for the single remaining classical input `h : KPEqualityClassification`
(the (5,21) KP equality classification). This supersedes the old `brouwerFacts` (retired — it
left its `equality21` field as an unproved placeholder): with `kp_saving` proven, the whole `BrouwerFacts`
interface is now conditional on exactly `KPEqualityClassification` and nothing else. -/
theorem brouwerFacts_of (h : KPEqualityClassification) : BrouwerFacts where
  saving := @kp_saving
  equality21 := fun F hα hK5 he => equality21_final h F hα hK5 he

end Erdos617
