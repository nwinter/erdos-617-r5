/-
Erdős Problem 617, r = 5 — milestone F8: the assembly of lemma [MM].

Target: `lemma_MM_of (pf : PrimFacts) : MM` (MM as in `Lean617.Statements`).

We mirror review_queue/mm-gpt56-candidate.md (frozen reference, incl. the adopted
r=7 repair in §5). The case split is on the maximum number of disjoint K_5's in
`H = G − T` (∈ {0,1,2,4} by the §1 peeling lemma), and every case is eliminated.

Infrastructure consumed from earlier milestones:
* `Lean617.Statements`: `edgeCountIn`, `IsIndep`, `card_offdiag`, `MM`.
* `Lean617.Counting` (F4): the double-counting identity + cap-11 nbhd bound.
* `Lean617.LTable` (F5): `PrimFacts`, `capAtMost11`, `alphaAtMost`, `Mfloor`,
  the L-lemmas `L13..L19`, `mantel_general`, and the `comap` transport toolkit.

Research project: Mathlib style linters disabled.
-/
import Lean617.LTable

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.style.multiGoal false
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
set_option linter.style.setOption false
set_option maxHeartbeats 4000000

open Finset SimpleGraph
open scoped Classical

namespace Erdos617

variable {n : ℕ}

/-! ## §0. Shared infrastructure: cliques, in-degree into a K_5, transport -/

/-- A finset clique predicate mirroring `IsIndep`: every pair inside `Q` is
adjacent. -/
def IsCliqueOn (G : SimpleGraph (Fin n)) (Q : Finset (Fin n)) : Prop :=
  ∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → G.Adj u v

/-- A clique spans all `C(|Q|,2)` off-diagonal pairs. -/
theorem edgeCountIn_eq_choose_of_clique (G : SimpleGraph (Fin n)) {Q : Finset (Fin n)}
    (h : IsCliqueOn G Q) : edgeCountIn G Q = Q.card.choose 2 := by
  rw [← card_offdiag Q]
  unfold edgeCountIn
  congr 1
  apply Finset.filter_congr
  intro e he
  revert he
  induction e using Sym2.ind with
  | _ x y =>
    intro he
    rw [Finset.mk_mem_sym2_iff] at he
    rw [SimpleGraph.mem_edgeSet, Sym2.mk_isDiag_iff]
    constructor
    · intro hadj; exact G.ne_of_adj hadj
    · intro hne; exact h x he.1 y he.2 hne

/-- Adding a vertex `x ∉ Q` to `Q` gains at least its number of `Q`-neighbours in
edges. (The exact identity, but the `≥` direction is all we need.) -/
theorem edgeCountIn_insert_ge_mm (G : SimpleGraph (Fin n)) {x : Fin n} {Q : Finset (Fin n)}
    (hx : x ∉ Q) :
    edgeCountIn G Q + (Q.filter (fun q => G.Adj x q)).card ≤ edgeCountIn G (insert x Q) := by
  set A := Q.filter (fun q => G.Adj x q) with hA
  set spokes := A.image (fun w => s(x, w)) with hsp
  have hinj : Set.InjOn (fun w => s(x, w)) A := by
    intro a ha b hb hab
    simp only [Sym2.eq_iff] at hab
    rcases hab with ⟨_, h⟩ | ⟨_, hav⟩
    · exact h
    · exact absurd (hav ▸ (Finset.filter_subset _ Q (Finset.mem_coe.mp ha))) hx
  have hspoke_card : spokes.card = A.card := by
    rw [hsp, Finset.card_image_of_injOn hinj]
  have hsub : (Q.sym2.filter (fun e => e ∈ G.edgeSet)) ∪ spokes
      ⊆ (insert x Q).sym2.filter (fun e => e ∈ G.edgeSet) := by
    intro e he
    rw [Finset.mem_union] at he
    rw [Finset.mem_filter]
    rcases he with he | he
    · rw [Finset.mem_filter] at he
      exact ⟨Finset.sym2_mono (Finset.subset_insert x Q) he.1, he.2⟩
    · rw [hsp, Finset.mem_image] at he
      obtain ⟨w, hw, rfl⟩ := he
      rw [hA, Finset.mem_filter] at hw
      refine ⟨?_, ?_⟩
      · rw [Finset.mk_mem_sym2_iff]
        exact ⟨Finset.mem_insert_self x Q, Finset.mem_insert_of_mem hw.1⟩
      · rw [SimpleGraph.mem_edgeSet]; exact hw.2
  have hdisj : Disjoint (Q.sym2.filter (fun e => e ∈ G.edgeSet)) spokes := by
    rw [Finset.disjoint_left]
    intro e he hesp
    rw [Finset.mem_filter] at he
    rw [hsp, Finset.mem_image] at hesp
    obtain ⟨w, hw, hwe⟩ := hesp
    have hmem := he.1
    rw [← hwe, Finset.mk_mem_sym2_iff] at hmem
    exact hx hmem.1
  calc edgeCountIn G Q + A.card
      = (Q.sym2.filter (fun e => e ∈ G.edgeSet)).card + spokes.card := by
        unfold edgeCountIn; rw [hspoke_card]
    _ = ((Q.sym2.filter (fun e => e ∈ G.edgeSet)) ∪ spokes).card :=
        (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ ((insert x Q).sym2.filter (fun e => e ∈ G.edgeSet)).card := Finset.card_le_card hsub
    _ = edgeCountIn G (insert x Q) := rfl

/-- **In-degree into a K_5.** Under cap-11, a vertex outside a 5-clique `Q` has at
most one neighbour in `Q` (else `Q ∪ {x}` is a 6-set with ≥ 12 edges). -/
theorem indeg_clique5_le_one (G : SimpleGraph (Fin n)) (hcap : capAtMost11 G)
    {Q : Finset (Fin n)} (hQ : IsCliqueOn G Q) (hQc : Q.card = 5) {x : Fin n} (hx : x ∉ Q) :
    (Q.filter (fun q => G.Adj x q)).card ≤ 1 := by
  have h10 : edgeCountIn G Q = 10 := by
    rw [edgeCountIn_eq_choose_of_clique G hQ, hQc]; rfl
  have hins_card : (insert x Q).card = 6 := by rw [Finset.card_insert_of_notMem hx, hQc]
  have hcap6 := hcap (insert x Q) hins_card
  have hge := edgeCountIn_insert_ge_mm G hx (Q := Q)
  omega

/-- A `CliqueFree 5` graph has no 5-element clique-on set. -/
theorem not_isCliqueOn_of_cliqueFree {G : SimpleGraph (Fin n)} (hω : G.CliqueFree 5)
    {Q : Finset (Fin n)} (hQc : Q.card = 5) : ¬ IsCliqueOn G Q := by
  intro hQ
  apply hω Q
  rw [SimpleGraph.isNClique_iff]
  refine ⟨?_, hQc⟩
  intro u hu v hv huv
  exact hQ u (Finset.mem_coe.mp hu) v (Finset.mem_coe.mp hv) huv

/-! ### Transport wrappers for subsets of `Fin n`

To apply the (concrete `Fin s`) L-lemmas and Turán floors to an induced subgraph
on a `t`-vertex subset `W ⊆ Fin n`, we pull `G` back along an embedding with image
`W`. These generalise F5's `alphaAtMost_comap` (any bound `m`) and add the
`CliqueFree` transport in the direction we need ("no K_5 in `W`" ⇒ comap K_5-free). -/

/-- `α ≤ m` transports across `comap` for any `m`. (F5's version fixes `m = 2`.) -/
theorem alphaAtMost_comap_mm {s : ℕ} (X : SimpleGraph (Fin n)) (f : Fin s ↪ Fin n) {m : ℕ}
    (hα : ∀ S : Finset (Fin n), S ⊆ Finset.univ.image f → IsIndep X S → S.card ≤ m) :
    alphaAtMost (X.comap f) m := by
  intro S' hS'
  rw [isIndep_comap] at hS'
  have hsub : S'.image f ⊆ Finset.univ.image f :=
    Finset.image_subset_image (Finset.subset_univ S')
  have := hα (S'.image f) hsub hS'
  rwa [Finset.card_image_of_injective _ f.injective] at this

/-- If no 5-subset of `image f` is a clique of `X`, then `X.comap f` is K_5-free. -/
theorem cliqueFree_comap_of_no_clique {s : ℕ} (X : SimpleGraph (Fin n)) (f : Fin s ↪ Fin n)
    (h : ∀ Q : Finset (Fin n), Q ⊆ Finset.univ.image f → Q.card = 5 → ¬ IsCliqueOn X Q) :
    (X.comap f).CliqueFree 5 := by
  intro S hS
  rw [SimpleGraph.isNClique_iff] at hS
  obtain ⟨hclique, hcard⟩ := hS
  refine h (S.image f) (Finset.image_subset_image (Finset.subset_univ S))
    (by rw [Finset.card_image_of_injective _ f.injective, hcard]) ?_
  intro u hu v hv huv
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
  have hab : a ≠ b := fun h => huv (by rw [h])
  have := hclique (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab
  rwa [SimpleGraph.comap_adj] at this

/-- **Sub-additivity of the edge count over a disjoint union.** For disjoint `A`,
`B` the edges inside `A` and inside `B` are disjoint sub-families of the edges
inside `A ∪ B`. (Used by the §4/§5 budgets: `e(H) ≥ e(Q) + e(R)`, and by the §2
`m = 50` endgame.) -/
theorem edgeCountIn_add_le_union_disjoint (G : SimpleGraph (Fin n)) {A B : Finset (Fin n)}
    (h : Disjoint A B) :
    edgeCountIn G A + edgeCountIn G B ≤ edgeCountIn G (A ∪ B) := by
  rw [edgeCountIn_eq_filter_edgeFinset G A, edgeCountIn_eq_filter_edgeFinset G B,
      edgeCountIn_eq_filter_edgeFinset G (A ∪ B)]
  have hdisj : Disjoint (G.edgeFinset.filter (fun e => e ∈ A.sym2))
      (G.edgeFinset.filter (fun e => e ∈ B.sym2)) := by
    rw [Finset.disjoint_left]
    intro e heA heB
    rw [Finset.mem_filter] at heA heB
    revert heA heB
    induction e using Sym2.ind with
    | _ u v =>
      intro heA heB
      rw [Finset.mk_mem_sym2_iff] at heA heB
      exact Finset.disjoint_left.mp h heA.2.1 heB.2.1
  rw [← Finset.card_union_of_disjoint hdisj]
  apply Finset.card_le_card
  intro e he
  rw [Finset.mem_union] at he
  rw [Finset.mem_filter]
  rcases he with he | he <;> rw [Finset.mem_filter] at he
  · exact ⟨he.1, Finset.sym2_mono Finset.subset_union_left he.2⟩
  · exact ⟨he.1, Finset.sym2_mono Finset.subset_union_right he.2⟩

/-! ### §2 floors: the α ≤ 3 complement-Turán bound and the `ell` table -/

/-- **α ≤ 3 complement-Turán floor.** The complement of an `α ≤ 3` graph is
`K₄`-free (no independent 4-set), so Turán (`r = 3`) bounds `e(Gᶜ)`. -/
theorem turan3_general_mm {t : ℕ} (G : SimpleGraph (Fin t)) (hα : alphaAtMost G 3) :
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

/-- The §2 edge floor `ℓ(q)` (vector (4) of the informal proof): the L-table for
`13 ≤ q ≤ 19`, and the complement-Turán bound `C(q,2) − t₃(q)` for `q ≤ 12`. -/
def ell (q : ℕ) : ℕ :=
  match q with
  | 4 => 1 | 5 => 2 | 6 => 3 | 7 => 5 | 8 => 7 | 9 => 9 | 10 => 12
  | 11 => 15 | 12 => 18 | 13 => 24 | 14 => 31 | 15 => 38 | 16 => 46
  | 17 => 53 | 18 => 62 | 19 => 73
  | _ => 0

/-- **The `ℓ`-floor on `Fin s`.** For `X` on `Fin s` (`s ≤ 19`) with `α ≤ 3`,
`ω ≤ 4` (`CliqueFree 5`) and cap-11: `ℓ(s) ≤ e(X)`. Turán for `s ≤ 12`, the F5
L-lemmas for `13 ≤ s ≤ 19`. -/
theorem ell_le_fin (pf : PrimFacts) {s : ℕ} (X : SimpleGraph (Fin s))
    (hα3 : alphaAtMost X 3) (hω : X.CliqueFree 5) (hcap : capAtMost11 X)
    (hs : s ≤ 19) : ell s ≤ edgeCountIn X Finset.univ := by
  interval_cases s
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact le_trans (by decide) (turan3_general_mm X hα3)
  · exact le_trans (by decide) (turan3_general_mm X hα3)
  · exact le_trans (by decide) (turan3_general_mm X hα3)
  · exact le_trans (by decide) (turan3_general_mm X hα3)
  · exact le_trans (by decide) (turan3_general_mm X hα3)
  · exact le_trans (by decide) (turan3_general_mm X hα3)
  · exact le_trans (by decide) (turan3_general_mm X hα3)
  · exact le_trans (by decide) (turan3_general_mm X hα3)
  · exact le_trans (by decide) (turan3_general_mm X hα3)
  · exact L13 pf X hα3 hω hcap
  · exact L14 pf X hα3 hω hcap
  · exact L15 pf X hα3 hω hcap
  · exact L16 pf X hα3 hω hcap
  · exact L17 pf X hα3 hω hcap
  · exact L18 pf X hα3 hω hcap
  · exact L19 pf X hα3 hω hcap

/-- **The `ℓ`-floor on a subset `W ⊆ Fin n`.** Transports `ell_le_fin` to the
induced subgraph on `W`, given the α-bound and K_5-freeness restricted to `W`. -/
theorem ell_le_edgeCountIn (pf : PrimFacts) (G : SimpleGraph (Fin n))
    (W : Finset (Fin n)) (hcap : capAtMost11 G)
    (hα3 : ∀ S : Finset (Fin n), S ⊆ W → IsIndep G S → S.card ≤ 3)
    (hK5 : ∀ Q : Finset (Fin n), Q ⊆ W → Q.card = 5 → ¬ IsCliqueOn G Q)
    (hWle : W.card ≤ 19) : ell W.card ≤ edgeCountIn G W := by
  obtain ⟨f, hf⟩ := exists_embedding_image_eq W rfl
  have hEC : edgeCountIn (G.comap f) Finset.univ = edgeCountIn G W := by
    rw [edgeCountIn_comap, hf]
  rw [← hEC]
  refine ell_le_fin pf (G.comap f) ?_ ?_ (capAtMost11_comap G f hcap) hWle
  · refine alphaAtMost_comap_mm G f ?_
    intro S hSsub hSindep
    rw [hf] at hSsub
    exact hα3 S hSsub hSindep
  · refine cliqueFree_comap_of_no_clique G f ?_
    intro Q hQsub hQcard
    rw [hf] at hQsub
    exact hK5 Q hQsub hQcard

/-- **α-drop for `W_v`, general bound.** If `α(X) ≤ m+1`, then `α(X[W_v]) ≤ m`
(an independent set of `W_v` extends by `v`). Generalises F5's `alpha_W`. -/
theorem alpha_W_gen {X : SimpleGraph (Fin n)} {m : ℕ} (hα : alphaAtMost X (m + 1))
    (v : Fin n) (S : Finset (Fin n)) (hSW : S ⊆ complClosedNbhd X v) (hSindep : IsIndep X S) :
    S.card ≤ m := by
  have hvS : v ∉ S := by
    intro hv
    have hmem := hSW hv
    rw [mem_complClosedNbhd] at hmem
    exact hmem.1 rfl
  have hins : IsIndep X (insert v S) := by
    intro a ha b hb hab
    rw [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact absurd rfl hab
    · have hmem := hSW hb; rw [mem_complClosedNbhd] at hmem; exact hmem.2
    · have hmem := hSW ha; rw [mem_complClosedNbhd] at hmem; exact fun h => hmem.2 h.symm
    · exact hSindep a ha b hb hab
  have hcard : (insert v S).card = S.card + 1 := Finset.card_insert_of_notMem hvS
  have := hα (insert v S) hins
  omega

/-- **Per-vertex `ℓ`-floor.** For `H` with `α ≤ 4`, K_5-free, cap-11:
`ℓ(|W_v|) ≤ e(H[W_v])` (`W_v` has `α ≤ 3`, is K_5-free, and `|W_v| ≤ 19`). -/
theorem ell_le_edgeCountIn_complNbhd (pf : PrimFacts) (H : SimpleGraph (Fin n))
    (hα4 : alphaAtMost H 4) (hω : H.CliqueFree 5) (hcap : capAtMost11 H) (v : Fin n)
    (hv : (complClosedNbhd H v).card ≤ 19) :
    ell ((complClosedNbhd H v).card) ≤ edgeCountIn H (complClosedNbhd H v) := by
  refine ell_le_edgeCountIn pf H (complClosedNbhd H v) hcap ?_ ?_ hv
  · intro S hSsub hSindep
    exact alpha_W_gen hα4 v S hSsub hSindep
  · intro Q _ hQcard
    exact not_isCliqueOn_of_cliqueFree hω hQcard

/-- Per-degree affine bound for §2 (`s = 20`, floor 50), over `d ∈ [0,19]`. The
`ℓ`-floor covers all `|W_v| ≤ 19`, so no lower restriction on `d` is needed. -/
theorem affineBound_20_mm (d : ℕ) (hhi : d ≤ 19) :
    84 + 3 * d + 2 * ufloor d ≤ 2 * ell (20 - 1 - d) + 2 * d ^ 2 := by
  interval_cases d <;> decide

/-- **§2, part A: `m ≥ 50`.** A `K_5`-free graph on 20 vertices with `α ≤ 4` and
cap-11 has at least 50 edges. (The informal `m ≥ 50`, via the F4 identity + `ℓ`
floors + the affine bound, exactly mirroring F5's L-lemma assembly.) -/
theorem A20 (pf : PrimFacts) (X : SimpleGraph (Fin 20)) (hα4 : alphaAtMost X 4)
    (hω : X.CliqueFree 5) (hcap : capAtMost11 X) : 50 ≤ edgeCountIn X Finset.univ := by
  rw [edgeCountIn_univ_eq_card_edgeFinset]
  have hWcard : ∀ v, (complClosedNbhd X v).card = 20 - 1 - X.degree v := complNbhd_card X
  have hWle : ∀ v, (complClosedNbhd X v).card ≤ 19 := by
    intro v; rw [hWcard v]; omega
  have h_ell_lb : ∀ v, ell (20 - 1 - X.degree v) ≤ edgeCountIn X (complClosedNbhd X v) := by
    intro v; rw [← hWcard v]; exact ell_le_edgeCountIn_complNbhd pf X hα4 hω hcap v (hWle v)
  have hN_ub : ∀ v, edgeCountIn X (X.neighborFinset v) ≤ ufloor (X.degree v) :=
    fun v => edgeCountIn_nbhd_le_ufloor X hω hcap v
  have hAff : ∀ v, 84 + 3 * X.degree v + 2 * ufloor (X.degree v)
      ≤ 2 * ell (20 - 1 - X.degree v) + 2 * (X.degree v) ^ 2 := by
    intro v
    exact affineBound_20_mm (X.degree v) (by have := degree_le_pred X v; omega)
  have hId := sum_edgeCountIn_compl_nbhd_add_sq_deg X
  have hDeg := X.sum_degrees_eq_twice_card_edges
  have hPM := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => h_ell_lb v)
  have hSN := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hN_ub v)
  have hAffSum := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hAff v)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at hAffSum
  omega

/-- **The `Mfloor` (α ≤ 2) floor on a subset `W ⊆ Fin n`** (`|W| ≤ 10`): transports
`Mfloor_le_of_props` to the induced subgraph on `W`. Used by §5 (`e(B) ≥ M(10) = 25`)
and §4/§5 residuals. -/
theorem Mfloor_le_edgeCountIn (pf : PrimFacts) (G : SimpleGraph (Fin n))
    (W : Finset (Fin n)) (hcap : capAtMost11 G)
    (hα2 : ∀ S : Finset (Fin n), S ⊆ W → IsIndep G S → S.card ≤ 2)
    (hK5 : ∀ Q : Finset (Fin n), Q ⊆ W → Q.card = 5 → ¬ IsCliqueOn G Q)
    (hWle : W.card ≤ 10) : Mfloor W.card ≤ edgeCountIn G W := by
  obtain ⟨f, hf⟩ := exists_embedding_image_eq W rfl
  have hEC : edgeCountIn (G.comap f) Finset.univ = edgeCountIn G W := by
    rw [edgeCountIn_comap, hf]
  rw [← hEC]
  refine Mfloor_le_of_props pf (G.comap f) ?_ ?_ (capAtMost11_comap G f hcap) hWle
  · refine alphaAtMost_comap_mm G f ?_
    intro S hSsub hSindep
    rw [hf] at hSsub
    exact hα2 S hSsub hSindep
  · refine cliqueFree_comap_of_no_clique G f ?_
    intro Q hQsub hQcard
    rw [hf] at hQsub
    exact hK5 Q hQsub hQcard

/-! ## §1. The peeling lemma -/

/-- **One greedy peel step.** Given a 5-clique `Q` and an independent set `S`
disjoint from `Q` with `|S| ≤ 4`, some `q ∈ Q` extends `S` to an independent set.
(Each `s ∈ S` forbids ≤ 1 vertex of `Q` by the in-degree bound, so ≤ 4 < 5 are
forbidden.) -/
theorem one_peel (G : SimpleGraph (Fin n)) (hcap : capAtMost11 G) {Q S : Finset (Fin n)}
    (hQ : IsCliqueOn G Q) (hQc : Q.card = 5) (hS : IsIndep G S) (hdisj : Disjoint S Q)
    (hScard : S.card ≤ 4) : ∃ q ∈ Q, IsIndep G (insert q S) := by
  set F := Q.filter (fun q => ∃ s ∈ S, G.Adj s q) with hF
  have hFsub : F ⊆ S.biUnion (fun s => Q.filter (fun q => G.Adj s q)) := by
    intro q hq
    rw [hF, Finset.mem_filter] at hq
    obtain ⟨hqQ, s, hsS, hadj⟩ := hq
    rw [Finset.mem_biUnion]
    exact ⟨s, hsS, Finset.mem_filter.mpr ⟨hqQ, hadj⟩⟩
  have hFcard : F.card ≤ S.card := by
    calc F.card ≤ (S.biUnion (fun s => Q.filter (fun q => G.Adj s q))).card :=
          Finset.card_le_card hFsub
      _ ≤ ∑ s ∈ S, (Q.filter (fun q => G.Adj s q)).card := Finset.card_biUnion_le
      _ ≤ ∑ _s ∈ S, 1 := by
          refine Finset.sum_le_sum ?_
          intro s hs
          have hsQ : s ∉ Q := Finset.disjoint_left.mp hdisj hs
          exact indeg_clique5_le_one G hcap hQ hQc hsQ
      _ = S.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
  have hFQ : F ⊆ Q := by intro x hx; rw [hF, Finset.mem_filter] at hx; exact hx.1
  have hss : F ⊂ Q := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨hFQ, ?_⟩
    intro heq
    rw [heq] at hFcard
    omega
  obtain ⟨q, hqQ, hqF⟩ := Finset.exists_of_ssubset hss
  refine ⟨q, hqQ, ?_⟩
  have hqnotadj : ∀ s ∈ S, ¬ G.Adj s q := by
    intro s hsS hadj
    exact hqF (by rw [hF, Finset.mem_filter]; exact ⟨hqQ, s, hsS, hadj⟩)
  intro a ha b hb hab
  rw [Finset.mem_insert] at ha hb
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  · exact absurd rfl hab
  · exact fun hadj => hqnotadj b hb (G.symm hadj)
  · exact fun hadj => hqnotadj a ha hadj
  · exact hS a ha b hb hab

/-- **Peeling (greedy transversal).** Given a list `L` of pairwise-disjoint
5-cliques, all disjoint from an independent `S`, with `|S| + |L| ≤ 5`, one can
extend `S` to an independent set of size `|S| + |L|` inside `S ∪ ⋃L`. -/
theorem peel_list (G : SimpleGraph (Fin n)) (hcap : capAtMost11 G) :
    ∀ (L : List (Finset (Fin n))), (∀ Q ∈ L, IsCliqueOn G Q ∧ Q.card = 5) →
      L.Pairwise (fun A B => Disjoint A B) →
      ∀ S : Finset (Fin n), IsIndep G S → (∀ Q ∈ L, Disjoint S Q) → S.card + L.length ≤ 5 →
      ∃ S' : Finset (Fin n), IsIndep G S' ∧ S'.card = S.card + L.length ∧
        (∀ x ∈ S', x ∈ S ∨ ∃ Q ∈ L, x ∈ Q) := by
  intro L
  induction L with
  | nil =>
    intro _ _ S hS _ _
    exact ⟨S, hS, by simp, fun x hx => Or.inl hx⟩
  | cons Q L' ih =>
    intro hcliques hpair S hS hSdisj hlen
    rw [List.pairwise_cons] at hpair
    obtain ⟨hQdisj, hpair'⟩ := hpair
    have hcliques' : ∀ Q'' ∈ L', IsCliqueOn G Q'' ∧ Q''.card = 5 :=
      fun Q'' hQ'' => hcliques Q'' (List.mem_cons_of_mem _ hQ'')
    have hSdisj' : ∀ Q'' ∈ L', Disjoint S Q'' :=
      fun Q'' hQ'' => hSdisj Q'' (List.mem_cons_of_mem _ hQ'')
    have hlen' : S.card + L'.length ≤ 5 := by
      simp only [List.length_cons] at hlen; omega
    obtain ⟨S'', hS''indep, hS''card, hS''mem⟩ := ih hcliques' hpair' S hS hSdisj' hlen'
    have hS''disjQ : Disjoint S'' Q := by
      rw [Finset.disjoint_left]
      intro x hxS'' hxQ
      rcases hS''mem x hxS'' with hxS | ⟨Q'', hQ''L', hxQ''⟩
      · exact Finset.disjoint_left.mp (hSdisj Q (by simp)) hxS hxQ
      · exact Finset.disjoint_left.mp (hQdisj Q'' hQ''L') hxQ hxQ''
    obtain ⟨hQclique, hQcard⟩ := hcliques Q (by simp)
    have hScard'' : S''.card ≤ 4 := by
      rw [hS''card]; simp only [List.length_cons] at hlen; omega
    obtain ⟨q, hqQ, hqindep⟩ := one_peel G hcap hQclique hQcard hS''indep hS''disjQ hScard''
    have hqnotin : q ∉ S'' := Finset.disjoint_right.mp hS''disjQ hqQ
    refine ⟨insert q S'', hqindep, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hqnotin, hS''card]
      simp only [List.length_cons]; omega
    · intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact Or.inr ⟨Q, (by simp), hqQ⟩
      · rcases hS''mem x hx with hxS | ⟨Q'', hQ''L', hxQ''⟩
        · exact Or.inl hxS
        · exact Or.inr ⟨Q'', List.mem_cons_of_mem _ hQ''L', hxQ''⟩

/-! ## Edge budget: the `T` / `H` partition -/

/-- `e_G(T, H)`, counted from the `T` side: `∑_{t∈T} |N_H(t)|` with `H = univ∖T`. -/
noncomputable def crossCount {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) : ℕ :=
  ∑ t ∈ T, ((Finset.univ \ T).filter (fun v => G.Adj t v)).card

/-- The cross edges (one endpoint in `T`, one in `H = univ∖T`) number `crossCount`. -/
theorem card_cross_eq_crossCount {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) :
    (G.edgeFinset.filter (fun e => ¬ e ∈ (Finset.univ \ T).sym2 ∧ ¬ e ∈ T.sym2)).card
      = crossCount G T := by
  let H : Finset (Fin n) := Finset.univ \ T
  let E (t : Fin n) : Finset (Sym2 (Fin n)) :=
    (H.filter (fun v => G.Adj t v)).image (fun h => s(t, h))
  have hcross :
      G.edgeFinset.filter (fun e => ¬ e ∈ H.sym2 ∧ ¬ e ∈ T.sym2) = T.biUnion E := by
    ext e
    constructor
    · intro he
      rw [Finset.mem_filter] at he
      revert he
      induction e using Sym2.ind with
      | _ u v =>
        intro he
        have hadj : G.Adj u v := by
          rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
          exact he.1
        by_cases hu : u ∈ T
        · have hv : v ∉ T := by
            intro hv
            exact he.2.2 (Finset.mk_mem_sym2_iff.mpr ⟨hu, hv⟩)
          have hvH : v ∈ H := by
            rw [show H = Finset.univ \ T from rfl, Finset.mem_sdiff]
            exact ⟨Finset.mem_univ _, hv⟩
          rw [Finset.mem_biUnion]
          exact ⟨u, hu, Finset.mem_image.mpr ⟨v,
            Finset.mem_filter.mpr ⟨hvH, hadj⟩, rfl⟩⟩
        · have huH : u ∈ H := by
            rw [show H = Finset.univ \ T from rfl, Finset.mem_sdiff]
            exact ⟨Finset.mem_univ _, hu⟩
          have hv : v ∈ T := by
            by_contra hv
            have hvH : v ∈ H := by
              rw [show H = Finset.univ \ T from rfl, Finset.mem_sdiff]
              exact ⟨Finset.mem_univ _, hv⟩
            exact he.2.1 (Finset.mk_mem_sym2_iff.mpr ⟨huH, hvH⟩)
          rw [Finset.mem_biUnion]
          exact ⟨v, hv, Finset.mem_image.mpr ⟨u,
            Finset.mem_filter.mpr ⟨huH, G.adj_symm hadj⟩, Sym2.eq_swap⟩⟩
    · intro he
      rw [Finset.mem_biUnion] at he
      obtain ⟨t, ht, het⟩ := he
      simp only [E, Finset.mem_image] at het
      obtain ⟨h, hh, rfl⟩ := het
      rw [Finset.mem_filter] at hh
      rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      refine ⟨hh.2, ?_, ?_⟩
      · intro hboth
        rw [Finset.mk_mem_sym2_iff] at hboth
        exact (Finset.mem_sdiff.mp hboth.1).2 ht
      · intro hboth
        rw [Finset.mk_mem_sym2_iff] at hboth
        exact (Finset.mem_sdiff.mp hh.1).2 hboth.2
  have hdisj : ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → Disjoint (E t₁) (E t₂) := by
    intro t₁ ht₁ t₂ ht₂ hne
    rw [Finset.disjoint_left]
    intro e he₁ he₂
    simp only [E, Finset.mem_image] at he₁ he₂
    obtain ⟨h₁, hh₁, rfl⟩ := he₁
    obtain ⟨h₂, hh₂, heq⟩ := he₂
    simp only [Sym2.eq_iff] at heq
    rcases heq with heq | heq
    · exact hne heq.1.symm
    · have ht₁h₂ : t₁ = h₂ := heq.2.symm
      have hh₂H := (Finset.mem_filter.mp hh₂).1
      exact (Finset.mem_sdiff.mp hh₂H).2 (ht₁h₂ ▸ ht₁)
  rw [show Finset.univ \ T = H from rfl, hcross, Finset.card_biUnion hdisj]
  unfold crossCount
  simp only [E]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.card_image_of_injOn]
  intro a ha b hb hab
  simp only [Sym2.eq_iff] at hab
  rcases hab with hab | hab
  · exact hab.2
  · have hbH := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).1
    exact False.elim ((Finset.mem_sdiff.mp hbH).2 (hab.1.symm ▸ ht))

/-- **Edge budget split.** `e(G) = e(G[H]) + e(G[T]) + e_G(T,H)` for `H = univ∖T`. -/
theorem edgeCountIn_univ_split {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) :
    edgeCountIn G Finset.univ
      = edgeCountIn G (Finset.univ \ T) + edgeCountIn G T + crossCount G T := by
  rw [edgeCountIn_univ_eq_card_edgeFinset,
      edgeCountIn_eq_filter_edgeFinset G (Finset.univ \ T),
      edgeCountIn_eq_filter_edgeFinset G T, ← card_cross_eq_crossCount G T]
  have key : ∀ e ∈ G.edgeFinset, e ∈ (Finset.univ \ T).sym2 → ¬ e ∈ T.sym2 := by
    intro e _ hpH hpT
    revert hpH hpT
    induction e using Sym2.ind with
    | _ u v =>
      intro hpH hpT
      rw [Finset.mk_mem_sym2_iff] at hpH hpT
      exact (Finset.mem_sdiff.mp hpH.1).2 hpT.1
  have e1 := Finset.card_filter_add_card_filter_not (fun e => e ∈ T.sym2) (s := G.edgeFinset)
  have e2 := Finset.card_filter_add_card_filter_not (fun e => e ∈ (Finset.univ \ T).sym2)
    (s := G.edgeFinset.filter (fun e => ¬ e ∈ T.sym2))
  have e3 : (G.edgeFinset.filter (fun e => ¬ e ∈ T.sym2)).filter
        (fun e => e ∈ (Finset.univ \ T).sym2)
      = G.edgeFinset.filter (fun e => e ∈ (Finset.univ \ T).sym2) := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro e he
    exact ⟨fun h => h.2, fun h => ⟨key e he h, h⟩⟩
  have e4 : (G.edgeFinset.filter (fun e => ¬ e ∈ T.sym2)).filter
        (fun e => ¬ e ∈ (Finset.univ \ T).sym2)
      = G.edgeFinset.filter (fun e => ¬ e ∈ (Finset.univ \ T).sym2 ∧ ¬ e ∈ T.sym2) := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro e _
    tauto
  rw [e3, e4] at e2
  omega

/-! ## Main theorem: bundling and the case split -/

/-- The bundled hypotheses of [MM]: `G` on 25 vertices with `α ≤ 5`, cap-11,
`≤ 60` edges, a 5-set `T` with `α(G−T) ≤ 4` and `e(G[T]) ≤ 6`. -/
structure MMCtx (G : SimpleGraph (Fin 25)) (T : Finset (Fin 25)) : Prop where
  hα5 : ∀ S : Finset (Fin 25), IsIndep G S → S.card ≤ 5
  hcap : capAtMost11 G
  he60 : edgeCountIn G Finset.univ ≤ 60
  hT : T.card = 5
  hαT : ∀ S : Finset (Fin 25), IsIndep G S → Disjoint S T → S.card ≤ 4
  hsT : edgeCountIn G T ≤ 6

/-- `|H| = |univ ∖ T| = 20`. -/
theorem card_H {G : SimpleGraph (Fin 25)} {T : Finset (Fin 25)} (ctx : MMCtx G T) :
    (Finset.univ \ T).card = 20 := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ T), Finset.card_univ, Fintype.card_fin,
    ctx.hT]

/-- **Peeling contradiction.** Pairwise-disjoint 5-cliques `L` inside `H = univ∖T`,
together with an independent set `S ⊆ H` disjoint from all of them with
`|S| + |L| = 5`, contradict `α(H) ≤ 4`: the greedy transversal extends `S` to an
independent 5-set disjoint from `T`. -/
theorem peel_alpha_bound {G : SimpleGraph (Fin 25)} {T : Finset (Fin 25)} (ctx : MMCtx G T)
    (L : List (Finset (Fin 25))) (hcliques : ∀ Q ∈ L, IsCliqueOn G Q ∧ Q.card = 5)
    (hpair : L.Pairwise (fun A B => Disjoint A B)) (hLsub : ∀ Q ∈ L, Q ⊆ Finset.univ \ T)
    {S : Finset (Fin 25)} (hSindep : IsIndep G S) (hSsub : S ⊆ Finset.univ \ T)
    (hSdisj : ∀ Q ∈ L, Disjoint S Q) (hSlen : S.card + L.length = 5) : False := by
  obtain ⟨S', hS'indep, hS'card, hS'mem⟩ :=
    peel_list G ctx.hcap L hcliques hpair S hSindep hSdisj (by omega)
  have hS'sub : S' ⊆ Finset.univ \ T := by
    intro x hx
    rcases hS'mem x hx with hxS | ⟨Q, hQ, hxQ⟩
    · exact hSsub hxS
    · exact hLsub Q hQ hxQ
  have hS'disjT : Disjoint S' T := by
    rw [Finset.disjoint_left]; intro x hx hxT
    exact (Finset.mem_sdiff.mp (hS'sub hx)).2 hxT
  have := ctx.hαT S' hS'indep hS'disjT
  omega

/-! ### The four section lemmas (proved below / stubbed) -/

/-- Transport of `H = G[univ∖T]` to `Fin 20`: it is `α ≤ 4`, cap-11, and (when
`H` is `K_5`-free) `e(H) ≥ 50`. Packaged so §2 can consume `A20` directly. -/
theorem edge_H_ge_fifty {G : SimpleGraph (Fin 25)} {T : Finset (Fin 25)} (ctx : MMCtx G T)
    (pf : PrimFacts)
    (hfree : ∀ Q : Finset (Fin 25), Q ⊆ Finset.univ \ T → Q.card = 5 → ¬ IsCliqueOn G Q) :
    50 ≤ edgeCountIn G (Finset.univ \ T) := by
  obtain ⟨e20, he20⟩ := exists_embedding_image_eq (Finset.univ \ T) (card_H ctx)
  have hHα4 : alphaAtMost (G.comap e20) 4 := by
    refine alphaAtMost_comap_mm G e20 ?_
    intro S hSsub hSindep
    rw [he20] at hSsub
    refine ctx.hαT S hSindep ?_
    rw [Finset.disjoint_left]
    intro x hx hxT
    exact (Finset.mem_sdiff.mp (hSsub hx)).2 hxT
  have hHω : (G.comap e20).CliqueFree 5 := by
    refine cliqueFree_comap_of_no_clique G e20 ?_
    intro Q hQsub hQc
    rw [he20] at hQsub
    exact hfree Q hQsub hQc
  have hHcap : capAtMost11 (G.comap e20) := capAtMost11_comap G e20 ctx.hcap
  have h := A20 pf (G.comap e20) hHα4 hHω hHcap
  rwa [edgeCountIn_comap, he20] at h

/-- **§2, the `U_{tt'}` floor.** For a non-edge `tt'` of `G[T]`, if `e(H) < ℓ(k)`
(for some `k ≤ 19`), then the neighbourhood-union `U = N_H(t) ∪ N_H(t')` has
`≥ 21 − k` vertices. (Residual `R = H − U` has `α ≤ 3` via `S ∪ {t,t'}`, is
`K_5`-free and cap-11, so a `k`-subset would force `ℓ(k) ≤ e(R) ≤ e(H)`.) -/
theorem nonedge_U_ge {G : SimpleGraph (Fin 25)} {T : Finset (Fin 25)} (ctx : MMCtx G T)
    (hfree : ∀ Q : Finset (Fin 25), Q ⊆ Finset.univ \ T → Q.card = 5 → ¬ IsCliqueOn G Q)
    (pf : PrimFacts) {t t' : Fin 25} (htT : t ∈ T) (ht'T : t' ∈ T) (hne : t ≠ t')
    (hnadj : ¬ G.Adj t t') (k : ℕ) (hk : k ≤ 19)
    (hm : edgeCountIn G (Finset.univ \ T) < ell k) :
    21 - k ≤ ((Finset.univ \ T).filter (fun v => G.Adj t v ∨ G.Adj t' v)).card := by
  set Hset := Finset.univ \ T with hHdef
  have hHcard : Hset.card = 20 := card_H ctx
  set Uset := Hset.filter (fun v => G.Adj t v ∨ G.Adj t' v) with hUdef
  set Rset := Hset.filter (fun v => ¬ (G.Adj t v ∨ G.Adj t' v)) with hRdef
  have hpart : Uset.card + Rset.card = 20 := by
    have h := Finset.card_filter_add_card_filter_not (fun v => G.Adj t v ∨ G.Adj t' v)
      (s := Hset)
    rw [hUdef, hRdef]; omega
  have hαR : ∀ S : Finset (Fin 25), S ⊆ Rset → IsIndep G S → S.card ≤ 3 := by
    intro S hSsub hSindep
    have hmemR : ∀ v ∈ S, ¬ G.Adj t v ∧ ¬ G.Adj t' v := by
      intro v hv
      have := hSsub hv
      rw [hRdef, Finset.mem_filter] at this
      exact not_or.mp this.2
    have htnS : t ∉ S := by
      intro h; have := hSsub h
      rw [hRdef, Finset.mem_filter, hHdef, Finset.mem_sdiff] at this
      exact this.1.2 htT
    have ht'nS : t' ∉ S := by
      intro h; have := hSsub h
      rw [hRdef, Finset.mem_filter, hHdef, Finset.mem_sdiff] at this
      exact this.1.2 ht'T
    have hindep : IsIndep G (insert t (insert t' S)) := by
      intro a ha b hb hab
      simp only [Finset.mem_insert] at ha hb
      rcases ha with rfl | rfl | ha <;> rcases hb with rfl | rfl | hb
      · exact absurd rfl hab
      · exact hnadj
      · exact (hmemR b hb).1
      · exact fun h => hnadj (G.symm h)
      · exact absurd rfl hab
      · exact (hmemR b hb).2
      · exact fun h => (hmemR a ha).1 (G.symm h)
      · exact fun h => (hmemR a ha).2 (G.symm h)
      · exact hSindep a ha b hb hab
    have hcard : (insert t (insert t' S)).card = S.card + 2 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ht'nS]
      rw [Finset.mem_insert, not_or]
      exact ⟨hne, htnS⟩
    have := ctx.hα5 _ hindep
    omega
  by_contra hlt
  push Not at hlt
  have hRk : k ≤ Rset.card := by omega
  obtain ⟨W, hWsub, hWcard⟩ := Finset.exists_subset_card_eq hRk
  have hWHset : W ⊆ Hset := hWsub.trans (Finset.filter_subset _ _)
  have hell : ell k ≤ edgeCountIn G W := by
    rw [← hWcard]
    refine ell_le_edgeCountIn pf G W ctx.hcap ?_ ?_ (by rw [hWcard]; exact hk)
    · intro S hSsub hSindep
      exact hαR S (hSsub.trans hWsub) hSindep
    · intro Q hQsub hQc
      exact hfree Q (hQsub.trans hWHset) hQc
  have hWm : edgeCountIn G W ≤ edgeCountIn G Hset := edgeCountIn_mono G hWHset
  omega

/-- **§2 counting (9).** If every non-edge `tt'` of `G[T]` (|T|=5) has
`|N_H(t) ∪ N_H(t')| ≥ c`, then `c · (20 − 2·e(G[T])) ≤ 8 · e_G(T,H)`. (Sum the
per-non-edge bound over the `20 − 2s` ordered non-edges; `|U| ≤ d_H(t)+d_H(t')`,
and each `d_H(t)` occurs ≤ 4 times, giving `≤ 8·crossCount`.) -/
theorem sum_U_counting {G : SimpleGraph (Fin 25)} {T : Finset (Fin 25)} {c : ℕ}
    (hT : T.card = 5)
    (hUlb : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → ¬ G.Adj t t' →
      c ≤ ((Finset.univ \ T).filter (fun v => G.Adj t v ∨ G.Adj t' v)).card) :
    c * (20 - 2 * edgeCountIn G T) ≤ 8 * crossCount G T := by
  let OD := (T ×ˢ T).filter (fun p => p.1 ≠ p.2)
  let A := (T ×ˢ T).filter (fun p => G.Adj p.1 p.2)
  let ONE := OD.filter (fun p => ¬ G.Adj p.1 p.2)
  let H := Finset.univ \ T
  let d (t : Fin 25) := (H.filter (fun v => G.Adj t v)).card
  -- The ordered adjacent pairs are ≤ 2·e(G[T]) (each edge has ≤ 2 ordered preimages).
  have hAle : A.card ≤ 2 * edgeCountIn G T := by
    have himg : A.image (fun p => s(p.1, p.2)) ⊆ T.sym2.filter (fun e => e ∈ G.edgeSet) := by
      intro e he
      rw [Finset.mem_image] at he
      obtain ⟨p, hp, rfl⟩ := he
      simp only [A, Finset.mem_filter, Finset.mem_product] at hp
      rw [Finset.mem_filter]
      exact ⟨Finset.mk_mem_sym2_iff.mpr ⟨hp.1.1, hp.1.2⟩,
        by rw [SimpleGraph.mem_edgeSet]; exact hp.2⟩
    have hfib : ∀ e ∈ A.image (fun p => s(p.1, p.2)),
        (A.filter (fun p => s(p.1, p.2) = e)).card ≤ 2 := by
      intro e he
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp he
      have hsub2 : A.filter (fun p => s(p.1, p.2) = s(q.1, q.2)) ⊆
          ({(q.1, q.2), (q.2, q.1)} : Finset (Fin 25 × Fin 25)) := by
        intro p hp
        rw [Finset.mem_filter] at hp
        have hpe := hp.2
        rw [Sym2.eq_iff] at hpe
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases hpe with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl (Prod.ext h1 h2)
        · exact Or.inr (Prod.ext h1 h2)
      calc (A.filter (fun p => s(p.1, p.2) = s(q.1, q.2))).card
          ≤ ({(q.1, q.2), (q.2, q.1)} : Finset (Fin 25 × Fin 25)).card :=
            Finset.card_le_card hsub2
        _ ≤ 2 := le_trans (Finset.card_insert_le _ _) (by simp)
    calc A.card ≤ 2 * (A.image (fun p => s(p.1, p.2))).card :=
          Finset.card_le_mul_card_image _ _ hfib
      _ ≤ 2 * edgeCountIn G T :=
          Nat.mul_le_mul_left 2 (Finset.card_le_card himg)
  have hdiag : ((T ×ˢ T).filter (fun p => p.1 = p.2)).card = 5 := by
    rw [← hT]
    refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
    · intro p hp; exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    · intro p hp q hq h
      rw [Finset.mem_filter] at hp hq
      refine Prod.ext h ?_
      rw [← hp.2, ← hq.2]; exact h
    · intro t ht
      exact ⟨(t, t), by rw [Finset.mem_filter, Finset.mem_product]; exact ⟨⟨ht, ht⟩, rfl⟩, rfl⟩
  have hODcard : OD.card = 20 := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (fun p : Fin 25 × Fin 25 => p.1 = p.2) (s := T ×ˢ T)
    have hprod : (T ×ˢ T).card = 25 := by rw [Finset.card_product, hT]
    rw [hprod, hdiag] at hsplit
    show (OD).card = 20
    have hODeq : OD = (T ×ˢ T).filter (fun p => ¬ p.1 = p.2) := rfl
    rw [hODeq]; omega
  have hAfilt : OD.filter (fun p => G.Adj p.1 p.2) = A := by
    simp only [OD, A, Finset.filter_filter]
    apply Finset.filter_congr
    intro p _
    exact ⟨fun h => h.2, fun h => ⟨G.ne_of_adj h, h⟩⟩
  have hONEge : 20 - 2 * edgeCountIn G T ≤ ONE.card := by
    have hs := Finset.card_filter_add_card_filter_not
      (fun p : Fin 25 × Fin 25 => G.Adj p.1 p.2) (s := OD)
    rw [hAfilt, hODcard] at hs
    show 20 - 2 * edgeCountIn G T ≤ (OD.filter (fun p => ¬ G.Adj p.1 p.2)).card
    omega
  have hlow : c * ONE.card ≤ ∑ p ∈ ONE,
      (H.filter (fun v => G.Adj p.1 v ∨ G.Adj p.2 v)).card := by
    have hconst : c * ONE.card = ∑ _p ∈ ONE, c := by
      rw [Finset.sum_const, smul_eq_mul, mul_comm]
    rw [hconst]
    apply Finset.sum_le_sum
    intro p hp
    have hpOD : p ∈ OD := (Finset.mem_filter.mp hp).1
    have hp2 : ¬ G.Adj p.1 p.2 := (Finset.mem_filter.mp hp).2
    have hpprod : p.1 ∈ T ∧ p.2 ∈ T := Finset.mem_product.mp (Finset.mem_filter.mp hpOD).1
    have hpne : p.1 ≠ p.2 := (Finset.mem_filter.mp hpOD).2
    exact hUlb p.1 hpprod.1 p.2 hpprod.2 hpne hp2
  have hmid : (∑ p ∈ ONE, (H.filter (fun v => G.Adj p.1 v ∨ G.Adj p.2 v)).card) ≤
      ∑ p ∈ ONE, (d p.1 + d p.2) := by
    apply Finset.sum_le_sum
    intro p _
    rw [Finset.filter_or]
    exact Finset.card_union_le _ _
  have hsub : ONE ⊆ OD := fun p hp => (Finset.mem_filter.mp hp).1
  have hfirst : (∑ p ∈ ONE, d p.1) ≤ 4 * ∑ t ∈ T, d t := by
    calc (∑ p ∈ ONE, d p.1) ≤ ∑ p ∈ OD, d p.1 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
      _ = ∑ p ∈ (T ×ˢ T).filter (fun p => p.1 ≠ p.2), d p.1 := by simp only [OD]
      _ = ∑ p ∈ T ×ˢ T, (if p.1 ≠ p.2 then d p.1 else 0) := by rw [Finset.sum_filter]
      _ = ∑ t ∈ T, ∑ t' ∈ T, (if t ≠ t' then d t else 0) := by rw [Finset.sum_product]
      _ = ∑ t ∈ T, 4 * d t := by
          apply Finset.sum_congr rfl
          intro t ht
          have he : T.filter (fun t' => t ≠ t') = T.erase t := by
            ext a
            simp only [Finset.mem_filter, Finset.mem_erase]
            exact ⟨fun h => ⟨fun ha => h.2 ha.symm, h.1⟩, fun h => ⟨h.2, fun ha => h.1 ha.symm⟩⟩
          rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, he,
            Finset.card_erase_of_mem ht, hT]
      _ = 4 * ∑ t ∈ T, d t := by rw [Finset.mul_sum]
  have hsecond : (∑ p ∈ ONE, d p.2) ≤ 4 * ∑ t ∈ T, d t := by
    calc (∑ p ∈ ONE, d p.2) ≤ ∑ p ∈ OD, d p.2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
      _ = ∑ p ∈ (T ×ˢ T).filter (fun p => p.1 ≠ p.2), d p.2 := by simp only [OD]
      _ = ∑ p ∈ T ×ˢ T, (if p.1 ≠ p.2 then d p.2 else 0) := by rw [Finset.sum_filter]
      _ = ∑ t ∈ T, ∑ t' ∈ T, (if t ≠ t' then d t' else 0) := by rw [Finset.sum_product]
      _ = ∑ t' ∈ T, ∑ t ∈ T, (if t ≠ t' then d t' else 0) := Finset.sum_comm
      _ = ∑ t' ∈ T, 4 * d t' := by
          apply Finset.sum_congr rfl
          intro t' ht'
          have he : T.filter (fun t => t ≠ t') = T.erase t' := by
            ext a
            simp only [Finset.mem_filter, Finset.mem_erase]
            exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
          rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, he,
            Finset.card_erase_of_mem ht', hT]
      _ = 4 * ∑ t' ∈ T, d t' := by rw [Finset.mul_sum]
  calc c * (20 - 2 * edgeCountIn G T)
      ≤ c * ONE.card := Nat.mul_le_mul_left c hONEge
    _ ≤ ∑ p ∈ ONE, (H.filter (fun v => G.Adj p.1 v ∨ G.Adj p.2 v)).card := hlow
    _ ≤ ∑ p ∈ ONE, (d p.1 + d p.2) := hmid
    _ = (∑ p ∈ ONE, d p.1) + ∑ p ∈ ONE, d p.2 := by rw [Finset.sum_add_distrib]
    _ ≤ 4 * (∑ t ∈ T, d t) + 4 * (∑ t ∈ T, d t) := Nat.add_le_add hfirst hsecond
    _ = 8 * ∑ t ∈ T, d t := by ring
    _ = 8 * crossCount G T := by unfold crossCount; rfl

/-- **Insert edge count (equality).** `edgeCountIn G (insert x Q) = e(Q) + (# Q-neighbours of x)`. -/
theorem edgeCountIn_insert_eq (G : SimpleGraph (Fin n)) {x : Fin n} {Q : Finset (Fin n)}
    (hx : x ∉ Q) :
    edgeCountIn G (insert x Q) = edgeCountIn G Q + (Q.filter (fun q => G.Adj x q)).card := by
  set A := Q.filter (fun q => G.Adj x q) with hA
  set spokes := A.image (fun w => s(x, w)) with hsp
  have hinj : Set.InjOn (fun w => s(x, w)) A := by
    intro a ha b hb hab
    simp only [Sym2.eq_iff] at hab
    rcases hab with ⟨_, h⟩ | ⟨_, hav⟩
    · exact h
    · exact absurd (hav ▸ (Finset.filter_subset _ Q (Finset.mem_coe.mp ha))) hx
  have hspoke_card : spokes.card = A.card := by
    rw [hsp, Finset.card_image_of_injOn hinj]
  have hdisj : Disjoint (Q.sym2.filter (fun e => e ∈ G.edgeSet)) spokes := by
    rw [Finset.disjoint_left]
    intro e he hesp
    rw [Finset.mem_filter] at he
    rw [hsp, Finset.mem_image] at hesp
    obtain ⟨w, hw, hwe⟩ := hesp
    have hmem := he.1
    rw [← hwe, Finset.mk_mem_sym2_iff] at hmem
    exact hx hmem.1
  have hset : (Q.sym2.filter (fun e => e ∈ G.edgeSet)) ∪ spokes
      = (insert x Q).sym2.filter (fun e => e ∈ G.edgeSet) := by
    apply Finset.Subset.antisymm
    · intro e he
      rw [Finset.mem_union] at he
      rw [Finset.mem_filter]
      rcases he with he | he
      · rw [Finset.mem_filter] at he
        exact ⟨Finset.sym2_mono (Finset.subset_insert x Q) he.1, he.2⟩
      · rw [hsp, Finset.mem_image] at he
        obtain ⟨w, hw, rfl⟩ := he
        rw [hA, Finset.mem_filter] at hw
        refine ⟨?_, ?_⟩
        · rw [Finset.mk_mem_sym2_iff]
          exact ⟨Finset.mem_insert_self x Q, Finset.mem_insert_of_mem hw.1⟩
        · rw [SimpleGraph.mem_edgeSet]; exact hw.2
    · intro e he
      rw [Finset.mem_filter] at he
      revert he
      induction e using Sym2.ind with
      | _ u v =>
        intro he
        obtain ⟨hmem, hedge⟩ := he
        rw [Finset.mk_mem_sym2_iff] at hmem
        have hadj : G.Adj u v := by rw [SimpleGraph.mem_edgeSet] at hedge; exact hedge
        have huv : u ≠ v := G.ne_of_adj hadj
        rw [Finset.mem_union]
        rcases Finset.mem_insert.mp hmem.1 with rfl | huQ <;>
          rcases Finset.mem_insert.mp hmem.2 with rfl | hvQ
        · exact absurd rfl huv
        · right
          rw [hsp, Finset.mem_image]
          exact ⟨v, Finset.mem_filter.mpr ⟨hvQ, hadj⟩, rfl⟩
        · right
          rw [hsp, Finset.mem_image]
          exact ⟨u, Finset.mem_filter.mpr ⟨huQ, G.symm hadj⟩, Sym2.eq_swap⟩
        · left
          rw [Finset.mem_filter]
          exact ⟨Finset.mk_mem_sym2_iff.mpr ⟨huQ, hvQ⟩, hedge⟩
  unfold edgeCountIn
  rw [← hset, Finset.card_union_of_disjoint hdisj, hspoke_card]

/-- **3-way disjoint edge split (equality).** For disjoint `A B`,
`e(A ∪ B) = e(A) + e(B) + ∑_{b∈B} (# A-neighbours of b)`. -/
theorem edgeCountIn_union_disjoint_eq (G : SimpleGraph (Fin n)) {A B : Finset (Fin n)}
    (h : Disjoint A B) :
    edgeCountIn G (A ∪ B)
      = edgeCountIn G A + edgeCountIn G B
        + ∑ b ∈ B, (A.filter (fun v => G.Adj b v)).card := by
  induction B using Finset.induction with
  | empty =>
    simp only [Finset.union_empty, Finset.sum_empty, add_zero]
    have h0 : edgeCountIn G (∅ : Finset (Fin n)) = 0 := by unfold edgeCountIn; simp
    rw [h0, add_zero]
  | insert b B' hbB' ih =>
    have hb_notin_A : b ∉ A := Finset.disjoint_right.mp h (Finset.mem_insert_self b B')
    have hAB' : Disjoint A B' := h.mono_right (Finset.subset_insert b B')
    have hb_notin_AB' : b ∉ A ∪ B' :=
      fun hc => (Finset.mem_union.mp hc).elim hb_notin_A hbB'
    have hunion : A ∪ insert b B' = insert b (A ∪ B') := by rw [Finset.union_insert]
    rw [hunion, edgeCountIn_insert_eq G hb_notin_AB', ih hAB',
        edgeCountIn_insert_eq G hbB']
    have hfiltdisj : Disjoint (A.filter (fun q => G.Adj b q)) (B'.filter (fun q => G.Adj b q)) := by
      rw [Finset.disjoint_left]
      intro e he he'
      exact Finset.disjoint_left.mp hAB' (Finset.mem_of_mem_filter _ he)
        (Finset.mem_of_mem_filter _ he')
    have hfilt : ((A ∪ B').filter (fun q => G.Adj b q)).card
        = (A.filter (fun v => G.Adj b v)).card + (B'.filter (fun q => G.Adj b q)).card := by
      rw [Finset.filter_union, Finset.card_union_of_disjoint hfiltdisj]
    rw [hfilt, Finset.sum_insert hbB']
    ring

/-- **Handshake on a set.** `∑_{u∈U} (# U-neighbours of u) = 2·e(U)`. -/
theorem sum_adj_filter_eq_two_mul (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) :
    ∑ u ∈ U, (U.filter (fun w => G.Adj u w)).card = 2 * edgeCountIn G U := by
  induction U using Finset.induction with
  | empty => simp [edgeCountIn]
  | insert a U' haU' ih =>
    have key : ∀ u ∈ U', ((insert a U').filter (fun w => G.Adj u w)).card
        = (U'.filter (fun w => G.Adj u w)).card + (if G.Adj u a then 1 else 0) := by
      intro u hu
      rw [Finset.filter_insert]
      by_cases hua : G.Adj u a
      · rw [if_pos hua, Finset.card_insert_of_notMem, if_pos hua]
        rw [Finset.mem_filter]; push_neg; intro ha'; exact absurd ha' haU'
      · rw [if_neg hua, if_neg hua, add_zero]
    have hself : ((insert a U').filter (fun w => G.Adj a w)).card
        = (U'.filter (fun w => G.Adj a w)).card := by
      rw [Finset.filter_insert, if_neg (fun h => (G.ne_of_adj h) rfl)]
    rw [Finset.sum_insert haU', hself, Finset.sum_congr rfl key, Finset.sum_add_distrib]
    have hcount : ∑ u ∈ U', (if G.Adj u a then 1 else 0)
        = (U'.filter (fun w => G.Adj a w)).card := by
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro u _
      by_cases hua : G.Adj u a
      · rw [if_pos hua, if_pos (G.symm hua)]
      · rw [if_neg hua, if_neg (fun h => hua (G.symm h))]
    rw [hcount, ih, edgeCountIn_insert_eq G haU']
    ring

/-- **δ(H) ≥ 3 at m = 50.** Every `v ∈ H = univ∖T` has ≥ 3 `H`-neighbours: else
`m ≥ d_H(v) + ℓ(19−d_H(v)) ≥ 55 > 50`. -/
theorem deltaH_ge_three {G : SimpleGraph (Fin 25)} {T : Finset (Fin 25)} (ctx : MMCtx G T)
    (pf : PrimFacts)
    (hfree : ∀ Q : Finset (Fin 25), Q ⊆ Finset.univ \ T → Q.card = 5 → ¬ IsCliqueOn G Q)
    (hm50 : edgeCountIn G (Finset.univ \ T) = 50)
    {v : Fin 25} (hv : v ∈ Finset.univ \ T) :
    3 ≤ ((Finset.univ \ T).filter (fun w => G.Adj v w)).card := by
  set H := Finset.univ \ T with hHdef
  have hHcard : H.card = 20 := card_H ctx
  set Nv := H.filter (fun w => G.Adj v w) with hNvdef
  have hvNv : v ∉ Nv := by
    rw [hNvdef, Finset.mem_filter]; push_neg; intro _; exact G.irrefl
  have hNvH : Nv ⊆ H := Finset.filter_subset _ _
  have hinsertsub : insert v Nv ⊆ H := Finset.insert_subset hv hNvH
  have hinsertcard : (insert v Nv).card = Nv.card + 1 := Finset.card_insert_of_notMem hvNv
  set Wv := H \ insert v Nv with hWvdef
  have hWvcard : Wv.card = 19 - Nv.card := by
    have hc := Finset.card_sdiff_add_card_eq_card hinsertsub
    rw [hinsertcard, hHcard] at hc
    rw [hWvdef]; omega
  have hd19 : Nv.card ≤ 19 := by
    have := Finset.card_le_card hinsertsub
    rw [hinsertcard, hHcard] at this; omega
  have hαWv : ∀ S : Finset (Fin 25), S ⊆ Wv → IsIndep G S → S.card ≤ 3 := by
    intro S hSsub hSindep
    have hvS : v ∉ S := by
      intro hvS'
      have := hSsub hvS'
      rw [hWvdef, Finset.mem_sdiff] at this
      exact this.2 (Finset.mem_insert_self v Nv)
    have hnadj : ∀ w ∈ S, ¬ G.Adj v w := by
      intro w hw
      have hwWv := hSsub hw
      rw [hWvdef, Finset.mem_sdiff] at hwWv
      intro hadj
      exact hwWv.2 (Finset.mem_insert_of_mem
        (by rw [hNvdef, Finset.mem_filter]; exact ⟨hwWv.1, hadj⟩))
    have hins : IsIndep G (insert v S) := by
      intro a ha b hb hab
      rw [Finset.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact hnadj b hb
      · exact fun h => hnadj a ha (G.symm h)
      · exact hSindep a ha b hb hab
    have hdisjT : Disjoint (insert v S) T := by
      rw [Finset.disjoint_left]
      intro x hx hxT
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact (Finset.mem_sdiff.mp hv).2 hxT
      · have := hSsub hx
        rw [hWvdef, Finset.mem_sdiff] at this
        exact (Finset.mem_sdiff.mp this.1).2 hxT
    have hcard : (insert v S).card = S.card + 1 := Finset.card_insert_of_notMem hvS
    have := ctx.hαT (insert v S) hins hdisjT
    omega
  have hellWv : ell (19 - Nv.card) ≤ edgeCountIn G Wv := by
    have h := ell_le_edgeCountIn pf G Wv ctx.hcap hαWv
      (fun Q hQsub hQc => hfree Q (hQsub.trans (by rw [hWvdef]; exact Finset.sdiff_subset)) hQc)
      (by rw [hWvcard]; omega)
    rwa [hWvcard] at h
  have hinsertge : Nv.card ≤ edgeCountIn G (insert v Nv) := by
    rw [edgeCountIn_insert_eq G hvNv]
    have hfilt : Nv.filter (fun q => G.Adj v q) = Nv := by
      apply Finset.filter_true_of_mem
      intro w hw
      rw [hNvdef, Finset.mem_filter] at hw; exact hw.2
    rw [hfilt]; omega
  have hdisj : Disjoint (insert v Nv) Wv := by rw [hWvdef]; exact Finset.disjoint_sdiff
  have hunion : insert v Nv ∪ Wv = H := by
    rw [hWvdef, Finset.union_comm]; exact Finset.sdiff_union_of_subset hinsertsub
  have hfloor : Nv.card + ell (19 - Nv.card) ≤ edgeCountIn G H := by
    have h := edgeCountIn_add_le_union_disjoint G hdisj
    rw [hunion] at h; omega
  rw [hm50] at hfloor
  rcases Nat.lt_or_ge (Nv.card) 3 with hlt | hge
  · exfalso
    have hcases : Nv.card = 0 ∨ Nv.card = 1 ∨ Nv.card = 2 := by omega
    rcases hcases with h | h | h <;> rw [h] at hfloor <;> revert hfloor <;> decide
  · exact hge

/-- **No 4-set with α ≤ 3 residual (at m = 50).** With `δ(H) ≥ 3`, a 4-set `U ⊆ H`
with `α(G[H∖U]) ≤ 3` forces `e(H) ≥ e(H∖U) + 6 ≥ 46 + 6 = 52 > 50 = m`. -/
theorem no_four_set_alpha3 {G : SimpleGraph (Fin 25)} {T : Finset (Fin 25)} (ctx : MMCtx G T)
    (pf : PrimFacts)
    (hfree : ∀ Q : Finset (Fin 25), Q ⊆ Finset.univ \ T → Q.card = 5 → ¬ IsCliqueOn G Q)
    (hm50 : edgeCountIn G (Finset.univ \ T) = 50)
    (hδ : ∀ v ∈ Finset.univ \ T, 3 ≤ ((Finset.univ \ T).filter (fun w => G.Adj v w)).card)
    {U : Finset (Fin 25)} (hUH : U ⊆ Finset.univ \ T) (hUcard : U.card = 4)
    (hUα : ∀ S : Finset (Fin 25), S ⊆ (Finset.univ \ T) \ U → IsIndep G S → S.card ≤ 3) :
    False := by
  set H := Finset.univ \ T with hHdef
  have hHcard : H.card = 20 := card_H ctx
  have hHUcard : (H \ U).card = 16 := by
    have hc := Finset.card_sdiff_add_card_eq_card hUH
    rw [hHcard, hUcard] at hc; omega
  have hell16 : 46 ≤ edgeCountIn G (H \ U) := by
    have h := ell_le_edgeCountIn pf G (H \ U) ctx.hcap
      (fun S hSsub hSindep => hUα S hSsub hSindep)
      (fun Q hQsub hQc => hfree Q (hQsub.trans Finset.sdiff_subset) hQc)
      (by rw [hHUcard]; norm_num)
    rwa [hHUcard, show ell 16 = 46 from by decide] at h
  have hdisjHU : Disjoint (H \ U) U := Finset.sdiff_disjoint
  have hsplit := edgeCountIn_union_disjoint_eq G hdisjHU
  rw [Finset.sdiff_union_of_subset hUH] at hsplit
  have hpt : ∀ u, (H.filter (fun w => G.Adj u w)).card
      = ((H \ U).filter (fun w => G.Adj u w)).card + (U.filter (fun w => G.Adj u w)).card := by
    intro u
    have hHeq : H = (H \ U) ∪ U := (Finset.sdiff_union_of_subset hUH).symm
    conv_lhs => rw [hHeq]
    rw [Finset.filter_union, Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]; intro e he he'
    exact Finset.disjoint_left.mp Finset.sdiff_disjoint
      (Finset.mem_of_mem_filter _ he) (Finset.mem_of_mem_filter _ he')
  have hsumdeg : ∑ u ∈ U, (H.filter (fun w => G.Adj u w)).card
      = (∑ u ∈ U, ((H \ U).filter (fun w => G.Adj u w)).card) + 2 * edgeCountIn G U := by
    rw [show (∑ u ∈ U, (H.filter (fun w => G.Adj u w)).card)
        = ∑ u ∈ U, (((H \ U).filter (fun w => G.Adj u w)).card
          + (U.filter (fun w => G.Adj u w)).card) from Finset.sum_congr rfl (fun u _ => hpt u),
        Finset.sum_add_distrib, sum_adj_filter_eq_two_mul]
  have hdeglb : 12 ≤ ∑ u ∈ U, (H.filter (fun w => G.Adj u w)).card := by
    calc 12 = ∑ _u ∈ U, 3 := by rw [Finset.sum_const, hUcard, smul_eq_mul]
      _ ≤ ∑ u ∈ U, (H.filter (fun w => G.Adj u w)).card :=
          Finset.sum_le_sum (fun u hu => hδ u (hUH hu))
  have heU6 : edgeCountIn G U ≤ 6 := by
    have h := edgeCountIn_le_choose_two G U
    rw [hUcard] at h; simpa using h
  omega

/-- **α(H − U_{tt'}) ≤ 3.** For a non-edge `tt'` of `G[T]`, the residual
`H \ (N_H(t) ∪ N_H(t'))` has independence number ≤ 3 (an independent 4-set plus
`t, t'` would be an independent 6-set). -/
theorem nonedge_residual_alpha3 {G : SimpleGraph (Fin 25)} {T : Finset (Fin 25)} (ctx : MMCtx G T)
    {t t' : Fin 25} (htT : t ∈ T) (ht'T : t' ∈ T) (hne : t ≠ t') (hnadj : ¬ G.Adj t t') :
    ∀ S : Finset (Fin 25),
      S ⊆ (Finset.univ \ T) \ ((Finset.univ \ T).filter (fun v => G.Adj t v ∨ G.Adj t' v)) →
      IsIndep G S → S.card ≤ 3 := by
  intro S hSsub hSindep
  have hmemR : ∀ v ∈ S, ¬ G.Adj t v ∧ ¬ G.Adj t' v := by
    intro v hv
    have hvR := hSsub hv
    rw [Finset.mem_sdiff] at hvR
    have hvnU := hvR.2
    rw [Finset.mem_filter, not_and] at hvnU
    exact not_or.mp (hvnU hvR.1)
  have htnS : t ∉ S := by
    intro h; have hh := hSsub h
    rw [Finset.mem_sdiff, Finset.mem_sdiff] at hh
    exact hh.1.2 htT
  have ht'nS : t' ∉ S := by
    intro h; have hh := hSsub h
    rw [Finset.mem_sdiff, Finset.mem_sdiff] at hh
    exact hh.1.2 ht'T
  have hindep : IsIndep G (insert t (insert t' S)) := by
    intro a ha b hb hab
    simp only [Finset.mem_insert] at ha hb
    rcases ha with rfl | rfl | ha <;> rcases hb with rfl | rfl | hb
    · exact absurd rfl hab
    · exact hnadj
    · exact (hmemR b hb).1
    · exact fun h => hnadj (G.symm h)
    · exact absurd rfl hab
    · exact (hmemR b hb).2
    · exact fun h => (hmemR a ha).1 (G.symm h)
    · exact fun h => (hmemR a ha).2 (G.symm h)
    · exact hSindep a ha b hb hab
  have hcard : (insert t (insert t' S)).card = S.card + 2 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ht'nS]
    rw [Finset.mem_insert, not_or]
    exact ⟨hne, htnS⟩
  have := ctx.hα5 _ hindep
  omega

/-- **§2.** `H = G − T` is `K_5`-free ⇒ contradiction. -/
theorem section2_free {G : SimpleGraph (Fin 25)} {T : Finset (Fin 25)} (ctx : MMCtx G T)
    (pf : PrimFacts)
    (hfree : ∀ Q : Finset (Fin 25), Q ⊆ Finset.univ \ T → Q.card = 5 → ¬ IsCliqueOn G Q) :
    False := by
  -- m = e(H) ≥ 50; budget m + x + s ≤ 60; s = e(G[T]) ≤ 6, so r := 10 − s ≥ 4.
  have hm50 : 50 ≤ edgeCountIn G (Finset.univ \ T) := edge_H_ge_fifty ctx pf hfree
  have hsplit := edgeCountIn_univ_split G T
  have hbudget : edgeCountIn G (Finset.univ \ T) + edgeCountIn G T + crossCount G T ≤ 60 := by
    have := ctx.he60; omega
  set m := edgeCountIn G (Finset.univ \ T) with hmdef
  set s := edgeCountIn G T with hsdef
  set x := crossCount G T with hxdef
  have hs6 : s ≤ 6 := ctx.hsT
  by_cases hm53 : 53 ≤ m
  · -- m ≥ 53: every non-edge has |U| ≥ 3 (ℓ(18) = 62 > m).
    have hUlb : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → ¬ G.Adj t t' →
        3 ≤ ((Finset.univ \ T).filter (fun v => G.Adj t v ∨ G.Adj t' v)).card := by
      intro t htT t' ht'T hne hnadj
      have h := nonedge_U_ge ctx hfree pf htT ht'T hne hnadj 18 (by norm_num)
        (by show m < ell 18; rw [show ell 18 = 62 from by decide]; omega)
      simpa using h
    have hcount := sum_U_counting ctx.hT hUlb
    rw [← hsdef, ← hxdef] at hcount
    omega
  · by_cases hm51 : 51 ≤ m
    · -- m ∈ {51,52}: every non-edge has |U| ≥ 4 (ℓ(17) = 53 > m).
      have hUlb : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → ¬ G.Adj t t' →
          4 ≤ ((Finset.univ \ T).filter (fun v => G.Adj t v ∨ G.Adj t' v)).card := by
        intro t htT t' ht'T hne hnadj
        have h := nonedge_U_ge ctx hfree pf htT ht'T hne hnadj 17 (by norm_num)
          (by show m < ell 17; rw [show ell 17 = 53 from by decide]; omega)
        simpa using h
      have hcount := sum_U_counting ctx.hT hUlb
      rw [← hsdef, ← hxdef] at hcount
      omega
    · -- m = 50: δ(H) ≥ 3 (else `d(v) + ℓ(19−d(v)) ≥ 55`); every |U_{tt'}| ≥ 5 (a
      -- 4-set residual with α ≤ 3 would give `e(H) ≥ ℓ(16) + 6 = 52 > 50` via the
      -- subset handshake); then `5r ≤ 4x ≤ 4r`.
      have hm50' : m = 50 := by omega
      have hm50'' : edgeCountIn G (Finset.univ \ T) = 50 := by rw [← hmdef]; exact hm50'
      have hδ : ∀ v ∈ Finset.univ \ T,
          3 ≤ ((Finset.univ \ T).filter (fun w => G.Adj v w)).card :=
        fun v hv => deltaH_ge_three ctx pf hfree hm50'' hv
      have hU5 : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → ¬ G.Adj t t' →
          5 ≤ ((Finset.univ \ T).filter (fun v => G.Adj t v ∨ G.Adj t' v)).card := by
        intro t htT t' ht'T hne hnadj
        by_contra hlt
        push_neg at hlt
        have hU4 := nonedge_U_ge ctx hfree pf htT ht'T hne hnadj 17 (by norm_num)
          (by rw [hm50'', show ell 17 = 53 from by decide]; norm_num)
        have hUcard : ((Finset.univ \ T).filter (fun v => G.Adj t v ∨ G.Adj t' v)).card = 4 := by
          omega
        exact no_four_set_alpha3 ctx pf hfree hm50'' hδ (Finset.filter_subset _ _) hUcard
          (nonedge_residual_alpha3 ctx htT ht'T hne hnadj)
      have hcount := sum_U_counting ctx.hT hU5
      rw [← hsdef, ← hxdef] at hcount
      omega

/-- **§4 entry.** `R = H − Q₁` (15 vertices): `α(R) ≤ 3` (peel `k = 1`),
`K_5`-free, cap-11, so `e(R) ≥ L(15) = 38`. -/
theorem edge_R_ge_38 {G : SimpleGraph (Fin 25)} {T : Finset (Fin 25)} (ctx : MMCtx G T)
    (pf : PrimFacts) {Q1 : Finset (Fin 25)} (hQ1sub : Q1 ⊆ Finset.univ \ T) (hQ1c : Q1.card = 5)
    (hQ1clq : IsCliqueOn G Q1)
    (hRfree : ∀ Q : Finset (Fin 25), Q ⊆ (Finset.univ \ T) \ Q1 → Q.card = 5 → ¬ IsCliqueOn G Q) :
    38 ≤ edgeCountIn G ((Finset.univ \ T) \ Q1) := by
  have hRsub : (Finset.univ \ T) \ Q1 ⊆ Finset.univ \ T := Finset.sdiff_subset
  have hαR3 : ∀ S : Finset (Fin 25), S ⊆ (Finset.univ \ T) \ Q1 → IsIndep G S → S.card ≤ 3 := by
    intro S hSsub hSindep
    by_contra hc
    push Not at hc
    obtain ⟨S4, hS4sub, hS4card⟩ := Finset.exists_subset_card_eq (show 4 ≤ S.card by omega)
    refine peel_alpha_bound ctx [Q1] ?_ ?_ ?_
      (fun a ha b hb hab => hSindep a (hS4sub ha) b (hS4sub hb) hab)
      ((hS4sub.trans hSsub).trans hRsub) ?_ (by simp [hS4card])
    · intro Q hQ; simp only [List.mem_singleton] at hQ; subst hQ; exact ⟨hQ1clq, hQ1c⟩
    · simp
    · intro Q hQ; simp only [List.mem_singleton] at hQ; subst hQ; exact hQ1sub
    · intro Q hQ; simp only [List.mem_singleton] at hQ; subst hQ
      rw [Finset.disjoint_left]; intro x hx hxQ1
      exact (Finset.mem_sdiff.mp ((hS4sub.trans hSsub) hx)).2 hxQ1
  have hRcard : ((Finset.univ \ T) \ Q1).card = 15 := by
    have h1 := Finset.card_sdiff_of_subset hQ1sub
    have h2 := card_H ctx
    omega
  have h := ell_le_edgeCountIn pf G ((Finset.univ \ T) \ Q1) ctx.hcap hαR3
    (fun Q hQsub hQc => hRfree Q hQsub hQc) (by rw [hRcard]; norm_num)
  rwa [hRcard, show ell 15 = 38 from by decide] at h

/-- **§5 entry.** `B = H − Q₁ − Q₂` (10 vertices): `α(B) ≤ 2` (peel `k = 2`),
`K_5`-free, cap-11, so `e(B) ≥ M(10) = 25`. -/
theorem edge_B_ge_25 {G : SimpleGraph (Fin 25)} {T : Finset (Fin 25)} (ctx : MMCtx G T)
    (pf : PrimFacts) {Q1 Q2 : Finset (Fin 25)} (hQ1sub : Q1 ⊆ Finset.univ \ T) (hQ1c : Q1.card = 5)
    (hQ1clq : IsCliqueOn G Q1) (hQ2sub : Q2 ⊆ (Finset.univ \ T) \ Q1) (hQ2c : Q2.card = 5)
    (hQ2clq : IsCliqueOn G Q2)
    (hBfree : ∀ Q : Finset (Fin 25), Q ⊆ ((Finset.univ \ T) \ Q1) \ Q2 → Q.card = 5 →
      ¬ IsCliqueOn G Q) :
    25 ≤ edgeCountIn G (((Finset.univ \ T) \ Q1) \ Q2) := by
  have hd12 : Disjoint Q1 Q2 := by
    rw [Finset.disjoint_left]; intro x hx hxQ2
    exact (Finset.mem_sdiff.mp (hQ2sub hxQ2)).2 hx
  have hBsubH : ((Finset.univ \ T) \ Q1) \ Q2 ⊆ Finset.univ \ T :=
    Finset.sdiff_subset.trans Finset.sdiff_subset
  have hαB2 : ∀ S : Finset (Fin 25), S ⊆ ((Finset.univ \ T) \ Q1) \ Q2 → IsIndep G S →
      S.card ≤ 2 := by
    intro S hSsub hSindep
    by_contra hc
    push Not at hc
    obtain ⟨S3, hS3sub, hS3card⟩ := Finset.exists_subset_card_eq (show 3 ≤ S.card by omega)
    refine peel_alpha_bound ctx [Q1, Q2] ?_ ?_ ?_
      (fun a ha b hb hab => hSindep a (hS3sub ha) b (hS3sub hb) hab)
      ((hS3sub.trans hSsub).trans hBsubH) ?_ (by simp [hS3card])
    · intro Q hQ; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hQ
      rcases hQ with rfl | rfl
      · exact ⟨hQ1clq, hQ1c⟩
      · exact ⟨hQ2clq, hQ2c⟩
    · refine List.Pairwise.cons ?_ (by simp)
      intro Q hQ; simp only [List.mem_singleton] at hQ; subst hQ; exact hd12
    · intro Q hQ; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hQ
      rcases hQ with rfl | rfl
      · exact hQ1sub
      · exact hQ2sub.trans Finset.sdiff_subset
    · intro Q hQ; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hQ
      have hxB : ∀ x ∈ S3, x ∈ ((Finset.univ \ T) \ Q1) \ Q2 := fun x hx => (hS3sub.trans hSsub) hx
      rcases hQ with rfl | rfl
      · rw [Finset.disjoint_left]; intro x hx hxQ1
        exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (hxB x hx)).1).2 hxQ1
      · rw [Finset.disjoint_left]; intro x hx hxQ2
        exact (Finset.mem_sdiff.mp (hxB x hx)).2 hxQ2
  have hBcard : (((Finset.univ \ T) \ Q1) \ Q2).card = 10 := by
    have h1 := Finset.card_sdiff_of_subset hQ1sub
    have h2 := Finset.card_sdiff_of_subset hQ2sub
    have h3 := card_H ctx
    omega
  have h := Mfloor_le_edgeCountIn pf G (((Finset.univ \ T) \ Q1) \ Q2) ctx.hcap hαB2
    (fun Q hQsub hQc => hBfree Q hQsub hQc) (by rw [hBcard])
  rwa [hBcard, show Mfloor 10 = 25 from by decide] at h

/-- Helper: a filtered set `S.filter (¬ P)` has card `≥ S.card − (# P-satisfiers)`. -/
theorem card_filter_not_ge (S : Finset (Fin 25)) (P : Fin 25 → Prop) :
    S.card - (S.filter (fun x => P x)).card ≤ (S.filter (fun x => ¬ P x)).card := by
  have h := Finset.filter_card_add_filter_neg_card_eq_card (s := S) (p := fun x => P x)
  omega

/-- **The elementary transversal fact (contrapositive).** Four parts `{v}∪…`, cross
matchings, and no independent transversal: if `v` (rep. of part `A`) has NO neighbour
in `B`, we build an independent transversal, contradicting `hNT`. -/
theorem saturate_contra (G : SimpleGraph (Fin 25)) {v : Fin 25} {B C D : Finset (Fin 25)}
    (hB : 3 ≤ B.card) (hC : 2 ≤ C.card) (hD : 3 ≤ D.card)
    (hvC : (C.filter (fun w => G.Adj v w)).card ≤ 1)
    (hvD : (D.filter (fun w => G.Adj v w)).card ≤ 1)
    (hyD : ∀ y ∈ C, (D.filter (fun w => G.Adj y w)).card ≤ 1)
    (hyB : ∀ y ∈ C, (B.filter (fun w => G.Adj y w)).card ≤ 1)
    (hzB : ∀ z ∈ D, (B.filter (fun w => G.Adj z w)).card ≤ 1)
    (hvB : ∀ b ∈ B, ¬ G.Adj v b)
    (hNT : ∀ b ∈ B, ∀ c ∈ C, ∀ d ∈ D,
      G.Adj v b ∨ G.Adj v c ∨ G.Adj v d ∨ G.Adj b c ∨ G.Adj b d ∨ G.Adj c d) :
    False := by
  -- pick y ∈ C nonadjacent to v
  have hC' : (C.filter (fun w => ¬ G.Adj v w)).Nonempty := by
    rw [← Finset.card_pos]
    have := card_filter_not_ge C (fun w => G.Adj v w); omega
  obtain ⟨y, hy⟩ := hC'
  rw [Finset.mem_filter] at hy
  obtain ⟨hyC, hvy⟩ := hy
  -- pick z ∈ D nonadjacent to v and to y
  have hD' : (D.filter (fun w => ¬ G.Adj v w ∧ ¬ G.Adj y w)).Nonempty := by
    rw [← Finset.card_pos]
    have hun : (D.filter (fun w => G.Adj v w ∨ G.Adj y w)).card
        ≤ (D.filter (fun w => G.Adj v w)).card + (D.filter (fun w => G.Adj y w)).card := by
      have hsub : D.filter (fun w => G.Adj v w ∨ G.Adj y w)
          ⊆ D.filter (fun w => G.Adj v w) ∪ D.filter (fun w => G.Adj y w) := by
        intro b hb; rw [Finset.mem_filter] at hb
        rcases hb.2 with h | h
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hb.1, h⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hb.1, h⟩)
      exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card (s := D)
      (p := fun w => G.Adj v w ∨ G.Adj y w)
    have hneg : (D.filter (fun w => ¬ (G.Adj v w ∨ G.Adj y w)))
        = (D.filter (fun w => ¬ G.Adj v w ∧ ¬ G.Adj y w)) := by
      apply Finset.filter_congr; intro w _; rw [not_or]
    rw [← hneg]
    have := hyD y hyC
    omega
  obtain ⟨z, hz⟩ := hD'
  rw [Finset.mem_filter] at hz
  obtain ⟨hzD, hvz, hyz⟩ := hz
  -- pick w ∈ B nonadjacent to v, y, z
  have hB' : (B.filter (fun b => ¬ G.Adj v b ∧ ¬ G.Adj y b ∧ ¬ G.Adj z b)).Nonempty := by
    rw [← Finset.card_pos]
    have hun : (B.filter (fun b => G.Adj v b ∨ G.Adj y b ∨ G.Adj z b)).card
        ≤ (B.filter (fun b => G.Adj v b)).card + (B.filter (fun b => G.Adj y b)).card
          + (B.filter (fun b => G.Adj z b)).card := by
      have hsub : B.filter (fun b => G.Adj v b ∨ G.Adj y b ∨ G.Adj z b)
          ⊆ B.filter (fun b => G.Adj v b) ∪ B.filter (fun b => G.Adj y b)
            ∪ B.filter (fun b => G.Adj z b) := by
        intro b hb; rw [Finset.mem_filter] at hb
        rcases hb.2 with h | h | h
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hb.1, h⟩))
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hb.1, h⟩))
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hb.1, h⟩)
      refine le_trans (Finset.card_le_card hsub) ?_
      exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card (s := B)
      (p := fun b => G.Adj v b ∨ G.Adj y b ∨ G.Adj z b)
    have hneg : (B.filter (fun b => ¬ (G.Adj v b ∨ G.Adj y b ∨ G.Adj z b)))
        = (B.filter (fun b => ¬ G.Adj v b ∧ ¬ G.Adj y b ∧ ¬ G.Adj z b)) := by
      apply Finset.filter_congr; intro b _; rw [not_or, not_or]
    rw [← hneg]
    have hbv : (B.filter (fun b => G.Adj v b)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; exact fun b hb => hvB b hb
    have := hyB y hyC
    have := hzB z hzD
    omega
  obtain ⟨w, hw⟩ := hB'
  rw [Finset.mem_filter] at hw
  obtain ⟨hwB, hvw, hyw, hzw⟩ := hw
  -- contradiction with hNT (b=w, c=y, d=z)
  rcases hNT w hwB y hyC z hzD with h | h | h | h | h | h
  · exact hvw h
  · exact hvy h
  · exact hvz h
  · exact hyw (G.symm h)
  · exact hzw (G.symm h)
  · exact hyz h

/-- **No independent 6-set** (given `α(G) ≤ 5`): six pairwise-distinct,
pairwise-nonadjacent vertices are impossible. -/
theorem no_indep_six {G : SimpleGraph (Fin 25)}
    (hα5 : ∀ S : Finset (Fin 25), IsIndep G S → S.card ≤ 5)
    {a b c d e f : Fin 25}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f)
    (nab : ¬ G.Adj a b) (nac : ¬ G.Adj a c) (nad : ¬ G.Adj a d) (nae : ¬ G.Adj a e)
    (naf : ¬ G.Adj a f) (nbc : ¬ G.Adj b c) (nbd : ¬ G.Adj b d) (nbe : ¬ G.Adj b e)
    (nbf : ¬ G.Adj b f) (ncd : ¬ G.Adj c d) (nce : ¬ G.Adj c e) (ncf : ¬ G.Adj c f)
    (nde : ¬ G.Adj d e) (ndf : ¬ G.Adj d f) (nef : ¬ G.Adj e f) : False := by
  have hindep : IsIndep G {a, b, c, d, e, f} := by
    intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hxy
        | assumption
        | (rw [SimpleGraph.adj_comm]; assumption)
  have hcard : ({a, b, c, d, e, f} : Finset (Fin 25)).card = 6 := by
    rw [Finset.card_insert_of_notMem
          (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg;
              exact ⟨hab, hac, had, hae, haf⟩),
        Finset.card_insert_of_notMem
          (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg;
              exact ⟨hbc, hbd, hbe, hbf⟩),
        Finset.card_insert_of_notMem
          (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg;
              exact ⟨hcd, hce, hcf⟩),
        Finset.card_insert_of_notMem
          (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg;
              exact ⟨hde, hdf⟩),
        Finset.card_pair hef]
  have := hα5 _ hindep
  omega

/-- Matching helper: `x ∈ Ai ⊆ Qi` has ≤ 1 neighbour in `Aj ⊆ Qj` (a K₅ disjoint
from `Qi`), via `indeg_clique5_le_one` + filter-monotonicity. -/
theorem cross_match {G : SimpleGraph (Fin 25)} (hcap : capAtMost11 G)
    {Ai Aj Qi Qj : Finset (Fin 25)} (hAiQi : Ai ⊆ Qi) (hAjQj : Aj ⊆ Qj)
    (hQjclq : IsCliqueOn G Qj) (hQjc : Qj.card = 5) (hdisj : Disjoint Qi Qj)
    {x : Fin 25} (hx : x ∈ Ai) : (Aj.filter (fun w => G.Adj x w)).card ≤ 1 := by
  have hxnQj : x ∉ Qj := Finset.disjoint_left.mp hdisj (hAiQi hx)
  exact le_trans (Finset.card_le_card (Finset.filter_subset_filter _ hAjQj))
    (indeg_clique5_le_one G hcap hQjclq hQjc hxnQj)

/-- **§3.** Four disjoint `K_5`'s (given three, the fourth is the leftover, forced
to be a clique by peeling) ⇒ contradiction. -/
theorem section3_four {G : SimpleGraph (Fin 25)} {T : Finset (Fin 25)} (ctx : MMCtx G T)
    (pf : PrimFacts) {Q1 Q2 Q3 : Finset (Fin 25)} (hQ1sub : Q1 ⊆ Finset.univ \ T) (hQ1c : Q1.card = 5)
    (hQ1clq : IsCliqueOn G Q1) (hQ2sub : Q2 ⊆ (Finset.univ \ T) \ Q1) (hQ2c : Q2.card = 5)
    (hQ2clq : IsCliqueOn G Q2) (hQ3sub : Q3 ⊆ ((Finset.univ \ T) \ Q1) \ Q2) (hQ3c : Q3.card = 5)
    (hQ3clq : IsCliqueOn G Q3) : False := by
  set H := Finset.univ \ T with hHdef
  have hHcard : H.card = 20 := card_H ctx
  -- pairwise disjointness of Q1,Q2,Q3
  have hd12 : Disjoint Q1 Q2 := by
    rw [Finset.disjoint_left]; intro x hx hx2
    exact (Finset.mem_sdiff.mp (hQ2sub hx2)).2 hx
  have hd13 : Disjoint Q1 Q3 := by
    rw [Finset.disjoint_left]; intro x hx hx3
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (hQ3sub hx3)).1).2 hx
  have hd23 : Disjoint Q2 Q3 := by
    rw [Finset.disjoint_left]; intro x hx hx3
    exact (Finset.mem_sdiff.mp (hQ3sub hx3)).2 hx
  have hQ1H : Q1 ⊆ H := hQ1sub
  have hQ2H : Q2 ⊆ H := hQ2sub.trans Finset.sdiff_subset
  have hQ3H : Q3 ⊆ H := (hQ3sub.trans Finset.sdiff_subset).trans Finset.sdiff_subset
  -- Q4 = leftover
  set Q4 := ((H \ Q1) \ Q2) \ Q3 with hQ4def
  have hQ4sub : Q4 ⊆ H := (Finset.sdiff_subset.trans Finset.sdiff_subset).trans Finset.sdiff_subset
  have hQ4c : Q4.card = 5 := by
    have e1 := Finset.card_sdiff_add_card_eq_card hQ1H
    have e2 := Finset.card_sdiff_add_card_eq_card (show Q2 ⊆ H \ Q1 from hQ2sub)
    have e3 := Finset.card_sdiff_add_card_eq_card (show Q3 ⊆ (H \ Q1) \ Q2 from hQ3sub)
    rw [hQ4def]; omega
  -- Q4 is a clique (α ≤ 1 via peel k=3)
  have hQ4clq : IsCliqueOn G Q4 := by
    intro u hu w hw huw
    by_contra hnadj
    refine peel_alpha_bound ctx [Q1, Q2, Q3] ?_ ?_ ?_ (S := {u, w}) ?_ ?_ ?_
      (by rw [Finset.card_pair huw]; rfl)
    · intro Q hQ; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hQ
      rcases hQ with rfl | rfl | rfl
      · exact ⟨hQ1clq, hQ1c⟩
      · exact ⟨hQ2clq, hQ2c⟩
      · exact ⟨hQ3clq, hQ3c⟩
    · refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (by simp))
      · intro Q hQ; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hQ
        rcases hQ with rfl | rfl
        · exact hd12
        · exact hd13
      · intro Q hQ; simp only [List.mem_singleton] at hQ; subst hQ; exact hd23
    · intro Q hQ; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hQ
      rcases hQ with rfl | rfl | rfl
      · exact hQ1H
      · exact hQ2H
      · exact hQ3H
    · intro a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · exact hnadj
      · exact fun h => hnadj (G.symm h)
      · exact absurd rfl hab
    · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hQ4sub hu
      · exact hQ4sub hw
    · intro Q hQ; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hQ
      have hmem : ∀ p ∈ ({u, w} : Finset (Fin 25)), p ∈ Q4 := by
        intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl; exacts [hu, hw]
      rcases hQ with rfl | rfl | rfl
      · rw [Finset.disjoint_left]; intro p hp hpQ
        exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (hmem p hp)).1).1).2 hpQ
      · rw [Finset.disjoint_left]; intro p hp hpQ
        exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (hmem p hp)).1).2 hpQ
      · rw [Finset.disjoint_left]; intro p hp hpQ
        exact (Finset.mem_sdiff.mp (hmem p hp)).2 hpQ
  -- disjointness of Q4 from Q1,Q2,Q3
  have hd14 : Disjoint Q1 Q4 := by
    rw [Finset.disjoint_left]; intro p hp1 hp4
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hp4).1).1).2 hp1
  have hd24 : Disjoint Q2 Q4 := by
    rw [Finset.disjoint_left]; intro p hp2 hp4
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hp4).1).2 hp2
  have hd34 : Disjoint Q3 Q4 := by
    rw [Finset.disjoint_left]; intro p hp3 hp4
    exact (Finset.mem_sdiff.mp hp4).2 hp3
  have hQ4H : Q4 ⊆ H := hQ4sub
  -- a non-edge tt' of G[T]
  obtain ⟨t, htT, t', ht'T, hne, hnadj⟩ : ∃ t ∈ T, ∃ t' ∈ T, t ≠ t' ∧ ¬ G.Adj t t' := by
    by_contra hcon
    push_neg at hcon
    have hclq : IsCliqueOn G T := hcon
    have h10 := edgeCountIn_eq_choose_of_clique G hclq
    rw [ctx.hT] at h10
    have hc : (5 : ℕ).choose 2 = 10 := by decide
    have := ctx.hsT; omega
  -- the four A-parts and their sizes
  set A1 := Q1.filter (fun q => ¬ G.Adj t q ∧ ¬ G.Adj t' q) with hA1def
  set A2 := Q2.filter (fun q => ¬ G.Adj t q ∧ ¬ G.Adj t' q) with hA2def
  set A3 := Q3.filter (fun q => ¬ G.Adj t q ∧ ¬ G.Adj t' q) with hA3def
  set A4 := Q4.filter (fun q => ¬ G.Adj t q ∧ ¬ G.Adj t' q) with hA4def
  have hAcard : ∀ (Qi : Finset (Fin 25)), IsCliqueOn G Qi → Qi.card = 5 → Qi ⊆ H →
      3 ≤ (Qi.filter (fun q => ¬ G.Adj t q ∧ ¬ G.Adj t' q)).card := by
    intro Qi hQiclq hQic hQiH
    have htnQi : t ∉ Qi := fun h => (Finset.mem_sdiff.mp (hQiH h)).2 htT
    have ht'nQi : t' ∉ Qi := fun h => (Finset.mem_sdiff.mp (hQiH h)).2 ht'T
    have h1 := indeg_clique5_le_one G ctx.hcap hQiclq hQic htnQi
    have h2 := indeg_clique5_le_one G ctx.hcap hQiclq hQic ht'nQi
    have hun : (Qi.filter (fun q => G.Adj t q ∨ G.Adj t' q)).card
        ≤ (Qi.filter (fun q => G.Adj t q)).card + (Qi.filter (fun q => G.Adj t' q)).card := by
      have hsub : Qi.filter (fun q => G.Adj t q ∨ G.Adj t' q)
          ⊆ Qi.filter (fun q => G.Adj t q) ∪ Qi.filter (fun q => G.Adj t' q) := by
        intro q hq; rw [Finset.mem_filter] at hq; rcases hq.2 with h | h
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hq.1, h⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hq.1, h⟩)
      exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card (s := Qi)
      (p := fun q => G.Adj t q ∨ G.Adj t' q)
    have hneg : Qi.filter (fun q => ¬ (G.Adj t q ∨ G.Adj t' q))
        = Qi.filter (fun q => ¬ G.Adj t q ∧ ¬ G.Adj t' q) := by
      apply Finset.filter_congr; intro q _; rw [not_or]
    rw [hneg, hQic] at hsplit
    omega
  have hA1card : 3 ≤ A1.card := hAcard Q1 hQ1clq hQ1c hQ1H
  have hA2card : 3 ≤ A2.card := hAcard Q2 hQ2clq hQ2c hQ2H
  have hA3card : 3 ≤ A3.card := hAcard Q3 hQ3clq hQ3c hQ3H
  have hA4card : 3 ≤ A4.card := hAcard Q4 hQ4clq hQ4c hQ4H
  have hA1Q1 : A1 ⊆ Q1 := Finset.filter_subset _ _
  have hA2Q2 : A2 ⊆ Q2 := Finset.filter_subset _ _
  have hA3Q3 : A3 ⊆ Q3 := Finset.filter_subset _ _
  have hA4Q4 : A4 ⊆ Q4 := Finset.filter_subset _ _
  -- membership: a ∈ Ai ⇒ ¬Adj t a ∧ ¬Adj t' a
  have hAnt : ∀ {Qi : Finset (Fin 25)} {a : Fin 25},
      a ∈ Qi.filter (fun q => ¬ G.Adj t q ∧ ¬ G.Adj t' q) → ¬ G.Adj t a ∧ ¬ G.Adj t' a :=
    fun ha => (Finset.mem_filter.mp ha).2
  -- no independent transversal of A1,A2,A3,A4
  have hNTcanon : ∀ a1 ∈ A1, ∀ a2 ∈ A2, ∀ a3 ∈ A3, ∀ a4 ∈ A4,
      G.Adj a1 a2 ∨ G.Adj a1 a3 ∨ G.Adj a1 a4 ∨ G.Adj a2 a3 ∨ G.Adj a2 a4 ∨ G.Adj a3 a4 := by
    intro a1 ha1 a2 ha2 a3 ha3 a4 ha4
    by_contra hcon
    push_neg at hcon
    obtain ⟨n12, n13, n14, n23, n24, n34⟩ := hcon
    have hq1 : a1 ∈ Q1 := hA1Q1 ha1
    have hq2 : a2 ∈ Q2 := hA2Q2 ha2
    have hq3 : a3 ∈ Q3 := hA3Q3 ha3
    have hq4 : a4 ∈ Q4 := hA4Q4 ha4
    have ht1 := hAnt ha1; have ht2 := hAnt ha2; have ht3 := hAnt ha3; have ht4 := hAnt ha4
    exact no_indep_six ctx.hα5
      (by rintro rfl; exact Finset.disjoint_left.mp hd12 hq1 hq2)
      (by rintro rfl; exact Finset.disjoint_left.mp hd13 hq1 hq3)
      (by rintro rfl; exact Finset.disjoint_left.mp hd14 hq1 hq4)
      (by rintro rfl; exact (Finset.mem_sdiff.mp (hQ1H hq1)).2 htT)
      (by rintro rfl; exact (Finset.mem_sdiff.mp (hQ1H hq1)).2 ht'T)
      (by rintro rfl; exact Finset.disjoint_left.mp hd23 hq2 hq3)
      (by rintro rfl; exact Finset.disjoint_left.mp hd24 hq2 hq4)
      (by rintro rfl; exact (Finset.mem_sdiff.mp (hQ2H hq2)).2 htT)
      (by rintro rfl; exact (Finset.mem_sdiff.mp (hQ2H hq2)).2 ht'T)
      (by rintro rfl; exact Finset.disjoint_left.mp hd34 hq3 hq4)
      (by rintro rfl; exact (Finset.mem_sdiff.mp (hQ3H hq3)).2 htT)
      (by rintro rfl; exact (Finset.mem_sdiff.mp (hQ3H hq3)).2 ht'T)
      (by rintro rfl; exact (Finset.mem_sdiff.mp (hQ4H hq4)).2 htT)
      (by rintro rfl; exact (Finset.mem_sdiff.mp (hQ4H hq4)).2 ht'T)
      hne
      n12 n13 n14 (fun h => ht1.1 (G.symm h)) (fun h => ht1.2 (G.symm h))
      n23 n24 (fun h => ht2.1 (G.symm h)) (fun h => ht2.2 (G.symm h))
      n34 (fun h => ht3.1 (G.symm h)) (fun h => ht3.2 (G.symm h))
      (fun h => ht4.1 (G.symm h)) (fun h => ht4.2 (G.symm h)) hnadj
  -- generic saturation: `As`-vertices have a neighbour in `At`
  have doSat : ∀ (As At Ac Ad Qs Qt Qc Qd : Finset (Fin 25)),
      As ⊆ Qs → At ⊆ Qt → Ac ⊆ Qc → Ad ⊆ Qd →
      IsCliqueOn G Qt → Qt.card = 5 → IsCliqueOn G Qc → Qc.card = 5 →
      IsCliqueOn G Qd → Qd.card = 5 →
      Disjoint Qs Qc → Disjoint Qs Qd → Disjoint Qc Qd → Disjoint Qc Qt → Disjoint Qd Qt →
      3 ≤ At.card → 2 ≤ Ac.card → 3 ≤ Ad.card →
      (∀ v ∈ As, ∀ b ∈ At, ∀ c ∈ Ac, ∀ d ∈ Ad,
        G.Adj v b ∨ G.Adj v c ∨ G.Adj v d ∨ G.Adj b c ∨ G.Adj b d ∨ G.Adj c d) →
      ∀ v ∈ As, ∃ b ∈ At, G.Adj v b := by
    intro As At Ac Ad Qs Qt Qc Qd hAsQs hAtQt hAcQc hAdQd hQtclq hQtc hQcclq hQcc hQdclq hQdc
      hdsc hdsd hdcd hdct hddt hAtc hAcc hAdc hNTs v hv
    by_contra hcon
    push_neg at hcon
    exact saturate_contra G hAtc hAcc hAdc
      (cross_match ctx.hcap hAsQs hAcQc hQcclq hQcc hdsc hv)
      (cross_match ctx.hcap hAsQs hAdQd hQdclq hQdc hdsd hv)
      (fun y hy => cross_match ctx.hcap hAcQc hAdQd hQdclq hQdc hdcd hy)
      (fun y hy => cross_match ctx.hcap hAcQc hAtQt hQtclq hQtc hdct hy)
      (fun z hz => cross_match ctx.hcap hAdQd hAtQt hQtclq hQtc hddt hz)
      hcon (fun b hb c hc d hd => hNTs v hv b hb c hc d hd)
  have sat21 : ∀ v ∈ A2, ∃ b ∈ A1, G.Adj v b :=
    doSat A2 A1 A3 A4 Q2 Q1 Q3 Q4 hA2Q2 hA1Q1 hA3Q3 hA4Q4 hQ1clq hQ1c hQ3clq hQ3c hQ4clq hQ4c
      hd23 hd24 hd34 hd13.symm hd14.symm hA1card (by omega) hA4card
      (by intro v hv b hb c hc d hd; rcases hNTcanon b hb v hv c hc d hd with h|h|h|h|h|h <;>
        first | tauto | (rw [SimpleGraph.adj_comm] at h; tauto))
  have sat31 : ∀ v ∈ A3, ∃ b ∈ A1, G.Adj v b :=
    doSat A3 A1 A2 A4 Q3 Q1 Q2 Q4 hA3Q3 hA1Q1 hA2Q2 hA4Q4 hQ1clq hQ1c hQ2clq hQ2c hQ4clq hQ4c
      hd23.symm hd34 hd24 hd12.symm hd14.symm hA1card (by omega) hA4card
      (by intro v hv b hb c hc d hd; rcases hNTcanon b hb c hc v hv d hd with h|h|h|h|h|h <;>
        first | tauto | (rw [SimpleGraph.adj_comm] at h; tauto))
  have sat41 : ∀ v ∈ A4, ∃ b ∈ A1, G.Adj v b :=
    doSat A4 A1 A2 A3 Q4 Q1 Q2 Q3 hA4Q4 hA1Q1 hA2Q2 hA3Q3 hQ1clq hQ1c hQ2clq hQ2c hQ3clq hQ3c
      hd24.symm hd34.symm hd23 hd12.symm hd13.symm hA1card (by omega) hA3card
      (by intro v hv b hb c hc d hd; rcases hNTcanon b hb c hc d hd v hv with h|h|h|h|h|h <;>
        first | tauto | (rw [SimpleGraph.adj_comm] at h; tauto))
  have sat32 : ∀ v ∈ A3, ∃ b ∈ A2, G.Adj v b :=
    doSat A3 A2 A1 A4 Q3 Q2 Q1 Q4 hA3Q3 hA2Q2 hA1Q1 hA4Q4 hQ2clq hQ2c hQ1clq hQ1c hQ4clq hQ4c
      hd13.symm hd34 hd14 hd12 hd24.symm hA2card (by omega) hA4card
      (by intro v hv b hb c hc d hd; rcases hNTcanon c hc b hb v hv d hd with h|h|h|h|h|h <;>
        first | tauto | (rw [SimpleGraph.adj_comm] at h; tauto))
  have sat42 : ∀ v ∈ A4, ∃ b ∈ A2, G.Adj v b :=
    doSat A4 A2 A1 A3 Q4 Q2 Q1 Q3 hA4Q4 hA2Q2 hA1Q1 hA3Q3 hQ2clq hQ2c hQ1clq hQ1c hQ3clq hQ3c
      hd14.symm hd34.symm hd13 hd12 hd23.symm hA2card (by omega) hA3card
      (by intro v hv b hb c hc d hd; rcases hNTcanon c hc b hb d hd v hv with h|h|h|h|h|h <;>
        first | tauto | (rw [SimpleGraph.adj_comm] at h; tauto))
  have sat43 : ∀ v ∈ A4, ∃ b ∈ A3, G.Adj v b :=
    doSat A4 A3 A1 A2 Q4 Q3 Q1 Q2 hA4Q4 hA3Q3 hA1Q1 hA2Q2 hQ3clq hQ3c hQ1clq hQ1c hQ2clq hQ2c
      hd14.symm hd24.symm hd12 hd13 hd23 hA3card (by omega) hA2card
      (by intro v hv b hb c hc d hd; rcases hNTcanon c hc d hd b hb v hv with h|h|h|h|h|h <;>
        first | tauto | (rw [SimpleGraph.adj_comm] at h; tauto))
  -- e(H) ≥ 58 via three disjoint splits
  have heQ : ∀ (Qi : Finset (Fin 25)), IsCliqueOn G Qi → Qi.card = 5 → edgeCountIn G Qi = 10 := by
    intro Qi hclq hc; rw [edgeCountIn_eq_choose_of_clique G hclq, hc]; rfl
  have hcross_ge : ∀ (Ai Aj Qi : Finset (Fin 25)), Ai ⊆ Qi → 3 ≤ Aj.card →
      (∀ v ∈ Aj, ∃ a ∈ Ai, G.Adj v a) →
      3 ≤ ∑ b ∈ Aj, (Qi.filter (fun w => G.Adj b w)).card := by
    intro Ai Aj Qi hAiQi hAjc hsat
    calc 3 ≤ Aj.card := hAjc
      _ = ∑ _b ∈ Aj, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ b ∈ Aj, (Qi.filter (fun w => G.Adj b w)).card := by
          apply Finset.sum_le_sum; intro b hb
          obtain ⟨a, haAi, hba⟩ := hsat b hb
          exact Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨hAiQi haAi, hba⟩⟩
  have hADisj : ∀ {Ai Aj Qi Qj : Finset (Fin 25)}, Ai ⊆ Qi → Aj ⊆ Qj → Disjoint Qi Qj →
      Disjoint Ai Aj :=
    fun hi hj hd => Finset.disjoint_of_subset_left hi (Finset.disjoint_of_subset_right hj hd)
  have hQ4subH1 : Q4 ⊆ H \ Q1 := by
    rw [hQ4def]; exact Finset.sdiff_subset.trans Finset.sdiff_subset
  have hsplit1 : edgeCountIn G H = edgeCountIn G Q1 + edgeCountIn G (H \ Q1)
      + ∑ b ∈ H \ Q1, (Q1.filter (fun w => G.Adj b w)).card := by
    have hd : Disjoint Q1 (H \ Q1) := (Finset.sdiff_disjoint).symm
    have hu : Q1 ∪ (H \ Q1) = H := by
      rw [Finset.union_comm]; exact Finset.sdiff_union_of_subset hQ1H
    have hh := edgeCountIn_union_disjoint_eq G hd; rwa [hu] at hh
  have hsplit2 : edgeCountIn G (H \ Q1) = edgeCountIn G Q2 + edgeCountIn G ((H \ Q1) \ Q2)
      + ∑ b ∈ (H \ Q1) \ Q2, (Q2.filter (fun w => G.Adj b w)).card := by
    have hd : Disjoint Q2 ((H \ Q1) \ Q2) := (Finset.sdiff_disjoint).symm
    have hu : Q2 ∪ ((H \ Q1) \ Q2) = H \ Q1 := by
      rw [Finset.union_comm]; exact Finset.sdiff_union_of_subset hQ2sub
    have hh := edgeCountIn_union_disjoint_eq G hd; rwa [hu] at hh
  have hsplit3 : edgeCountIn G ((H \ Q1) \ Q2) = edgeCountIn G Q3 + edgeCountIn G Q4
      + ∑ b ∈ Q4, (Q3.filter (fun w => G.Adj b w)).card := by
    have hu : Q3 ∪ Q4 = (H \ Q1) \ Q2 := by
      rw [hQ4def, Finset.union_comm]; exact Finset.sdiff_union_of_subset hQ3sub
    have hh := edgeCountIn_union_disjoint_eq G hd34; rwa [hu] at hh
  have hX1 : 9 ≤ ∑ b ∈ H \ Q1, (Q1.filter (fun w => G.Adj b w)).card := by
    have hsub : A2 ∪ A3 ∪ A4 ⊆ H \ Q1 :=
      Finset.union_subset (Finset.union_subset (hA2Q2.trans hQ2sub)
        (hA3Q3.trans (hQ3sub.trans Finset.sdiff_subset))) (hA4Q4.trans hQ4subH1)
    have hle : (∑ b ∈ A2 ∪ A3 ∪ A4, (Q1.filter (fun w => G.Adj b w)).card)
        ≤ ∑ b ∈ H \ Q1, (Q1.filter (fun w => G.Adj b w)).card :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    rw [Finset.sum_union (Finset.disjoint_union_left.mpr
        ⟨hADisj hA2Q2 hA4Q4 hd24, hADisj hA3Q3 hA4Q4 hd34⟩),
        Finset.sum_union (hADisj hA2Q2 hA3Q3 hd23)] at hle
    have h2 := hcross_ge A1 A2 Q1 hA1Q1 hA2card sat21
    have h3 := hcross_ge A1 A3 Q1 hA1Q1 hA3card sat31
    have h4 := hcross_ge A1 A4 Q1 hA1Q1 hA4card sat41
    omega
  have hX2 : 6 ≤ ∑ b ∈ (H \ Q1) \ Q2, (Q2.filter (fun w => G.Adj b w)).card := by
    have hsub : A3 ∪ A4 ⊆ (H \ Q1) \ Q2 :=
      Finset.union_subset (hA3Q3.trans hQ3sub)
        (hA4Q4.trans (by rw [hQ4def]; exact Finset.sdiff_subset))
    have hle : (∑ b ∈ A3 ∪ A4, (Q2.filter (fun w => G.Adj b w)).card)
        ≤ ∑ b ∈ (H \ Q1) \ Q2, (Q2.filter (fun w => G.Adj b w)).card :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    rw [Finset.sum_union (hADisj hA3Q3 hA4Q4 hd34)] at hle
    have h3 := hcross_ge A2 A3 Q2 hA2Q2 hA3card sat32
    have h4 := hcross_ge A2 A4 Q2 hA2Q2 hA4card sat42
    omega
  have hX3 : 3 ≤ ∑ b ∈ Q4, (Q3.filter (fun w => G.Adj b w)).card := by
    have hle : (∑ b ∈ A4, (Q3.filter (fun w => G.Adj b w)).card)
        ≤ ∑ b ∈ Q4, (Q3.filter (fun w => G.Adj b w)).card :=
      Finset.sum_le_sum_of_subset_of_nonneg hA4Q4 (fun _ _ _ => Nat.zero_le _)
    have h4 := hcross_ge A3 A4 Q3 hA3Q3 hA4card sat43
    omega
  have heH58 : 58 ≤ edgeCountIn G H := by
    rw [hsplit1, hsplit2, hsplit3, heQ Q1 hQ1clq hQ1c, heQ Q2 hQ2clq hQ2c,
        heQ Q3 hQ3clq hQ3c, heQ Q4 hQ4clq hQ4c]
    omega
  -- Part II: `s + x ≤ 2`, an independent triple `P ⊆ T`, and a greedy transversal
  have hbudget := edgeCountIn_univ_split G T
  rw [← hHdef] at hbudget
  have hs2 : edgeCountIn G T ≤ 2 := by have := ctx.he60; omega
  have hx2 : crossCount G T ≤ 2 := by have := ctx.he60; omega
  obtain ⟨P0, hP0sub, hP0indep, hP0card⟩ : ∃ P ⊆ T, IsIndep G P ∧ 3 ≤ P.card := by
    by_contra hcon
    push_neg at hcon
    have hα2 : ∀ S : Finset (Fin 25), S ⊆ T → IsIndep G S → S.card ≤ 2 :=
      fun S hS hind => by have := hcon S hS hind; omega
    have hK5free : ∀ Q : Finset (Fin 25), Q ⊆ T → Q.card = 5 → ¬ IsCliqueOn G Q := by
      intro Q hQ hQc hclq
      have hQT : Q = T := Finset.eq_of_subset_of_card_le hQ (le_of_eq (by rw [ctx.hT, hQc]))
      subst hQT
      have h10 := edgeCountIn_eq_choose_of_clique G hclq
      rw [ctx.hT] at h10
      have hchoose : (5 : ℕ).choose 2 = 10 := by decide
      omega
    have hfloor := Mfloor_le_edgeCountIn pf G T ctx.hcap hα2 hK5free (by rw [ctx.hT]; norm_num)
    rw [ctx.hT, show Mfloor 5 = 4 from by decide] at hfloor
    omega
  obtain ⟨P, hPP0, hPcard⟩ := Finset.exists_subset_card_eq hP0card
  have hPsub : P ⊆ T := hPP0.trans hP0sub
  have hPindep : IsIndep G P := fun a ha b hb hab => hP0indep a (hPP0 ha) b (hPP0 hb) hab
  -- forbidden-by-`P` count in each `Qi` is ≤ 2
  have hDi_le : ∀ Qi : Finset (Fin 25),
      (Qi.filter (fun q => ∃ p ∈ P, G.Adj p q)).card
        ≤ ∑ p ∈ P, (Qi.filter (fun q => G.Adj p q)).card := by
    intro Qi
    refine le_trans (Finset.card_le_card ?_) Finset.card_biUnion_le
    intro q hq; rw [Finset.mem_filter] at hq
    obtain ⟨hqQi, p, hpP, hpq⟩ := hq
    rw [Finset.mem_biUnion]; exact ⟨p, hpP, Finset.mem_filter.mpr ⟨hqQi, hpq⟩⟩
  have hper_p : ∀ p : Fin 25, (Q1.filter (fun q => G.Adj p q)).card
      + (Q2.filter (fun q => G.Adj p q)).card + (Q3.filter (fun q => G.Adj p q)).card
      ≤ ((Finset.univ \ T).filter (fun q => G.Adj p q)).card := by
    intro p
    have hd1 : Disjoint (Q1.filter (fun q => G.Adj p q)) (Q2.filter (fun q => G.Adj p q)) :=
      hADisj (Finset.filter_subset _ _) (Finset.filter_subset _ _) hd12
    have hd2 : Disjoint (Q1.filter (fun q => G.Adj p q) ∪ Q2.filter (fun q => G.Adj p q))
        (Q3.filter (fun q => G.Adj p q)) := Finset.disjoint_union_left.mpr
      ⟨hADisj (Finset.filter_subset _ _) (Finset.filter_subset _ _) hd13,
       hADisj (Finset.filter_subset _ _) (Finset.filter_subset _ _) hd23⟩
    have hsub : Q1.filter (fun q => G.Adj p q) ∪ Q2.filter (fun q => G.Adj p q)
        ∪ Q3.filter (fun q => G.Adj p q) ⊆ (Finset.univ \ T).filter (fun q => G.Adj p q) :=
      Finset.union_subset (Finset.union_subset (Finset.filter_subset_filter _ hQ1H)
        (Finset.filter_subset_filter _ hQ2H)) (Finset.filter_subset_filter _ hQ3H)
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1] at this
    omega
  have hsumforbid : (Q1.filter (fun q => ∃ p ∈ P, G.Adj p q)).card
      + (Q2.filter (fun q => ∃ p ∈ P, G.Adj p q)).card
      + (Q3.filter (fun q => ∃ p ∈ P, G.Adj p q)).card ≤ crossCount G T := by
    have h1 := hDi_le Q1; have h2 := hDi_le Q2; have h3 := hDi_le Q3
    have hsum : (∑ p ∈ P, (Q1.filter (fun q => G.Adj p q)).card)
        + (∑ p ∈ P, (Q2.filter (fun q => G.Adj p q)).card)
        + (∑ p ∈ P, (Q3.filter (fun q => G.Adj p q)).card)
        ≤ ∑ p ∈ P, ((Finset.univ \ T).filter (fun q => G.Adj p q)).card := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun p _ => hper_p p)
    have hPT : (∑ p ∈ P, ((Finset.univ \ T).filter (fun q => G.Adj p q)).card) ≤ crossCount G T :=
      Finset.sum_le_sum_of_subset_of_nonneg hPsub (fun _ _ _ => Nat.zero_le _)
    omega
  have hf1 : (Q1.filter (fun q => ∃ p ∈ P, G.Adj p q)).card ≤ 2 := by omega
  have hf2 : (Q2.filter (fun q => ∃ p ∈ P, G.Adj p q)).card ≤ 2 := by omega
  have hf3 : (Q3.filter (fun q => ∃ p ∈ P, G.Adj p q)).card ≤ 2 := by omega
  -- pick q1 ∈ Q1 with no P-neighbour
  have hq1e : (Q1.filter (fun q => ¬ ∃ p ∈ P, G.Adj p q)).Nonempty := by
    rw [← Finset.card_pos]
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card (s := Q1)
      (p := fun q => ∃ p ∈ P, G.Adj p q)
    omega
  obtain ⟨q1, hq1⟩ := hq1e
  rw [Finset.mem_filter] at hq1
  obtain ⟨hq1Q1, hq1P⟩ := hq1
  push_neg at hq1P
  -- pick q2 ∈ Q2 with no P-neighbour and not adjacent to q1
  have hq2e : (Q2.filter (fun q => (¬ ∃ p ∈ P, G.Adj p q) ∧ ¬ G.Adj q1 q)).Nonempty := by
    rw [← Finset.card_pos]
    have hq1Q2 : (Q2.filter (fun q => G.Adj q1 q)).card ≤ 1 :=
      indeg_clique5_le_one G ctx.hcap hQ2clq hQ2c (Finset.disjoint_left.mp hd12 hq1Q1)
    have hun : (Q2.filter (fun q => (∃ p ∈ P, G.Adj p q) ∨ G.Adj q1 q)).card
        ≤ (Q2.filter (fun q => ∃ p ∈ P, G.Adj p q)).card + (Q2.filter (fun q => G.Adj q1 q)).card := by
      refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
      intro q hq; rw [Finset.mem_filter] at hq; rcases hq.2 with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hq.1, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hq.1, h⟩)
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card (s := Q2)
      (p := fun q => (∃ p ∈ P, G.Adj p q) ∨ G.Adj q1 q)
    have hneg : Q2.filter (fun q => ¬ ((∃ p ∈ P, G.Adj p q) ∨ G.Adj q1 q))
        = Q2.filter (fun q => (¬ ∃ p ∈ P, G.Adj p q) ∧ ¬ G.Adj q1 q) := by
      apply Finset.filter_congr; intro q _; rw [not_or]
    rw [← hneg]; omega
  obtain ⟨q2, hq2⟩ := hq2e
  rw [Finset.mem_filter] at hq2
  obtain ⟨hq2Q2, hq2P, hq12⟩ := hq2
  push_neg at hq2P
  -- pick q3 ∈ Q3 with no P-neighbour and not adjacent to q1, q2
  have hq3e : (Q3.filter (fun q => (¬ ∃ p ∈ P, G.Adj p q) ∧ ¬ G.Adj q1 q ∧ ¬ G.Adj q2 q)).Nonempty := by
    rw [← Finset.card_pos]
    have hq1Q3 : (Q3.filter (fun q => G.Adj q1 q)).card ≤ 1 :=
      indeg_clique5_le_one G ctx.hcap hQ3clq hQ3c (Finset.disjoint_left.mp hd13 hq1Q1)
    have hq2Q3 : (Q3.filter (fun q => G.Adj q2 q)).card ≤ 1 :=
      indeg_clique5_le_one G ctx.hcap hQ3clq hQ3c (Finset.disjoint_left.mp hd23 hq2Q2)
    have hun : (Q3.filter (fun q => (∃ p ∈ P, G.Adj p q) ∨ G.Adj q1 q ∨ G.Adj q2 q)).card
        ≤ (Q3.filter (fun q => ∃ p ∈ P, G.Adj p q)).card + (Q3.filter (fun q => G.Adj q1 q)).card
          + (Q3.filter (fun q => G.Adj q2 q)).card := by
      have hsub : Q3.filter (fun q => (∃ p ∈ P, G.Adj p q) ∨ G.Adj q1 q ∨ G.Adj q2 q)
          ⊆ Q3.filter (fun q => ∃ p ∈ P, G.Adj p q) ∪ Q3.filter (fun q => G.Adj q1 q)
            ∪ Q3.filter (fun q => G.Adj q2 q) := by
        intro q hq; rw [Finset.mem_filter] at hq
        rcases hq.2 with h | h | h
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hq.1, h⟩))
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hq.1, h⟩))
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hq.1, h⟩)
      refine le_trans (Finset.card_le_card hsub) ?_
      exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card (s := Q3)
      (p := fun q => (∃ p ∈ P, G.Adj p q) ∨ G.Adj q1 q ∨ G.Adj q2 q)
    have hneg : Q3.filter (fun q => ¬ ((∃ p ∈ P, G.Adj p q) ∨ G.Adj q1 q ∨ G.Adj q2 q))
        = Q3.filter (fun q => (¬ ∃ p ∈ P, G.Adj p q) ∧ ¬ G.Adj q1 q ∧ ¬ G.Adj q2 q) := by
      apply Finset.filter_congr; intro q _; rw [not_or, not_or]
    rw [← hneg]; omega
  obtain ⟨q3, hq3⟩ := hq3e
  rw [Finset.mem_filter] at hq3
  obtain ⟨hq3Q3, hq3P, hq13, hq23⟩ := hq3
  push_neg at hq3P
  -- P ∪ {q1,q2,q3} is an independent 6-set
  obtain ⟨p1, p2, p3, hp12, hp13, hp23, hPeq⟩ := Finset.card_eq_three.mp hPcard
  have hp1P : p1 ∈ P := by rw [hPeq]; exact Finset.mem_insert_self _ _
  have hp2P : p2 ∈ P := by rw [hPeq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hp3P : p3 ∈ P := by
    rw [hPeq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hpiT : ∀ p ∈ P, p ∈ T := fun p hp => hPsub hp
  have hqiH : q1 ∈ H ∧ q2 ∈ H ∧ q3 ∈ H := ⟨hQ1H hq1Q1, hQ2H hq2Q2, hQ3H hq3Q3⟩
  have hne_pq : ∀ p ∈ P, ∀ (q : Fin 25), q ∈ H → p ≠ q :=
    fun p hp q hq => by rintro rfl; exact (Finset.mem_sdiff.mp hq).2 (hpiT p hp)
  exact no_indep_six ctx.hα5
    hp12 hp13 (hne_pq p1 hp1P q1 hqiH.1) (hne_pq p1 hp1P q2 hqiH.2.1) (hne_pq p1 hp1P q3 hqiH.2.2)
    hp23 (hne_pq p2 hp2P q1 hqiH.1) (hne_pq p2 hp2P q2 hqiH.2.1) (hne_pq p2 hp2P q3 hqiH.2.2)
    (hne_pq p3 hp3P q1 hqiH.1) (hne_pq p3 hp3P q2 hqiH.2.1) (hne_pq p3 hp3P q3 hqiH.2.2)
    (fun h => Finset.disjoint_left.mp hd12 hq1Q1 (h ▸ hq2Q2))
    (fun h => Finset.disjoint_left.mp hd13 hq1Q1 (h ▸ hq3Q3))
    (fun h => Finset.disjoint_left.mp hd23 hq2Q2 (h ▸ hq3Q3))
    (hPindep p1 hp1P p2 hp2P hp12) (hPindep p1 hp1P p3 hp3P hp13)
    (hq1P p1 hp1P) (hq2P p1 hp1P) (hq3P p1 hp1P)
    (hPindep p2 hp2P p3 hp3P hp23) (hq1P p2 hp2P) (hq2P p2 hp2P) (hq3P p2 hp2P)
    (hq1P p3 hp3P) (hq2P p3 hp3P) (hq3P p3 hp3P)
    hq12 hq13 hq23

/-! ## §5 finite facts over the 10 pairwise adjacencies of  -/

/-- ≤5 edges ⇒ two disjoint non-edges (15 configs). -/
theorem deg_split {G : SimpleGraph (Fin 25)} {A Bs : Finset (Fin 25)} (h : Disjoint A Bs)
    (v : Fin 25) :
    ((A ∪ Bs).filter (fun w => G.Adj v w)).card
      = (A.filter (fun w => G.Adj v w)).card + (Bs.filter (fun w => G.Adj v w)).card := by
  rw [Finset.filter_union, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter h

theorem cross_symm {G : SimpleGraph (Fin 25)} (A Bs : Finset (Fin 25)) :
    (∑ a ∈ A, (Bs.filter (fun w => G.Adj a w)).card)
      = ∑ b ∈ Bs, (A.filter (fun w => G.Adj b w)).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _; apply Finset.sum_congr rfl; intro a _
  by_cases h : G.Adj a b
  · rw [if_pos h, if_pos (G.symm h)]
  · rw [if_neg h, if_neg (fun hh => h (G.symm hh))]

/-- **§5 r=4 star endgame** (informal (28)–(32)). -/
theorem sec5_star_endgame {G : SimpleGraph (Fin 25)} (hcap : capAtMost11 G)
    {Bset : Finset (Fin 25)} (hBc : Bset.card = 10)
    (hαB2 : ∀ S : Finset (Fin 25), S ⊆ Bset → IsIndep G S → S.card ≤ 2)
    (hBfree : ∀ Q : Finset (Fin 25), Q ⊆ Bset → Q.card = 5 → ¬ IsCliqueOn G Q)
    (heB25 : edgeCountIn G Bset = 25)
    {t0 leaf : Fin 25} (ht0nB : t0 ∉ Bset)
    (hZ5 : (Bset.filter (fun v => G.Adj t0 v)).card = 5)
    (hleaf1 : (Bset.filter (fun v => G.Adj leaf v)).card = 1)
    (hhit : IsCliqueOn G (Bset.filter (fun v => ¬ G.Adj t0 v ∧ ¬ G.Adj leaf v))) : False := by
  classical
  set Z := Bset.filter (fun v => G.Adj t0 v) with hZdef
  have hZB : Z ⊆ Bset := Finset.filter_subset _ _
  set C := Bset \ Z with hCdef
  have hCB : C ⊆ Bset := Finset.sdiff_subset
  have hZCdisj : Disjoint Z C := by rw [hCdef]; exact Finset.disjoint_sdiff
  have hZCunion : Z ∪ C = Bset := by rw [hCdef]; exact Finset.union_sdiff_of_subset hZB
  have hCc : C.card = 5 := by
    have h := Finset.card_sdiff_of_subset hZB; rw [hCdef]; omega
  obtain ⟨zs, hzs⟩ := Finset.card_eq_one.mp hleaf1
  have hzsB : zs ∈ Bset :=
    Finset.mem_of_mem_filter _ (by rw [hzs]; exact Finset.mem_singleton_self zs)
  have hAleafzs : G.Adj leaf zs :=
    (Finset.mem_filter.mp (show zs ∈ Bset.filter (fun v => G.Adj leaf v) by
      rw [hzs]; exact Finset.mem_singleton_self zs)).2
  have hleaf_char : ∀ v ∈ Bset, (G.Adj leaf v ↔ v = zs) := by
    intro v hv
    refine ⟨fun hadj => ?_, fun hveq => hveq ▸ hAleafzs⟩
    have hmem : v ∈ Bset.filter (fun v => G.Adj leaf v) := Finset.mem_filter.mpr ⟨hv, hadj⟩
    rw [hzs, Finset.mem_singleton] at hmem; exact hmem
  have hCchar : ∀ v, v ∈ C ↔ (v ∈ Bset ∧ ¬ G.Adj t0 v) := by
    intro v; rw [hCdef, Finset.mem_sdiff, hZdef, Finset.mem_filter]
    exact ⟨fun ⟨hvB, hnZ⟩ => ⟨hvB, fun hadj => hnZ ⟨hvB, hadj⟩⟩,
           fun ⟨hvB, hnadj⟩ => ⟨hvB, fun h => hnadj h.2⟩⟩
  have hres_eq : Bset.filter (fun v => ¬ G.Adj t0 v ∧ ¬ G.Adj leaf v) = C.erase zs := by
    ext v; simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hvB, hn0, hnl⟩
      exact ⟨fun hveq => hnl ((hleaf_char v hvB).mpr hveq), (hCchar v).mpr ⟨hvB, hn0⟩⟩
    · rintro ⟨hvne, hvC⟩
      have hvB := (hCchar v).mp hvC
      exact ⟨hvB.1, hvB.2, fun hadj => hvne ((hleaf_char v hvB.1).mp hadj)⟩
  have hzsC : zs ∈ C := by
    by_contra hzsnC
    apply hBfree C hCB hCc
    intro u hu v hv huv
    have := hhit
    rw [hres_eq, Finset.erase_eq_of_notMem hzsnC] at this
    exact this u hu v hv huv
  have hCez : (C.erase zs).card = 4 := by rw [Finset.card_erase_of_mem hzsC, hCc]
  have hK4 : IsCliqueOn G (C.erase zs) := by rw [← hres_eq]; exact hhit
  have heCez6 : edgeCountIn G (C.erase zs) = 6 := by
    rw [edgeCountIn_eq_choose_of_clique G hK4, hCez]; rfl
  have hnbr_split : ∀ v, (Bset.filter (fun w => G.Adj v w)).card
      = (Z.filter (fun w => G.Adj v w)).card + (C.filter (fun w => G.Adj v w)).card := by
    intro v; rw [← hZCunion]; exact deg_split hZCdisj v
  have hdeg_ge : ∀ v ∈ Bset, 5 ≤ (Bset.filter (fun w => G.Adj v w)).card := by
    intro v hv
    set NB := Bset.filter (fun w => w ≠ v ∧ ¬ G.Adj v w) with hNBdef
    have hNBclq : IsCliqueOn G NB := by
      intro a ha b hb hab
      by_contra hnadj
      have haB := (Finset.mem_filter.mp ha).1; have hbB := (Finset.mem_filter.mp hb).1
      have hav := (Finset.mem_filter.mp ha).2; have hbv := (Finset.mem_filter.mp hb).2
      have hind : IsIndep G {v, a, b} := by
        intro x hx y hy hxy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
          first
            | exact absurd rfl hxy
            | exact hav.2 | exact hbv.2
            | exact fun h => hav.2 (G.symm h) | exact fun h => hbv.2 (G.symm h)
            | exact hnadj | exact fun h => hnadj (G.symm h)
      have hcard3 : ({v, a, b} : Finset (Fin 25)).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp only [Finset.mem_singleton]; exact fun h => hab h
        · simp only [Finset.mem_insert, Finset.mem_singleton]
          exact fun h => h.elim (fun h => hav.1 h.symm) (fun h => hbv.1 h.symm)
      have := hαB2 {v, a, b} (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        exacts [hv, haB, hbB]) hind
      omega
    have hNBle : NB.card ≤ 4 := by
      by_contra h; push_neg at h
      obtain ⟨Q, hQsub, hQc⟩ := Finset.exists_subset_card_eq (show 5 ≤ NB.card by omega)
      exact hBfree Q (hQsub.trans (Finset.filter_subset _ _)) hQc
        (fun a ha b hb hab => hNBclq a (hQsub ha) b (hQsub hb) hab)
    have e1 := Finset.filter_card_add_filter_neg_card_eq_card (s := Bset)
      (p := fun w => G.Adj v w)
    have hfnv : Bset.filter (fun w => ¬ G.Adj v w) = insert v NB := by
      ext w; simp only [hNBdef, Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hwB, hnadj⟩
        by_cases hwv : w = v
        · exact Or.inl hwv
        · exact Or.inr ⟨hwB, hwv, hnadj⟩
      · rintro (rfl | ⟨hwB, _, hnadj⟩)
        · exact ⟨hv, G.irrefl⟩
        · exact ⟨hwB, hnadj⟩
    have hvNB : v ∉ NB := by rw [hNBdef, Finset.mem_filter]; exact fun h => h.2.1 rfl
    rw [hfnv, Finset.card_insert_of_notMem hvNB] at e1
    omega
  have hdeg5 : ∀ v ∈ Bset, (Bset.filter (fun w => G.Adj v w)).card = 5 := by
    have hsum : (∑ v ∈ Bset, (Bset.filter (fun w => G.Adj v w)).card) = 50 := by
      rw [sum_adj_filter_eq_two_mul, heB25]
    intro v hv
    have hsplit : (∑ w ∈ Bset, (Bset.filter (fun u => G.Adj w u)).card)
        = (Bset.filter (fun u => G.Adj v u)).card
          + ∑ w ∈ Bset.erase v, (Bset.filter (fun u => G.Adj w u)).card := by
      rw [← Finset.sum_erase_add _ _ hv]; ring
    have hge_erase : (45 : ℕ) ≤ ∑ w ∈ Bset.erase v, (Bset.filter (fun u => G.Adj w u)).card := by
      calc (45 : ℕ) = ∑ _w ∈ Bset.erase v, 5 := by
            rw [Finset.sum_const, Finset.card_erase_of_mem hv, hBc]; rfl
        _ ≤ _ := Finset.sum_le_sum (fun w hw => hdeg_ge w (Finset.mem_of_mem_erase hw))
    have := hdeg_ge v hv
    omega
  have hZadj : ∀ z ∈ Z, G.Adj t0 z := fun z hz => (Finset.mem_filter.mp hz).2
  have ht0nZ : t0 ∉ Z := fun h => ht0nB (hZB h)
  have heZ_le : edgeCountIn G Z ≤ 6 := by
    have hins : edgeCountIn G (insert t0 Z) = edgeCountIn G Z + (Z.filter (fun q => G.Adj t0 q)).card :=
      edgeCountIn_insert_eq G ht0nZ
    have hfilt : Z.filter (fun q => G.Adj t0 q) = Z :=
      Finset.filter_true_of_mem (fun z hz => hZadj z hz)
    rw [hfilt, hZ5] at hins
    have hcard6 : (insert t0 Z).card = 6 := by rw [Finset.card_insert_of_notMem ht0nZ, hZ5]
    have := hcap (insert t0 Z) hcard6
    omega
  have heC_ge : 6 ≤ edgeCountIn G C := by
    rw [← heCez6]; exact edgeCountIn_mono G (Finset.erase_subset _ _)
  have hZreg : (∑ z ∈ Z, (Bset.filter (fun w => G.Adj z w)).card) = 25 := by
    calc _ = ∑ _z ∈ Z, 5 := Finset.sum_congr rfl (fun z hz => hdeg5 z (hZB hz))
      _ = 25 := by rw [Finset.sum_const, hZ5]; rfl
  have hCreg : (∑ c ∈ C, (Bset.filter (fun w => G.Adj c w)).card) = 25 := by
    calc _ = ∑ _c ∈ C, 5 := Finset.sum_congr rfl (fun c hc => hdeg5 c (hCB hc))
      _ = 25 := by rw [Finset.sum_const, hCc]; rfl
  have hZsum : (∑ z ∈ Z, (Bset.filter (fun w => G.Adj z w)).card)
      = 2 * edgeCountIn G Z + ∑ z ∈ Z, (C.filter (fun w => G.Adj z w)).card := by
    rw [← sum_adj_filter_eq_two_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun z _ => hnbr_split z)
  have hCsum : (∑ c ∈ C, (Bset.filter (fun w => G.Adj c w)).card)
      = 2 * edgeCountIn G C + ∑ c ∈ C, (Z.filter (fun w => G.Adj c w)).card := by
    rw [← sum_adj_filter_eq_two_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [hnbr_split c]; ring
  have hcross := cross_symm (G := G) Z C
  have heZ6 : edgeCountIn G Z = 6 := by omega
  have heC6 : edgeCountIn G C = 6 := by omega
  have hzs_isoC : (C.erase zs).filter (fun w => G.Adj zs w) = ∅ := by
    have hins : edgeCountIn G C = edgeCountIn G (C.erase zs)
        + ((C.erase zs).filter (fun q => G.Adj zs q)).card := by
      conv_lhs => rw [← Finset.insert_erase hzsC]
      exact edgeCountIn_insert_eq G (Finset.notMem_erase zs C)
    rw [heC6, heCez6] at hins
    exact Finset.card_eq_zero.mp (by omega)
  have hzsCzero : (C.filter (fun w => G.Adj zs w)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    rw [Finset.mem_filter] at hw
    have hwerase : w ∈ C.erase zs := by
      rw [Finset.mem_erase]; exact ⟨fun h => G.irrefl (h ▸ hw.2), hw.1⟩
    have hmem : w ∈ (C.erase zs).filter (fun w => G.Adj zs w) :=
      Finset.mem_filter.mpr ⟨hwerase, hw.2⟩
    rw [hzs_isoC] at hmem; exact Finset.notMem_empty w hmem
  have hzsB' := hzsB
  have hzsZfull : (Z.filter (fun w => G.Adj zs w)).card = 5 := by
    have hd := hdeg5 zs hzsB
    have hsp := hnbr_split zs
    rw [hzsCzero] at hsp
    omega
  have hzsZall : ∀ z ∈ Z, G.Adj zs z := by
    have heq : Z.filter (fun w => G.Adj zs w) = Z :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
        (by rw [hzsZfull]; exact le_of_eq hZ5)
    intro z hz
    have hmem : z ∈ Z.filter (fun w => G.Adj zs w) := by rw [heq]; exact hz
    exact (Finset.mem_filter.mp hmem).2
  have ht0zs : ¬ G.Adj t0 zs := ((hCchar zs).mp hzsC).2
  have hzsnZ : zs ∉ Z := Finset.disjoint_left.mp hZCdisj.symm hzsC
  have hZdeg_ge3 : ∀ z ∈ Z, 3 ≤ (Z.filter (fun w => G.Adj z w)).card := by
    intro z hz
    set S := insert t0 (insert zs (Z.erase z)) with hSdef
    have hzsnZez : zs ∉ Z.erase z := fun h => hzsnZ (Finset.mem_of_mem_erase h)
    have ht0nZez : t0 ∉ insert zs (Z.erase z) := by
      rw [Finset.mem_insert]; push_neg
      exact ⟨fun h => ht0nB (h ▸ hzsB), fun h => ht0nZ (Finset.mem_of_mem_erase h)⟩
    have hScard : S.card = 6 := by
      rw [hSdef, Finset.card_insert_of_notMem ht0nZez, Finset.card_insert_of_notMem hzsnZez,
        Finset.card_erase_of_mem hz, hZ5]
    have hZez_adj_zs : (Z.erase z).filter (fun q => G.Adj zs q) = Z.erase z :=
      Finset.filter_true_of_mem (fun w hw => hzsZall w (Finset.mem_of_mem_erase hw))
    have hZez_card : (Z.erase z).card = 4 := by rw [Finset.card_erase_of_mem hz, hZ5]
    have heInner : edgeCountIn G (insert zs (Z.erase z)) = edgeCountIn G (Z.erase z) + 4 := by
      rw [edgeCountIn_insert_eq G hzsnZez, hZez_adj_zs, hZez_card]
    have hZez_e : edgeCountIn G (Z.erase z) = 6 - (Z.filter (fun w => G.Adj z w)).card := by
      have hins : edgeCountIn G Z = edgeCountIn G (Z.erase z)
          + ((Z.erase z).filter (fun q => G.Adj z q)).card := by
        conv_lhs => rw [← Finset.insert_erase hz]
        exact edgeCountIn_insert_eq G (Finset.notMem_erase z Z)
      have hfz : (Z.erase z).filter (fun q => G.Adj z q) = Z.filter (fun q => G.Adj z q) := by
        rw [Finset.filter_erase]
        exact Finset.erase_eq_of_notMem (fun h => G.irrefl (Finset.mem_filter.mp h).2)
      rw [heZ6, hfz] at hins; omega
    have ht0_adj_inner : (insert zs (Z.erase z)).filter (fun q => G.Adj t0 q) = Z.erase z := by
      ext w; simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hw, hadj⟩
        · exact absurd hadj ht0zs
        · exact hw
      · intro hw; exact ⟨Or.inr hw, hZadj w (Finset.mem_of_mem_erase hw)⟩
    have heS : edgeCountIn G S = (6 - (Z.filter (fun w => G.Adj z w)).card) + 4 + 4 := by
      rw [hSdef, edgeCountIn_insert_eq G ht0nZez, ht0_adj_inner, hZez_card, heInner, hZez_e]
    have hcapS := hcap S hScard
    omega
  have h2eZ : (∑ z ∈ Z, (Z.filter (fun w => G.Adj z w)).card) = 2 * edgeCountIn G Z :=
    sum_adj_filter_eq_two_mul G Z
  have hge15 : (15 : ℕ) ≤ ∑ z ∈ Z, (Z.filter (fun w => G.Adj z w)).card := by
    calc (15 : ℕ) = ∑ _z ∈ Z, 3 := by rw [Finset.sum_const, hZ5]; rfl
      _ ≤ _ := Finset.sum_le_sum (fun z hz => hZdeg_ge3 z hz)
  rw [h2eZ, heZ6] at hge15
  omega


/-- Budget variant giving `e(B) + D ≤ 40 − s` (so at r=4, D=9, s=6 ⇒ e(B) ≤ 25). -/
theorem sec5_eB_D_le {G : SimpleGraph (Fin 25)} {T Q1 Q2 : Finset (Fin 25)}
    (he60 : edgeCountIn G Finset.univ ≤ 60)
    (hQ1H : Q1 ⊆ Finset.univ \ T) (hQ2sub : Q2 ⊆ (Finset.univ \ T) \ Q1)
    (hQ1clq : IsCliqueOn G Q1) (hQ1c : Q1.card = 5)
    (hQ2clq : IsCliqueOn G Q2) (hQ2c : Q2.card = 5) :
    edgeCountIn G (((Finset.univ \ T) \ Q1) \ Q2)
      + (∑ t ∈ T, ((((Finset.univ \ T) \ Q1) \ Q2).filter (fun v => G.Adj t v)).card)
      ≤ 40 - edgeCountIn G T := by
  set H := Finset.univ \ T with hHdef
  set Bset := ((Finset.univ \ T) \ Q1) \ Q2 with hBdef
  have heQ1 : edgeCountIn G Q1 = 10 := by
    rw [edgeCountIn_eq_choose_of_clique G hQ1clq, hQ1c]; rfl
  have heQ2 : edgeCountIn G Q2 = 10 := by
    rw [edgeCountIn_eq_choose_of_clique G hQ2clq, hQ2c]; rfl
  have hsplitA : edgeCountIn G Q1 + edgeCountIn G (H \ Q1) ≤ edgeCountIn G H := by
    have hd : Disjoint Q1 (H \ Q1) := Finset.disjoint_sdiff
    have hu : Q1 ∪ (H \ Q1) = H := by
      rw [Finset.union_comm]; exact Finset.sdiff_union_of_subset hQ1H
    have h := edgeCountIn_add_le_union_disjoint G hd; rwa [hu] at h
  have hsplitB : edgeCountIn G Q2 + edgeCountIn G Bset ≤ edgeCountIn G (H \ Q1) := by
    have hd : Disjoint Q2 ((H \ Q1) \ Q2) := Finset.disjoint_sdiff
    have hu : Q2 ∪ ((H \ Q1) \ Q2) = H \ Q1 := by
      rw [Finset.union_comm]; exact Finset.sdiff_union_of_subset hQ2sub
    have h := edgeCountIn_add_le_union_disjoint G hd; rw [hu] at h; rw [hBdef]; exact h
  have hHge : 20 + edgeCountIn G Bset ≤ edgeCountIn G H := by omega
  have hBH : Bset ⊆ H := hBdef ▸ (Finset.sdiff_subset.trans Finset.sdiff_subset)
  have hDcross : (∑ t ∈ T, (Bset.filter (fun v => G.Adj t v)).card) ≤ crossCount G T := by
    unfold crossCount
    apply Finset.sum_le_sum
    intro t _
    exact Finset.card_le_card (Finset.filter_subset_filter _ hBH)
  have hsplit := edgeCountIn_univ_split G T
  rw [← hHdef] at hsplit
  omega


theorem twoDisjoint : ∀ (b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 : Bool),
    (b01.toNat+b02.toNat+b03.toNat+b04.toNat+b12.toNat
      +b13.toNat+b14.toNat+b23.toNat+b24.toNat+b34.toNat ≤ 5) →
    ((!b01 && !b23) || (!b01 && !b24) || (!b01 && !b34)
    || (!b02 && !b13) || (!b02 && !b14) || (!b02 && !b34)
    || (!b03 && !b12) || (!b03 && !b14) || (!b03 && !b24)
    || (!b04 && !b12) || (!b04 && !b13) || (!b04 && !b23)
    || (!b12 && !b34) || (!b13 && !b24) || (!b14 && !b23)) = true := by
  decide

/-- ≤2 edges ⇒ a 5-cycle of non-edges (all 12 Hamilton cycles of K₅). -/
theorem fiveCycle : ∀ (b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 : Bool),
    (b01.toNat+b02.toNat+b03.toNat+b04.toNat+b12.toNat
      +b13.toNat+b14.toNat+b23.toNat+b24.toNat+b34.toNat ≤ 2) →
    ((!b01 && !b13 && !b34 && !b24 && !b02) || (!b01 && !b14 && !b34 && !b23 && !b02)
    || (!b01 && !b12 && !b24 && !b34 && !b03) || (!b01 && !b14 && !b24 && !b23 && !b03)
    || (!b01 && !b12 && !b23 && !b34 && !b04) || (!b01 && !b13 && !b23 && !b24 && !b04)
    || (!b02 && !b12 && !b14 && !b34 && !b03) || (!b02 && !b24 && !b14 && !b13 && !b03)
    || (!b02 && !b12 && !b13 && !b34 && !b04) || (!b02 && !b23 && !b13 && !b14 && !b04)
    || (!b03 && !b13 && !b12 && !b24 && !b04) || (!b03 && !b23 && !b12 && !b14 && !b04)) = true := by
  decide

/-- ≤6 edges ⇒ two disjoint non-edges OR a star centre. -/
theorem starOrDisjoint : ∀ (b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 : Bool),
    (b01.toNat+b02.toNat+b03.toNat+b04.toNat+b12.toNat
      +b13.toNat+b14.toNat+b23.toNat+b24.toNat+b34.toNat ≤ 6) →
    ((!b01 && !b23) || (!b01 && !b24) || (!b01 && !b34)
    || (!b02 && !b13) || (!b02 && !b14) || (!b02 && !b34)
    || (!b03 && !b12) || (!b03 && !b14) || (!b03 && !b24)
    || (!b04 && !b12) || (!b04 && !b13) || (!b04 && !b23)
    || (!b12 && !b34) || (!b13 && !b24) || (!b14 && !b23)
    || (!b01 && !b02 && !b03 && !b04) || (!b01 && !b12 && !b13 && !b14)
    || (!b02 && !b12 && !b23 && !b24) || (!b03 && !b13 && !b23 && !b34)
    || (!b04 && !b14 && !b24 && !b34)) = true := by
  decide

/-! ## §5 boolean/edge-count bridge -/

/-- Edge count of a 5-set (image of injective `e : Fin 5 → Fin 25`) as the double
sum of adjacency indicators. -/
theorem edgeCount_five {G : SimpleGraph (Fin 25)} {e : Fin 5 → Fin 25}
    (hinj : Function.Injective e) :
    2 * edgeCountIn G (Finset.image e Finset.univ)
      = ∑ i : Fin 5, ∑ j : Fin 5, (if G.Adj (e i) (e j) then 1 else 0) := by
  have hii : ∀ x ∈ (Finset.univ : Finset (Fin 5)), ∀ y ∈ (Finset.univ : Finset (Fin 5)),
      e x = e y → x = y := fun x _ y _ h => hinj h
  rw [← sum_adj_filter_eq_two_mul, Finset.sum_image hii]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.card_filter, Finset.sum_image hii]

/-- Edge count of a 5-set as the sum of the 10 pairwise adjacency indicators. -/
theorem s_expand {G : SimpleGraph (Fin 25)} {e : Fin 5 → Fin 25}
    (hinj : Function.Injective e) :
    edgeCountIn G (Finset.image e Finset.univ)
      = (if G.Adj (e 0) (e 1) then 1 else 0) + (if G.Adj (e 0) (e 2) then 1 else 0)
      + (if G.Adj (e 0) (e 3) then 1 else 0) + (if G.Adj (e 0) (e 4) then 1 else 0)
      + (if G.Adj (e 1) (e 2) then 1 else 0) + (if G.Adj (e 1) (e 3) then 1 else 0)
      + (if G.Adj (e 1) (e 4) then 1 else 0) + (if G.Adj (e 2) (e 3) then 1 else 0)
      + (if G.Adj (e 2) (e 4) then 1 else 0) + (if G.Adj (e 3) (e 4) then 1 else 0) := by
  have h := edgeCount_five (G := G) hinj
  have hdiag : ∀ k : Fin 5, (if G.Adj (e k) (e k) then (1:ℕ) else 0) = 0 := by
    intro k; rw [if_neg]; exact G.irrefl
  have hsym : ∀ i j : Fin 5,
      (if G.Adj (e j) (e i) then (1:ℕ) else 0) = (if G.Adj (e i) (e j) then 1 else 0) :=
    fun i j => by rw [G.adj_comm]
  simp only [Fin.sum_univ_five, hdiag] at h
  rw [hsym 0 1, hsym 0 2, hsym 0 3, hsym 0 4, hsym 1 2, hsym 1 3, hsym 1 4,
      hsym 2 3, hsym 2 4, hsym 3 4] at h
  omega


/-- **KEY (nonex11 transport).** An `α ≤ 2` subset `X` of size 11 under cap-11 is
impossible (F3's ω-free 11-vertex nonexistence, transported via `comap`). -/
theorem nonex11_transport (pf : PrimFacts) {G : SimpleGraph (Fin n)} (hcap : capAtMost11 G)
    {X : Finset (Fin n)} (hXc : X.card = 11)
    (hα2 : ∀ S : Finset (Fin n), S ⊆ X → IsIndep G S → S.card ≤ 2) : False := by
  obtain ⟨f, hf⟩ := exists_embedding_image_eq X hXc
  refine pf.nonex11 (G.comap f) (capAtMost11_comap G f hcap) (alphaAtMost_comap_mm G f ?_)
  intro S hSsub hSindep
  rw [hf] at hSsub
  exact hα2 S hSsub hSindep

/-- An independent subset of a clique has at most one vertex. -/
theorem indep_subset_clique_le_one {G : SimpleGraph (Fin n)} {K S : Finset (Fin n)}
    (hK : IsCliqueOn G K) (hSK : S ⊆ K) (hS : IsIndep G S) : S.card ≤ 1 := by
  by_contra hc
  push_neg at hc
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hc
  exact hS u hu v hv huv (hK u (hSK hu) v (hSK hv) huv)

/-- **The `B + t` collapse.** If `B` (10 vertices, `α(B) ≤ 2`) and `t ∉ B` are such
that the `B`-nonneighbours of `t` form a clique, then `X = insert t B` is an
`α ≤ 2` graph on 11 vertices — impossible by `nonex11`. (This is the common
closing move of the r=7 repair and the r=4 zero-leaf case.) -/
theorem sec5_Bt_clique_false (pf : PrimFacts) {G : SimpleGraph (Fin n)} (hcap : capAtMost11 G)
    {B : Finset (Fin n)} (hBc : B.card = 10)
    (hαB : ∀ S : Finset (Fin n), S ⊆ B → IsIndep G S → S.card ≤ 2)
    {t : Fin n} (htB : t ∉ B)
    (hclq : IsCliqueOn G (B.filter (fun v => ¬ G.Adj t v))) : False := by
  refine nonex11_transport pf hcap (X := insert t B)
    (by rw [Finset.card_insert_of_notMem htB, hBc]) ?_
  intro S hSsub hSindep
  by_cases htS : t ∈ S
  · -- S \ {t} is an independent subset of the nonneighbour-clique ⇒ ≤ 1 vertex.
    have hSt : S.erase t ⊆ B.filter (fun v => ¬ G.Adj t v) := by
      intro u hu
      rw [Finset.mem_erase] at hu
      have huB : u ∈ B := by
        have hmem := hSsub hu.2
        rw [Finset.mem_insert] at hmem
        rcases hmem with h | h
        · exact absurd h hu.1
        · exact h
      rw [Finset.mem_filter]
      exact ⟨huB, fun hadj => hSindep t htS u hu.2 (Ne.symm hu.1) hadj⟩
    have hindep_erase : IsIndep G (S.erase t) :=
      fun a ha b hb hab =>
        hSindep a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) hab
    have h1 := indep_subset_clique_le_one hclq hSt hindep_erase
    have hce := Finset.card_erase_of_mem htS
    have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨t, htS⟩
    omega
  · have hSB : S ⊆ B := by
      intro u hu
      have hmem := hSsub hu
      rw [Finset.mem_insert] at hmem
      rcases hmem with rfl | h
      · exact absurd hu htS
      · exact h
    exact hαB S hSB hSindep

/-! ## §5 setup: hit/union bound and budget -/

/-- **Hit ⟹ union ≥ 6.** For non-adjacent `t,t'` (in `T`), if the `B`-vertices
non-adjacent to both form a clique (the edge is "hit"), then since `ω(B) ≤ 4`,
`|N_B(t) ∪ N_B(t')| ≥ 6`. -/
theorem sec5_hit_union_ge {G : SimpleGraph (Fin 25)} {Bset : Finset (Fin 25)}
    (hBfree : ∀ Q, Q ⊆ Bset → Q.card = 5 → ¬ IsCliqueOn G Q)
    (hBc : Bset.card = 10) {t t' : Fin 25}
    (hclq : IsCliqueOn G (Bset.filter (fun v => ¬ G.Adj t v ∧ ¬ G.Adj t' v))) :
    6 ≤ (Bset.filter (fun v => G.Adj t v ∨ G.Adj t' v)).card := by
  set res := Bset.filter (fun v => ¬ G.Adj t v ∧ ¬ G.Adj t' v) with hres
  have hpart : (Bset.filter (fun v => G.Adj t v ∨ G.Adj t' v)).card + res.card = 10 := by
    have h := Finset.filter_card_add_filter_neg_card_eq_card (s := Bset)
      (p := fun v => G.Adj t v ∨ G.Adj t' v)
    have hne : Bset.filter (fun v => ¬ (G.Adj t v ∨ G.Adj t' v)) = res := by
      rw [hres]; apply Finset.filter_congr; intro v _; rw [not_or]
    rw [hne, hBc] at h; exact h
  have hres4 : res.card ≤ 4 := by
    by_contra hc
    push_neg at hc
    obtain ⟨Q, hQsub, hQc⟩ := Finset.exists_subset_card_eq (show 5 ≤ res.card by omega)
    exact hBfree Q (hQsub.trans (Finset.filter_subset _ _)) hQc
      (fun u hu v hv huv => hclq u (hQsub hu) v (hQsub hv) huv)
  omega

/-- **§5 budget: `D ≤ 15 − s`.** `e(T,B) = ∑_t d_B(t) ≤ crossCount ≤ 60 − e(H) − e(T)`,
and `e(H) ≥ e(Q₁)+e(Q₂)+e(B) ≥ 45`. -/
theorem sec5_D_le {G : SimpleGraph (Fin 25)} {T Q1 Q2 : Finset (Fin 25)}
    (he60 : edgeCountIn G Finset.univ ≤ 60)
    (hQ1H : Q1 ⊆ Finset.univ \ T) (hQ2sub : Q2 ⊆ (Finset.univ \ T) \ Q1)
    (hQ1clq : IsCliqueOn G Q1) (hQ1c : Q1.card = 5)
    (hQ2clq : IsCliqueOn G Q2) (hQ2c : Q2.card = 5)
    (heB25 : 25 ≤ edgeCountIn G (((Finset.univ \ T) \ Q1) \ Q2)) :
    (∑ t ∈ T, ((((Finset.univ \ T) \ Q1) \ Q2).filter (fun v => G.Adj t v)).card)
      ≤ 15 - edgeCountIn G T := by
  set H := Finset.univ \ T with hHdef
  set Bset := ((Finset.univ \ T) \ Q1) \ Q2 with hBdef
  have heQ1 : edgeCountIn G Q1 = 10 := by
    rw [edgeCountIn_eq_choose_of_clique G hQ1clq, hQ1c]; rfl
  have heQ2 : edgeCountIn G Q2 = 10 := by
    rw [edgeCountIn_eq_choose_of_clique G hQ2clq, hQ2c]; rfl
  -- e(H) ≥ e(Q1) + e(H\Q1), and e(H\Q1) ≥ e(Q2) + e(Bset)
  have hsplitA : edgeCountIn G Q1 + edgeCountIn G (H \ Q1) ≤ edgeCountIn G H := by
    have hd : Disjoint Q1 (H \ Q1) := Finset.disjoint_sdiff
    have hu : Q1 ∪ (H \ Q1) = H := by
      rw [Finset.union_comm]; exact Finset.sdiff_union_of_subset hQ1H
    have h := edgeCountIn_add_le_union_disjoint G hd; rwa [hu] at h
  have hsplitB : edgeCountIn G Q2 + edgeCountIn G Bset ≤ edgeCountIn G (H \ Q1) := by
    have hd : Disjoint Q2 ((H \ Q1) \ Q2) := Finset.disjoint_sdiff
    have hu : Q2 ∪ ((H \ Q1) \ Q2) = H \ Q1 := by
      rw [Finset.union_comm]; exact Finset.sdiff_union_of_subset hQ2sub
    have h := edgeCountIn_add_le_union_disjoint G hd; rw [hu] at h; rw [hBdef]; exact h
  have hH45 : 45 ≤ edgeCountIn G H := by omega
  -- D ≤ crossCount
  have hBH : Bset ⊆ H := hBdef ▸ (Finset.sdiff_subset.trans Finset.sdiff_subset)
  have hDcross : (∑ t ∈ T, (Bset.filter (fun v => G.Adj t v)).card) ≤ crossCount G T := by
    unfold crossCount
    apply Finset.sum_le_sum
    intro t _
    exact Finset.card_le_card (Finset.filter_subset_filter _ hBH)
  have hsplit := edgeCountIn_univ_split G T
  rw [← hHdef] at hsplit
  omega

/-- `(decide P).toNat = if P then 1 else 0`. -/
theorem toNat_decide' (P : Prop) [Decidable P] : (decide P).toNat = if P then 1 else 0 := by
  by_cases h : P <;> simp [h]

/-- **§5 unhit structure.** An independent 4-set `{a,b,c,d}` disjoint from two
disjoint 5-cliques `Q1,Q2` (cap-11, α≤5) forces each of the four vertices to have
a neighbour in each `Qℓ` (the four "hit" vertices of `Qℓ` exhaust it but one), and
forces a `Q1`–`Q2` edge (the two unique missed vertices are adjacent). -/
theorem sec5_unhit_core {G : SimpleGraph (Fin 25)} (hcap : capAtMost11 G)
    (hα5 : ∀ S : Finset (Fin 25), IsIndep G S → S.card ≤ 5)
    {Q1 Q2 : Finset (Fin 25)} (hQ1clq : IsCliqueOn G Q1) (hQ1c : Q1.card = 5)
    (hQ2clq : IsCliqueOn G Q2) (hQ2c : Q2.card = 5) (hd12 : Disjoint Q1 Q2)
    {a b c d : Fin 25}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (nab : ¬ G.Adj a b) (nac : ¬ G.Adj a c) (nad : ¬ G.Adj a d)
    (nbc : ¬ G.Adj b c) (nbd : ¬ G.Adj b d) (ncd : ¬ G.Adj c d)
    (haQ1 : a ∉ Q1) (hbQ1 : b ∉ Q1) (hcQ1 : c ∉ Q1) (hdQ1 : d ∉ Q1)
    (haQ2 : a ∉ Q2) (hbQ2 : b ∉ Q2) (hcQ2 : c ∉ Q2) (hdQ2 : d ∉ Q2) :
    1 ≤ (Q1.filter (fun w => G.Adj a w)).card ∧ 1 ≤ (Q1.filter (fun w => G.Adj b w)).card
    ∧ 1 ≤ (Q1.filter (fun w => G.Adj c w)).card ∧ 1 ≤ (Q1.filter (fun w => G.Adj d w)).card
    ∧ 1 ≤ (Q2.filter (fun w => G.Adj a w)).card ∧ 1 ≤ (Q2.filter (fun w => G.Adj b w)).card
    ∧ 1 ≤ (Q2.filter (fun w => G.Adj c w)).card ∧ 1 ≤ (Q2.filter (fun w => G.Adj d w)).card
    ∧ (∃ w1 ∈ Q1, ∃ w2 ∈ Q2, G.Adj w1 w2) := by
  classical
  -- generic single-clique analysis: in-degrees ≤ 1, and |M| + Σ(in-deg) ≥ 5.
  have analyze : ∀ Q : Finset (Fin 25), IsCliqueOn G Q → Q.card = 5 →
      a ∉ Q → b ∉ Q → c ∉ Q → d ∉ Q →
      ((Q.filter (fun w => G.Adj a w)).card ≤ 1 ∧ (Q.filter (fun w => G.Adj b w)).card ≤ 1 ∧
        (Q.filter (fun w => G.Adj c w)).card ≤ 1 ∧ (Q.filter (fun w => G.Adj d w)).card ≤ 1) ∧
      5 ≤ (Q.filter (fun w => ¬ G.Adj a w ∧ ¬ G.Adj b w ∧ ¬ G.Adj c w ∧ ¬ G.Adj d w)).card
        + ((Q.filter (fun w => G.Adj a w)).card + (Q.filter (fun w => G.Adj b w)).card
          + (Q.filter (fun w => G.Adj c w)).card + (Q.filter (fun w => G.Adj d w)).card) := by
    intro Q hQclq hQc haQ hbQ hcQ hdQ
    have h1a := indeg_clique5_le_one G hcap hQclq hQc haQ
    have h1b := indeg_clique5_le_one G hcap hQclq hQc hbQ
    have h1c := indeg_clique5_le_one G hcap hQclq hQc hcQ
    have h1d := indeg_clique5_le_one G hcap hQclq hQc hdQ
    refine ⟨⟨h1a, h1b, h1c, h1d⟩, ?_⟩
    have hcov_le : (Q.filter (fun w => G.Adj a w ∨ G.Adj b w ∨ G.Adj c w ∨ G.Adj d w)).card
        ≤ (Q.filter (fun w => G.Adj a w)).card + (Q.filter (fun w => G.Adj b w)).card
          + (Q.filter (fun w => G.Adj c w)).card + (Q.filter (fun w => G.Adj d w)).card := by
      have hsub : Q.filter (fun w => G.Adj a w ∨ G.Adj b w ∨ G.Adj c w ∨ G.Adj d w)
          ⊆ Q.filter (fun w => G.Adj a w) ∪ Q.filter (fun w => G.Adj b w)
            ∪ Q.filter (fun w => G.Adj c w) ∪ Q.filter (fun w => G.Adj d w) := by
        intro w hw; rw [Finset.mem_filter] at hw
        rcases hw.2 with h | h | h | h
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨hw.1, h⟩)))
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨hw.1, h⟩)))
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw.1, h⟩))
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw.1, h⟩)
      refine le_trans (Finset.card_le_card hsub) ?_
      refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right ?_ _)
      exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    have hpart := Finset.filter_card_add_filter_neg_card_eq_card (s := Q)
      (p := fun w => G.Adj a w ∨ G.Adj b w ∨ G.Adj c w ∨ G.Adj d w)
    have hneg : Q.filter (fun w => ¬ (G.Adj a w ∨ G.Adj b w ∨ G.Adj c w ∨ G.Adj d w))
        = Q.filter (fun w => ¬ G.Adj a w ∧ ¬ G.Adj b w ∧ ¬ G.Adj c w ∧ ¬ G.Adj d w) := by
      apply Finset.filter_congr; intro w _; rw [not_or, not_or, not_or]
    rw [hneg, hQc] at hpart
    omega
  obtain ⟨⟨h1a1, h1b1, h1c1, h1d1⟩, hM1sum⟩ := analyze Q1 hQ1clq hQ1c haQ1 hbQ1 hcQ1 hdQ1
  obtain ⟨⟨h1a2, h1b2, h1c2, h1d2⟩, hM2sum⟩ := analyze Q2 hQ2clq hQ2c haQ2 hbQ2 hcQ2 hdQ2
  set M1 := Q1.filter (fun w => ¬ G.Adj a w ∧ ¬ G.Adj b w ∧ ¬ G.Adj c w ∧ ¬ G.Adj d w) with hM1def
  set M2 := Q2.filter (fun w => ¬ G.Adj a w ∧ ¬ G.Adj b w ∧ ¬ G.Adj c w ∧ ¬ G.Adj d w) with hM2def
  -- M1, M2 nonempty
  have hM1ne : M1.Nonempty := by rw [← Finset.card_pos]; omega
  have hM2ne : M2.Nonempty := by rw [← Finset.card_pos]; omega
  obtain ⟨w1, hw1⟩ := hM1ne
  obtain ⟨w2, hw2⟩ := hM2ne
  have hw1Q1 : w1 ∈ Q1 := (Finset.mem_filter.mp (hM1def ▸ hw1)).1
  have hw2Q2 : w2 ∈ Q2 := (Finset.mem_filter.mp (hM2def ▸ hw2)).1
  -- membership decoder
  have decM : ∀ {Q : Finset (Fin 25)} {w : Fin 25},
      w ∈ Q.filter (fun w => ¬ G.Adj a w ∧ ¬ G.Adj b w ∧ ¬ G.Adj c w ∧ ¬ G.Adj d w) →
      w ∈ Q ∧ ¬ G.Adj a w ∧ ¬ G.Adj b w ∧ ¬ G.Adj c w ∧ ¬ G.Adj d w := by
    intro Q w hw; exact ⟨(Finset.mem_filter.mp hw).1, (Finset.mem_filter.mp hw).2⟩
  -- missed pairs are adjacent (else independent 6-set)
  have hedge : ∀ x1 ∈ M1, ∀ x2 ∈ M2, G.Adj x1 x2 := by
    intro x1 hx1 x2 hx2
    obtain ⟨hx1Q1, na1, nb1, nc1, nd1⟩ := decM (hM1def ▸ hx1)
    obtain ⟨hx2Q2, na2, nb2, nc2, nd2⟩ := decM (hM2def ▸ hx2)
    by_contra hnadj
    have hax1 : a ≠ x1 := fun h => haQ1 (h ▸ hx1Q1)
    have hbx1 : b ≠ x1 := fun h => hbQ1 (h ▸ hx1Q1)
    have hcx1 : c ≠ x1 := fun h => hcQ1 (h ▸ hx1Q1)
    have hdx1 : d ≠ x1 := fun h => hdQ1 (h ▸ hx1Q1)
    have hax2 : a ≠ x2 := fun h => haQ2 (h ▸ hx2Q2)
    have hbx2 : b ≠ x2 := fun h => hbQ2 (h ▸ hx2Q2)
    have hcx2 : c ≠ x2 := fun h => hcQ2 (h ▸ hx2Q2)
    have hdx2 : d ≠ x2 := fun h => hdQ2 (h ▸ hx2Q2)
    have hx1x2 : x1 ≠ x2 := fun h => Finset.disjoint_left.mp hd12 hx1Q1 (h ▸ hx2Q2)
    exact no_indep_six hα5 hab hac had hax1 hax2 hbc hbd hbx1 hbx2 hcd hcx1 hcx2
      hdx1 hdx2 hx1x2 nab nac nad na1 na2 nbc nbd nb1 nb2 ncd nc1 nc2 nd1 nd2 hnadj
  -- |M1| ≤ 1: else two elements both adjacent to w2, giving w2 two Q1-neighbours.
  have hM1le : M1.card ≤ 1 := by
    by_contra hc
    push_neg at hc
    obtain ⟨x, hx, x', hx', hxx'⟩ := Finset.one_lt_card.mp hc
    have hxQ1 : x ∈ Q1 := (Finset.mem_filter.mp (hM1def ▸ hx)).1
    have hx'Q1 : x' ∈ Q1 := (Finset.mem_filter.mp (hM1def ▸ hx')).1
    have hxw2 : G.Adj w2 x := G.symm (hedge x hx w2 hw2)
    have hx'w2 : G.Adj w2 x' := G.symm (hedge x' hx' w2 hw2)
    have hw2nQ1 : w2 ∉ Q1 := Finset.disjoint_right.mp hd12 hw2Q2
    have h2 : 2 ≤ (Q1.filter (fun w => G.Adj w2 w)).card := by
      have hsub : ({x, x'} : Finset (Fin 25)) ⊆ Q1.filter (fun w => G.Adj w2 w) := by
        intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨hxQ1, hxw2⟩
        · exact Finset.mem_filter.mpr ⟨hx'Q1, hx'w2⟩
      have := Finset.card_le_card hsub
      rwa [Finset.card_pair hxx'] at this
    have := indeg_clique5_le_one G hcap hQ1clq hQ1c hw2nQ1
    omega
  have hM2le : M2.card ≤ 1 := by
    by_contra hc
    push_neg at hc
    obtain ⟨x, hx, x', hx', hxx'⟩ := Finset.one_lt_card.mp hc
    have hxQ2 : x ∈ Q2 := (Finset.mem_filter.mp (hM2def ▸ hx)).1
    have hx'Q2 : x' ∈ Q2 := (Finset.mem_filter.mp (hM2def ▸ hx')).1
    have hxw1 : G.Adj w1 x := hedge w1 hw1 x hx
    have hx'w1 : G.Adj w1 x' := hedge w1 hw1 x' hx'
    have hw1nQ2 : w1 ∉ Q2 := Finset.disjoint_left.mp hd12 hw1Q1
    have h2 : 2 ≤ (Q2.filter (fun w => G.Adj w1 w)).card := by
      have hsub : ({x, x'} : Finset (Fin 25)) ⊆ Q2.filter (fun w => G.Adj w1 w) := by
        intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨hxQ2, hxw1⟩
        · exact Finset.mem_filter.mpr ⟨hx'Q2, hx'w1⟩
      have := Finset.card_le_card hsub
      rwa [Finset.card_pair hxx'] at this
    have := indeg_clique5_le_one G hcap hQ2clq hQ2c hw1nQ2
    omega
  -- now |M1| = 1, |M2| = 1 forces all eight in-degrees to be exactly 1.
  have hM1eq : M1.card = 1 := by have := Finset.card_pos.mpr ⟨w1, hw1⟩; omega
  have hM2eq : M2.card = 1 := by have := Finset.card_pos.mpr ⟨w2, hw2⟩; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨w1, hw1Q1, w2, hw2Q2, hedge w1 hw1 w2 hw2⟩⟩ <;> omega

/-- **§5, every non-edge of `G[T]` is hit** (the informal (22)–(24) ρ-counting,
`h = 0`). If some non-edge `{i,j}` were unhit (`B∖(Z_i∪Z_j)` not a clique), a
weighted count forces `ρ ∈ {2,3,4}` impossible (via `r ≥ 4`) and `ρ = 5` to give
`r=10, D=0`, an independent 6-set. -/
theorem sec5_all_hit {G : SimpleGraph (Fin 25)} {T : Finset (Fin 25)} (ctx : MMCtx G T)
    (pf : PrimFacts) {Q1 Q2 : Finset (Fin 25)}
    (hQ1sub : Q1 ⊆ Finset.univ \ T) (hQ1c : Q1.card = 5) (hQ1clq : IsCliqueOn G Q1)
    (hQ2sub : Q2 ⊆ (Finset.univ \ T) \ Q1) (hQ2c : Q2.card = 5) (hQ2clq : IsCliqueOn G Q2)
    (hBfree : ∀ Q : Finset (Fin 25), Q ⊆ ((Finset.univ \ T) \ Q1) \ Q2 → Q.card = 5 →
      ¬ IsCliqueOn G Q)
    (hαB2 : ∀ S : Finset (Fin 25), S ⊆ ((Finset.univ \ T) \ Q1) \ Q2 → IsIndep G S → S.card ≤ 2)
    (heB25 : 25 ≤ edgeCountIn G (((Finset.univ \ T) \ Q1) \ Q2))
    (vt : Fin 5 ↪ Fin 25) (hvtim : Finset.univ.image vt = T) :
    ∀ i j : Fin 5, i ≠ j → ¬ G.Adj (vt i) (vt j) →
      IsCliqueOn G ((((Finset.univ \ T) \ Q1) \ Q2).filter
        (fun v => ¬ G.Adj (vt i) v ∧ ¬ G.Adj (vt j) v)) := by
  classical
  set H := Finset.univ \ T with hHdef
  set Bset := (H \ Q1) \ Q2 with hBdef
  -- basic geometry
  have hd12 : Disjoint Q1 Q2 := by
    rw [Finset.disjoint_left]; intro x hx hxQ2
    exact (Finset.mem_sdiff.mp (hQ2sub hxQ2)).2 hx
  have hBc : Bset.card = 10 := by
    have h1 := Finset.card_sdiff_of_subset hQ1sub
    have h2 := Finset.card_sdiff_of_subset hQ2sub
    have h3 : H.card = 20 := by
      rw [hHdef, Finset.card_sdiff_of_subset (Finset.subset_univ T), Finset.card_univ,
        Fintype.card_fin, ctx.hT]
    rw [hBdef]; omega
  have hQ1H : Q1 ⊆ H := hQ1sub
  have hQ2H : Q2 ⊆ H := hQ2sub.trans Finset.sdiff_subset
  have hBH : Bset ⊆ H := hBdef ▸ (Finset.sdiff_subset.trans Finset.sdiff_subset)
  have hvtinj : Function.Injective vt := vt.injective
  have hvtT : ∀ i, vt i ∈ T := fun i => hvtim ▸ Finset.mem_image_of_mem vt (Finset.mem_univ i)
  have hvtnH : ∀ i, vt i ∉ H := fun i h => (Finset.mem_sdiff.mp h).2 (hvtT i)
  have hvtnQ1 : ∀ i, vt i ∉ Q1 := fun i h => hvtnH i (hQ1H h)
  have hvtnQ2 : ∀ i, vt i ∉ Q2 := fun i h => hvtnH i (hQ2H h)
  have hvtnB : ∀ i, vt i ∉ Bset := fun i h => hvtnH i (hBH h)
  have hBnQ1 : ∀ v ∈ Bset, v ∉ Q1 := fun v hv =>
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hv).1).2
  have hBnQ2 : ∀ v ∈ Bset, v ∉ Q2 := fun v hv => (Finset.mem_sdiff.mp hv).2
  -- H = Q1 ⊔ Q2 ⊔ B, and the two disjoint splits of e(H)
  have hunion12 : Q2 ∪ Bset = H \ Q1 := by
    rw [hBdef, Finset.union_comm]; exact Finset.sdiff_union_of_subset hQ2sub
  have heQ1 : edgeCountIn G Q1 = 10 := by
    rw [edgeCountIn_eq_choose_of_clique G hQ1clq, hQ1c]; rfl
  have heQ2 : edgeCountIn G Q2 = 10 := by
    rw [edgeCountIn_eq_choose_of_clique G hQ2clq, hQ2c]; rfl
  set s := edgeCountIn G T with hsdef
  set D := ∑ i : Fin 5, (Bset.filter (fun v => G.Adj (vt i) v)).card with hDdef
  set y := ∑ i : Fin 5, ((Q1.filter (fun v => G.Adj (vt i) v)).card
    + (Q2.filter (fun v => G.Adj (vt i) v)).card) with hydef
  set cA := ∑ w ∈ (H \ Q1), (Q1.filter (fun v => G.Adj w v)).card with hcAdef
  set cB := ∑ w ∈ Bset, (Q2.filter (fun v => G.Adj w v)).card with hcBdef
  -- crossCount = y + D
  have hcross_eq : crossCount G T = y + D := by
    have hreindex : crossCount G T
        = ∑ i : Fin 5, (H.filter (fun v => G.Adj (vt i) v)).card := by
      unfold crossCount
      rw [← hHdef, ← hvtim, Finset.sum_image (fun a _ b _ h => hvtinj h)]
    have hHsplit_i : ∀ i : Fin 5, (H.filter (fun v => G.Adj (vt i) v)).card
        = (Q1.filter (fun v => G.Adj (vt i) v)).card + (Q2.filter (fun v => G.Adj (vt i) v)).card
          + (Bset.filter (fun v => G.Adj (vt i) v)).card := by
      intro i
      have hHU : H = Q1 ∪ (Q2 ∪ Bset) := by
        rw [hunion12, Finset.union_comm]; exact (Finset.sdiff_union_of_subset hQ1H).symm
      have hd1 : Disjoint Q1 (Q2 ∪ Bset) := by
        rw [Finset.disjoint_union_right]
        exact ⟨hd12, by rw [Finset.disjoint_left]; intro x hx hxB; exact hBnQ1 x hxB hx⟩
      have hd2 : Disjoint Q2 Bset := by
        rw [Finset.disjoint_left]; intro x hx hxB; exact hBnQ2 x hxB hx
      rw [hHU, deg_split hd1 (vt i), deg_split hd2 (vt i)]; ring
    rw [hreindex, hydef, hDdef, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => hHsplit_i i)
  -- e(H) = 20 + e(B) + cA + cB
  have hH_eq : edgeCountIn G H = 20 + edgeCountIn G Bset + (cA + cB) := by
    have hsplit1 : edgeCountIn G H = edgeCountIn G Q1 + edgeCountIn G (H \ Q1) + cA := by
      have hd : Disjoint Q1 (H \ Q1) := Finset.disjoint_sdiff
      have hu : Q1 ∪ (H \ Q1) = H := by
        rw [Finset.union_comm]; exact Finset.sdiff_union_of_subset hQ1H
      have h := edgeCountIn_union_disjoint_eq G hd; rw [hu] at h; rw [h, hcAdef]
    have hsplit2 : edgeCountIn G (H \ Q1) = edgeCountIn G Q2 + edgeCountIn G Bset + cB := by
      have hd : Disjoint Q2 Bset := by
        rw [Finset.disjoint_left]; intro x hx hxB; exact hBnQ2 x hxB hx
      have h := edgeCountIn_union_disjoint_eq G hd; rw [hunion12] at h; rw [h, hcBdef]
    rw [hsplit1, hsplit2, heQ1, heQ2]; ring
  -- budget: cA + cB + y + D + s ≤ 15
  have hbudget : cA + cB + y + D + s ≤ 15 := by
    have hsplit := edgeCountIn_univ_split G T
    rw [← hHdef, ← hsdef, hcross_eq, hH_eq] at hsplit
    have h60 := ctx.he60
    omega
  -- res is symmetric in i,j
  have hres_symm : ∀ i j : Fin 5, Bset.filter (fun v => ¬ G.Adj (vt i) v ∧ ¬ G.Adj (vt j) v)
      = Bset.filter (fun v => ¬ G.Adj (vt j) v ∧ ¬ G.Adj (vt i) v) := by
    intro i j; apply Finset.filter_congr; intro v _; rw [and_comm]
  -- unhit structure packaged
  have unhit_facts : ∀ i j : Fin 5, i ≠ j → ¬ G.Adj (vt i) (vt j) →
      ¬ IsCliqueOn G (Bset.filter (fun v => ¬ G.Adj (vt i) v ∧ ¬ G.Adj (vt j) v)) →
      (1 ≤ (Q1.filter (fun v => G.Adj (vt i) v)).card
        ∧ 1 ≤ (Q2.filter (fun v => G.Adj (vt i) v)).card
        ∧ 1 ≤ (Q1.filter (fun v => G.Adj (vt j) v)).card
        ∧ 1 ≤ (Q2.filter (fun v => G.Adj (vt j) v)).card)
      ∧ (∃ u ∈ Bset, ∃ v ∈ Bset, u ≠ v
        ∧ 1 ≤ (Q1.filter (fun w => G.Adj u w)).card ∧ 1 ≤ (Q2.filter (fun w => G.Adj u w)).card
        ∧ 1 ≤ (Q1.filter (fun w => G.Adj v w)).card ∧ 1 ≤ (Q2.filter (fun w => G.Adj v w)).card
        ∧ ∃ w2 ∈ Q2, 1 ≤ (Q1.filter (fun w => G.Adj w2 w)).card) := by
    intro i j hij hnadj hnclq
    simp only [IsCliqueOn] at hnclq
    push_neg at hnclq
    obtain ⟨u, hu, v, hv, huv, hnuv⟩ := hnclq
    obtain ⟨huB, hnui, hnuj⟩ := Finset.mem_filter.mp hu
    obtain ⟨hvB, hnvi, hnvj⟩ := Finset.mem_filter.mp hv
    have hijv : vt i ≠ vt j := fun h => hij (hvtinj h)
    have hiu : vt i ≠ u := by rintro rfl; exact hvtnB i huB
    have hiv : vt i ≠ v := by rintro rfl; exact hvtnB i hvB
    have hju : vt j ≠ u := by rintro rfl; exact hvtnB j huB
    have hjv : vt j ≠ v := by rintro rfl; exact hvtnB j hvB
    have hcore := sec5_unhit_core ctx.hcap ctx.hα5 hQ1clq hQ1c hQ2clq hQ2c hd12
      hijv hiu hiv hju hjv huv hnadj hnui hnvi hnuj hnvj hnuv
      (hvtnQ1 i) (hvtnQ1 j) (hBnQ1 u huB) (hBnQ1 v hvB)
      (hvtnQ2 i) (hvtnQ2 j) (hBnQ2 u huB) (hBnQ2 v hvB)
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, w1, hw1Q1, w2, hw2Q2, hw12⟩ := hcore
    exact ⟨⟨c1, c5, c2, c6⟩, u, huB, v, hvB, huv, c3, c7, c4, c8, w2, hw2Q2,
      Finset.card_pos.mpr ⟨w1, Finset.mem_filter.mpr ⟨hw1Q1, G.symm hw12⟩⟩⟩
  -- assume an unhit edge exists (else done)
  by_contra hcon
  push_neg at hcon
  obtain ⟨i0, j0, hij0, hnadj0, hnclq0⟩ := hcon
  -- c ≥ 5 from this one unhit edge
  have hc5 : 5 ≤ cA + cB := by
    obtain ⟨_, u, huB, v, hvB, huv, hu1, hu2, hv1, hv2, w2, hw2Q2, hw2Q1⟩ :=
      unhit_facts i0 j0 hij0 hnadj0 hnclq0
    have huvB : ({u, v} : Finset (Fin 25)) ⊆ Bset := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl; exacts [huB, hvB]
    have huw2 : u ≠ w2 := fun h => hBnQ2 u huB (h ▸ hw2Q2)
    have hvw2 : v ≠ w2 := fun h => hBnQ2 v hvB (h ▸ hw2Q2)
    have hset3 : ({u, v, w2} : Finset (Fin 25)) ⊆ H \ Q1 := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_sdiff]
      rcases hx with rfl | rfl | rfl
      · exact ⟨hBH huB, hBnQ1 _ huB⟩
      · exact ⟨hBH hvB, hBnQ1 _ hvB⟩
      · exact ⟨hQ2H hw2Q2, Finset.disjoint_right.mp hd12 hw2Q2⟩
    have hcB2 : 2 ≤ cB := by
      have hle : (∑ w ∈ ({u, v} : Finset (Fin 25)), (Q2.filter (fun w' => G.Adj w w')).card) ≤ cB :=
        Finset.sum_le_sum_of_subset_of_nonneg huvB (fun _ _ _ => Nat.zero_le _)
      rw [Finset.sum_pair huv] at hle; omega
    have hcA3 : 3 ≤ cA := by
      have hle : (∑ w ∈ ({u, v, w2} : Finset (Fin 25)), (Q1.filter (fun w' => G.Adj w w')).card)
          ≤ cA := Finset.sum_le_sum_of_subset_of_nonneg hset3 (fun _ _ _ => Nat.zero_le _)
      rw [show ({u, v, w2} : Finset (Fin 25)) = insert u {v, w2} from rfl,
        Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨huv, huw2⟩),
        Finset.sum_pair hvw2] at hle
      omega
    omega
  -- INC = incident vertices; hy2rho : 2ρ ≤ y
  set INC := Finset.univ.filter (fun i : Fin 5 => ∃ j, i ≠ j ∧ ¬ G.Adj (vt i) (vt j)
    ∧ ¬ IsCliqueOn G (Bset.filter (fun v => ¬ G.Adj (vt i) v ∧ ¬ G.Adj (vt j) v))) with hINCdef
  have hINC2 : ∀ i ∈ INC, 2 ≤ (Q1.filter (fun v => G.Adj (vt i) v)).card
      + (Q2.filter (fun v => G.Adj (vt i) v)).card := by
    intro i hi
    rw [hINCdef, Finset.mem_filter] at hi
    obtain ⟨-, j, hij, hnadj, hnclq⟩ := hi
    obtain ⟨⟨h1, h2, _, _⟩, _⟩ := unhit_facts i j hij hnadj hnclq
    omega
  have hy2rho : 2 * INC.card ≤ y := by
    have hsub : INC ⊆ (Finset.univ : Finset (Fin 5)) := Finset.filter_subset _ _
    calc 2 * INC.card = ∑ _i ∈ INC, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ i ∈ INC, ((Q1.filter (fun v => G.Adj (vt i) v)).card
          + (Q2.filter (fun v => G.Adj (vt i) v)).card) := Finset.sum_le_sum (fun i hi => hINC2 i hi)
      _ ≤ y := by
          rw [hydef]; exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  -- the ordered pairs
  set NEpairs := Finset.univ.filter (fun p : Fin 5 × Fin 5 =>
    p.1 ≠ p.2 ∧ ¬ G.Adj (vt p.1) (vt p.2)) with hNEdef
  set UHpairs := NEpairs.filter (fun p =>
    ¬ IsCliqueOn G (Bset.filter (fun v => ¬ G.Adj (vt p.1) v ∧ ¬ G.Adj (vt p.2) v))) with hUHdef
  set Hitpairs := NEpairs.filter (fun p =>
    IsCliqueOn G (Bset.filter (fun v => ¬ G.Adj (vt p.1) v ∧ ¬ G.Adj (vt p.2) v))) with hHitdef
  have hHitUH : Hitpairs.card + UHpairs.card = NEpairs.card := by
    rw [hHitdef, hUHdef]
    exact Finset.card_filter_add_card_filter_not (s := NEpairs)
      (p := fun p => IsCliqueOn G (Bset.filter (fun v => ¬ G.Adj (vt p.1) v ∧ ¬ G.Adj (vt p.2) v)))
  have hUH2 : 2 ≤ UHpairs.card := by
    have hmem1 : (i0, j0) ∈ UHpairs := by
      rw [hUHdef, Finset.mem_filter, hNEdef, Finset.mem_filter]
      exact ⟨⟨Finset.mem_univ _, hij0, hnadj0⟩, hnclq0⟩
    have hmem2 : (j0, i0) ∈ UHpairs := by
      rw [hUHdef]
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · rw [hNEdef]
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, Ne.symm hij0, fun h => hnadj0 (G.symm h)⟩
      · show ¬ IsCliqueOn G (Bset.filter (fun v => ¬ G.Adj (vt j0) v ∧ ¬ G.Adj (vt i0) v))
        rw [hres_symm j0 i0]; exact hnclq0
    have hsub : ({(i0, j0), (j0, i0)} : Finset (Fin 5 × Fin 5)) ⊆ UHpairs := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl; exacts [hmem1, hmem2]
    have hne : ((i0, j0) : Fin 5 × Fin 5) ≠ (j0, i0) := by
      simp only [ne_eq, Prod.mk.injEq, not_and]; intro h; exact absurd h hij0
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair hne] at this
  set INCoff := (INC ×ˢ INC).filter (fun p => ¬ p.1 = p.2) with hINCoffdef
  have hUHoc : UHpairs.card ≤ INCoff.card := by
    apply Finset.card_le_card
    intro p hp
    rw [hUHdef, Finset.mem_filter, hNEdef, Finset.mem_filter] at hp
    obtain ⟨⟨_, hp12, hpadj⟩, hpclq⟩ := hp
    rw [hINCoffdef, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨?_, ?_⟩, hp12⟩
    · rw [hINCdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, p.2, hp12, hpadj, hpclq⟩
    · rw [hINCdef, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, p.1, Ne.symm hp12, fun h => hpadj (G.symm h), ?_⟩
      rw [hres_symm p.2 p.1]; exact hpclq
  have hoc : INCoff.card + INC.card = INC.card * INC.card := by
    have hdiag : ((INC ×ˢ INC).filter (fun p => p.1 = p.2)).card = INC.card := by
      refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
      · intro p hp; exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
      · intro p hp q hq h
        rw [Finset.mem_filter] at hp hq
        exact Prod.ext h (by rw [← hp.2, ← hq.2]; exact h)
      · intro i hi
        exact ⟨(i, i), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi, hi⟩, rfl⟩, rfl⟩
    have hsplit := Finset.card_filter_add_card_filter_not (s := INC ×ˢ INC)
      (p := fun p => p.1 = p.2)
    rw [Finset.card_product, hdiag] at hsplit
    rw [hINCoffdef]; omega
  -- handshake: 6·|Hitpairs| ≤ 10·D
  have hhand : 6 * Hitpairs.card ≤ 10 * D := by
    have hge : 6 * Hitpairs.card ≤ ∑ p ∈ Hitpairs,
        ((Bset.filter (fun v => G.Adj (vt p.1) v)).card
          + (Bset.filter (fun v => G.Adj (vt p.2) v)).card) := by
      rw [show 6 * Hitpairs.card = ∑ _p ∈ Hitpairs, 6 from by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]]
      apply Finset.sum_le_sum
      intro p hp
      rw [hHitdef, Finset.mem_filter] at hp
      have hpclq := hp.2
      have hhit := sec5_hit_union_ge (t := vt p.1) (t' := vt p.2) hBfree hBc hpclq
      have hle : (Bset.filter (fun v => G.Adj (vt p.1) v ∨ G.Adj (vt p.2) v)).card
          ≤ (Bset.filter (fun v => G.Adj (vt p.1) v)).card
            + (Bset.filter (fun v => G.Adj (vt p.2) v)).card := by
        rw [Finset.filter_or]; exact Finset.card_union_le _ _
      omega
    have hle10 : (∑ p ∈ Hitpairs, ((Bset.filter (fun v => G.Adj (vt p.1) v)).card
        + (Bset.filter (fun v => G.Adj (vt p.2) v)).card)) ≤ 10 * D := by
      have hsub : Hitpairs ⊆ (Finset.univ : Finset (Fin 5 × Fin 5)) := Finset.subset_univ _
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)) ?_
      rw [Finset.sum_add_distrib]
      have h1 : (∑ p : Fin 5 × Fin 5, (Bset.filter (fun v => G.Adj (vt p.1) v)).card) = 5 * D := by
        rw [Fintype.sum_prod_type]
        show (∑ a : Fin 5, ∑ _b : Fin 5, (Bset.filter (fun v => G.Adj (vt a) v)).card) = 5 * D
        rw [hDdef, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro a _
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      have h2 : (∑ p : Fin 5 × Fin 5, (Bset.filter (fun v => G.Adj (vt p.2) v)).card) = 5 * D := by
        rw [Fintype.sum_prod_type]
        show (∑ _a : Fin 5, ∑ b : Fin 5, (Bset.filter (fun v => G.Adj (vt b) v)).card) = 5 * D
        rw [Finset.sum_congr rfl (fun a _ => (hDdef.symm : (∑ b : Fin 5,
          (Bset.filter (fun v => G.Adj (vt b) v)).card) = D)), Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      rw [h1, h2]; omega
    omega
  -- NEpairs count: |NEpairs| + 2s = 20
  have hNEcount : NEpairs.card + 2 * s = 20 := by
    have hoff20 : (Finset.univ.filter (fun p : Fin 5 × Fin 5 => p.1 ≠ p.2)).card = 20 := by decide
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter (fun p : Fin 5 × Fin 5 => p.1 ≠ p.2))
      (p := fun p => G.Adj (vt p.1) (vt p.2))
    rw [hoff20] at hsplit
    have hNEeq : (Finset.univ.filter (fun p : Fin 5 × Fin 5 => p.1 ≠ p.2)).filter
        (fun p => ¬ G.Adj (vt p.1) (vt p.2)) = NEpairs := by
      rw [hNEdef, Finset.filter_filter]
    have hAeq : ((Finset.univ.filter (fun p : Fin 5 × Fin 5 => p.1 ≠ p.2)).filter
        (fun p => G.Adj (vt p.1) (vt p.2))).card = 2 * s := by
      have hall : (Finset.univ.filter (fun p : Fin 5 × Fin 5 => p.1 ≠ p.2)).filter
          (fun p => G.Adj (vt p.1) (vt p.2))
          = Finset.univ.filter (fun p : Fin 5 × Fin 5 => G.Adj (vt p.1) (vt p.2)) := by
        rw [Finset.filter_filter]
        apply Finset.filter_congr
        intro p _
        exact ⟨fun h => h.2, fun h => ⟨fun he => G.ne_of_adj h (by rw [he]), h⟩⟩
      rw [hall, Finset.card_filter, Fintype.sum_prod_type]
      show (∑ a : Fin 5, ∑ b : Fin 5, (if G.Adj (vt a) (vt b) then 1 else 0)) = 2 * s
      have h := edgeCount_five (G := G) hvtinj
      rw [hvtim] at h
      rw [← h, hsdef]
    rw [hNEeq] at hsplit; rw [hAeq] at hsplit; omega
  -- all non-edges of T from s = 0
  have hallnadj : s = 0 → ∀ i j : Fin 5, i ≠ j → ¬ G.Adj (vt i) (vt j) := by
    intro hs0
    have hexp := s_expand (G := G) hvtinj
    rw [hvtim, ← hsdef, hs0] at hexp
    have b01 : ¬ G.Adj (vt 0) (vt 1) := fun h => by simp only [if_pos h] at hexp; omega
    have b02 : ¬ G.Adj (vt 0) (vt 2) := fun h => by simp only [if_pos h] at hexp; omega
    have b03 : ¬ G.Adj (vt 0) (vt 3) := fun h => by simp only [if_pos h] at hexp; omega
    have b04 : ¬ G.Adj (vt 0) (vt 4) := fun h => by simp only [if_pos h] at hexp; omega
    have b12 : ¬ G.Adj (vt 1) (vt 2) := fun h => by simp only [if_pos h] at hexp; omega
    have b13 : ¬ G.Adj (vt 1) (vt 3) := fun h => by simp only [if_pos h] at hexp; omega
    have b14 : ¬ G.Adj (vt 1) (vt 4) := fun h => by simp only [if_pos h] at hexp; omega
    have b23 : ¬ G.Adj (vt 2) (vt 3) := fun h => by simp only [if_pos h] at hexp; omega
    have b24 : ¬ G.Adj (vt 2) (vt 4) := fun h => by simp only [if_pos h] at hexp; omega
    have b34 : ¬ G.Adj (vt 3) (vt 4) := fun h => by simp only [if_pos h] at hexp; omega
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | assumption
        | (intro h; exact b01 (G.symm h)) | (intro h; exact b02 (G.symm h))
        | (intro h; exact b03 (G.symm h)) | (intro h; exact b04 (G.symm h))
        | (intro h; exact b12 (G.symm h)) | (intro h; exact b13 (G.symm h))
        | (intro h; exact b14 (G.symm h)) | (intro h; exact b23 (G.symm h))
        | (intro h; exact b24 (G.symm h)) | (intro h; exact b34 (G.symm h))
  have hs6 : s ≤ 6 := by rw [hsdef]; exact ctx.hsT
  have hρ5 : INC.card ≤ 5 := by
    have h := Finset.card_le_card (Finset.subset_univ INC)
    simpa using h
  -- final arithmetic on ρ = |INC|
  set ρ := INC.card with hρeq
  clear_value ρ
  interval_cases ρ
  · omega
  · omega
  · omega
  · omega
  · omega
  · -- ρ = 5: D = 0, s = 0 ⇒ independent 6-set
    have hD0 : D = 0 := by omega
    have hs0 : s = 0 := by omega
    have hdBi : ∀ i : Fin 5, (Bset.filter (fun v => G.Adj (vt i) v)).card = 0 := by
      have hz := Finset.sum_eq_zero_iff.mp (show (∑ i : Fin 5,
        (Bset.filter (fun v => G.Adj (vt i) v)).card) = 0 from hDdef ▸ hD0)
      exact fun i => hz i (Finset.mem_univ i)
    have hnbB : ∀ i : Fin 5, ∀ b ∈ Bset, ¬ G.Adj (vt i) b := by
      intro i b hb hadj
      have : b ∈ Bset.filter (fun v => G.Adj (vt i) v) := Finset.mem_filter.mpr ⟨hb, hadj⟩
      rw [Finset.card_eq_zero.mp (hdBi i)] at this; exact Finset.notMem_empty b this
    have hna := hallnadj hs0
    have hvtd : ∀ i j : Fin 5, i ≠ j → vt i ≠ vt j := fun i j hij h => hij (hvtinj h)
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < Bset.card by rw [hBc]; norm_num)
    have hbne : ∀ i : Fin 5, vt i ≠ b := fun i h => hvtnB i (h ▸ hb)
    exact no_indep_six ctx.hα5
      (hvtd 0 1 (by decide)) (hvtd 0 2 (by decide)) (hvtd 0 3 (by decide)) (hvtd 0 4 (by decide))
      (hbne 0) (hvtd 1 2 (by decide)) (hvtd 1 3 (by decide)) (hvtd 1 4 (by decide)) (hbne 1)
      (hvtd 2 3 (by decide)) (hvtd 2 4 (by decide)) (hbne 2)
      (hvtd 3 4 (by decide)) (hbne 3) (hbne 4)
      (hna 0 1 (by decide)) (hna 0 2 (by decide)) (hna 0 3 (by decide)) (hna 0 4 (by decide))
      (hnbB 0 b hb) (hna 1 2 (by decide)) (hna 1 3 (by decide)) (hna 1 4 (by decide))
      (hnbB 1 b hb) (hna 2 3 (by decide)) (hna 2 4 (by decide)) (hnbB 2 b hb)
      (hna 3 4 (by decide)) (hnbB 3 b hb) (hnbB 4 b hb)


/-! ## §5 main assembly -/

theorem section5_two {G : SimpleGraph (Fin 25)} {T : Finset (Fin 25)} (ctx : MMCtx G T)
    (pf : PrimFacts) {Q1 Q2 : Finset (Fin 25)} (hQ1sub : Q1 ⊆ Finset.univ \ T) (hQ1c : Q1.card = 5)
    (hQ1clq : IsCliqueOn G Q1) (hQ2sub : Q2 ⊆ (Finset.univ \ T) \ Q1) (hQ2c : Q2.card = 5)
    (hQ2clq : IsCliqueOn G Q2)
    (hBfree : ∀ Q : Finset (Fin 25), Q ⊆ ((Finset.univ \ T) \ Q1) \ Q2 → Q.card = 5 →
      ¬ IsCliqueOn G Q) : False := by
  classical
  set Bset := ((Finset.univ \ T) \ Q1) \ Q2 with hBdef
  have hd12 : Disjoint Q1 Q2 := by
    rw [Finset.disjoint_left]; intro x hx hxQ2
    exact (Finset.mem_sdiff.mp (hQ2sub hxQ2)).2 hx
  have hBc : Bset.card = 10 := by
    have h1 := Finset.card_sdiff_of_subset hQ1sub
    have h2 := Finset.card_sdiff_of_subset hQ2sub
    have h3 := card_H ctx
    rw [hBdef]; omega
  have hBsubH : Bset ⊆ Finset.univ \ T := hBdef ▸ (Finset.sdiff_subset.trans Finset.sdiff_subset)
  -- α(B) ≤ 2 (peel k = 2)
  have hαB2 : ∀ S : Finset (Fin 25), S ⊆ Bset → IsIndep G S → S.card ≤ 2 := by
    intro S hSsub hSindep
    by_contra hc
    push_neg at hc
    obtain ⟨S3, hS3sub, hS3card⟩ := Finset.exists_subset_card_eq (show 3 ≤ S.card by omega)
    refine peel_alpha_bound ctx [Q1, Q2] ?_ ?_ ?_
      (fun a ha b hb hab => hSindep a (hS3sub ha) b (hS3sub hb) hab)
      ((hS3sub.trans hSsub).trans hBsubH) ?_ (by simp [hS3card])
    · intro Q hQ; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hQ
      rcases hQ with rfl | rfl
      · exact ⟨hQ1clq, hQ1c⟩
      · exact ⟨hQ2clq, hQ2c⟩
    · refine List.Pairwise.cons ?_ (by simp)
      intro Q hQ; simp only [List.mem_singleton] at hQ; subst hQ; exact hd12
    · intro Q hQ; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hQ
      rcases hQ with rfl | rfl
      · exact hQ1sub
      · exact hQ2sub.trans Finset.sdiff_subset
    · intro Q hQ; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hQ
      have hxB : ∀ x ∈ S3, x ∈ Bset := fun x hx => (hS3sub.trans hSsub) hx
      rcases hQ with rfl | rfl
      · rw [Finset.disjoint_left]; intro x hx hxQ1
        exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (hxB x hx)).1).2 hxQ1
      · rw [Finset.disjoint_left]; intro x hx hxQ2
        exact (Finset.mem_sdiff.mp (hxB x hx)).2 hxQ2
  have heB25 : 25 ≤ edgeCountIn G Bset :=
    edge_B_ge_25 ctx pf hQ1sub hQ1c hQ1clq hQ2sub hQ2c hQ2clq hBfree
  -- budget: D ≤ 15 − s
  have hDle : (∑ t ∈ T, (Bset.filter (fun v => G.Adj t v)).card) ≤ 15 - edgeCountIn G T :=
    sec5_D_le ctx.he60 hQ1sub hQ2sub hQ1clq hQ1c hQ2clq hQ2c heB25
  -- vertex extraction
  obtain ⟨vt, hvtim⟩ := exists_embedding_image_eq T ctx.hT
  have hvtinj : Function.Injective vt := vt.injective
  have hvtT : ∀ i, vt i ∈ T := fun i => hvtim ▸ Finset.mem_image_of_mem vt (Finset.mem_univ i)
  -- ∑ dd over Fin 5 equals the T-sum, so ≤ 15 − s
  have hDimg : (∑ t ∈ T, (Bset.filter (fun v => G.Adj t v)).card)
      = ∑ i : Fin 5, (Bset.filter (fun v => G.Adj (vt i) v)).card := by
    rw [← hvtim, Finset.sum_image (fun a _ b _ h => hvtinj h)]
  have hDval : (∑ i : Fin 5, (Bset.filter (fun v => G.Adj (vt i) v)).card)
      ≤ 15 - edgeCountIn G T := hDimg ▸ hDle
  have hDexp : (∑ i : Fin 5, (Bset.filter (fun v => G.Adj (vt i) v)).card)
      = (Bset.filter (fun v => G.Adj (vt 0) v)).card + (Bset.filter (fun v => G.Adj (vt 1) v)).card
      + (Bset.filter (fun v => G.Adj (vt 2) v)).card + (Bset.filter (fun v => G.Adj (vt 3) v)).card
      + (Bset.filter (fun v => G.Adj (vt 4) v)).card := by rw [Fin.sum_univ_five]
  -- s in terms of the 10 pairwise adjacency indicators
  have hs_eq : edgeCountIn G T
      = (if G.Adj (vt 0) (vt 1) then 1 else 0) + (if G.Adj (vt 0) (vt 2) then 1 else 0)
      + (if G.Adj (vt 0) (vt 3) then 1 else 0) + (if G.Adj (vt 0) (vt 4) then 1 else 0)
      + (if G.Adj (vt 1) (vt 2) then 1 else 0) + (if G.Adj (vt 1) (vt 3) then 1 else 0)
      + (if G.Adj (vt 1) (vt 4) then 1 else 0) + (if G.Adj (vt 2) (vt 3) then 1 else 0)
      + (if G.Adj (vt 2) (vt 4) then 1 else 0) + (if G.Adj (vt 3) (vt 4) then 1 else 0) := by
    rw [← hvtim]; exact s_expand hvtinj
  have hbridge : (decide (G.Adj (vt 0) (vt 1))).toNat + (decide (G.Adj (vt 0) (vt 2))).toNat
      + (decide (G.Adj (vt 0) (vt 3))).toNat + (decide (G.Adj (vt 0) (vt 4))).toNat
      + (decide (G.Adj (vt 1) (vt 2))).toNat + (decide (G.Adj (vt 1) (vt 3))).toNat
      + (decide (G.Adj (vt 1) (vt 4))).toNat + (decide (G.Adj (vt 2) (vt 3))).toNat
      + (decide (G.Adj (vt 2) (vt 4))).toNat + (decide (G.Adj (vt 3) (vt 4))).toNat
      = edgeCountIn G T := by
    rw [hs_eq]; simp only [toNat_decide']
  -- every non-edge is hit (ρ-counting, informal (22)–(24))
  have all_hit : ∀ i j : Fin 5, i ≠ j → ¬ G.Adj (vt i) (vt j) →
      IsCliqueOn G (Bset.filter (fun v => ¬ G.Adj (vt i) v ∧ ¬ G.Adj (vt j) v)) :=
    sec5_all_hit ctx pf hQ1sub hQ1c hQ1clq hQ2sub hQ2c hQ2clq hBfree hαB2 heB25 vt hvtim
  -- hit ⇒ d_i + d_j ≥ 6
  have hdsum : ∀ i j : Fin 5, i ≠ j → ¬ G.Adj (vt i) (vt j) →
      6 ≤ (Bset.filter (fun v => G.Adj (vt i) v)).card
        + (Bset.filter (fun v => G.Adj (vt j) v)).card := by
    intro i j hij hnadj
    have hhit := sec5_hit_union_ge hBfree hBc (all_hit i j hij hnadj)
    have hUle : (Bset.filter (fun v => G.Adj (vt i) v ∨ G.Adj (vt j) v)).card
        ≤ (Bset.filter (fun v => G.Adj (vt i) v)).card
          + (Bset.filter (fun v => G.Adj (vt j) v)).card := by
      rw [Finset.filter_or]; exact Finset.card_union_le _ _
    omega
  have hunioncard : ∀ i j : Fin 5, i ≠ j → ¬ G.Adj (vt i) (vt j) →
      6 ≤ (Bset.filter (fun v => G.Adj (vt i) v ∨ G.Adj (vt j) v)).card :=
    fun i j hij hn => sec5_hit_union_ge hBfree hBc (all_hit i j hij hn)
  have hvtnB : ∀ i : Fin 5, vt i ∉ Bset :=
    fun i h => (Finset.mem_sdiff.mp (hBsubH h)).2 (hvtT i)
  -- collapse: a non-edge {i,j} with d_j = 0 gives `B + t_i` an 11-vtx α≤2 graph
  have collapse_of_zero : ∀ i j : Fin 5, i ≠ j → ¬ G.Adj (vt i) (vt j) →
      (Bset.filter (fun v => G.Adj (vt j) v)).card = 0 → False := by
    intro i j hij hnadj hdj0
    have hZj0 : ∀ v ∈ Bset, ¬ G.Adj (vt j) v := by
      intro v hv hadj
      have hmem : v ∈ Bset.filter (fun v => G.Adj (vt j) v) := Finset.mem_filter.mpr ⟨hv, hadj⟩
      rw [Finset.card_eq_zero] at hdj0
      rw [hdj0] at hmem; simp at hmem
    have hclq := all_hit i j hij hnadj
    have hfeq : Bset.filter (fun v => ¬ G.Adj (vt i) v ∧ ¬ G.Adj (vt j) v)
        = Bset.filter (fun v => ¬ G.Adj (vt i) v) := by
      apply Finset.filter_congr
      intro v hv
      simp only [and_iff_left_iff_imp]
      intro _; exact hZj0 v hv
    rw [hfeq] at hclq
    exact sec5_Bt_clique_false pf ctx.hcap hBc hαB2 (hvtnB i) hclq
  -- two disjoint non-edges ⇒ D ≥ 12
  have close2 : ∀ i j k l : Fin 5, (i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l) →
      ¬ G.Adj (vt i) (vt j) → ¬ G.Adj (vt k) (vt l) →
      12 ≤ (∑ x : Fin 5, (Bset.filter (fun v => G.Adj (vt x) v)).card) := by
    rintro i j k l ⟨hij, hik, hil, hjk, hjl, hkl⟩ hnij hnkl
    have h1 := hdsum i j hij hnij
    have h2 := hdsum k l hkl hnkl
    have hsub : ({i, j, k, l} : Finset (Fin 5)) ⊆ Finset.univ := Finset.subset_univ _
    have hle : ∑ x ∈ ({i, j, k, l} : Finset (Fin 5)), (Bset.filter (fun v => G.Adj (vt x) v)).card
        ≤ ∑ x : Fin 5, (Bset.filter (fun v => G.Adj (vt x) v)).card :=
      Finset.sum_le_sum_of_subset hsub
    have hsum4 : ∑ x ∈ ({i, j, k, l} : Finset (Fin 5)), (Bset.filter (fun v => G.Adj (vt x) v)).card
        = (Bset.filter (fun v => G.Adj (vt i) v)).card + (Bset.filter (fun v => G.Adj (vt j) v)).card
        + (Bset.filter (fun v => G.Adj (vt k) v)).card
        + (Bset.filter (fun v => G.Adj (vt l) v)).card := by
      rw [Finset.sum_insert (by simp [hij, hik, hil]),
          Finset.sum_insert (by simp [hjk, hjl]),
          Finset.sum_insert (by simp [hkl]), Finset.sum_singleton]
      ring
    omega
  -- twoDisjoint packaging for s ≤ 5
  have disjClose : edgeCountIn G T ≤ 5 →
      (∑ i : Fin 5, (Bset.filter (fun v => G.Adj (vt i) v)).card) ≤ 11 → False := by
    intro hs5 hD11
    have h5 := hbridge ▸ hs5
    have hf := twoDisjoint _ _ _ _ _ _ _ _ _ _ h5
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, or_assoc, and_assoc] at hf
    rcases hf with ⟨a, b⟩|⟨a, b⟩|⟨a, b⟩|⟨a, b⟩|⟨a, b⟩|⟨a, b⟩|⟨a, b⟩|⟨a, b⟩|⟨a, b⟩|⟨a, b⟩|⟨a, b⟩|⟨a, b⟩|⟨a, b⟩|⟨a, b⟩|⟨a, b⟩
    · have := close2 0 1 2 3 (by decide) a b; omega
    · have := close2 0 1 2 4 (by decide) a b; omega
    · have := close2 0 1 3 4 (by decide) a b; omega
    · have := close2 0 2 1 3 (by decide) a b; omega
    · have := close2 0 2 1 4 (by decide) a b; omega
    · have := close2 0 2 3 4 (by decide) a b; omega
    · have := close2 0 3 1 2 (by decide) a b; omega
    · have := close2 0 3 1 4 (by decide) a b; omega
    · have := close2 0 3 2 4 (by decide) a b; omega
    · have := close2 0 4 1 2 (by decide) a b; omega
    · have := close2 0 4 1 3 (by decide) a b; omega
    · have := close2 0 4 2 3 (by decide) a b; omega
    · have := close2 1 2 3 4 (by decide) a b; omega
    · have := close2 1 3 2 4 (by decide) a b; omega
    · have := close2 1 4 2 3 (by decide) a b; omega
  -- fiveCycle packaging for s ≤ 2
  have cycClose : edgeCountIn G T ≤ 2 →
      (∑ i : Fin 5, (Bset.filter (fun v => G.Adj (vt i) v)).card) ≤ 14 → False := by
    intro hs2 hD14
    have h2 := hbridge ▸ hs2
    have hf := fiveCycle _ _ _ _ _ _ _ _ _ _ h2
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, or_assoc, and_assoc] at hf
    rcases hf with ⟨c1,c2,c3,c4,c5⟩|⟨c1,c2,c3,c4,c5⟩|⟨c1,c2,c3,c4,c5⟩|⟨c1,c2,c3,c4,c5⟩|⟨c1,c2,c3,c4,c5⟩|⟨c1,c2,c3,c4,c5⟩|⟨c1,c2,c3,c4,c5⟩|⟨c1,c2,c3,c4,c5⟩|⟨c1,c2,c3,c4,c5⟩|⟨c1,c2,c3,c4,c5⟩|⟨c1,c2,c3,c4,c5⟩|⟨c1,c2,c3,c4,c5⟩
    · have a1 := hdsum 0 1 (by decide) c1; have a2 := hdsum 1 3 (by decide) c2
      have a3 := hdsum 3 4 (by decide) c3; have a4 := hdsum 2 4 (by decide) c4
      have a5 := hdsum 0 2 (by decide) c5; omega
    · have a1 := hdsum 0 1 (by decide) c1; have a2 := hdsum 1 4 (by decide) c2
      have a3 := hdsum 3 4 (by decide) c3; have a4 := hdsum 2 3 (by decide) c4
      have a5 := hdsum 0 2 (by decide) c5; omega
    · have a1 := hdsum 0 1 (by decide) c1; have a2 := hdsum 1 2 (by decide) c2
      have a3 := hdsum 2 4 (by decide) c3; have a4 := hdsum 3 4 (by decide) c4
      have a5 := hdsum 0 3 (by decide) c5; omega
    · have a1 := hdsum 0 1 (by decide) c1; have a2 := hdsum 1 4 (by decide) c2
      have a3 := hdsum 2 4 (by decide) c3; have a4 := hdsum 2 3 (by decide) c4
      have a5 := hdsum 0 3 (by decide) c5; omega
    · have a1 := hdsum 0 1 (by decide) c1; have a2 := hdsum 1 2 (by decide) c2
      have a3 := hdsum 2 3 (by decide) c3; have a4 := hdsum 3 4 (by decide) c4
      have a5 := hdsum 0 4 (by decide) c5; omega
    · have a1 := hdsum 0 1 (by decide) c1; have a2 := hdsum 1 3 (by decide) c2
      have a3 := hdsum 2 3 (by decide) c3; have a4 := hdsum 2 4 (by decide) c4
      have a5 := hdsum 0 4 (by decide) c5; omega
    · have a1 := hdsum 0 2 (by decide) c1; have a2 := hdsum 1 2 (by decide) c2
      have a3 := hdsum 1 4 (by decide) c3; have a4 := hdsum 3 4 (by decide) c4
      have a5 := hdsum 0 3 (by decide) c5; omega
    · have a1 := hdsum 0 2 (by decide) c1; have a2 := hdsum 2 4 (by decide) c2
      have a3 := hdsum 1 4 (by decide) c3; have a4 := hdsum 1 3 (by decide) c4
      have a5 := hdsum 0 3 (by decide) c5; omega
    · have a1 := hdsum 0 2 (by decide) c1; have a2 := hdsum 1 2 (by decide) c2
      have a3 := hdsum 1 3 (by decide) c3; have a4 := hdsum 3 4 (by decide) c4
      have a5 := hdsum 0 4 (by decide) c5; omega
    · have a1 := hdsum 0 2 (by decide) c1; have a2 := hdsum 2 3 (by decide) c2
      have a3 := hdsum 1 3 (by decide) c3; have a4 := hdsum 1 4 (by decide) c4
      have a5 := hdsum 0 4 (by decide) c5; omega
    · have a1 := hdsum 0 3 (by decide) c1; have a2 := hdsum 1 3 (by decide) c2
      have a3 := hdsum 1 2 (by decide) c3; have a4 := hdsum 2 4 (by decide) c4
      have a5 := hdsum 0 4 (by decide) c5; omega
    · have a1 := hdsum 0 3 (by decide) c1; have a2 := hdsum 2 3 (by decide) c2
      have a3 := hdsum 1 2 (by decide) c3; have a4 := hdsum 1 4 (by decide) c4
      have a5 := hdsum 0 4 (by decide) c5; omega
  -- r = 4 star endgame, parametrised by the centre `c`
  have sec5_r4_star : ∀ c : Fin 5, (∀ i, i ≠ c → ¬ G.Adj (vt c) (vt i)) →
      edgeCountIn G T = 6 → False := by
    intro c hstar hval6
    by_cases hzl : ∃ i, i ≠ c ∧ (Bset.filter (fun v => G.Adj (vt i) v)).card = 0
    · obtain ⟨i, hic, hi0⟩ := hzl
      exact collapse_of_zero c i (Ne.symm hic) (hstar i hic) hi0
    · -- all four leaves have positive B-degree: forced d_c = 5, leaves = 1, then a cap-11
      -- contradiction on B (the (28)–(32) endgame)
      push_neg at hzl
      have hedge : ∀ i ∈ Finset.univ.erase c, 6 ≤ (Bset.filter (fun v => G.Adj (vt c) v)).card
          + (Bset.filter (fun v => G.Adj (vt i) v)).card := fun i hi =>
        hdsum c i (Ne.symm (Finset.ne_of_mem_erase hi)) (hstar i (Finset.ne_of_mem_erase hi))
      have hpos : ∀ i ∈ Finset.univ.erase c, 1 ≤ (Bset.filter (fun v => G.Adj (vt i) v)).card :=
        fun i hi => Nat.one_le_iff_ne_zero.mpr (hzl i (Finset.ne_of_mem_erase hi))
      have herc : (Finset.univ.erase c).card = 4 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
      have hsum_edge : (24 : ℕ) ≤ ∑ i ∈ Finset.univ.erase c,
          ((Bset.filter (fun v => G.Adj (vt c) v)).card
            + (Bset.filter (fun v => G.Adj (vt i) v)).card) := by
        calc (24:ℕ) = ∑ _i ∈ Finset.univ.erase c, 6 := by rw [Finset.sum_const, herc, smul_eq_mul]
          _ ≤ _ := Finset.sum_le_sum hedge
      have hsum_split : (∑ i ∈ Finset.univ.erase c,
          ((Bset.filter (fun v => G.Adj (vt c) v)).card
            + (Bset.filter (fun v => G.Adj (vt i) v)).card))
          = 4 * (Bset.filter (fun v => G.Adj (vt c) v)).card
            + ∑ i ∈ Finset.univ.erase c, (Bset.filter (fun v => G.Adj (vt i) v)).card := by
        rw [Finset.sum_add_distrib, Finset.sum_const, herc]; ring
      have hsum_pos : (4:ℕ) ≤ ∑ i ∈ Finset.univ.erase c,
          (Bset.filter (fun v => G.Adj (vt i) v)).card := by
        calc (4:ℕ) = ∑ _i ∈ Finset.univ.erase c, 1 := by rw [Finset.sum_const, herc, smul_eq_mul]
          _ ≤ _ := Finset.sum_le_sum hpos
      have hD_erase : (∑ i : Fin 5, (Bset.filter (fun v => G.Adj (vt i) v)).card)
          = (Bset.filter (fun v => G.Adj (vt c) v)).card
            + ∑ i ∈ Finset.univ.erase c, (Bset.filter (fun v => G.Adj (vt i) v)).card := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ c)]; ring
      have hDle9 : (∑ i : Fin 5, (Bset.filter (fun v => G.Adj (vt i) v)).card) ≤ 9 := by
        have h := hDval; rw [hval6] at h; omega
      have hddc5 : (Bset.filter (fun v => G.Adj (vt c) v)).card = 5 := by omega
      have hsum_erase4 : (∑ i ∈ Finset.univ.erase c,
          (Bset.filter (fun v => G.Adj (vt i) v)).card) = 4 := by omega
      obtain ⟨i0, hi0⟩ := Finset.card_pos.mp
        (show 0 < (Finset.univ.erase c).card by rw [herc]; norm_num)
      have hi0c : i0 ≠ c := Finset.ne_of_mem_erase hi0
      have hi0_1 : (Bset.filter (fun v => G.Adj (vt i0) v)).card = 1 := by
        have hsplit2 : (∑ i ∈ (Finset.univ.erase c).erase i0,
              (Bset.filter (fun v => G.Adj (vt i) v)).card)
            + (Bset.filter (fun v => G.Adj (vt i0) v)).card
            = ∑ i ∈ Finset.univ.erase c, (Bset.filter (fun v => G.Adj (vt i) v)).card :=
          Finset.sum_erase_add _ _ hi0
        have hrc : ((Finset.univ.erase c).erase i0).card = 3 := by
          rw [Finset.card_erase_of_mem hi0, herc]
        have hrest_ge : (3:ℕ) ≤ ∑ i ∈ (Finset.univ.erase c).erase i0,
            (Bset.filter (fun v => G.Adj (vt i) v)).card := by
          calc (3:ℕ) = ∑ _i ∈ (Finset.univ.erase c).erase i0, 1 := by
                rw [Finset.sum_const, hrc, smul_eq_mul]
            _ ≤ _ := Finset.sum_le_sum (fun i hi => hpos i (Finset.mem_of_mem_erase hi))
        have hp0 := hpos i0 hi0
        omega
      have heB25' : edgeCountIn G Bset = 25 := by
        have hbud := sec5_eB_D_le ctx.he60 hQ1sub hQ2sub hQ1clq hQ1c hQ2clq hQ2c
        rw [← hBdef] at hbud
        rw [hval6, hDimg] at hbud
        have hDeq9 : (∑ i : Fin 5, (Bset.filter (fun v => G.Adj (vt i) v)).card) = 9 := by omega
        omega
      have hhit := all_hit c i0 (Ne.symm hi0c) (hstar i0 hi0c)
      exact sec5_star_endgame ctx.hcap hBc hαB2 hBfree heB25' (hvtnB c) hddc5 hi0_1 hhit
  -- case on s = e(G[T]) ∈ {0,…,6}
  have hs6 : edgeCountIn G T ≤ 6 := ctx.hsT
  rcases (by omega : edgeCountIn G T = 0 ∨ edgeCountIn G T = 1 ∨ edgeCountIn G T = 2
      ∨ edgeCountIn G T = 3 ∨ edgeCountIn G T = 4 ∨ edgeCountIn G T = 5 ∨ edgeCountIn G T = 6)
    with hval|hval|hval|hval|hval|hval|hval
  · -- r = 10: T independent ⇒ five disjoint 3-sets in a 10-set
    have hsum0 : (decide (G.Adj (vt 0) (vt 1))).toNat + (decide (G.Adj (vt 0) (vt 2))).toNat
        + (decide (G.Adj (vt 0) (vt 3))).toNat + (decide (G.Adj (vt 0) (vt 4))).toNat
        + (decide (G.Adj (vt 1) (vt 2))).toNat + (decide (G.Adj (vt 1) (vt 3))).toNat
        + (decide (G.Adj (vt 1) (vt 4))).toNat + (decide (G.Adj (vt 2) (vt 3))).toNat
        + (decide (G.Adj (vt 2) (vt 4))).toNat + (decide (G.Adj (vt 3) (vt 4))).toNat = 0 := by
      rw [hbridge]; exact hval
    have hna : ∀ i j : Fin 5, i ≠ j → ¬ G.Adj (vt i) (vt j) := by
      have b01 : ¬ G.Adj (vt 0) (vt 1) := of_decide_eq_false (by rw [← Bool.toNat_eq_zero]; omega)
      have b02 : ¬ G.Adj (vt 0) (vt 2) := of_decide_eq_false (by rw [← Bool.toNat_eq_zero]; omega)
      have b03 : ¬ G.Adj (vt 0) (vt 3) := of_decide_eq_false (by rw [← Bool.toNat_eq_zero]; omega)
      have b04 : ¬ G.Adj (vt 0) (vt 4) := of_decide_eq_false (by rw [← Bool.toNat_eq_zero]; omega)
      have b12 : ¬ G.Adj (vt 1) (vt 2) := of_decide_eq_false (by rw [← Bool.toNat_eq_zero]; omega)
      have b13 : ¬ G.Adj (vt 1) (vt 3) := of_decide_eq_false (by rw [← Bool.toNat_eq_zero]; omega)
      have b14 : ¬ G.Adj (vt 1) (vt 4) := of_decide_eq_false (by rw [← Bool.toNat_eq_zero]; omega)
      have b23 : ¬ G.Adj (vt 2) (vt 3) := of_decide_eq_false (by rw [← Bool.toNat_eq_zero]; omega)
      have b24 : ¬ G.Adj (vt 2) (vt 4) := of_decide_eq_false (by rw [← Bool.toNat_eq_zero]; omega)
      have b34 : ¬ G.Adj (vt 3) (vt 4) := of_decide_eq_false (by rw [← Bool.toNat_eq_zero]; omega)
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        first
          | exact absurd rfl hij
          | assumption
          | (intro h; exact b01 (G.symm h)) | (intro h; exact b02 (G.symm h))
          | (intro h; exact b03 (G.symm h)) | (intro h; exact b04 (G.symm h))
          | (intro h; exact b12 (G.symm h)) | (intro h; exact b13 (G.symm h))
          | (intro h; exact b14 (G.symm h)) | (intro h; exact b23 (G.symm h))
          | (intro h; exact b24 (G.symm h)) | (intro h; exact b34 (G.symm h))
    -- all d_i = 3
    have a01 := hdsum 0 1 (by decide) (hna 0 1 (by decide))
    have a02 := hdsum 0 2 (by decide) (hna 0 2 (by decide))
    have a03 := hdsum 0 3 (by decide) (hna 0 3 (by decide))
    have a04 := hdsum 0 4 (by decide) (hna 0 4 (by decide))
    have a12 := hdsum 1 2 (by decide) (hna 1 2 (by decide))
    have a13 := hdsum 1 3 (by decide) (hna 1 3 (by decide))
    have a14 := hdsum 1 4 (by decide) (hna 1 4 (by decide))
    have a23 := hdsum 2 3 (by decide) (hna 2 3 (by decide))
    have a24 := hdsum 2 4 (by decide) (hna 2 4 (by decide))
    have a34 := hdsum 3 4 (by decide) (hna 3 4 (by decide))
    have hd0 : (Bset.filter (fun v => G.Adj (vt 0) v)).card = 3 := by omega
    have hd1 : (Bset.filter (fun v => G.Adj (vt 1) v)).card = 3 := by omega
    have hd2 : (Bset.filter (fun v => G.Adj (vt 2) v)).card = 3 := by omega
    have hd3 : (Bset.filter (fun v => G.Adj (vt 3) v)).card = 3 := by omega
    have hd4 : (Bset.filter (fun v => G.Adj (vt 4) v)).card = 3 := by omega
    have hdall : ∀ i : Fin 5, (Bset.filter (fun v => G.Adj (vt i) v)).card = 3 := by
      intro i; fin_cases i
      · exact hd0
      · exact hd1
      · exact hd2
      · exact hd3
      · exact hd4
    -- pairwise disjoint
    have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin 5)), ∀ j ∈ (Finset.univ : Finset (Fin 5)),
        i ≠ j → Disjoint (Bset.filter (fun v => G.Adj (vt i) v))
          (Bset.filter (fun v => G.Adj (vt j) v)) := by
      intro i _ j _ hij
      set A := Bset.filter (fun v => G.Adj (vt i) v) with hA
      set B := Bset.filter (fun v => G.Adj (vt j) v) with hB
      have huc := hunioncard i j hij (hna i j hij)
      have hfor : Bset.filter (fun v => G.Adj (vt i) v ∨ G.Adj (vt j) v) = A ∪ B := by
        rw [hA, hB, Finset.filter_or]
      rw [hfor] at huc
      have hun := Finset.card_union_add_card_inter A B
      have hi : A.card = 3 := hdall i
      have hj : B.card = 3 := hdall j
      have hz : (A ∩ B).card = 0 := by omega
      exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hz)
    have hbig : (Finset.univ.biUnion (fun i => Bset.filter (fun v => G.Adj (vt i) v))).card = 15 := by
      rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl (fun i _ => hdall i)]
      decide
    have hsub : Finset.univ.biUnion (fun i => Bset.filter (fun v => G.Adj (vt i) v)) ⊆ Bset := by
      intro x hx; rw [Finset.mem_biUnion] at hx; obtain ⟨i, _, hxi⟩ := hx
      exact Finset.filter_subset _ _ hxi
    have := Finset.card_le_card hsub; rw [hbig, hBc] at this; omega
  · exact cycClose (by omega) (by omega)
  · exact cycClose (by omega) (by omega)
  · -- r = 7: D = 12, weight vector (0,0,0,6,6) ⇒ a zero-degree vertex in a non-edge ⇒ collapse
    have hbsum : (decide (G.Adj (vt 0) (vt 1))).toNat + (decide (G.Adj (vt 0) (vt 2))).toNat
        + (decide (G.Adj (vt 0) (vt 3))).toNat + (decide (G.Adj (vt 0) (vt 4))).toNat
        + (decide (G.Adj (vt 1) (vt 2))).toNat + (decide (G.Adj (vt 1) (vt 3))).toNat
        + (decide (G.Adj (vt 1) (vt 4))).toNat + (decide (G.Adj (vt 2) (vt 3))).toNat
        + (decide (G.Adj (vt 2) (vt 4))).toNat + (decide (G.Adj (vt 3) (vt 4))).toNat = 3 := by
      rw [hbridge]; exact hval
    -- D = 12
    have h12 : 12 ≤ (∑ i : Fin 5, (Bset.filter (fun v => G.Adj (vt i) v)).card) := by
      have h5 := hbridge ▸ (by omega : edgeCountIn G T ≤ 5)
      have hf := twoDisjoint _ _ _ _ _ _ _ _ _ _ h5
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not, or_assoc, and_assoc] at hf
      rcases hf with ⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩
      · exact close2 0 1 2 3 (by decide) a b
      · exact close2 0 1 2 4 (by decide) a b
      · exact close2 0 1 3 4 (by decide) a b
      · exact close2 0 2 1 3 (by decide) a b
      · exact close2 0 2 1 4 (by decide) a b
      · exact close2 0 2 3 4 (by decide) a b
      · exact close2 0 3 1 2 (by decide) a b
      · exact close2 0 3 1 4 (by decide) a b
      · exact close2 0 3 2 4 (by decide) a b
      · exact close2 0 4 1 2 (by decide) a b
      · exact close2 0 4 1 3 (by decide) a b
      · exact close2 0 4 2 3 (by decide) a b
      · exact close2 1 2 3 4 (by decide) a b
      · exact close2 1 3 2 4 (by decide) a b
      · exact close2 1 4 2 3 (by decide) a b
    -- per-pair constraint 6 ≤ d_i + d_j + 6·[edge]
    have hc : ∀ i j : Fin 5, i ≠ j → 6 ≤ (Bset.filter (fun v => G.Adj (vt i) v)).card
        + (Bset.filter (fun v => G.Adj (vt j) v)).card
        + 6 * (decide (G.Adj (vt i) (vt j))).toNat := by
      intro i j hij
      by_cases h : G.Adj (vt i) (vt j)
      · have hb1 : (decide (G.Adj (vt i) (vt j))).toNat = 1 := by simp [h]
        omega
      · have h6 := hdsum i j hij h
        have hb0 : (decide (G.Adj (vt i) (vt j))).toNat = 0 := by simp [h]
        omega
    have c01 := hc 0 1 (by decide); have c02 := hc 0 2 (by decide); have c03 := hc 0 3 (by decide)
    have c04 := hc 0 4 (by decide); have c12 := hc 1 2 (by decide); have c13 := hc 1 3 (by decide)
    have c14 := hc 1 4 (by decide); have c23 := hc 2 3 (by decide); have c24 := hc 2 4 (by decide)
    have c34 := hc 3 4 (by decide)
    have bfalse : ∀ a d : Fin 5, (decide (G.Adj (vt a) (vt d))).toNat = 0 → ¬ G.Adj (vt a) (vt d) :=
      fun a d h => of_decide_eq_false (Bool.toNat_eq_zero.mp h)
    -- some vertex has degree 0 (else omega refutes)
    have hzero5 : (Bset.filter (fun v => G.Adj (vt 0) v)).card = 0
        ∨ (Bset.filter (fun v => G.Adj (vt 1) v)).card = 0
        ∨ (Bset.filter (fun v => G.Adj (vt 2) v)).card = 0
        ∨ (Bset.filter (fun v => G.Adj (vt 3) v)).card = 0
        ∨ (Bset.filter (fun v => G.Adj (vt 4) v)).card = 0 := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨z0, z1, z2, z3, z4⟩ := hcon
      omega
    rcases hzero5 with hz|hz|hz|hz|hz
    · rcases (show (decide (G.Adj (vt 0) (vt 1))).toNat = 0 ∨ (decide (G.Adj (vt 0) (vt 2))).toNat = 0
          ∨ (decide (G.Adj (vt 0) (vt 3))).toNat = 0 ∨ (decide (G.Adj (vt 0) (vt 4))).toNat = 0
          from by omega) with hp|hp|hp|hp
      · exact collapse_of_zero 1 0 (by decide) (by have hb := bfalse 0 1 hp; first | exact hb | exact fun h => hb (G.symm h)) hz
      · exact collapse_of_zero 2 0 (by decide) (by have hb := bfalse 0 2 hp; first | exact hb | exact fun h => hb (G.symm h)) hz
      · exact collapse_of_zero 3 0 (by decide) (by have hb := bfalse 0 3 hp; first | exact hb | exact fun h => hb (G.symm h)) hz
      · exact collapse_of_zero 4 0 (by decide) (by have hb := bfalse 0 4 hp; first | exact hb | exact fun h => hb (G.symm h)) hz
    · rcases (show (decide (G.Adj (vt 0) (vt 1))).toNat = 0 ∨ (decide (G.Adj (vt 1) (vt 2))).toNat = 0
          ∨ (decide (G.Adj (vt 1) (vt 3))).toNat = 0 ∨ (decide (G.Adj (vt 1) (vt 4))).toNat = 0
          from by omega) with hp|hp|hp|hp
      · exact collapse_of_zero 0 1 (by decide) (by have hb := bfalse 0 1 hp; first | exact hb | exact fun h => hb (G.symm h)) hz
      · exact collapse_of_zero 2 1 (by decide) (by have hb := bfalse 1 2 hp; first | exact hb | exact fun h => hb (G.symm h)) hz
      · exact collapse_of_zero 3 1 (by decide) (by have hb := bfalse 1 3 hp; first | exact hb | exact fun h => hb (G.symm h)) hz
      · exact collapse_of_zero 4 1 (by decide) (by have hb := bfalse 1 4 hp; first | exact hb | exact fun h => hb (G.symm h)) hz
    · rcases (show (decide (G.Adj (vt 0) (vt 2))).toNat = 0 ∨ (decide (G.Adj (vt 1) (vt 2))).toNat = 0
          ∨ (decide (G.Adj (vt 2) (vt 3))).toNat = 0 ∨ (decide (G.Adj (vt 2) (vt 4))).toNat = 0
          from by omega) with hp|hp|hp|hp
      · exact collapse_of_zero 0 2 (by decide) (by have hb := bfalse 0 2 hp; first | exact hb | exact fun h => hb (G.symm h)) hz
      · exact collapse_of_zero 1 2 (by decide) (by have hb := bfalse 1 2 hp; first | exact hb | exact fun h => hb (G.symm h)) hz
      · exact collapse_of_zero 3 2 (by decide) (by have hb := bfalse 2 3 hp; first | exact hb | exact fun h => hb (G.symm h)) hz
      · exact collapse_of_zero 4 2 (by decide) (by have hb := bfalse 2 4 hp; first | exact hb | exact fun h => hb (G.symm h)) hz
    · rcases (show (decide (G.Adj (vt 0) (vt 3))).toNat = 0 ∨ (decide (G.Adj (vt 1) (vt 3))).toNat = 0
          ∨ (decide (G.Adj (vt 2) (vt 3))).toNat = 0 ∨ (decide (G.Adj (vt 3) (vt 4))).toNat = 0
          from by omega) with hp|hp|hp|hp
      · exact collapse_of_zero 0 3 (by decide) (by have hb := bfalse 0 3 hp; first | exact hb | exact fun h => hb (G.symm h)) hz
      · exact collapse_of_zero 1 3 (by decide) (by have hb := bfalse 1 3 hp; first | exact hb | exact fun h => hb (G.symm h)) hz
      · exact collapse_of_zero 2 3 (by decide) (by have hb := bfalse 2 3 hp; first | exact hb | exact fun h => hb (G.symm h)) hz
      · exact collapse_of_zero 4 3 (by decide) (by have hb := bfalse 3 4 hp; first | exact hb | exact fun h => hb (G.symm h)) hz
    · rcases (show (decide (G.Adj (vt 0) (vt 4))).toNat = 0 ∨ (decide (G.Adj (vt 1) (vt 4))).toNat = 0
          ∨ (decide (G.Adj (vt 2) (vt 4))).toNat = 0 ∨ (decide (G.Adj (vt 3) (vt 4))).toNat = 0
          from by omega) with hp|hp|hp|hp
      · exact collapse_of_zero 0 4 (by decide) (by have hb := bfalse 0 4 hp; first | exact hb | exact fun h => hb (G.symm h)) hz
      · exact collapse_of_zero 1 4 (by decide) (by have hb := bfalse 1 4 hp; first | exact hb | exact fun h => hb (G.symm h)) hz
      · exact collapse_of_zero 2 4 (by decide) (by have hb := bfalse 2 4 hp; first | exact hb | exact fun h => hb (G.symm h)) hz
      · exact collapse_of_zero 3 4 (by decide) (by have hb := bfalse 3 4 hp; first | exact hb | exact fun h => hb (G.symm h)) hz
  · exact disjClose (by omega) (by omega)
  · exact disjClose (by omega) (by omega)
  · -- r = 4: star or two disjoint non-edges
    have h6 := hbridge ▸ (le_of_eq hval)
    have hf := starOrDisjoint _ _ _ _ _ _ _ _ _ _ h6
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, or_assoc, and_assoc] at hf
    rcases hf with ⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|hstar|hstar|hstar|hstar|hstar
    · have := close2 0 1 2 3 (by decide) a b; omega
    · have := close2 0 1 2 4 (by decide) a b; omega
    · have := close2 0 1 3 4 (by decide) a b; omega
    · have := close2 0 2 1 3 (by decide) a b; omega
    · have := close2 0 2 1 4 (by decide) a b; omega
    · have := close2 0 2 3 4 (by decide) a b; omega
    · have := close2 0 3 1 2 (by decide) a b; omega
    · have := close2 0 3 1 4 (by decide) a b; omega
    · have := close2 0 3 2 4 (by decide) a b; omega
    · have := close2 0 4 1 2 (by decide) a b; omega
    · have := close2 0 4 1 3 (by decide) a b; omega
    · have := close2 0 4 2 3 (by decide) a b; omega
    · have := close2 1 2 3 4 (by decide) a b; omega
    · have := close2 1 3 2 4 (by decide) a b; omega
    · have := close2 1 4 2 3 (by decide) a b; omega
    · obtain ⟨s1, s2, s3, s4⟩ := hstar
      refine sec5_r4_star 0 ?_ hval
      intro i hi; fin_cases i
      · exact absurd rfl hi
      · exact s1
      · exact s2
      · exact s3
      · exact s4
    · obtain ⟨s1, s2, s3, s4⟩ := hstar
      refine sec5_r4_star 1 ?_ hval
      intro i hi; fin_cases i
      · exact fun h => s1 (G.symm h)
      · exact absurd rfl hi
      · exact s2
      · exact s3
      · exact s4
    · obtain ⟨s1, s2, s3, s4⟩ := hstar
      refine sec5_r4_star 2 ?_ hval
      intro i hi; fin_cases i
      · exact fun h => s1 (G.symm h)
      · exact fun h => s2 (G.symm h)
      · exact absurd rfl hi
      · exact s3
      · exact s4
    · obtain ⟨s1, s2, s3, s4⟩ := hstar
      refine sec5_r4_star 3 ?_ hval
      intro i hi; fin_cases i
      · exact fun h => s1 (G.symm h)
      · exact fun h => s2 (G.symm h)
      · exact fun h => s3 (G.symm h)
      · exact absurd rfl hi
      · exact s4
    · obtain ⟨s1, s2, s3, s4⟩ := hstar
      refine sec5_r4_star 4 ?_ hval
      intro i hi; fin_cases i
      · exact fun h => s1 (G.symm h)
      · exact fun h => s2 (G.symm h)
      · exact fun h => s3 (G.symm h)
      · exact fun h => s4 (G.symm h)
      · exact absurd rfl hi


/-- **Missed `Q`-vertex ⇒ 6-set.** An independent 5-set `{a,b,c,d,e}` disjoint from
a 5-clique `Q` whose vertices see at most four vertices of `Q` leaves a `Q`-vertex
non-adjacent to all five, an independent 6-set. (§4 (14)/(15) and §4.2 core.) -/
theorem indep5_missedQ_false {G : SimpleGraph (Fin 25)}
    (hα5 : ∀ S : Finset (Fin 25), IsIndep G S → S.card ≤ 5)
    {Q : Finset (Fin 25)} (hQc : Q.card = 5)
    {a b c d e : Fin 25}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (nab : ¬ G.Adj a b) (nac : ¬ G.Adj a c) (nad : ¬ G.Adj a d) (nae : ¬ G.Adj a e)
    (nbc : ¬ G.Adj b c) (nbd : ¬ G.Adj b d) (nbe : ¬ G.Adj b e)
    (ncd : ¬ G.Adj c d) (nce : ¬ G.Adj c e) (nde : ¬ G.Adj d e)
    (haQ : a ∉ Q) (hbQ : b ∉ Q) (hcQ : c ∉ Q) (hdQ : d ∉ Q) (heQ : e ∉ Q)
    (hcover : (Q.filter (fun w => G.Adj a w ∨ G.Adj b w ∨ G.Adj c w ∨ G.Adj d w
      ∨ G.Adj e w)).card ≤ 4) : False := by
  classical
  have hpart := Finset.card_filter_add_card_filter_not (s := Q)
    (p := fun w => G.Adj a w ∨ G.Adj b w ∨ G.Adj c w ∨ G.Adj d w ∨ G.Adj e w)
  rw [hQc] at hpart
  have hMpos : 0 < (Q.filter (fun w => ¬ (G.Adj a w ∨ G.Adj b w ∨ G.Adj c w ∨ G.Adj d w
      ∨ G.Adj e w))).card := by omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hMpos
  rw [Finset.mem_filter] at hw
  obtain ⟨hwQ, hwn⟩ := hw
  push_neg at hwn
  obtain ⟨nwa, nwb, nwc, nwd, nwe⟩ := hwn
  have haw : a ≠ w := fun h => haQ (h ▸ hwQ)
  have hbw : b ≠ w := fun h => hbQ (h ▸ hwQ)
  have hcw : c ≠ w := fun h => hcQ (h ▸ hwQ)
  have hdw : d ≠ w := fun h => hdQ (h ▸ hwQ)
  have hew : e ≠ w := fun h => heQ (h ▸ hwQ)
  exact no_indep_six hα5 hab hac had hae haw hbc hbd hbe hbw hcd hce hcw hde hdw hew
    nab nac nad nae nwa nbc nbd nbe nwb ncd nce nwc nde nwd nwe

/-- **Missed `K`-vertex ⇒ 4-set.** An independent triple `{a,b,c}` disjoint from a
5-clique `K` under cap-11 leaves a `K`-vertex non-adjacent to all three (the three
see at most three of `K`'s five). Used in §4.1's `K₅`-through-`t` branch. -/
theorem exists_missed_in_clique5 {G : SimpleGraph (Fin 25)} (hcap : capAtMost11 G)
    {K : Finset (Fin 25)} (hKclq : IsCliqueOn G K) (hKc : K.card = 5)
    {a b c : Fin 25} (haK : a ∉ K) (hbK : b ∉ K) (hcK : c ∉ K) :
    ∃ w ∈ K, ¬ G.Adj a w ∧ ¬ G.Adj b w ∧ ¬ G.Adj c w := by
  classical
  have h1a := indeg_clique5_le_one G hcap hKclq hKc haK
  have h1b := indeg_clique5_le_one G hcap hKclq hKc hbK
  have h1c := indeg_clique5_le_one G hcap hKclq hKc hcK
  have hcov_le : (K.filter (fun w => G.Adj a w ∨ G.Adj b w ∨ G.Adj c w)).card
      ≤ (K.filter (fun w => G.Adj a w)).card + (K.filter (fun w => G.Adj b w)).card
        + (K.filter (fun w => G.Adj c w)).card := by
    have hsub : K.filter (fun w => G.Adj a w ∨ G.Adj b w ∨ G.Adj c w)
        ⊆ K.filter (fun w => G.Adj a w) ∪ K.filter (fun w => G.Adj b w)
          ∪ K.filter (fun w => G.Adj c w) := by
      intro w hw; rw [Finset.mem_filter] at hw
      rcases hw.2 with h | h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw.1, h⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw.1, h⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw.1, h⟩)
    refine le_trans (Finset.card_le_card hsub) ?_
    exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have hpart := Finset.card_filter_add_card_filter_not (s := K)
    (p := fun w => G.Adj a w ∨ G.Adj b w ∨ G.Adj c w)
  rw [hKc] at hpart
  have hMpos : 0 < (K.filter (fun w => ¬ (G.Adj a w ∨ G.Adj b w ∨ G.Adj c w))).card := by omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hMpos
  rw [Finset.mem_filter] at hw
  obtain ⟨hwK, hwn⟩ := hw
  push_neg at hwn
  exact ⟨w, hwK, hwn.1, hwn.2.1, hwn.2.2⟩


/-- Ordered off-diagonal pairs of an `S : Finset (Fin n)` number `|S|² − |S|`. -/
theorem offdiag_prod_card {n : ℕ} (S : Finset (Fin n)) :
    ((S ×ˢ S).filter (fun p => ¬ p.1 = p.2)).card + S.card = S.card * S.card := by
  have hdiag : ((S ×ˢ S).filter (fun p => p.1 = p.2)).card = S.card := by
    refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
    · intro p hp; exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    · intro p hp q hq h
      rw [Finset.mem_filter] at hp hq
      exact Prod.ext h (by rw [← hp.2, ← hq.2]; exact h)
    · intro i hi
      exact ⟨(i, i), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi, hi⟩, rfl⟩, rfl⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := S ×ˢ S) (p := fun p => p.1 = p.2)
  rw [Finset.card_product, hdiag] at hsplit
  omega


/-- `∑` of `f ∘ fst` over ordered off-diagonal pairs of `Fin 5` is `4·∑ f`. -/
theorem sum_offdiag_fst (f : Fin 5 → ℕ) :
    ∑ q ∈ Finset.univ.filter (fun p : Fin 5 × Fin 5 => p.1 ≠ p.2), f q.1 = 4 * ∑ i, f i := by
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hrw : (∑ j : Fin 5, if (i, j).1 ≠ (i, j).2 then f (i, j).1 else 0)
      = ∑ j : Fin 5, if i ≠ j then f i else 0 := rfl
  have hc : (Finset.univ.filter (fun j : Fin 5 => i ≠ j)).card = 4 := by
    rw [Finset.filter_ne, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
  rw [hrw, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, hc, smul_eq_mul,
    Nat.mul_comm]

/-- `∑` of `f ∘ snd` over ordered off-diagonal pairs of `Fin 5` is `4·∑ f`. -/
theorem sum_offdiag_snd (f : Fin 5 → ℕ) :
    ∑ q ∈ Finset.univ.filter (fun p : Fin 5 × Fin 5 => p.1 ≠ p.2), f q.2 = 4 * ∑ i, f i := by
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hrw : (∑ i : Fin 5, if (i, j).1 ≠ (i, j).2 then f (i, j).2 else 0)
      = ∑ i : Fin 5, if i ≠ j then f j else 0 := rfl
  have hc : (Finset.univ.filter (fun i : Fin 5 => i ≠ j)).card = 4 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
      Fintype.card_fin]
  rw [hrw, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, hc, smul_eq_mul,
    Nat.mul_comm]

/-- **§4 (16) elimination** (decidable finite check). Any `(a,p,r)` surviving the
weighted-count inequality lies in `p+a ≤ 1`, or `a=5` with `(p,r)=(4,10)` or
`p∈{5,6,7}`. -/
theorem sec4_elim (a p r cb : ℕ) (ha : a ≤ 5) (hp : p ≤ 12) (hr4 : 4 ≤ r) (hr10 : r ≤ 10)
    (hpar : p + a ≤ r + 2) (hcb2r : cb ≤ 2 * r) (hcbaa : cb + a ≤ a * a)
    (hcond : 10 * r ≤ 8 * (r + 2 - p - a) + p * cb) :
    (p + a ≤ 1) ∨ (a = 5 ∧ p = 4 ∧ r = 10) ∨ (a = 5 ∧ 5 ≤ p ∧ p ≤ 7) := by
  interval_cases a <;> interval_cases p <;> omega


/-- 5-way union bound for `Q`-neighbourhood covers. -/
theorem cover5_le {G : SimpleGraph (Fin 25)} (Q : Finset (Fin 25)) (a b c d e : Fin 25) :
    (Q.filter (fun w => G.Adj a w ∨ G.Adj b w ∨ G.Adj c w ∨ G.Adj d w ∨ G.Adj e w)).card
    ≤ (Q.filter (fun w => G.Adj a w)).card + (Q.filter (fun w => G.Adj b w)).card
      + (Q.filter (fun w => G.Adj c w)).card + (Q.filter (fun w => G.Adj d w)).card
      + (Q.filter (fun w => G.Adj e w)).card := by
  have hsub : Q.filter (fun w => G.Adj a w ∨ G.Adj b w ∨ G.Adj c w ∨ G.Adj d w ∨ G.Adj e w)
      ⊆ Q.filter (fun w => G.Adj a w) ∪ Q.filter (fun w => G.Adj b w)
        ∪ Q.filter (fun w => G.Adj c w) ∪ Q.filter (fun w => G.Adj d w)
        ∪ Q.filter (fun w => G.Adj e w) := by
    intro w hw; rw [Finset.mem_filter] at hw
    rcases hw.2 with h | h | h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw.1, h⟩))))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw.1, h⟩))))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hw.1, h⟩)))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw.1, h⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw.1, h⟩)
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right ?_ _)
  refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right ?_ _)
  refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right ?_ _)
  exact Finset.card_union_le _ _

/-- Cover bound grouping the last two neighbourhoods (for §4 (14)'s `≤ 3 + u_ij`). -/
theorem cover_3plus2_le {G : SimpleGraph (Fin 25)} (Q : Finset (Fin 25)) (a b c d e : Fin 25) :
    (Q.filter (fun w => G.Adj a w ∨ G.Adj b w ∨ G.Adj c w ∨ G.Adj d w ∨ G.Adj e w)).card
    ≤ (Q.filter (fun w => G.Adj a w)).card + (Q.filter (fun w => G.Adj b w)).card
      + (Q.filter (fun w => G.Adj c w)).card + (Q.filter (fun w => G.Adj d w ∨ G.Adj e w)).card := by
  have hsub : Q.filter (fun w => G.Adj a w ∨ G.Adj b w ∨ G.Adj c w ∨ G.Adj d w ∨ G.Adj e w)
      ⊆ Q.filter (fun w => G.Adj a w) ∪ Q.filter (fun w => G.Adj b w)
        ∪ Q.filter (fun w => G.Adj c w) ∪ Q.filter (fun w => G.Adj d w ∨ G.Adj e w) := by
    intro w hw; rw [Finset.mem_filter] at hw
    rcases hw.2 with h | h | h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hw.1, h⟩)))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hw.1, h⟩)))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw.1, h⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw.1, Or.inl h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw.1, Or.inr h⟩)
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right ?_ _)
  refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right ?_ _)
  exact Finset.card_union_le _ _


/-- **§4.** Exactly one disjoint `K_5` (`R = H − Q₁` is `K_5`-free) ⇒ contradiction. -/
theorem section4_one {G : SimpleGraph (Fin 25)} {T : Finset (Fin 25)} (ctx : MMCtx G T)
    (pf : PrimFacts) {Q1 : Finset (Fin 25)} (hQ1sub : Q1 ⊆ Finset.univ \ T) (hQ1c : Q1.card = 5)
    (hQ1clq : IsCliqueOn G Q1)
    (hRfree : ∀ Q : Finset (Fin 25), Q ⊆ (Finset.univ \ T) \ Q1 → Q.card = 5 → ¬ IsCliqueOn G Q) :
    False := by
  have hR38 : 38 ≤ edgeCountIn G ((Finset.univ \ T) \ Q1) :=
    edge_R_ge_38 ctx pf hQ1sub hQ1c hQ1clq hRfree
  classical
  set H := Finset.univ \ T with hHdef
  set R := H \ Q1 with hRdef
  -- geometry
  have hQ1H : Q1 ⊆ H := hQ1sub
  have hRH : R ⊆ H := hRdef ▸ Finset.sdiff_subset
  have hHcard : H.card = 20 := by
    rw [hHdef, Finset.card_sdiff_of_subset (Finset.subset_univ T), Finset.card_univ,
      Fintype.card_fin, ctx.hT]
  have hRcard : R.card = 15 := by
    have := Finset.card_sdiff_of_subset hQ1H; rw [hRdef]; omega
  obtain ⟨vt, hvtim⟩ := exists_embedding_image_eq T ctx.hT
  have hvtinj : Function.Injective vt := vt.injective
  have hvtT : ∀ i, vt i ∈ T := fun i => hvtim ▸ Finset.mem_image_of_mem vt (Finset.mem_univ i)
  have hvtnH : ∀ i, vt i ∉ H := fun i h => (Finset.mem_sdiff.mp h).2 (hvtT i)
  have hvtnQ1 : ∀ i, vt i ∉ Q1 := fun i h => hvtnH i (hQ1H h)
  have hvtnR : ∀ i, vt i ∉ R := fun i h => hvtnH i (hRH h)
  have hRnQ1 : ∀ v ∈ R, v ∉ Q1 := fun v hv => (Finset.mem_sdiff.mp hv).2
  have hRnT : ∀ v ∈ R, v ∉ T := fun v hv => (Finset.mem_sdiff.mp (hRH hv)).2
  -- R is K5-free (a K5 ⊆ R is disjoint from Q1)
  have hRfree' : ∀ Q : Finset (Fin 25), Q ⊆ R → Q.card = 5 → ¬ IsCliqueOn G Q :=
    fun Q hQ hQc => hRfree Q hQ hQc
  -- α(R) ≤ 3 (peel k = 1)
  have hαR3 : ∀ S : Finset (Fin 25), S ⊆ R → IsIndep G S → S.card ≤ 3 := by
    intro S hSsub hSindep
    by_contra hc
    push_neg at hc
    obtain ⟨S4, hS4sub, hS4card⟩ := Finset.exists_subset_card_eq (show 4 ≤ S.card by omega)
    refine peel_alpha_bound ctx [Q1] ?_ ?_ ?_
      (fun a ha b hb hab => hSindep a (hS4sub ha) b (hS4sub hb) hab)
      ((hS4sub.trans hSsub).trans hRH) ?_ (by simp [hS4card])
    · intro Q hQ; simp only [List.mem_singleton] at hQ; subst hQ; exact ⟨hQ1clq, hQ1c⟩
    · simp
    · intro Q hQ; simp only [List.mem_singleton] at hQ; subst hQ; exact hQ1H
    · intro Q hQ; simp only [List.mem_singleton] at hQ; subst hQ
      rw [Finset.disjoint_left]; intro x hx hxQ1
      exact hRnQ1 x ((hS4sub.trans hSsub) hx) hxQ1
  -- degree quantities
  set s := edgeCountIn G T with hsdef
  set D := ∑ i : Fin 5, (R.filter (fun v => G.Adj (vt i) v)).card with hDdef
  set a := ∑ i : Fin 5, (Q1.filter (fun v => G.Adj (vt i) v)).card with hadef
  set p := ∑ w ∈ R, (Q1.filter (fun v => G.Adj w v)).card with hpdef
  -- e(H) = 10 + e(R) + p ;  crossCount = a + D
  have heQ1 : edgeCountIn G Q1 = 10 := by
    rw [edgeCountIn_eq_choose_of_clique G hQ1clq, hQ1c]; rfl
  have hH_eq : edgeCountIn G H = edgeCountIn G Q1 + edgeCountIn G R + p := by
    have hd : Disjoint Q1 R := by
      rw [hRdef]; exact Finset.disjoint_sdiff
    have hu : Q1 ∪ R = H := by rw [hRdef, Finset.union_comm]; exact Finset.sdiff_union_of_subset hQ1H
    have h := edgeCountIn_union_disjoint_eq G hd; rw [hu] at h; rw [h, hpdef]
  have hcross_eq : crossCount G T = a + D := by
    have hreindex : crossCount G T = ∑ i : Fin 5, (H.filter (fun v => G.Adj (vt i) v)).card := by
      unfold crossCount
      rw [← hHdef, ← hvtim, Finset.sum_image (fun a _ b _ h => hvtinj h)]
    have hHsplit_i : ∀ i : Fin 5, (H.filter (fun v => G.Adj (vt i) v)).card
        = (Q1.filter (fun v => G.Adj (vt i) v)).card + (R.filter (fun v => G.Adj (vt i) v)).card := by
      intro i
      have hu : H = Q1 ∪ R := by
        rw [hRdef, Finset.union_comm]; exact (Finset.sdiff_union_of_subset hQ1H).symm
      have hd : Disjoint Q1 R := by rw [hRdef]; exact Finset.disjoint_sdiff
      rw [hu, deg_split hd (vt i)]
    rw [hreindex, hadef, hDdef, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => hHsplit_i i)
  -- budget (13): p + a + D + s ≤ 12
  have hbudget : p + a + D + s ≤ 12 := by
    have hsplit := edgeCountIn_univ_split G T
    rw [← hHdef, ← hsdef, hcross_eq, hH_eq, heQ1] at hsplit
    have h60 := ctx.he60
    omega

  -- residual bound: an α ≤ 2 subset of R has ≤ 10 vertices (nonex11)
  have hres_bound : ∀ res : Finset (Fin 25), res ⊆ R →
      (∀ S : Finset (Fin 25), S ⊆ res → IsIndep G S → S.card ≤ 2) → res.card ≤ 10 := by
    intro res _ hα2
    by_contra hc
    push_neg at hc
    obtain ⟨W, hWsub, hWc⟩ := Finset.exists_subset_card_eq (show 11 ≤ res.card by omega)
    exact nonex11_transport pf ctx.hcap hWc (fun S hS hind => hα2 S (hS.trans hWsub) hind)
  -- indeg into Q1 ≤ 1 for R-vertices and for t_i
  have hRindeg : ∀ v ∈ R, (Q1.filter (fun w => G.Adj v w)).card ≤ 1 :=
    fun v hv => indeg_clique5_le_one G ctx.hcap hQ1clq hQ1c (hRnQ1 v hv)
  have haQ1 : ∀ i : Fin 5, (Q1.filter (fun w => G.Adj (vt i) w)).card ≤ 1 :=
    fun i => indeg_clique5_le_one G ctx.hcap hQ1clq hQ1c (hvtnQ1 i)
  -- extract an independent triple from any α ≥ 3 residual and derive the 5-set / cover setup
  -- (15) holds for EVERY F-edge:  d_i + d_j + p ≥ 5.
  have hcaseb : ∀ i j : Fin 5, i ≠ j → ¬ G.Adj (vt i) (vt j) →
      5 ≤ (R.filter (fun v => G.Adj (vt i) v)).card + (R.filter (fun v => G.Adj (vt j) v)).card + p := by
    intro i j hij hnadj
    set resb := R.filter (fun v => ¬ G.Adj (vt i) v ∧ ¬ G.Adj (vt j) v
      ∧ (Q1.filter (fun w => G.Adj v w)).card = 0) with hresbdef
    have hresbR : resb ⊆ R := Finset.filter_subset _ _
    have hdec : ∀ v ∈ resb, ¬ G.Adj (vt i) v ∧ ¬ G.Adj (vt j) v
        ∧ (Q1.filter (fun w => G.Adj v w)).card = 0 := fun v hv => (Finset.mem_filter.mp hv).2
    have hα2 : ∀ S : Finset (Fin 25), S ⊆ resb → IsIndep G S → S.card ≤ 2 := by
      intro S hSsub hSindep
      by_contra hc3
      push_neg at hc3
      obtain ⟨S3, hS3sub, hS3c⟩ := Finset.exists_subset_card_eq (show 3 ≤ S.card by omega)
      obtain ⟨s1, s2, s3, h12, h13, h23, hSeq⟩ := Finset.card_eq_three.mp hS3c
      have i1 : s1 ∈ S3 := by rw [hSeq]; simp
      have i2 : s2 ∈ S3 := by rw [hSeq]; simp
      have i3 : s3 ∈ S3 := by rw [hSeq]; simp
      have m1 := hSsub (hS3sub i1)
      have m2 := hSsub (hS3sub i2)
      have m3 := hSsub (hS3sub i3)
      obtain ⟨n1i, n1j, z1⟩ := hdec s1 m1
      obtain ⟨n2i, n2j, z2⟩ := hdec s2 m2
      obtain ⟨n3i, n3j, z3⟩ := hdec s3 m3
      have hs1R : s1 ∈ R := hresbR m1
      have hs2R : s2 ∈ R := hresbR m2
      have hs3R : s3 ∈ R := hresbR m3
      have hSindep3 : IsIndep G S3 := fun x hx y hy hxy => hSindep x (hS3sub hx) y (hS3sub hy) hxy
      have hns12 : ¬ G.Adj s1 s2 := hSindep3 s1 i1 s2 i2 h12
      have hns13 : ¬ G.Adj s1 s3 := hSindep3 s1 i1 s3 i3 h13
      have hns23 : ¬ G.Adj s2 s3 := hSindep3 s2 i2 s3 i3 h23
      -- cover ≤ 2: the s_k have no Q1-neighbour
      have hcover : (Q1.filter (fun w => G.Adj s1 w ∨ G.Adj s2 w ∨ G.Adj s3 w
          ∨ G.Adj (vt i) w ∨ G.Adj (vt j) w)).card ≤ 4 := by
        have h1 : (Q1.filter (fun w => G.Adj s1 w)).card = 0 := z1
        have h2 : (Q1.filter (fun w => G.Adj s2 w)).card = 0 := z2
        have h3 : (Q1.filter (fun w => G.Adj s3 w)).card = 0 := z3
        have := cover5_le (G := G) Q1 s1 s2 s3 (vt i) (vt j)
        have hi := haQ1 i; have hj := haQ1 j
        omega
      exact indep5_missedQ_false ctx.hα5 hQ1c h12 h13 (by rintro rfl; exact hvtnR i hs1R)
        (by rintro rfl; exact hvtnR j hs1R) h23 (by rintro rfl; exact hvtnR i hs2R) (by rintro rfl; exact hvtnR j hs2R)
        (by rintro rfl; exact hvtnR i hs3R) (by rintro rfl; exact hvtnR j hs3R) (fun h => hij (hvtinj h))
        hns12 hns13 (fun h => n1i (G.symm h)) (fun h => n1j (G.symm h))
        hns23 (fun h => n2i (G.symm h)) (fun h => n2j (G.symm h))
        (fun h => n3i (G.symm h)) (fun h => n3j (G.symm h)) hnadj
        (hRnQ1 s1 hs1R) (hRnQ1 s2 hs2R) (hRnQ1 s3 hs3R) (hvtnQ1 i) (hvtnQ1 j) hcover
    have hle10 := hres_bound resb hresbR hα2
    -- |R ∖ resb| ≥ 5, and ≤ d_i + d_j + p
    have hpartR := Finset.card_filter_add_card_filter_not (s := R)
      (p := fun v => ¬ G.Adj (vt i) v ∧ ¬ G.Adj (vt j) v ∧ (Q1.filter (fun w => G.Adj v w)).card = 0)
    rw [hRcard] at hpartR
    -- the "bad" filter ⊆ Z_i ∪ Z_j ∪ P
    have hbad : (R.filter (fun v => ¬ (¬ G.Adj (vt i) v ∧ ¬ G.Adj (vt j) v
        ∧ (Q1.filter (fun w => G.Adj v w)).card = 0))).card
        ≤ (R.filter (fun v => G.Adj (vt i) v)).card + (R.filter (fun v => G.Adj (vt j) v)).card + p := by
      have hsub : R.filter (fun v => ¬ (¬ G.Adj (vt i) v ∧ ¬ G.Adj (vt j) v
          ∧ (Q1.filter (fun w => G.Adj v w)).card = 0))
          ⊆ R.filter (fun v => G.Adj (vt i) v) ∪ R.filter (fun v => G.Adj (vt j) v)
            ∪ R.filter (fun v => 0 < (Q1.filter (fun w => G.Adj v w)).card) := by
        intro v hv; rw [Finset.mem_filter] at hv
        obtain ⟨hvR, hvn⟩ := hv
        push_neg at hvn
        by_cases hi : G.Adj (vt i) v
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hvR, hi⟩))
        · by_cases hj : G.Adj (vt j) v
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hvR, hj⟩))
          · have := hvn hi hj
            exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hvR, Nat.pos_of_ne_zero this⟩)
      have hPp : (R.filter (fun v => 0 < (Q1.filter (fun w => G.Adj v w)).card)).card ≤ p := by
        rw [hpdef]
        calc (R.filter (fun v => 0 < (Q1.filter (fun w => G.Adj v w)).card)).card
            = ∑ _v ∈ R.filter (fun v => 0 < (Q1.filter (fun w => G.Adj v w)).card), 1 := by
              rw [Finset.sum_const, smul_eq_mul, mul_one]
          _ ≤ ∑ v ∈ R.filter (fun v => 0 < (Q1.filter (fun w => G.Adj v w)).card),
              (Q1.filter (fun w => G.Adj v w)).card :=
              Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2)
          _ ≤ ∑ v ∈ R, (Q1.filter (fun w => G.Adj v w)).card :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun _ _ _ => Nat.zero_le _)
      have h3 := Finset.card_le_card hsub
      have h1 := Finset.card_union_le (R.filter (fun v => G.Adj (vt i) v)
        ∪ R.filter (fun v => G.Adj (vt j) v))
        (R.filter (fun v => 0 < (Q1.filter (fun w => G.Adj v w)).card))
      have h2 := Finset.card_union_le (R.filter (fun v => G.Adj (vt i) v))
        (R.filter (fun v => G.Adj (vt j) v))
      omega
    rw [← hresbdef] at hpartR
    omega
  -- (14) case (a): if q_i, q_j not two distinct vertices, d_i + d_j ≥ 5.
  have hcasea : ∀ i j : Fin 5, i ≠ j → ¬ G.Adj (vt i) (vt j) →
      (Q1.filter (fun w => G.Adj (vt i) w ∨ G.Adj (vt j) w)).card ≤ 1 →
      5 ≤ (R.filter (fun v => G.Adj (vt i) v)).card + (R.filter (fun v => G.Adj (vt j) v)).card := by
    intro i j hij hnadj huQ
    set resa := R.filter (fun v => ¬ G.Adj (vt i) v ∧ ¬ G.Adj (vt j) v) with hresadef
    have hresaR : resa ⊆ R := Finset.filter_subset _ _
    have hdec : ∀ v ∈ resa, ¬ G.Adj (vt i) v ∧ ¬ G.Adj (vt j) v :=
      fun v hv => (Finset.mem_filter.mp hv).2
    have hα2 : ∀ S : Finset (Fin 25), S ⊆ resa → IsIndep G S → S.card ≤ 2 := by
      intro S hSsub hSindep
      by_contra hc3; push_neg at hc3
      obtain ⟨S3, hS3sub, hS3c⟩ := Finset.exists_subset_card_eq (show 3 ≤ S.card by omega)
      obtain ⟨s1, s2, s3, h12, h13, h23, hSeq⟩ := Finset.card_eq_three.mp hS3c
      have i1 : s1 ∈ S3 := by rw [hSeq]; simp
      have i2 : s2 ∈ S3 := by rw [hSeq]; simp
      have i3 : s3 ∈ S3 := by rw [hSeq]; simp
      have m1 := hSsub (hS3sub i1)
      have m2 := hSsub (hS3sub i2)
      have m3 := hSsub (hS3sub i3)
      obtain ⟨n1i, n1j⟩ := hdec s1 m1
      obtain ⟨n2i, n2j⟩ := hdec s2 m2
      obtain ⟨n3i, n3j⟩ := hdec s3 m3
      have hs1R : s1 ∈ R := hresaR m1
      have hs2R : s2 ∈ R := hresaR m2
      have hs3R : s3 ∈ R := hresaR m3
      have hSindep3 : IsIndep G S3 := fun x hx y hy hxy => hSindep x (hS3sub hx) y (hS3sub hy) hxy
      have hns12 : ¬ G.Adj s1 s2 := hSindep3 s1 i1 s2 i2 h12
      have hns13 : ¬ G.Adj s1 s3 := hSindep3 s1 i1 s3 i3 h13
      have hns23 : ¬ G.Adj s2 s3 := hSindep3 s2 i2 s3 i3 h23
      have hcover : (Q1.filter (fun w => G.Adj s1 w ∨ G.Adj s2 w ∨ G.Adj s3 w
          ∨ G.Adj (vt i) w ∨ G.Adj (vt j) w)).card ≤ 4 := by
        have := cover_3plus2_le (G := G) Q1 s1 s2 s3 (vt i) (vt j)
        have b1 := hRindeg s1 hs1R; have b2 := hRindeg s2 hs2R; have b3 := hRindeg s3 hs3R
        omega
      exact indep5_missedQ_false ctx.hα5 hQ1c h12 h13 (by rintro rfl; exact hvtnR i hs1R)
        (by rintro rfl; exact hvtnR j hs1R) h23 (by rintro rfl; exact hvtnR i hs2R) (by rintro rfl; exact hvtnR j hs2R)
        (by rintro rfl; exact hvtnR i hs3R) (by rintro rfl; exact hvtnR j hs3R) (fun h => hij (hvtinj h))
        hns12 hns13 (fun h => n1i (G.symm h)) (fun h => n1j (G.symm h))
        hns23 (fun h => n2i (G.symm h)) (fun h => n2j (G.symm h))
        (fun h => n3i (G.symm h)) (fun h => n3j (G.symm h)) hnadj
        (hRnQ1 s1 hs1R) (hRnQ1 s2 hs2R) (hRnQ1 s3 hs3R) (hvtnQ1 i) (hvtnQ1 j) hcover
    have hle10 := hres_bound resa hresaR hα2
    have hpartR := Finset.card_filter_add_card_filter_not (s := R)
      (p := fun v => ¬ G.Adj (vt i) v ∧ ¬ G.Adj (vt j) v)
    rw [hRcard] at hpartR
    have hbad : (R.filter (fun v => ¬ (¬ G.Adj (vt i) v ∧ ¬ G.Adj (vt j) v))).card
        ≤ (R.filter (fun v => G.Adj (vt i) v)).card + (R.filter (fun v => G.Adj (vt j) v)).card := by
      have hsub : R.filter (fun v => ¬ (¬ G.Adj (vt i) v ∧ ¬ G.Adj (vt j) v))
          ⊆ R.filter (fun v => G.Adj (vt i) v) ∪ R.filter (fun v => G.Adj (vt j) v) := by
        intro v hv; rw [Finset.mem_filter] at hv
        obtain ⟨hvR, hvn⟩ := hv
        push_neg at hvn
        by_cases hi : G.Adj (vt i) v
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hvR, hi⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hvR, hvn hi⟩)
      exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    rw [← hresadef] at hpartR
    omega
  -- uniform per-edge bound for the count: 5 ≤ d_i + d_j + p·[case b]
  have hedge : ∀ i j : Fin 5, i ≠ j → ¬ G.Adj (vt i) (vt j) →
      5 ≤ (R.filter (fun v => G.Adj (vt i) v)).card + (R.filter (fun v => G.Adj (vt j) v)).card
        + p * (if 2 ≤ (Q1.filter (fun w => G.Adj (vt i) w ∨ G.Adj (vt j) w)).card
            then 1 else 0) := by
    intro i j hij hnadj
    by_cases hcb : 2 ≤ (Q1.filter (fun w => G.Adj (vt i) w ∨ G.Adj (vt j) w)).card
    · rw [if_pos hcb, mul_one]; exact hcaseb i j hij hnadj
    · rw [if_neg hcb, mul_zero, add_zero]
      exact hcasea i j hij hnadj (by omega)
  -- ordered non-edges and case-b edges
  set NEpairs := Finset.univ.filter (fun q : Fin 5 × Fin 5 =>
    q.1 ≠ q.2 ∧ ¬ G.Adj (vt q.1) (vt q.2)) with hNEdef
  set CBpairs := NEpairs.filter (fun q =>
    2 ≤ (Q1.filter (fun w => G.Adj (vt q.1) w ∨ G.Adj (vt q.2) w)).card) with hCBdef
  -- per-edge summed:  5·|NE| ≤ ∑(dR.1+dR.2) + p·|CB|
  have hsum5 : 5 * NEpairs.card ≤ (∑ q ∈ NEpairs, ((R.filter (fun v => G.Adj (vt q.1) v)).card
      + (R.filter (fun v => G.Adj (vt q.2) v)).card)) + p * CBpairs.card := by
    have hexp : ∀ q ∈ NEpairs, 5 ≤ (R.filter (fun v => G.Adj (vt q.1) v)).card
        + (R.filter (fun v => G.Adj (vt q.2) v)).card
        + p * (if 2 ≤ (Q1.filter (fun w => G.Adj (vt q.1) w ∨ G.Adj (vt q.2) w)).card
            then 1 else 0) := by
      intro q hq; rw [hNEdef, Finset.mem_filter] at hq; exact hedge q.1 q.2 hq.2.1 hq.2.2
    calc 5 * NEpairs.card = ∑ _q ∈ NEpairs, 5 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ q ∈ NEpairs, ((R.filter (fun v => G.Adj (vt q.1) v)).card
          + (R.filter (fun v => G.Adj (vt q.2) v)).card
          + p * (if 2 ≤ (Q1.filter (fun w => G.Adj (vt q.1) w ∨ G.Adj (vt q.2) w)).card
              then 1 else 0)) := Finset.sum_le_sum hexp
      _ = (∑ q ∈ NEpairs, ((R.filter (fun v => G.Adj (vt q.1) v)).card
          + (R.filter (fun v => G.Adj (vt q.2) v)).card))
          + ∑ q ∈ NEpairs, p * (if 2 ≤ (Q1.filter (fun w => G.Adj (vt q.1) w ∨ G.Adj (vt q.2) w)).card
              then 1 else 0) := Finset.sum_add_distrib
      _ = (∑ q ∈ NEpairs, ((R.filter (fun v => G.Adj (vt q.1) v)).card
          + (R.filter (fun v => G.Adj (vt q.2) v)).card)) + p * CBpairs.card := by
          rw [← Finset.mul_sum, ← Finset.card_filter, ← hCBdef]
  -- offdiag bound: ∑(dR.1+dR.2) ≤ 8·D
  have h8D : (∑ q ∈ NEpairs, ((R.filter (fun v => G.Adj (vt q.1) v)).card
      + (R.filter (fun v => G.Adj (vt q.2) v)).card)) ≤ 8 * D := by
    have hNEoff : NEpairs ⊆ Finset.univ.filter (fun q : Fin 5 × Fin 5 => q.1 ≠ q.2) := by
      intro q hq; rw [hNEdef, Finset.mem_filter] at hq
      exact Finset.mem_filter.mpr ⟨hq.1, hq.2.1⟩
    have hfst : (∑ q ∈ Finset.univ.filter (fun q : Fin 5 × Fin 5 => q.1 ≠ q.2),
        (R.filter (fun v => G.Adj (vt q.1) v)).card) = 4 * D := by
      rw [hDdef]; exact sum_offdiag_fst (fun i => (R.filter (fun v => G.Adj (vt i) v)).card)
    have hsnd : (∑ q ∈ Finset.univ.filter (fun q : Fin 5 × Fin 5 => q.1 ≠ q.2),
        (R.filter (fun v => G.Adj (vt q.2) v)).card) = 4 * D := by
      rw [hDdef]; exact sum_offdiag_snd (fun i => (R.filter (fun v => G.Adj (vt i) v)).card)
    have hsub := Finset.sum_le_sum_of_subset_of_nonneg hNEoff
      (f := fun q : Fin 5 × Fin 5 => (R.filter (fun v => G.Adj (vt q.1) v)).card
        + (R.filter (fun v => G.Adj (vt q.2) v)).card) (fun _ _ _ => Nat.zero_le _)
    have hoffeq : (∑ q ∈ Finset.univ.filter (fun q : Fin 5 × Fin 5 => q.1 ≠ q.2),
        ((R.filter (fun v => G.Adj (vt q.1) v)).card
          + (R.filter (fun v => G.Adj (vt q.2) v)).card)) = 8 * D := by
      rw [Finset.sum_add_distrib, hfst, hsnd]; ring
    exact le_trans hsub (le_of_eq hoffeq)
  -- |NE| + 2s = 20
  have hNEcount : NEpairs.card + 2 * s = 20 := by
    have hoff20 : (Finset.univ.filter (fun q : Fin 5 × Fin 5 => q.1 ≠ q.2)).card = 20 := by decide
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter (fun q : Fin 5 × Fin 5 => q.1 ≠ q.2))
      (p := fun q => G.Adj (vt q.1) (vt q.2))
    rw [hoff20] at hsplit
    have hNEeq : (Finset.univ.filter (fun q : Fin 5 × Fin 5 => q.1 ≠ q.2)).filter
        (fun q => ¬ G.Adj (vt q.1) (vt q.2)) = NEpairs := by rw [hNEdef, Finset.filter_filter]
    have hAeq : ((Finset.univ.filter (fun q : Fin 5 × Fin 5 => q.1 ≠ q.2)).filter
        (fun q => G.Adj (vt q.1) (vt q.2))).card = 2 * s := by
      have hall : (Finset.univ.filter (fun q : Fin 5 × Fin 5 => q.1 ≠ q.2)).filter
          (fun q => G.Adj (vt q.1) (vt q.2))
          = Finset.univ.filter (fun q : Fin 5 × Fin 5 => G.Adj (vt q.1) (vt q.2)) := by
        rw [Finset.filter_filter]; apply Finset.filter_congr; intro q _
        exact ⟨fun h => h.2, fun h => ⟨fun he => G.ne_of_adj h (by rw [he]), h⟩⟩
      rw [hall, Finset.card_filter, Fintype.sum_prod_type]
      show (∑ x : Fin 5, ∑ y : Fin 5, (if G.Adj (vt x) (vt y) then 1 else 0)) = 2 * s
      have h := edgeCount_five (G := G) hvtinj
      rw [hvtim] at h; rw [← h, hsdef]
    rw [hNEeq] at hsplit; rw [hAeq] at hsplit; omega
  -- |CB| ≤ |NE|  (⊆)
  have hCBNE : CBpairs.card ≤ NEpairs.card := Finset.card_le_card (Finset.filter_subset _ _)
  -- marked vertices; |Marked| = a and |CB| + a ≤ a·a
  set Marked := Finset.univ.filter (fun i : Fin 5 => 0 < (Q1.filter (fun w => G.Adj (vt i) w)).card)
    with hMkdef
  have haMarked : Marked.card = a := by
    rw [hadef, hMkdef]
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ)
      (fun i => 0 < (Q1.filter (fun w => G.Adj (vt i) w)).card)
      (fun i => (Q1.filter (fun w => G.Adj (vt i) w)).card)]
    have hz : (∑ i ∈ Finset.univ.filter (fun i => ¬ 0 < (Q1.filter (fun w => G.Adj (vt i) w)).card),
        (Q1.filter (fun w => G.Adj (vt i) w)).card) = 0 := by
      apply Finset.sum_eq_zero; intro i hi
      have := (Finset.mem_filter.mp hi).2; omega
    have ho : (∑ i ∈ Finset.univ.filter (fun i => 0 < (Q1.filter (fun w => G.Adj (vt i) w)).card),
        (Q1.filter (fun w => G.Adj (vt i) w)).card)
        = (Finset.univ.filter (fun i => 0 < (Q1.filter (fun w => G.Adj (vt i) w)).card)).card := by
      rw [Finset.card_eq_sum_ones]; apply Finset.sum_congr rfl; intro i hi
      have h0 := (Finset.mem_filter.mp hi).2; have h1 := haQ1 i; omega
    rw [hz, ho, add_zero]
  have hCBaa : CBpairs.card + a ≤ a * a := by
    have hsub : CBpairs ⊆ (Marked ×ˢ Marked).filter (fun q => ¬ q.1 = q.2) := by
      intro q hq
      rw [hCBdef, Finset.mem_filter, hNEdef, Finset.mem_filter] at hq
      obtain ⟨⟨_, hne, _⟩, hge2⟩ := hq
      have hu : (Q1.filter (fun w => G.Adj (vt q.1) w ∨ G.Adj (vt q.2) w)).card
          ≤ (Q1.filter (fun w => G.Adj (vt q.1) w)).card
            + (Q1.filter (fun w => G.Adj (vt q.2) w)).card := by
        refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
        intro w hw; rw [Finset.mem_filter] at hw
        rcases hw.2 with h | h
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw.1, h⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw.1, h⟩)
      have b1 := haQ1 q.1; have b2 := haQ1 q.2
      rw [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩, hne⟩
    have hoff := offdiag_prod_card Marked
    have := Finset.card_le_card hsub
    rw [haMarked] at hoff
    omega
  -- assemble & eliminate
  have hale5 : a ≤ 5 := by
    rw [hadef]
    calc (∑ i : Fin 5, (Q1.filter (fun w => G.Adj (vt i) w)).card) ≤ ∑ _i : Fin 5, 1 :=
          Finset.sum_le_sum (fun i _ => haQ1 i)
      _ = 5 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  have hs6 : s ≤ 6 := by rw [hsdef]; exact ctx.hsT
  have hcond : 10 * (10 - s) ≤ 8 * ((10 - s) + 2 - p - a) + p * CBpairs.card := by
    have hNE2 : NEpairs.card = 2 * (10 - s) := by omega
    have hD : D ≤ (10 - s) + 2 - p - a := by omega
    calc 10 * (10 - s) = 5 * NEpairs.card := by rw [hNE2]; ring
      _ ≤ (∑ q ∈ NEpairs, ((R.filter (fun v => G.Adj (vt q.1) v)).card
          + (R.filter (fun v => G.Adj (vt q.2) v)).card)) + p * CBpairs.card := hsum5
      _ ≤ 8 * D + p * CBpairs.card := Nat.add_le_add_right h8D _
      _ ≤ 8 * ((10 - s) + 2 - p - a) + p * CBpairs.card :=
          Nat.add_le_add_right (by omega) _
  have hdisj := sec4_elim a p (10 - s) CBpairs.card hale5 (by omega) (by omega) (by omega)
    (by omega) (by omega) hCBaa hcond
  -- dispatch to §4.1 / (4,5,10)-exclusion / §4.2
  rcases hdisj with hpa | ⟨ha5, hp4, hr10⟩ | ⟨ha5, hp5, hp7⟩
  · -- §4.1:  p + a ≤ 1.  Every F-edge is case (a) (a ≤ 1 ⇒ u_ij ≤ 1).
    have hstrong : ∀ i j : Fin 5, i ≠ j → ¬ G.Adj (vt i) (vt j) →
        5 ≤ (R.filter (fun v => G.Adj (vt i) v)).card + (R.filter (fun v => G.Adj (vt j) v)).card := by
      intro i j hij hnadj
      refine hcasea i j hij hnadj ?_
      have huQ : (Q1.filter (fun w => G.Adj (vt i) w ∨ G.Adj (vt j) w)).card
          ≤ (Q1.filter (fun w => G.Adj (vt i) w)).card
            + (Q1.filter (fun w => G.Adj (vt j) w)).card := by
        refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
        intro w hw; rw [Finset.mem_filter] at hw; rcases hw.2 with h | h
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw.1, h⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw.1, h⟩)
      have hpair : (Q1.filter (fun w => G.Adj (vt i) w)).card
          + (Q1.filter (fun w => G.Adj (vt j) w)).card ≤ a := by
        rw [hadef]
        have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ({i, j} : Finset (Fin 5)))
          (f := fun k => (Q1.filter (fun w => G.Adj (vt k) w)).card) (fun _ _ _ => Nat.zero_le _)
        rwa [Finset.sum_pair hij] at this
      omega
    -- Boolean bridge for the F-structure
    have hbr : (decide (G.Adj (vt 0) (vt 1))).toNat + (decide (G.Adj (vt 0) (vt 2))).toNat
        + (decide (G.Adj (vt 0) (vt 3))).toNat + (decide (G.Adj (vt 0) (vt 4))).toNat
        + (decide (G.Adj (vt 1) (vt 2))).toNat + (decide (G.Adj (vt 1) (vt 3))).toNat
        + (decide (G.Adj (vt 1) (vt 4))).toNat + (decide (G.Adj (vt 2) (vt 3))).toNat
        + (decide (G.Adj (vt 2) (vt 4))).toNat + (decide (G.Adj (vt 3) (vt 4))).toNat = s := by
      have he := s_expand (G := G) hvtinj
      rw [hvtim, ← hsdef] at he
      rw [he]; simp only [toNat_decide']
    have close2_4 : ∀ i j k l : Fin 5, (i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l) →
        ¬ G.Adj (vt i) (vt j) → ¬ G.Adj (vt k) (vt l) → 10 ≤ D := by
      rintro i j k l ⟨hij, hik, hil, hjk, hjl, hkl⟩ hnij hnkl
      have h1 := hstrong i j hij hnij
      have h2 := hstrong k l hkl hnkl
      have hle : ∑ x ∈ ({i, j, k, l} : Finset (Fin 5)), (R.filter (fun v => G.Adj (vt x) v)).card
          ≤ D := by rw [hDdef]; exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      rw [Finset.sum_insert (by simp [hij, hik, hil]), Finset.sum_insert (by simp [hjk, hjl]),
        Finset.sum_insert (by simp [hkl]), Finset.sum_singleton] at hle
      omega
    have hDbig : ∀ i j k l : Fin 5, (i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l) →
        ¬ G.Adj (vt i) (vt j) → ¬ G.Adj (vt k) (vt l) → False := by
      intro i j k l hd hnij hnkl
      have hD10 := close2_4 i j k l hd hnij hnkl
      have hs2 : s ≤ 2 := by omega
      have hDexp : D = (R.filter (fun v => G.Adj (vt 0) v)).card
          + (R.filter (fun v => G.Adj (vt 1) v)).card + (R.filter (fun v => G.Adj (vt 2) v)).card
          + (R.filter (fun v => G.Adj (vt 3) v)).card + (R.filter (fun v => G.Adj (vt 4) v)).card := by
        rw [hDdef, Fin.sum_univ_five]
      have hcyc := hbr ▸ hs2
      have hf := fiveCycle _ _ _ _ _ _ _ _ _ _ hcyc
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        or_assoc, and_assoc] at hf
      rcases hf with ⟨c1,c2,c3,c4,c5⟩|⟨c1,c2,c3,c4,c5⟩|⟨c1,c2,c3,c4,c5⟩|⟨c1,c2,c3,c4,c5⟩|⟨c1,c2,c3,c4,c5⟩|⟨c1,c2,c3,c4,c5⟩|⟨c1,c2,c3,c4,c5⟩|⟨c1,c2,c3,c4,c5⟩|⟨c1,c2,c3,c4,c5⟩|⟨c1,c2,c3,c4,c5⟩|⟨c1,c2,c3,c4,c5⟩|⟨c1,c2,c3,c4,c5⟩
      · have a1 := hstrong 0 1 (by decide) c1; have a2 := hstrong 1 3 (by decide) c2
        have a3 := hstrong 3 4 (by decide) c3; have a4 := hstrong 2 4 (by decide) c4
        have a5 := hstrong 0 2 (by decide) c5; omega
      · have a1 := hstrong 0 1 (by decide) c1; have a2 := hstrong 1 4 (by decide) c2
        have a3 := hstrong 3 4 (by decide) c3; have a4 := hstrong 2 3 (by decide) c4
        have a5 := hstrong 0 2 (by decide) c5; omega
      · have a1 := hstrong 0 1 (by decide) c1; have a2 := hstrong 1 2 (by decide) c2
        have a3 := hstrong 2 4 (by decide) c3; have a4 := hstrong 3 4 (by decide) c4
        have a5 := hstrong 0 3 (by decide) c5; omega
      · have a1 := hstrong 0 1 (by decide) c1; have a2 := hstrong 1 4 (by decide) c2
        have a3 := hstrong 2 4 (by decide) c3; have a4 := hstrong 2 3 (by decide) c4
        have a5 := hstrong 0 3 (by decide) c5; omega
      · have a1 := hstrong 0 1 (by decide) c1; have a2 := hstrong 1 2 (by decide) c2
        have a3 := hstrong 2 3 (by decide) c3; have a4 := hstrong 3 4 (by decide) c4
        have a5 := hstrong 0 4 (by decide) c5; omega
      · have a1 := hstrong 0 1 (by decide) c1; have a2 := hstrong 1 3 (by decide) c2
        have a3 := hstrong 2 3 (by decide) c3; have a4 := hstrong 2 4 (by decide) c4
        have a5 := hstrong 0 4 (by decide) c5; omega
      · have a1 := hstrong 0 2 (by decide) c1; have a2 := hstrong 1 2 (by decide) c2
        have a3 := hstrong 1 4 (by decide) c3; have a4 := hstrong 3 4 (by decide) c4
        have a5 := hstrong 0 3 (by decide) c5; omega
      · have a1 := hstrong 0 2 (by decide) c1; have a2 := hstrong 2 4 (by decide) c2
        have a3 := hstrong 1 4 (by decide) c3; have a4 := hstrong 1 3 (by decide) c4
        have a5 := hstrong 0 3 (by decide) c5; omega
      · have a1 := hstrong 0 2 (by decide) c1; have a2 := hstrong 1 2 (by decide) c2
        have a3 := hstrong 1 3 (by decide) c3; have a4 := hstrong 3 4 (by decide) c4
        have a5 := hstrong 0 4 (by decide) c5; omega
      · have a1 := hstrong 0 2 (by decide) c1; have a2 := hstrong 2 3 (by decide) c2
        have a3 := hstrong 1 3 (by decide) c3; have a4 := hstrong 1 4 (by decide) c4
        have a5 := hstrong 0 4 (by decide) c5; omega
      · have a1 := hstrong 0 3 (by decide) c1; have a2 := hstrong 1 3 (by decide) c2
        have a3 := hstrong 1 2 (by decide) c3; have a4 := hstrong 2 4 (by decide) c4
        have a5 := hstrong 0 4 (by decide) c5; omega
      · have a1 := hstrong 0 3 (by decide) c1; have a2 := hstrong 2 3 (by decide) c2
        have a3 := hstrong 1 2 (by decide) c3; have a4 := hstrong 1 4 (by decide) c4
        have a5 := hstrong 0 4 (by decide) c5; omega
    -- the star endgame (informal §4.1 second half): F=K_{1,4}, center c has d_c ≥ 5,
    -- a zero-leaf gives α(R−N_R(c))≤2, then X=R+t_c (α≤3, e≤44) is K₅-free (e≥ℓ16=46, contra)
    -- or has a K₅-through-t_c whose deletion leaves an 11-vtx α≤2 cap-11 set (nonex11).
    have hstarcase : ∀ c : Fin 5, (∀ i : Fin 5, i ≠ c → ¬ G.Adj (vt c) (vt i)) → s = 6 → False := by
      intro c hc hs6
      -- 4 star edges give 3·d_c + D ≥ 20, and the budget gives D ≤ 6, so d_c ≥ 5.
      have herc : (Finset.univ.erase c).card = 4 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
      have hsum20 : (20 : ℕ) ≤ ∑ i ∈ Finset.univ.erase c,
          ((R.filter (fun v => G.Adj (vt c) v)).card + (R.filter (fun v => G.Adj (vt i) v)).card) := by
        calc (20 : ℕ) = ∑ _i ∈ Finset.univ.erase c, 5 := by rw [Finset.sum_const, herc, smul_eq_mul]
          _ ≤ _ := Finset.sum_le_sum (fun i hi =>
              hstrong c i (Ne.symm (Finset.ne_of_mem_erase hi)) (hc i (Finset.ne_of_mem_erase hi)))
      have hsum_split : (∑ i ∈ Finset.univ.erase c,
          ((R.filter (fun v => G.Adj (vt c) v)).card + (R.filter (fun v => G.Adj (vt i) v)).card))
          = 4 * (R.filter (fun v => G.Adj (vt c) v)).card
            + ∑ i ∈ Finset.univ.erase c, (R.filter (fun v => G.Adj (vt i) v)).card := by
        rw [Finset.sum_add_distrib, Finset.sum_const, herc]; ring
      have hDerase : D = (R.filter (fun v => G.Adj (vt c) v)).card
          + ∑ i ∈ Finset.univ.erase c, (R.filter (fun v => G.Adj (vt i) v)).card := by
        rw [hDdef, ← Finset.sum_erase_add _ _ (Finset.mem_univ c)]; ring
      have hD6 : D ≤ 6 := by omega
      have hdc5 : 5 ≤ (R.filter (fun v => G.Adj (vt c) v)).card := by omega
      -- a zero-leaf ℓ ≠ c
      have hℓ : ∃ ℓ ∈ Finset.univ.erase c, (R.filter (fun v => G.Adj (vt ℓ) v)).card = 0 := by
        by_contra hcon
        push_neg at hcon
        have : (4 : ℕ) ≤ ∑ i ∈ Finset.univ.erase c, (R.filter (fun v => G.Adj (vt i) v)).card := by
          calc (4 : ℕ) = ∑ _i ∈ Finset.univ.erase c, 1 := by rw [Finset.sum_const, herc, smul_eq_mul]
            _ ≤ _ := Finset.sum_le_sum (fun i hi => Nat.one_le_iff_ne_zero.mpr (hcon i hi))
        omega
      obtain ⟨ℓ, hℓe, hℓ0⟩ := hℓ
      have hℓc : ℓ ≠ c := Finset.ne_of_mem_erase hℓe
      have hℓno : ∀ v ∈ R, ¬ G.Adj (vt ℓ) v := by
        intro v hv hadj
        have : v ∈ R.filter (fun v => G.Adj (vt ℓ) v) := Finset.mem_filter.mpr ⟨hv, hadj⟩
        rw [Finset.card_eq_zero.mp hℓ0] at this; exact Finset.notMem_empty v this
      -- u_{c,ℓ} ≤ 1  (case a, since a ≤ 1)
      have huQcℓ : (Q1.filter (fun w => G.Adj (vt c) w ∨ G.Adj (vt ℓ) w)).card ≤ 1 := by
        have hun : (Q1.filter (fun w => G.Adj (vt c) w ∨ G.Adj (vt ℓ) w)).card
            ≤ (Q1.filter (fun w => G.Adj (vt c) w)).card
              + (Q1.filter (fun w => G.Adj (vt ℓ) w)).card := by
          refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
          intro w hw; rw [Finset.mem_filter] at hw; rcases hw.2 with h | h
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw.1, h⟩)
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw.1, h⟩)
        have hpair : (Q1.filter (fun w => G.Adj (vt c) w)).card
            + (Q1.filter (fun w => G.Adj (vt ℓ) w)).card ≤ a := by
          rw [hadef]
          have := Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ ({c, ℓ} : Finset (Fin 5)))
            (f := fun k => (Q1.filter (fun w => G.Adj (vt k) w)).card) (fun _ _ _ => Nat.zero_le _)
          rwa [Finset.sum_pair (Ne.symm hℓc)] at this
        omega
      -- α(R − N_R(c)) ≤ 2
      have hαRc : ∀ S : Finset (Fin 25), S ⊆ R.filter (fun v => ¬ G.Adj (vt c) v) →
          IsIndep G S → S.card ≤ 2 := by
        intro S hSsub hSindep
        by_contra hc3; push_neg at hc3
        obtain ⟨S3, hS3sub, hS3c⟩ := Finset.exists_subset_card_eq (show 3 ≤ S.card by omega)
        obtain ⟨x, y, z, hxy, hxz, hyz, hSeq⟩ := Finset.card_eq_three.mp hS3c
        have ix : x ∈ S3 := by rw [hSeq]; simp
        have iy : y ∈ S3 := by rw [hSeq]; simp
        have iz : z ∈ S3 := by rw [hSeq]; simp
        have mx := hSsub (hS3sub ix); have my := hSsub (hS3sub iy); have mz := hSsub (hS3sub iz)
        have hxR : x ∈ R := (Finset.mem_filter.mp mx).1
        have hyR : y ∈ R := (Finset.mem_filter.mp my).1
        have hzR : z ∈ R := (Finset.mem_filter.mp mz).1
        have hxc : ¬ G.Adj (vt c) x := (Finset.mem_filter.mp mx).2
        have hyc : ¬ G.Adj (vt c) y := (Finset.mem_filter.mp my).2
        have hzc : ¬ G.Adj (vt c) z := (Finset.mem_filter.mp mz).2
        have hind3 : IsIndep G S3 := fun p hp q hq hpq => hSindep p (hS3sub hp) q (hS3sub hq) hpq
        have hcover : (Q1.filter (fun w => G.Adj x w ∨ G.Adj y w ∨ G.Adj z w
            ∨ G.Adj (vt c) w ∨ G.Adj (vt ℓ) w)).card ≤ 4 := by
          have := cover_3plus2_le (G := G) Q1 x y z (vt c) (vt ℓ)
          have b1 := hRindeg x hxR; have b2 := hRindeg y hyR; have b3 := hRindeg z hzR
          omega
        exact indep5_missedQ_false ctx.hα5 hQ1c hxy hxz
          (by rintro rfl; exact hvtnR c hxR) (by rintro rfl; exact hvtnR ℓ hxR)
          hyz (by rintro rfl; exact hvtnR c hyR) (by rintro rfl; exact hvtnR ℓ hyR)
          (by rintro rfl; exact hvtnR c hzR) (by rintro rfl; exact hvtnR ℓ hzR)
          (fun h => hℓc (hvtinj h).symm)
          (hind3 x ix y iy hxy) (hind3 x ix z iz hxz) (fun h => hxc (G.symm h))
          (fun h => hℓno x hxR (G.symm h))
          (hind3 y iy z iz hyz) (fun h => hyc (G.symm h)) (fun h => hℓno y hyR (G.symm h))
          (fun h => hzc (G.symm h)) (fun h => hℓno z hzR (G.symm h)) (hc ℓ hℓc)
          (hRnQ1 x hxR) (hRnQ1 y hyR) (hRnQ1 z hzR) (hvtnQ1 c) (hvtnQ1 ℓ) hcover
      -- X = R + vt c
      have hcnR : vt c ∉ R := hvtnR c
      set X := insert (vt c) R with hXdef
      have hXcard : X.card = 16 := by rw [hXdef, Finset.card_insert_of_notMem hcnR, hRcard]
      have hαX3 : ∀ S : Finset (Fin 25), S ⊆ X → IsIndep G S → S.card ≤ 3 := by
        intro S hSsub hSindep
        by_cases hcS : vt c ∈ S
        · have hSt : S.erase (vt c) ⊆ R.filter (fun v => ¬ G.Adj (vt c) v) := by
            intro u hu; rw [Finset.mem_erase] at hu
            have huX := hSsub hu.2; rw [hXdef, Finset.mem_insert] at huX
            have huR : u ∈ R := by rcases huX with h | h; exacts [absurd h hu.1, h]
            exact Finset.mem_filter.mpr ⟨huR, fun hadj => hSindep (vt c) hcS u hu.2 (Ne.symm hu.1) hadj⟩
          have := hαRc _ hSt (fun p hp q hq hpq =>
            hSindep p (Finset.mem_of_mem_erase hp) q (Finset.mem_of_mem_erase hq) hpq)
          have hce := Finset.card_erase_of_mem hcS; omega
        · have hSR : S ⊆ R := by
            intro u hu; have := hSsub hu; rw [hXdef, Finset.mem_insert] at this
            rcases this with h | h; exacts [absurd (h ▸ hu) hcS, h]
          exact hαR3 S hSR hSindep
      have hraw : edgeCountIn G R + p + a + D + s ≤ 50 := by
        have hsplit := edgeCountIn_univ_split G T
        rw [← hHdef, ← hsdef, hcross_eq, hH_eq, heQ1] at hsplit
        have := ctx.he60; omega
      have heX : edgeCountIn G X ≤ 44 := by
        have hins : edgeCountIn G X = edgeCountIn G R + (R.filter (fun q => G.Adj (vt c) q)).card := by
          rw [hXdef, edgeCountIn_insert_eq G hcnR]
        have hdcD : (R.filter (fun v => G.Adj (vt c) v)).card ≤ D := by
          rw [hDdef]; exact Finset.single_le_sum (f := fun i => (R.filter (fun v => G.Adj (vt i) v)).card)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
        omega
      by_cases hXfree : ∀ Q : Finset (Fin 25), Q ⊆ X → Q.card = 5 → ¬ IsCliqueOn G Q
      · have h46 := ell_le_edgeCountIn pf G X ctx.hcap
          (fun S hS hind => hαX3 S hS hind) hXfree (by rw [hXcard]; norm_num)
        rw [hXcard, show ell 16 = 46 from by decide] at h46
        omega
      · push_neg at hXfree
        obtain ⟨K, hKX, hKc, hKclq⟩ := hXfree
        have hcK : vt c ∈ K := by
          by_contra hcnK
          have hKR : K ⊆ R := by
            intro u hu; have := hKX hu; rw [hXdef, Finset.mem_insert] at this
            rcases this with h | h; exacts [absurd (h ▸ hu) hcnK, h]
          exact hRfree' K hKR hKc hKclq
        set W := X \ K with hWdef
        have hWR : W ⊆ R := by
          intro u hu; rw [hWdef, Finset.mem_sdiff] at hu
          have := hKX  -- unused
          have huX := hu.1; rw [hXdef, Finset.mem_insert] at huX
          rcases huX with h | h
          · exact absurd (h ▸ hcK) hu.2
          · exact h
        have hWcard : W.card = 11 := by
          have h1 := Finset.card_sdiff_of_subset hKX
          rw [hWdef]; omega
        have hαW : ∀ S : Finset (Fin 25), S ⊆ W → IsIndep G S → S.card ≤ 2 := by
          intro S hSsub hSindep
          by_contra hc3; push_neg at hc3
          obtain ⟨S3, hS3sub, hS3c⟩ := Finset.exists_subset_card_eq (show 3 ≤ S.card by omega)
          obtain ⟨x, y, z, hxy, hxz, hyz, hSeq⟩ := Finset.card_eq_three.mp hS3c
          have ix : x ∈ S3 := by rw [hSeq]; simp
          have iy : y ∈ S3 := by rw [hSeq]; simp
          have iz : z ∈ S3 := by rw [hSeq]; simp
          have hxW := hSsub (hS3sub ix); have hyW := hSsub (hS3sub iy); have hzW := hSsub (hS3sub iz)
          have hxnK : x ∉ K := (Finset.mem_sdiff.mp (hWdef ▸ hxW)).2
          have hynK : y ∉ K := (Finset.mem_sdiff.mp (hWdef ▸ hyW)).2
          have hznK : z ∉ K := (Finset.mem_sdiff.mp (hWdef ▸ hzW)).2
          obtain ⟨w, hwK, nwx, nwy, nwz⟩ := exists_missed_in_clique5 ctx.hcap hKclq hKc hxnK hynK hznK
          have hind3 : IsIndep G S3 := fun p hp q hq hpq => hSindep p (hS3sub hp) q (hS3sub hq) hpq
          have hwx : w ≠ x := fun h => hxnK (h ▸ hwK)
          have hwy : w ≠ y := fun h => hynK (h ▸ hwK)
          have hwz : w ≠ z := fun h => hznK (h ▸ hwK)
          have hxR : x ∈ R := hWR hxW
          have hyR : y ∈ R := hWR hyW
          have hzR : z ∈ R := hWR hzW
          have hS4X : ({x, y, z, w} : Finset (Fin 25)) ⊆ X := by
            intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
            rcases hu with rfl | rfl | rfl | rfl
            · exact hXdef ▸ Finset.mem_insert_of_mem hxR
            · exact hXdef ▸ Finset.mem_insert_of_mem hyR
            · exact hXdef ▸ Finset.mem_insert_of_mem hzR
            · exact hKX hwK
          have hS4indep : IsIndep G ({x, y, z, w} : Finset (Fin 25)) := by
            intro p hp q hq hpq
            simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
            obtain hpe|hpe|hpe|hpe := hp <;> obtain hqe|hqe|hqe|hqe := hq <;>
              first
                | exact absurd (hpe.trans hqe.symm) hpq
                | (rw [hpe, hqe]; first
                    | exact hind3 x ix y iy hxy | exact hind3 x ix z iz hxz | exact hind3 y iy z iz hyz
                    | exact nwx | exact nwy | exact nwz
                    | (exact fun h => (hind3 x ix y iy hxy) (G.symm h))
                    | (exact fun h => (hind3 x ix z iz hxz) (G.symm h))
                    | (exact fun h => (hind3 y iy z iz hyz) (G.symm h))
                    | (exact fun h => nwx (G.symm h)) | (exact fun h => nwy (G.symm h))
                    | (exact fun h => nwz (G.symm h)))
          have hS4card : ({x, y, z, w} : Finset (Fin 25)).card = 4 := by
            rw [Finset.card_insert_of_notMem (by
                  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                  exact ⟨hxy, hxz, Ne.symm hwx⟩),
              Finset.card_insert_of_notMem (by
                  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                  exact ⟨hyz, Ne.symm hwy⟩),
              Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact Ne.symm hwz),
              Finset.card_singleton]
          have hcon := hαX3 _ hS4X hS4indep
          rw [hS4card] at hcon; omega
        exact nonex11_transport pf ctx.hcap hWcard hαW

    by_cases hs6 : s = 6
    · have h6 : (decide (G.Adj (vt 0) (vt 1))).toNat + (decide (G.Adj (vt 0) (vt 2))).toNat
          + (decide (G.Adj (vt 0) (vt 3))).toNat + (decide (G.Adj (vt 0) (vt 4))).toNat
          + (decide (G.Adj (vt 1) (vt 2))).toNat + (decide (G.Adj (vt 1) (vt 3))).toNat
          + (decide (G.Adj (vt 1) (vt 4))).toNat + (decide (G.Adj (vt 2) (vt 3))).toNat
          + (decide (G.Adj (vt 2) (vt 4))).toNat + (decide (G.Adj (vt 3) (vt 4))).toNat ≤ 6 := by
        rw [hbr]; omega
      have hf := starOrDisjoint _ _ _ _ _ _ _ _ _ _ h6
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        or_assoc, and_assoc] at hf
      rcases hf with ⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|hstar|hstar|hstar|hstar|hstar
      · exact hDbig 0 1 2 3 (by decide) a b
      · exact hDbig 0 1 2 4 (by decide) a b
      · exact hDbig 0 1 3 4 (by decide) a b
      · exact hDbig 0 2 1 3 (by decide) a b
      · exact hDbig 0 2 1 4 (by decide) a b
      · exact hDbig 0 2 3 4 (by decide) a b
      · exact hDbig 0 3 1 2 (by decide) a b
      · exact hDbig 0 3 1 4 (by decide) a b
      · exact hDbig 0 3 2 4 (by decide) a b
      · exact hDbig 0 4 1 2 (by decide) a b
      · exact hDbig 0 4 1 3 (by decide) a b
      · exact hDbig 0 4 2 3 (by decide) a b
      · exact hDbig 1 2 3 4 (by decide) a b
      · exact hDbig 1 3 2 4 (by decide) a b
      · exact hDbig 1 4 2 3 (by decide) a b
      all_goals (obtain ⟨s1, s2, s3, s4⟩ := hstar)
      · refine hstarcase 0 ?_ hs6
        intro i hi; fin_cases i <;> first
          | exact absurd rfl hi | exact s1 | exact s2 | exact s3 | exact s4
          | (exact fun h => s1 (G.symm h)) | (exact fun h => s2 (G.symm h))
          | (exact fun h => s3 (G.symm h)) | (exact fun h => s4 (G.symm h))
      · refine hstarcase 1 ?_ hs6
        intro i hi; fin_cases i <;> first
          | exact absurd rfl hi | exact s1 | exact s2 | exact s3 | exact s4
          | (exact fun h => s1 (G.symm h)) | (exact fun h => s2 (G.symm h))
          | (exact fun h => s3 (G.symm h)) | (exact fun h => s4 (G.symm h))
      · refine hstarcase 2 ?_ hs6
        intro i hi; fin_cases i <;> first
          | exact absurd rfl hi | exact s1 | exact s2 | exact s3 | exact s4
          | (exact fun h => s1 (G.symm h)) | (exact fun h => s2 (G.symm h))
          | (exact fun h => s3 (G.symm h)) | (exact fun h => s4 (G.symm h))
      · refine hstarcase 3 ?_ hs6
        intro i hi; fin_cases i <;> first
          | exact absurd rfl hi | exact s1 | exact s2 | exact s3 | exact s4
          | (exact fun h => s1 (G.symm h)) | (exact fun h => s2 (G.symm h))
          | (exact fun h => s3 (G.symm h)) | (exact fun h => s4 (G.symm h))
      · refine hstarcase 4 ?_ hs6
        intro i hi; fin_cases i <;> first
          | exact absurd rfl hi | exact s1 | exact s2 | exact s3 | exact s4
          | (exact fun h => s1 (G.symm h)) | (exact fun h => s2 (G.symm h))
          | (exact fun h => s3 (G.symm h)) | (exact fun h => s4 (G.symm h))
    · have hs5 : s ≤ 5 := by omega
      have h5 := hbr ▸ hs5
      have hf := twoDisjoint _ _ _ _ _ _ _ _ _ _ h5
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        or_assoc, and_assoc] at hf
      rcases hf with ⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩
      · exact hDbig 0 1 2 3 (by decide) a b
      · exact hDbig 0 1 2 4 (by decide) a b
      · exact hDbig 0 1 3 4 (by decide) a b
      · exact hDbig 0 2 1 3 (by decide) a b
      · exact hDbig 0 2 1 4 (by decide) a b
      · exact hDbig 0 2 3 4 (by decide) a b
      · exact hDbig 0 3 1 2 (by decide) a b
      · exact hDbig 0 3 1 4 (by decide) a b
      · exact hDbig 0 3 2 4 (by decide) a b
      · exact hDbig 0 4 1 2 (by decide) a b
      · exact hDbig 0 4 1 3 (by decide) a b
      · exact hDbig 0 4 2 3 (by decide) a b
      · exact hDbig 1 2 3 4 (by decide) a b
      · exact hDbig 1 3 2 4 (by decide) a b
      · exact hDbig 1 4 2 3 (by decide) a b
  · -- (4,5,10):  a = 5, p = 4, s = 0.  Every pair is an F-edge with d_i+d_j ≥ 1,
    -- so ≤ 1 vertex has d = 0, giving D ≥ 4; but the budget forces D ≤ 3.
    have hs0 : s = 0 := by omega
    have hna : ∀ i j : Fin 5, i ≠ j → ¬ G.Adj (vt i) (vt j) := by
      have hexp := s_expand (G := G) hvtinj
      rw [hvtim, ← hsdef, hs0] at hexp
      have b01 : ¬ G.Adj (vt 0) (vt 1) := fun h => by simp only [if_pos h] at hexp; omega
      have b02 : ¬ G.Adj (vt 0) (vt 2) := fun h => by simp only [if_pos h] at hexp; omega
      have b03 : ¬ G.Adj (vt 0) (vt 3) := fun h => by simp only [if_pos h] at hexp; omega
      have b04 : ¬ G.Adj (vt 0) (vt 4) := fun h => by simp only [if_pos h] at hexp; omega
      have b12 : ¬ G.Adj (vt 1) (vt 2) := fun h => by simp only [if_pos h] at hexp; omega
      have b13 : ¬ G.Adj (vt 1) (vt 3) := fun h => by simp only [if_pos h] at hexp; omega
      have b14 : ¬ G.Adj (vt 1) (vt 4) := fun h => by simp only [if_pos h] at hexp; omega
      have b23 : ¬ G.Adj (vt 2) (vt 3) := fun h => by simp only [if_pos h] at hexp; omega
      have b24 : ¬ G.Adj (vt 2) (vt 4) := fun h => by simp only [if_pos h] at hexp; omega
      have b34 : ¬ G.Adj (vt 3) (vt 4) := fun h => by simp only [if_pos h] at hexp; omega
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        first
          | exact absurd rfl hij
          | assumption
          | (intro h; exact b01 (G.symm h)) | (intro h; exact b02 (G.symm h))
          | (intro h; exact b03 (G.symm h)) | (intro h; exact b04 (G.symm h))
          | (intro h; exact b12 (G.symm h)) | (intro h; exact b13 (G.symm h))
          | (intro h; exact b14 (G.symm h)) | (intro h; exact b23 (G.symm h))
          | (intro h; exact b24 (G.symm h)) | (intro h; exact b34 (G.symm h))
    have hpair1 : ∀ i j : Fin 5, i ≠ j → 1 ≤ (R.filter (fun v => G.Adj (vt i) v)).card
        + (R.filter (fun v => G.Adj (vt j) v)).card := by
      intro i j hij
      have := hcaseb i j hij (hna i j hij); omega
    have hpos : (Finset.univ.filter (fun i : Fin 5 =>
        0 < (R.filter (fun v => G.Adj (vt i) v)).card)).card ≤ D := by
      rw [hDdef]
      calc (Finset.univ.filter (fun i : Fin 5 =>
            0 < (R.filter (fun v => G.Adj (vt i) v)).card)).card
          = ∑ _i ∈ Finset.univ.filter (fun i : Fin 5 =>
              0 < (R.filter (fun v => G.Adj (vt i) v)).card), 1 := by rw [Finset.card_eq_sum_ones]
        _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin 5 =>
              0 < (R.filter (fun v => G.Adj (vt i) v)).card), (R.filter (fun v => G.Adj (vt i) v)).card :=
            Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp hi).2)
        _ ≤ ∑ i, (R.filter (fun v => G.Adj (vt i) v)).card :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
    have hZ2 : 2 ≤ (Finset.univ.filter (fun i : Fin 5 =>
        (R.filter (fun v => G.Adj (vt i) v)).card = 0)).card := by
      have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
        (s := (Finset.univ : Finset (Fin 5)))
        (p := fun i => 0 < (R.filter (fun v => G.Adj (vt i) v)).card)
      rw [Finset.card_univ, Fintype.card_fin] at hsplit
      have hneq : Finset.univ.filter (fun i : Fin 5 => ¬ 0 < (R.filter (fun v => G.Adj (vt i) v)).card)
          = Finset.univ.filter (fun i : Fin 5 => (R.filter (fun v => G.Adj (vt i) v)).card = 0) := by
        apply Finset.filter_congr; intro i _; omega
      rw [hneq] at hsplit; omega
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hZ2
    have hi0 : (R.filter (fun v => G.Adj (vt i) v)).card = 0 := (Finset.mem_filter.mp hi).2
    have hj0 : (R.filter (fun v => G.Adj (vt j) v)).card = 0 := (Finset.mem_filter.mp hj).2
    have := hpair1 i j hij
    omega
  · -- §4.2:  a = 5, 5 ≤ p ≤ 7.  D ≤ 2, r ≥ 8; a fixed independent triple S ⊆ R
    -- forces every F-edge to a common 2-set of Q-colours, so F is bipartite (e(F) ≤ 6).
    have hDs2 : D + s ≤ 2 := by omega
    -- U = ⋃ Z_i,  W = R − U  (≥ 13 vertices, none adjacent to any t_i)
    set U := R.filter (fun v => ∃ i : Fin 5, G.Adj (vt i) v) with hUdef
    have hUcard : U.card ≤ D := by
      have hsub : U ⊆ Finset.univ.biUnion (fun i : Fin 5 => R.filter (fun v => G.Adj (vt i) v)) := by
        intro v hv; rw [hUdef, Finset.mem_filter] at hv
        obtain ⟨i, hi⟩ := hv.2
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨hv.1, hi⟩⟩
      refine le_trans (Finset.card_le_card hsub) ?_
      rw [hDdef]; exact Finset.card_biUnion_le
    set W := R \ U with hWdef
    have hWcard : 13 ≤ W.card := by
      have h1 := Finset.card_sdiff_of_subset (show U ⊆ R from Finset.filter_subset _ _)
      rw [hWdef]; omega
    have hWR : W ⊆ R := hWdef ▸ Finset.sdiff_subset
    have hWno : ∀ v ∈ W, ∀ i : Fin 5, ¬ G.Adj (vt i) v := by
      intro v hv i hadj
      rw [hWdef, Finset.mem_sdiff] at hv
      exact hv.2 (Finset.mem_filter.mpr ⟨hv.1, ⟨i, hadj⟩⟩)
    -- an independent triple in W (else nonex11 on an 11-subset)
    obtain ⟨s1, s2, s3, h12, h13, h23, hs1W, hs2W, hs3W, hind⟩ :
        ∃ s1 s2 s3 : Fin 25, s1 ≠ s2 ∧ s1 ≠ s3 ∧ s2 ≠ s3 ∧ s1 ∈ W ∧ s2 ∈ W ∧ s3 ∈ W ∧
          (¬ G.Adj s1 s2 ∧ ¬ G.Adj s1 s3 ∧ ¬ G.Adj s2 s3) := by
      by_contra hcon
      have hαW : ∀ S : Finset (Fin 25), S ⊆ W → IsIndep G S → S.card ≤ 2 := by
        intro S hS hindS
        by_contra hc; push_neg at hc
        obtain ⟨S3, hS3, hS3c⟩ := Finset.exists_subset_card_eq (show 3 ≤ S.card by omega)
        obtain ⟨x, y, z, hxy, hxz, hyz, hSeq⟩ := Finset.card_eq_three.mp hS3c
        refine hcon ⟨x, y, z, hxy, hxz, hyz, hS (hS3 (by rw [hSeq]; simp)),
          hS (hS3 (by rw [hSeq]; simp)), hS (hS3 (by rw [hSeq]; simp)), ?_, ?_, ?_⟩
        · exact hindS x (hS3 (by rw [hSeq]; simp)) y (hS3 (by rw [hSeq]; simp)) hxy
        · exact hindS x (hS3 (by rw [hSeq]; simp)) z (hS3 (by rw [hSeq]; simp)) hxz
        · exact hindS y (hS3 (by rw [hSeq]; simp)) z (hS3 (by rw [hSeq]; simp)) hyz
      obtain ⟨W11, hW11, hW11c⟩ := Finset.exists_subset_card_eq (show 11 ≤ W.card by omega)
      exact nonex11_transport pf ctx.hcap hW11c
        (fun S hS hindS => hαW S (hS.trans hW11) hindS)
    have hs1R : s1 ∈ R := hWR hs1W; have hs2R : s2 ∈ R := hWR hs2W; have hs3R : s3 ∈ R := hWR hs3W
    have hindS3 : IsIndep G ({s1, s2, s3} : Finset (Fin 25)) := by
      intro p hp q hq hpq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
      obtain hpe|hpe|hpe := hp <;> obtain hqe|hqe|hqe := hq <;>
        first
          | exact absurd (hpe.trans hqe.symm) hpq
          | (rw [hpe, hqe]; first
              | exact hind.1 | exact hind.2.1 | exact hind.2.2
              | (exact fun h => hind.1 (G.symm h)) | (exact fun h => hind.2.1 (G.symm h))
              | (exact fun h => hind.2.2 (G.symm h)))
    -- M = Q1 minus N_Q(S) : the "missed" colours; |M| ≥ 2
    set M := Q1.filter (fun w => ¬ G.Adj s1 w ∧ ¬ G.Adj s2 w ∧ ¬ G.Adj s3 w) with hMdef
    have hM2 : 2 ≤ M.card := by
      have hcov : (Q1.filter (fun w => G.Adj s1 w ∨ G.Adj s2 w ∨ G.Adj s3 w)).card ≤ 3 := by
        have b1 := hRindeg s1 hs1R; have b2 := hRindeg s2 hs2R; have b3 := hRindeg s3 hs3R
        have hsub : Q1.filter (fun w => G.Adj s1 w ∨ G.Adj s2 w ∨ G.Adj s3 w)
            ⊆ Q1.filter (fun w => G.Adj s1 w) ∪ Q1.filter (fun w => G.Adj s2 w)
              ∪ Q1.filter (fun w => G.Adj s3 w) := by
          intro w hw; rw [Finset.mem_filter] at hw; rcases hw.2 with h|h|h
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw.1, h⟩))
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw.1, h⟩))
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw.1, h⟩)
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_union_le (Q1.filter (fun w => G.Adj s1 w)
          ∪ Q1.filter (fun w => G.Adj s2 w)) (Q1.filter (fun w => G.Adj s3 w))
        have h3 := Finset.card_union_le (Q1.filter (fun w => G.Adj s1 w))
          (Q1.filter (fun w => G.Adj s2 w))
        omega
      have hpart := Finset.card_filter_add_card_filter_not (s := Q1)
        (p := fun w => G.Adj s1 w ∨ G.Adj s2 w ∨ G.Adj s3 w)
      have hMeq : Q1.filter (fun w => ¬ (G.Adj s1 w ∨ G.Adj s2 w ∨ G.Adj s3 w)) = M := by
        rw [hMdef]; apply Finset.filter_congr; intro w _; rw [not_or, not_or]
      rw [hMeq, hQ1c] at hpart; omega
    -- s_k ∉ Q1, and each t_i has ≤ 1 Q1-neighbour
    have hsnQ1 : s1 ∉ Q1 ∧ s2 ∉ Q1 ∧ s3 ∉ Q1 := ⟨hRnQ1 s1 hs1R, hRnQ1 s2 hs2R, hRnQ1 s3 hs3R⟩
    -- 6-set forcing: for any F-edge and any w ∈ M, w is adjacent to t_i or t_j
    have hMforce : ∀ i j : Fin 5, i ≠ j → ¬ G.Adj (vt i) (vt j) → ∀ w ∈ M,
        G.Adj (vt i) w ∨ G.Adj (vt j) w := by
      intro i j hij hnadj w hw
      by_contra hbad; push_neg at hbad
      obtain ⟨hwi, hwj⟩ := hbad
      obtain ⟨hwQ1, hws1, hws2, hws3⟩ := Finset.mem_filter.mp hw
      exact no_indep_six ctx.hα5
        h12 h13 (fun he => hvtnR i (by rw [← he]; exact hs1R))
        (fun he => hvtnR j (by rw [← he]; exact hs1R))
        (fun he => hRnQ1 s1 hs1R (by rw [he]; exact hwQ1))
        h23 (fun he => hvtnR i (by rw [← he]; exact hs2R))
        (fun he => hvtnR j (by rw [← he]; exact hs2R))
        (fun he => hRnQ1 s2 hs2R (by rw [he]; exact hwQ1))
        (fun he => hvtnR i (by rw [← he]; exact hs3R))
        (fun he => hvtnR j (by rw [← he]; exact hs3R))
        (fun he => hRnQ1 s3 hs3R (by rw [he]; exact hwQ1))
        (fun he => hij (hvtinj he)) (fun he => hvtnQ1 i (by rw [he]; exact hwQ1))
        (fun he => hvtnQ1 j (by rw [he]; exact hwQ1))
        hind.1 hind.2.1 (fun h => hWno s1 hs1W i (G.symm h)) (fun h => hWno s1 hs1W j (G.symm h))
        hws1
        hind.2.2 (fun h => hWno s2 hs2W i (G.symm h)) (fun h => hWno s2 hs2W j (G.symm h))
        hws2
        (fun h => hWno s3 hs3W i (G.symm h)) (fun h => hWno s3 hs3W j (G.symm h))
        hws3
        hnadj hwi hwj
    -- there is an F-edge; force |M| = 2 and extract w1 ≠ w2
    have hrge8 : 8 ≤ 10 - s := by omega
    have hNEpos : 0 < NEpairs.card := by omega
    obtain ⟨p0, hp0⟩ := Finset.card_pos.mp hNEpos
    rw [hNEdef, Finset.mem_filter] at hp0
    obtain ⟨-, hp0ne, hp0nadj⟩ := hp0
    have hMle2 : M.card ≤ 2 := by
      have hMsub : M ⊆ Q1.filter (fun w => G.Adj (vt p0.1) w) ∪ Q1.filter (fun w => G.Adj (vt p0.2) w) := by
        intro w hw
        have hwQ1 := (Finset.mem_filter.mp hw).1
        rcases hMforce p0.1 p0.2 hp0ne hp0nadj w hw with h | h
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hwQ1, h⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hwQ1, h⟩)
      have b1 := haQ1 p0.1; have b2 := haQ1 p0.2
      exact le_trans (Finset.card_le_card hMsub) (le_trans (Finset.card_union_le _ _) (by omega))
    obtain ⟨w1, w2, hw12, hMeq2⟩ := Finset.card_eq_two.mp (le_antisymm hMle2 hM2)
    have hw1M : w1 ∈ M := by rw [hMeq2]; exact Finset.mem_insert_self _ _
    have hw2M : w2 ∈ M := by rw [hMeq2]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    -- A1, A2 : the two colour classes; F is bipartite between them
    set A1 := Finset.univ.filter (fun i : Fin 5 => G.Adj (vt i) w1) with hA1def
    set A2 := Finset.univ.filter (fun i : Fin 5 => G.Adj (vt i) w2) with hA2def
    have hnotboth : ∀ i : Fin 5, ¬ (G.Adj (vt i) w1 ∧ G.Adj (vt i) w2) := by
      rintro i ⟨ha, hb⟩
      have hw1Q1 : w1 ∈ Q1 := (Finset.mem_filter.mp hw1M).1
      have hw2Q1 : w2 ∈ Q1 := (Finset.mem_filter.mp hw2M).1
      have hsub : ({w1, w2} : Finset (Fin 25)) ⊆ Q1.filter (fun w => G.Adj (vt i) w) := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨hw1Q1, ha⟩
        · exact Finset.mem_filter.mpr ⟨hw2Q1, hb⟩
      have h2c := Finset.card_le_card hsub
      rw [Finset.card_pair hw12] at h2c
      have := haQ1 i; omega
    have hNEbip : NEpairs ⊆ (A1 ×ˢ A2) ∪ (A2 ×ˢ A1) := by
      intro q hq
      rw [hNEdef, Finset.mem_filter] at hq
      obtain ⟨-, hqne, hqnadj⟩ := hq
      have f1 := hMforce q.1 q.2 hqne hqnadj w1 hw1M
      have f2 := hMforce q.1 q.2 hqne hqnadj w2 hw2M
      have nb1 := hnotboth q.1; have nb2 := hnotboth q.2
      rw [Finset.mem_union, Finset.mem_product, Finset.mem_product, hA1def, hA2def]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      -- case on which of q.1, q.2 hits w1
      rcases f1 with h1 | h1
      · left; refine ⟨h1, ?_⟩
        rcases f2 with h2 | h2
        · exact absurd ⟨h1, h2⟩ nb1
        · exact h2
      · right; refine ⟨?_, h1⟩
        rcases f2 with h2 | h2
        · exact h2
        · exact absurd ⟨h1, h2⟩ nb2
    -- count: 2r = |NE| ≤ 2·|A1|·|A2| ≤ 12 < 16
    have hA12 : A1.card + A2.card ≤ 5 := by
      have : A1 ∪ A2 ⊆ Finset.univ := Finset.subset_univ _
      have hd : Disjoint A1 A2 := by
        rw [Finset.disjoint_left]; intro i hi1 hi2
        rw [hA1def, Finset.mem_filter] at hi1; rw [hA2def, Finset.mem_filter] at hi2
        exact hnotboth i ⟨hi1.2, hi2.2⟩
      have := Finset.card_le_card (Finset.subset_univ (A1 ∪ A2))
      rw [Finset.card_union_of_disjoint hd, Finset.card_univ, Fintype.card_fin] at this
      exact this
    have hbipcard : ((A1 ×ˢ A2) ∪ (A2 ×ˢ A1)).card ≤ 2 * (A1.card * A2.card) := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_product, Finset.card_product]; ring_nf; omega
    have mul_le_six : ∀ x y : ℕ, x + y ≤ 5 → x * y ≤ 6 := by
      intro x y h
      have hx : x ≤ 5 := by omega
      interval_cases x <;> omega
    have hprod : A1.card * A2.card ≤ 6 := mul_le_six _ _ hA12
    have hNEle := Finset.card_le_card hNEbip
    omega

/-- **[MM].** The case split on the maximum number of disjoint `K_5`'s in
`H = G − T` (∈ {0,1,2,4}), each case discharged by a section lemma. -/
theorem lemma_MM_of (pf : PrimFacts) : MM := by
  intro G hα5 hcap he60 T hT hαT hsT
  have ctx : MMCtx G T := ⟨hα5, hcap, he60, hT, hαT, hsT⟩
  by_cases hA : ∀ Q : Finset (Fin 25), Q ⊆ Finset.univ \ T → Q.card = 5 → ¬ IsCliqueOn G Q
  · exact section2_free ctx pf hA
  · push Not at hA
    obtain ⟨Q1, hQ1sub, hQ1c, hQ1clq⟩ := hA
    by_cases hB : ∀ Q : Finset (Fin 25), Q ⊆ (Finset.univ \ T) \ Q1 → Q.card = 5 → ¬ IsCliqueOn G Q
    · exact section4_one ctx pf hQ1sub hQ1c hQ1clq hB
    · push Not at hB
      obtain ⟨Q2, hQ2sub, hQ2c, hQ2clq⟩ := hB
      by_cases hC : ∀ Q : Finset (Fin 25), Q ⊆ ((Finset.univ \ T) \ Q1) \ Q2 → Q.card = 5 → ¬ IsCliqueOn G Q
      · exact section5_two ctx pf hQ1sub hQ1c hQ1clq hQ2sub hQ2c hQ2clq hC
      · push Not at hC
        obtain ⟨Q3, hQ3sub, hQ3c, hQ3clq⟩ := hC
        exact section3_four ctx pf hQ1sub hQ1c hQ1clq hQ2sub hQ2c hQ2clq hQ3sub hQ3c hQ3clq

end Erdos617
