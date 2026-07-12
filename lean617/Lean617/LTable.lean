/-
Erdős Problem 617, r = 5 — milestone F5: the L-table recursion.

We formalize, CONDITIONALLY on the four SAT-primitive facts (bundled as
`PrimFacts`, to be discharged by F3), the min-edge floors of
review_queue/mh2-gpt56-candidate.md §4.1–4.2:

* `M_floor_alpha2` : the (α ≤ 2, ω ≤ 4, cap-11) floor `M(m)` — Mantel for m ≤ 8,
  the SAT primitives for m = 9, 10, and nonexistence for m ≥ 11;
* the L-table `L(s) ≤ e(X)` for graphs `X` on `Fin s` with `α ≤ 3`, `ω ≤ 4`
  (`CliqueFree 5`) and cap-11, for s = 13,…,19 with L = 24,31,38,46,53,62,73.

The proof follows the candidate's §4.2: the F4 double-counting identity
`(∑ e(W_v)) + ∑ deg² = s·e(X) + ∑ e(N v)`, per-vertex floors `e(W_v) ≥ M(s-1-d_v)`
and `e(N v) ≤ u(d_v)`, and a per-degree affine bound replacing the informal DP.
See tools/verify_gpt_arith.py for the (machine-checked) arithmetic blueprint and
scratchpad/check_affine_f5.py for the exact integer/range refinements used here.

Research project: Mathlib style linters disabled.
-/
import Lean617.Counting

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.style.multiGoal false
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false

open Finset SimpleGraph
open scoped Classical

namespace Erdos617

/-! ## Definitions -/

/-- Every 6-set spans at most 11 edges. (The cap-11 hypothesis of MM, packaged.) -/
def capAtMost11 {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ S : Finset (Fin n), S.card = 6 → edgeCountIn G S ≤ 11

/-- Independence number at most `m`. -/
def alphaAtMost {n : ℕ} (G : SimpleGraph (Fin n)) (m : ℕ) : Prop :=
  ∀ S : Finset (Fin n), IsIndep G S → S.card ≤ m

/-- **The four SAT-primitive facts** (to be discharged by milestone F3). Stated
EXACTLY as the informal ledger: (i)/(ii) no `α ≤ 2` cap-11 graph exists on 11 or
12 vertices (ω-free); (iii)/(iv) an `α ≤ 2`, `ω ≤ 4` (`CliqueFree 5`), cap-11
graph on 9 (resp. 10) vertices has at least 19 (resp. 25) edges. -/
structure PrimFacts : Prop where
  nonex11 : ∀ G : SimpleGraph (Fin 11), capAtMost11 G → alphaAtMost G 2 → False
  nonex12 : ∀ G : SimpleGraph (Fin 12), capAtMost11 G → alphaAtMost G 2 → False
  M9  : ∀ G : SimpleGraph (Fin 9), capAtMost11 G → alphaAtMost G 2 → G.CliqueFree 5 →
          19 ≤ edgeCountIn G Finset.univ
  M10 : ∀ G : SimpleGraph (Fin 10), capAtMost11 G → alphaAtMost G 2 → G.CliqueFree 5 →
          25 ≤ edgeCountIn G Finset.univ

/-! ## Transport along a vertex embedding `f : Fin t ↪ Fin s`

To apply the primitives (stated over `Fin 9/10/11/12`) and Mantel (over `Fin t`)
to the induced subgraph on a `t`-vertex subset `W ⊆ Fin s`, we pull `X` back along
an embedding `f : Fin t ↪ Fin s` with `univ.image f = W`. `X.comap f` is that
induced subgraph relabelled onto `Fin t`. -/

variable {s t : ℕ}

/-- Edge counts transport: the edges of `X.comap f` inside `T` are exactly the
edges of `X` inside `f '' T`. -/
theorem edgeCountIn_comap (X : SimpleGraph (Fin s)) (f : Fin t ↪ Fin s)
    (T : Finset (Fin t)) :
    edgeCountIn (X.comap f) T = edgeCountIn X (T.image f) := by
  unfold edgeCountIn
  apply Finset.card_bij (fun e _ => Sym2.map f e)
  · -- maps to
    intro e he
    revert he
    induction e using Sym2.ind with
    | _ a b =>
      intro he
      rw [Finset.mem_filter] at he
      obtain ⟨hmem, hedge⟩ := he
      rw [Finset.mk_mem_sym2_iff] at hmem
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.comap_adj] at hedge
      rw [Finset.mem_filter, Sym2.map_mk]
      refine ⟨?_, ?_⟩
      · rw [Finset.mk_mem_sym2_iff]
        exact ⟨Finset.mem_image_of_mem f hmem.1, Finset.mem_image_of_mem f hmem.2⟩
      · rw [SimpleGraph.mem_edgeSet]; exact hedge
  · -- injective
    intro a _ b _ hab
    exact Sym2.map.injective f.injective hab
  · -- surjective
    intro e he
    revert he
    induction e using Sym2.ind with
    | _ u v =>
      intro he
      rw [Finset.mem_filter] at he
      obtain ⟨hmem, hedge⟩ := he
      rw [Finset.mk_mem_sym2_iff] at hmem
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hmem.1
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hmem.2
      refine ⟨s(a, b), ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mk_mem_sym2_iff.mpr ⟨ha, hb⟩, ?_⟩
        rw [SimpleGraph.mem_edgeSet, SimpleGraph.comap_adj]
        rw [SimpleGraph.mem_edgeSet] at hedge
        exact hedge
      · rw [Sym2.map_mk]

/-- Independence transports across `comap`. -/
theorem isIndep_comap (X : SimpleGraph (Fin s)) (f : Fin t ↪ Fin s)
    (T : Finset (Fin t)) :
    IsIndep (X.comap f) T ↔ IsIndep X (T.image f) := by
  constructor
  · intro h u hu v hv huv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
    have hab : a ≠ b := fun h => huv (by rw [h])
    have := h a ha b hb hab
    rwa [SimpleGraph.comap_adj] at this
  · intro h a ha b hb hab
    rw [SimpleGraph.comap_adj]
    exact h (f a) (Finset.mem_image_of_mem f ha) (f b) (Finset.mem_image_of_mem f hb)
      (fun he => hab (f.injective he))

/-- `CliqueFree` transports across `comap` (the pullback embeds into `X`). -/
theorem cliqueFree_comap (X : SimpleGraph (Fin s)) (f : Fin t ↪ Fin s) {n : ℕ}
    (h : X.CliqueFree n) : (X.comap f).CliqueFree n :=
  h.comap (SimpleGraph.Embedding.comap f X).isContained

/-- There is an embedding `Fin t ↪ Fin s` whose image is any `t`-element `W`. -/
theorem exists_embedding_image_eq (W : Finset (Fin s)) (hW : W.card = t) :
    ∃ f : Fin t ↪ Fin s, Finset.univ.image f = W := by
  refine ⟨(W.orderEmbOfFin hW).toEmbedding, ?_⟩
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, RelEmbedding.coe_toEmbedding]
  constructor
  · rintro ⟨i, rfl⟩
    exact W.orderEmbOfFin_mem hW i
  · intro hx
    have hx' : x ∈ Set.range (W.orderEmbOfFin hW) := by
      rw [Finset.range_orderEmbOfFin]; exact Finset.mem_coe.mpr hx
    exact hx'

/-! ## The `α ≤ 2` (Mantel) floor `M(m)` for `m ≤ 8`

The complement of an `α ≤ 2` graph is triangle-free; Turán's theorem (r = 2)
bounds its edges by those of `turanGraph t 2`, hence `e(G) ≥ C(t,2) − e(K_{t,t})`.
For each concrete `t ≤ 8` the Turán-graph edge count `= ⌊t²/4⌋` is decided. -/

/-- Complement edge identity in the `edgeCountIn` idiom: the edges of `G` and of
`Gᶜ` inside `univ` partition the `C(t,2)` off-diagonal pairs. -/
theorem edgeCountIn_add_compl (G : SimpleGraph (Fin t)) :
    edgeCountIn G Finset.univ + edgeCountIn Gᶜ Finset.univ = t.choose 2 := by
  -- Work over the off-diagonal base `B`, splitting on `∈ G.edgeSet`.
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin t)).sym2.filter (fun e => ¬ e.IsDiag))
    (fun e => e ∈ G.edgeSet)
  rw [card_offdiag, Finset.card_univ, Fintype.card_fin] at h
  have e1 : edgeCountIn G Finset.univ
      = (((Finset.univ : Finset (Fin t)).sym2.filter (fun e => ¬ e.IsDiag)).filter
          (fun e => e ∈ G.edgeSet)).card := by
    unfold edgeCountIn
    congr 1
    ext e
    revert e
    refine Sym2.ind (fun u v => ?_)
    simp only [Finset.mem_filter, Finset.mk_mem_sym2_iff, Finset.mem_univ, true_and,
      SimpleGraph.mem_edgeSet, Sym2.mk_isDiag_iff]
    exact ⟨fun h => ⟨G.ne_of_adj h, h⟩, fun h => h.2⟩
  have e2 : edgeCountIn Gᶜ Finset.univ
      = (((Finset.univ : Finset (Fin t)).sym2.filter (fun e => ¬ e.IsDiag)).filter
          (fun e => ¬ e ∈ G.edgeSet)).card := by
    unfold edgeCountIn
    congr 1
    ext e
    revert e
    refine Sym2.ind (fun u v => ?_)
    simp only [Finset.mem_filter, Finset.mk_mem_sym2_iff, Finset.mem_univ, true_and,
      SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj, Sym2.mk_isDiag_iff]
  rw [e1, e2, h]

/-- `edgeCountIn G univ = #G.edgeFinset`, but instance-robust: the explicit
`[DecidableRel G.Adj]` binder makes it usable to rewrite a `#Gᶜ.edgeFinset`
produced by Turán maximality (whose instance differs from the ambient Classical
one). -/
theorem card_edgeFinset_eq_edgeCountIn (G : SimpleGraph (Fin t)) [DecidableRel G.Adj] :
    G.edgeFinset.card = edgeCountIn G Finset.univ := by
  rw [edgeCountIn_univ_eq_card_edgeFinset]
  congr 1
  ext e
  simp only [SimpleGraph.mem_edgeFinset]

/-- **Mantel / complement-Turán floor.** For any `α ≤ 2` graph on `Fin t`,
`e(G) ≥ C(t,2) − e(turanGraph t 2)`. (For `t ≤ 8` the last term is `⌊t²/4⌋`,
decided per `t`.) -/
theorem mantel_general (G : SimpleGraph (Fin t)) (hα : alphaAtMost G 2) :
    t.choose 2 - (turanGraph t 2).edgeFinset.card ≤ edgeCountIn G Finset.univ := by
  have hcf : Gᶜ.CliqueFree 3 := by
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
  have hT := (isTuranMaximal_turanGraph (n := t) (r := 2) (by norm_num)).2 hcf
  rw [card_edgeFinset_eq_edgeCountIn Gᶜ] at hT
  have hid := edgeCountIn_add_compl G
  omega

/-! ## The floor functions `Mfloor` (α ≤ 2) and `ufloor` (cap-11 neighbourhood) -/

/-- The `α ≤ 2`, `ω ≤ 4`, cap-11 edge floor `M(m)`: Mantel `C(m,2) − ⌊m²/4⌋` for
`m ≤ 8`, the SAT primitives `19, 25` for `m = 9, 10`, and `0` for `m ≥ 11`
(those degrees are excluded by nonexistence, so the value is never used). -/
def Mfloor (m : ℕ) : ℕ :=
  if m ≤ 8 then m.choose 2 - m * m / 4 else if m = 9 then 19 else if m = 10 then 25 else 0

/-- The cap-11 neighbourhood edge cap `u(d) = min(b(d), ex(d,K₄))`. This equals
`b(d) = ⌊3d(d−1)/10⌋` (d ≥ 5) or `C(d,2)` (d ≤ 3) everywhere except `d = 4`,
where the `K₄`-free refinement `ex(4,K₄) = 5` is needed. -/
def ufloor (d : ℕ) : ℕ :=
  if d = 4 then 5 else if d ≤ 4 then d.choose 2 else 3 * d * (d - 1) / 10

/-! ## Per-vertex floors -/

/-- If a vertex set spans at least `C(|S|,2)` edges, it is a clique. -/
theorem adj_of_edgeCountIn_choose (X : SimpleGraph (Fin s)) (S : Finset (Fin s))
    (h : S.card.choose 2 ≤ edgeCountIn X S) {u v : Fin s} (hu : u ∈ S) (hv : v ∈ S)
    (huv : u ≠ v) : X.Adj u v := by
  have hsub : S.sym2.filter (fun e => e ∈ X.edgeSet) ⊆ S.sym2.filter (fun e => ¬ e.IsDiag) := by
    intro e he
    rw [Finset.mem_filter] at he ⊢
    exact ⟨he.1, X.not_isDiag_of_mem_edgeSet he.2⟩
  have hcard : (S.sym2.filter (fun e => ¬ e.IsDiag)).card ≤ (S.sym2.filter (fun e => e ∈ X.edgeSet)).card := by
    rw [card_offdiag]; exact h
  have heq : S.sym2.filter (fun e => e ∈ X.edgeSet) = S.sym2.filter (fun e => ¬ e.IsDiag) :=
    Finset.eq_of_subset_of_card_le hsub hcard
  have hmem : s(u, v) ∈ S.sym2.filter (fun e => ¬ e.IsDiag) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mk_mem_sym2_iff.mpr ⟨hu, hv⟩, by rw [Sym2.mk_isDiag_iff]; exact huv⟩
  rw [← heq, Finset.mem_filter, SimpleGraph.mem_edgeSet] at hmem
  exact hmem.2

/-- The key `α`-drop: an independent set inside `W_v = V∖N[v]`, together with `v`,
is independent in `X`; so `α(X) ≤ 3` forces `α(X[W_v]) ≤ 2`. -/
theorem alpha_W {X : SimpleGraph (Fin s)} (hα3 : alphaAtMost X 3) (v : Fin s)
    (S : Finset (Fin s)) (hSW : S ⊆ complClosedNbhd X v) (hSindep : IsIndep X S) :
    S.card ≤ 2 := by
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
  have := hα3 (insert v S) hins
  omega

/-- Cap-11 transports across `comap`. -/
theorem capAtMost11_comap (X : SimpleGraph (Fin s)) (f : Fin t ↪ Fin s)
    (hcap : capAtMost11 X) : capAtMost11 (X.comap f) := by
  intro S' hS'
  rw [edgeCountIn_comap]
  exact hcap _ (by rw [Finset.card_image_of_injective _ f.injective, hS'])

/-- `α ≤ 2` transports across `comap`, given the `α`-bound on subsets of the image. -/
theorem alphaAtMost_comap (X : SimpleGraph (Fin s)) (f : Fin t ↪ Fin s)
    (hα : ∀ S : Finset (Fin s), S ⊆ Finset.univ.image f → IsIndep X S → S.card ≤ 2) :
    alphaAtMost (X.comap f) 2 := by
  intro S' hS'
  rw [isIndep_comap] at hS'
  have hsub : S'.image f ⊆ Finset.univ.image f :=
    Finset.image_subset_image (Finset.subset_univ S')
  have := hα (S'.image f) hsub hS'
  rwa [Finset.card_image_of_injective _ f.injective] at this

/-- **The `α ≤ 2` floor, packaged for consumption.** For a graph `Y` on `Fin t`
(`t ≤ 10`) with `α ≤ 2`, `ω ≤ 4`, cap-11: `Mfloor t ≤ e(Y)`. Mantel for `t ≤ 8`,
the SAT primitives for `t = 9, 10`. -/
theorem Mfloor_le_of_props (h : PrimFacts) {t : ℕ} (Y : SimpleGraph (Fin t))
    (hα : alphaAtMost Y 2) (hω : Y.CliqueFree 5) (hcap : capAtMost11 Y) (ht : t ≤ 10) :
    Mfloor t ≤ edgeCountIn Y Finset.univ := by
  interval_cases t
  · exact le_trans (by decide) (mantel_general Y hα)
  · exact le_trans (by decide) (mantel_general Y hα)
  · exact le_trans (by decide) (mantel_general Y hα)
  · exact le_trans (by decide) (mantel_general Y hα)
  · exact le_trans (by decide) (mantel_general Y hα)
  · exact le_trans (by decide) (mantel_general Y hα)
  · exact le_trans (by decide) (mantel_general Y hα)
  · exact le_trans (by decide) (mantel_general Y hα)
  · exact le_trans (by decide) (mantel_general Y hα)
  · have hp := h.M9 Y hcap hα hω
    have h9 : Mfloor 9 = 19 := by decide
    omega
  · have hp := h.M10 Y hcap hα hω
    have h10 : Mfloor 10 = 25 := by decide
    omega

/-- `W_v` has at most 10 vertices: an 11-vertex `α ≤ 2` cap-11 subgraph is
forbidden by primitive (i). -/
theorem complNbhd_card_le_ten (h : PrimFacts) (X : SimpleGraph (Fin s))
    (hα3 : alphaAtMost X 3) (hcap : capAtMost11 X) (v : Fin s) :
    (complClosedNbhd X v).card ≤ 10 := by
  by_contra hgt
  push Not at hgt
  obtain ⟨W'', hW''sub, hW''card⟩ :=
    Finset.exists_subset_card_eq (show 11 ≤ (complClosedNbhd X v).card by omega)
  obtain ⟨f, hf⟩ := exists_embedding_image_eq W'' hW''card
  refine h.nonex11 (X.comap f) (capAtMost11_comap X f hcap) (alphaAtMost_comap X f ?_)
  intro S hSsub hSindep
  rw [hf] at hSsub
  exact alpha_W hα3 v S (hSsub.trans hW''sub) hSindep

/-- **Per-vertex `α ≤ 2` floor.** `Mfloor |W_v| ≤ e(X[W_v])`. -/
theorem Mfloor_le_edgeCountIn_complNbhd (h : PrimFacts) (X : SimpleGraph (Fin s))
    (hα3 : alphaAtMost X 3) (hω : X.CliqueFree 5) (hcap : capAtMost11 X) (v : Fin s) :
    Mfloor ((complClosedNbhd X v).card) ≤ edgeCountIn X (complClosedNbhd X v) := by
  obtain ⟨f, hf⟩ := exists_embedding_image_eq (complClosedNbhd X v) rfl
  have hEC : edgeCountIn (X.comap f) Finset.univ = edgeCountIn X (complClosedNbhd X v) := by
    rw [edgeCountIn_comap, hf]
  rw [← hEC]
  refine Mfloor_le_of_props h (X.comap f) (alphaAtMost_comap X f ?_)
    (cliqueFree_comap X f hω) (capAtMost11_comap X f hcap)
    (complNbhd_card_le_ten h X hα3 hcap v)
  intro S hSsub hSindep
  rw [hf] at hSsub
  exact alpha_W hα3 v S hSsub hSindep

/-- **Per-vertex neighbourhood cap.** `e(X[N v]) ≤ ufloor(deg v)`: the `K₄`-free
refinement `≤ 5` at degree 4, the cap-11 floor `⌊3d(d−1)/10⌋` for `d ≥ 5`, and
the trivial `C(d,2)` for `d ≤ 3`. -/
theorem edgeCountIn_nbhd_le_ufloor (X : SimpleGraph (Fin s)) (hω : X.CliqueFree 5)
    (hcap : capAtMost11 X) (v : Fin s) :
    edgeCountIn X (X.neighborFinset v) ≤ ufloor (X.degree v) := by
  set d := X.degree v with hd
  have hNcard : (X.neighborFinset v).card = d := by rw [X.card_neighborFinset_eq_degree]
  by_cases hd4 : d = 4
  · -- degree 4: N v is K₄-free, so ≤ 5 edges
    have huf : ufloor d = 5 := by rw [hd4]; decide
    rw [huf]
    by_contra hgt
    push Not at hgt
    have hNcard4 : (X.neighborFinset v).card = 4 := by rw [hNcard, hd4]
    have hchoose : (X.neighborFinset v).card.choose 2 ≤ edgeCountIn X (X.neighborFinset v) := by
      rw [hNcard4]
      have : (4 : ℕ).choose 2 = 6 := by decide
      omega
    have hclique : ∀ a ∈ X.neighborFinset v, ∀ b ∈ X.neighborFinset v, a ≠ b → X.Adj a b :=
      fun a ha b hb hab => adj_of_edgeCountIn_choose X _ hchoose ha hb hab
    have hvN : v ∉ X.neighborFinset v := by simp [SimpleGraph.mem_neighborFinset]
    have hclq5 : (insert v (X.neighborFinset v)).card = 5 := by
      rw [Finset.card_insert_of_notMem hvN, hNcard4]
    have h5 : X.IsNClique 5 (insert v (X.neighborFinset v)) := by
      rw [SimpleGraph.isNClique_iff]
      refine ⟨?_, hclq5⟩
      intro a ha b hb hab
      rw [Finset.mem_coe, Finset.mem_insert] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact absurd (ha.trans hb.symm) hab
      · rw [ha]; exact (X.mem_neighborFinset v b).mp hb
      · rw [hb]; exact ((X.mem_neighborFinset v a).mp ha).symm
      · exact hclique a ha b hb hab
    exact hω (insert v (X.neighborFinset v)) h5
  · by_cases hd5 : d ≤ 4
    · -- degree ≤ 3: trivial C(d,2)
      have hle := edgeCountIn_le_choose_two X (X.neighborFinset v)
      rw [hNcard] at hle
      have huf : ufloor d = d.choose 2 := by unfold ufloor; rw [if_neg hd4, if_pos hd5]
      omega
    · -- degree ≥ 5: cap-11 floor
      push Not at hd5
      have hb := nbhd_bound_cap11 X hcap hd.symm (by omega)
      have huf : ufloor d = 3 * d * (d - 1) / 10 := by unfold ufloor; rw [if_neg hd4, if_neg (by omega)]
      rw [huf, Nat.le_div_iff_mul_le (by norm_num)]
      omega

/-! ## The L-table assembly -/

/-- `|W_v| = s − 1 − deg v`. -/
theorem complNbhd_card (X : SimpleGraph (Fin s)) (v : Fin s) :
    (complClosedNbhd X v).card = s - 1 - X.degree v := by
  unfold complClosedNbhd
  have hvN : v ∉ X.neighborFinset v := by simp [SimpleGraph.mem_neighborFinset]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_insert_of_notMem hvN,
    X.card_neighborFinset_eq_degree, Finset.card_univ, Fintype.card_fin]
  omega

/-- Degrees are at most `s − 1`. -/
theorem degree_le_pred (X : SimpleGraph (Fin s)) (v : Fin s) : X.degree v ≤ s - 1 := by
  rw [← X.card_neighborFinset_eq_degree]
  have hsub : X.neighborFinset v ⊆ Finset.univ.erase v := by
    intro x hx
    have hadj := (X.mem_neighborFinset v x).mp hx
    rw [Finset.mem_erase]
    exact ⟨(X.ne_of_adj hadj).symm, Finset.mem_univ x⟩
  calc (X.neighborFinset v).card ≤ (Finset.univ.erase v).card := Finset.card_le_card hsub
    _ = s - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ,
        Fintype.card_fin]

/-- Per-degree affine bound for `s = 13` (`twoA = 50, twoB = 14`), checked over the
feasible range `d ∈ [s−11, s−1] = [2,12]` by `decide` (see check_affine_f5.py). -/
theorem affineBound_13 (d : ℕ) (hlo : 2 ≤ d) (hhi : d ≤ 12) :
    50 + 13 * d + 2 * ufloor d ≤ 2 * Mfloor (13 - 1 - d) + 2 * d ^ 2 + 14 * d := by
  interval_cases d <;> decide

/-- **L-table, s = 13: `L(13) = 24`.** -/
theorem L13 (h : PrimFacts) (X : SimpleGraph (Fin 13)) (hα3 : alphaAtMost X 3)
    (hω : X.CliqueFree 5) (hcap : capAtMost11 X) : 24 ≤ edgeCountIn X Finset.univ := by
  rw [edgeCountIn_univ_eq_card_edgeFinset]
  have hWcard : ∀ v, (complClosedNbhd X v).card = 13 - 1 - X.degree v := complNbhd_card X
  have hM_lb : ∀ v, Mfloor (13 - 1 - X.degree v) ≤ edgeCountIn X (complClosedNbhd X v) := by
    intro v; rw [← hWcard v]; exact Mfloor_le_edgeCountIn_complNbhd h X hα3 hω hcap v
  have hN_ub : ∀ v, edgeCountIn X (X.neighborFinset v) ≤ ufloor (X.degree v) :=
    fun v => edgeCountIn_nbhd_le_ufloor X hω hcap v
  have hAff : ∀ v, 50 + 13 * X.degree v + 2 * ufloor (X.degree v)
      ≤ 2 * Mfloor (13 - 1 - X.degree v) + 2 * (X.degree v) ^ 2 + 14 * X.degree v := by
    intro v
    refine affineBound_13 (X.degree v) ?_ (degree_le_pred X v)
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

/-- Per-degree affine bound for `s = 14` (`twoA = 52, twoB = 12`), `d ∈ [3,13]`. -/
theorem affineBound_14 (d : ℕ) (hlo : 3 ≤ d) (hhi : d ≤ 13) :
    52 + 14 * d + 2 * ufloor d ≤ 2 * Mfloor (14 - 1 - d) + 2 * d ^ 2 + 12 * d := by
  interval_cases d <;> decide

/-- **L-table, s = 14: `L(14) = 31`.** -/
theorem L14 (h : PrimFacts) (X : SimpleGraph (Fin 14)) (hα3 : alphaAtMost X 3)
    (hω : X.CliqueFree 5) (hcap : capAtMost11 X) : 31 ≤ edgeCountIn X Finset.univ := by
  rw [edgeCountIn_univ_eq_card_edgeFinset]
  have hWcard : ∀ v, (complClosedNbhd X v).card = 14 - 1 - X.degree v := complNbhd_card X
  have hM_lb : ∀ v, Mfloor (14 - 1 - X.degree v) ≤ edgeCountIn X (complClosedNbhd X v) := by
    intro v; rw [← hWcard v]; exact Mfloor_le_edgeCountIn_complNbhd h X hα3 hω hcap v
  have hN_ub : ∀ v, edgeCountIn X (X.neighborFinset v) ≤ ufloor (X.degree v) :=
    fun v => edgeCountIn_nbhd_le_ufloor X hω hcap v
  have hAff : ∀ v, 52 + 14 * X.degree v + 2 * ufloor (X.degree v)
      ≤ 2 * Mfloor (14 - 1 - X.degree v) + 2 * (X.degree v) ^ 2 + 12 * X.degree v := by
    intro v
    refine affineBound_14 (X.degree v) ?_ (degree_le_pred X v)
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

/-- Per-degree affine bound for `s = 15` (`twoA = 60, twoB = 12`), `d ∈ [4,14]`. -/
theorem affineBound_15 (d : ℕ) (hlo : 4 ≤ d) (hhi : d ≤ 14) :
    60 + 15 * d + 2 * ufloor d ≤ 2 * Mfloor (15 - 1 - d) + 2 * d ^ 2 + 12 * d := by
  interval_cases d <;> decide

/-- **L-table, s = 15: `L(15) = 38`.** -/
theorem L15 (h : PrimFacts) (X : SimpleGraph (Fin 15)) (hα3 : alphaAtMost X 3)
    (hω : X.CliqueFree 5) (hcap : capAtMost11 X) : 38 ≤ edgeCountIn X Finset.univ := by
  rw [edgeCountIn_univ_eq_card_edgeFinset]
  have hWcard : ∀ v, (complClosedNbhd X v).card = 15 - 1 - X.degree v := complNbhd_card X
  have hM_lb : ∀ v, Mfloor (15 - 1 - X.degree v) ≤ edgeCountIn X (complClosedNbhd X v) := by
    intro v; rw [← hWcard v]; exact Mfloor_le_edgeCountIn_complNbhd h X hα3 hω hcap v
  have hN_ub : ∀ v, edgeCountIn X (X.neighborFinset v) ≤ ufloor (X.degree v) :=
    fun v => edgeCountIn_nbhd_le_ufloor X hω hcap v
  have hAff : ∀ v, 60 + 15 * X.degree v + 2 * ufloor (X.degree v)
      ≤ 2 * Mfloor (15 - 1 - X.degree v) + 2 * (X.degree v) ^ 2 + 12 * X.degree v := by
    intro v
    refine affineBound_15 (X.degree v) ?_ (degree_le_pred X v)
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

/-- Per-degree affine bound for `s = 16` (`twoA = 68, twoB = 12`), `d ∈ [5,15]`. -/
theorem affineBound_16 (d : ℕ) (hlo : 5 ≤ d) (hhi : d ≤ 15) :
    68 + 16 * d + 2 * ufloor d ≤ 2 * Mfloor (16 - 1 - d) + 2 * d ^ 2 + 12 * d := by
  interval_cases d <;> decide

/-- **L-table, s = 16: `L(16) = 46`.** -/
theorem L16 (h : PrimFacts) (X : SimpleGraph (Fin 16)) (hα3 : alphaAtMost X 3)
    (hω : X.CliqueFree 5) (hcap : capAtMost11 X) : 46 ≤ edgeCountIn X Finset.univ := by
  rw [edgeCountIn_univ_eq_card_edgeFinset]
  have hWcard : ∀ v, (complClosedNbhd X v).card = 16 - 1 - X.degree v := complNbhd_card X
  have hM_lb : ∀ v, Mfloor (16 - 1 - X.degree v) ≤ edgeCountIn X (complClosedNbhd X v) := by
    intro v; rw [← hWcard v]; exact Mfloor_le_edgeCountIn_complNbhd h X hα3 hω hcap v
  have hN_ub : ∀ v, edgeCountIn X (X.neighborFinset v) ≤ ufloor (X.degree v) :=
    fun v => edgeCountIn_nbhd_le_ufloor X hω hcap v
  have hAff : ∀ v, 68 + 16 * X.degree v + 2 * ufloor (X.degree v)
      ≤ 2 * Mfloor (16 - 1 - X.degree v) + 2 * (X.degree v) ^ 2 + 12 * X.degree v := by
    intro v
    refine affineBound_16 (X.degree v) ?_ (degree_le_pred X v)
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

/-- Per-degree affine bound for `s = 17` (`twoA = 56, twoB = 9`), `d ∈ [6,16]`. -/
theorem affineBound_17 (d : ℕ) (hlo : 6 ≤ d) (hhi : d ≤ 16) :
    56 + 17 * d + 2 * ufloor d ≤ 2 * Mfloor (17 - 1 - d) + 2 * d ^ 2 + 9 * d := by
  interval_cases d <;> decide

/-- **L-table, s = 17: `L(17) = 53`.** -/
theorem L17 (h : PrimFacts) (X : SimpleGraph (Fin 17)) (hα3 : alphaAtMost X 3)
    (hω : X.CliqueFree 5) (hcap : capAtMost11 X) : 53 ≤ edgeCountIn X Finset.univ := by
  rw [edgeCountIn_univ_eq_card_edgeFinset]
  have hWcard : ∀ v, (complClosedNbhd X v).card = 17 - 1 - X.degree v := complNbhd_card X
  have hM_lb : ∀ v, Mfloor (17 - 1 - X.degree v) ≤ edgeCountIn X (complClosedNbhd X v) := by
    intro v; rw [← hWcard v]; exact Mfloor_le_edgeCountIn_complNbhd h X hα3 hω hcap v
  have hN_ub : ∀ v, edgeCountIn X (X.neighborFinset v) ≤ ufloor (X.degree v) :=
    fun v => edgeCountIn_nbhd_le_ufloor X hω hcap v
  have hAff : ∀ v, 56 + 17 * X.degree v + 2 * ufloor (X.degree v)
      ≤ 2 * Mfloor (17 - 1 - X.degree v) + 2 * (X.degree v) ^ 2 + 9 * X.degree v := by
    intro v
    refine affineBound_17 (X.degree v) ?_ (degree_le_pred X v)
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

/-- Per-degree affine bound for `s = 18` (`twoA = 68, twoB = 10`), `d ∈ [7,17]`. -/
theorem affineBound_18 (d : ℕ) (hlo : 7 ≤ d) (hhi : d ≤ 17) :
    68 + 18 * d + 2 * ufloor d ≤ 2 * Mfloor (18 - 1 - d) + 2 * d ^ 2 + 10 * d := by
  interval_cases d <;> decide

/-- **L-table, s = 18: `L(18) = 62`.** -/
theorem L18 (h : PrimFacts) (X : SimpleGraph (Fin 18)) (hα3 : alphaAtMost X 3)
    (hω : X.CliqueFree 5) (hcap : capAtMost11 X) : 62 ≤ edgeCountIn X Finset.univ := by
  rw [edgeCountIn_univ_eq_card_edgeFinset]
  have hWcard : ∀ v, (complClosedNbhd X v).card = 18 - 1 - X.degree v := complNbhd_card X
  have hM_lb : ∀ v, Mfloor (18 - 1 - X.degree v) ≤ edgeCountIn X (complClosedNbhd X v) := by
    intro v; rw [← hWcard v]; exact Mfloor_le_edgeCountIn_complNbhd h X hα3 hω hcap v
  have hN_ub : ∀ v, edgeCountIn X (X.neighborFinset v) ≤ ufloor (X.degree v) :=
    fun v => edgeCountIn_nbhd_le_ufloor X hω hcap v
  have hAff : ∀ v, 68 + 18 * X.degree v + 2 * ufloor (X.degree v)
      ≤ 2 * Mfloor (18 - 1 - X.degree v) + 2 * (X.degree v) ^ 2 + 10 * X.degree v := by
    intro v
    refine affineBound_18 (X.degree v) ?_ (degree_le_pred X v)
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

/-- Per-degree affine bound for `s = 19` (`twoA = 114, twoB = 15`), `d ∈ [8,18]`. -/
theorem affineBound_19 (d : ℕ) (hlo : 8 ≤ d) (hhi : d ≤ 18) :
    114 + 19 * d + 2 * ufloor d ≤ 2 * Mfloor (19 - 1 - d) + 2 * d ^ 2 + 15 * d := by
  interval_cases d <;> decide

/-- **L-table, s = 19: `L(19) = 73`.** -/
theorem L19 (h : PrimFacts) (X : SimpleGraph (Fin 19)) (hα3 : alphaAtMost X 3)
    (hω : X.CliqueFree 5) (hcap : capAtMost11 X) : 73 ≤ edgeCountIn X Finset.univ := by
  rw [edgeCountIn_univ_eq_card_edgeFinset]
  have hWcard : ∀ v, (complClosedNbhd X v).card = 19 - 1 - X.degree v := complNbhd_card X
  have hM_lb : ∀ v, Mfloor (19 - 1 - X.degree v) ≤ edgeCountIn X (complClosedNbhd X v) := by
    intro v; rw [← hWcard v]; exact Mfloor_le_edgeCountIn_complNbhd h X hα3 hω hcap v
  have hN_ub : ∀ v, edgeCountIn X (X.neighborFinset v) ≤ ufloor (X.degree v) :=
    fun v => edgeCountIn_nbhd_le_ufloor X hω hcap v
  have hAff : ∀ v, 114 + 19 * X.degree v + 2 * ufloor (X.degree v)
      ≤ 2 * Mfloor (19 - 1 - X.degree v) + 2 * (X.degree v) ^ 2 + 15 * X.degree v := by
    intro v
    refine affineBound_19 (X.degree v) ?_ (degree_le_pred X v)
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

end Erdos617
