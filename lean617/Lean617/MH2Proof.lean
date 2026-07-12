/-
Erdős Problem 617, r = 5 — milestone F7: the [MH″] assembly.

We prove `lemma_MH2_of (pf : PrimFacts) (bf : BrouwerFacts) : MH2`, following the
frozen reviewed proof `review_queue/mh2-gpt56-candidate.md` (the accepted text PLUS
the "Post-review repairs applied" section: §5 Case B is closed via the ω-free
11-vertex nonexistence `pf.nonex11`).

The shared L-table extension (`turan3_general`, `L20 = 84`, `Lfloor`,
`Lfloor_le_of_props`) lives in `Lean617/LTableExt.lean` (F7-owned, consumed by F8).

Structure (mirrors the informal §§):
  §1       reduction MH2 ⇐ (α(G_k−T) ≤ 4 gives False); the `Gc`/`col` context on Fin 21.
  §4.3     `edgeCount_ge_58` : α≤4, K₅-free, cap-11 on Fin 21 ⟹ e ≥ 58 (Ψ recursion).
  §3       `edgeCount_Fi_ge_38` : e(F_i) ≥ 38 (Brouwer 173 + equality exclusion).
  §5       `H_cliqueFree_five` : H is K₅-free.
  §6       equalities e(H)=58, e(F_i)=38.
  §7       endgame contradiction.

See FORMAL.md (F4/F5/F6 exports) for the consumed lemma shapes.

Research project: Mathlib style linters disabled.
-/
import Lean617.Brouwer
import Lean617.LTableExt

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.style.multiGoal false
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
set_option linter.style.setOption false
set_option maxHeartbeats 1000000

open Finset SimpleGraph
open scoped Classical

namespace Erdos617

/-! ## General graph helpers (clique edge counts, cap-11 ⟹ K₆-free, comap transport) -/

/-- The edges inside a clique `S` number exactly `C(|S|,2)`. -/
theorem edgeCountIn_clique {s : ℕ} (G : SimpleGraph (Fin s)) {S : Finset (Fin s)}
    (hS : G.IsClique ↑S) : edgeCountIn G S = S.card.choose 2 := by
  rw [← card_offdiag S]
  unfold edgeCountIn
  congr 1
  ext e
  revert e
  refine Sym2.ind (fun u v => ?_)
  simp only [Finset.mem_filter, Finset.mk_mem_sym2_iff, SimpleGraph.mem_edgeSet,
    Sym2.mk_isDiag_iff]
  constructor
  · rintro ⟨⟨hu, hv⟩, hadj⟩; exact ⟨⟨hu, hv⟩, G.ne_of_adj hadj⟩
  · rintro ⟨⟨hu, hv⟩, huv⟩
    rw [SimpleGraph.isClique_iff] at hS
    exact ⟨⟨hu, hv⟩, hS (Finset.mem_coe.mpr hu) (Finset.mem_coe.mpr hv) huv⟩

/-- Cap-11 forces `K₆`-freeness: a 6-clique would span `C(6,2) = 15 > 11` edges. -/
theorem cliqueFree6_of_capAtMost11 {s : ℕ} {G : SimpleGraph (Fin s)} (hcap : capAtMost11 G) :
    G.CliqueFree 6 := by
  intro S hS
  have hcard := hS.2
  have hc6 : (6 : ℕ).choose 2 = 15 := by decide
  have h15 : edgeCountIn G S = 15 := by rw [edgeCountIn_clique G hS.1, hcard, hc6]
  have := hcap S hcard
  omega

/-- `α ≤ m` transports across `comap` (general `m`; F5 only exported the `m = 2` case). -/
theorem alphaAtMost_comap_gen {s t m : ℕ} (X : SimpleGraph (Fin s)) (f : Fin t ↪ Fin s)
    (hα : ∀ S : Finset (Fin s), S ⊆ Finset.univ.image f → IsIndep X S → S.card ≤ m) :
    alphaAtMost (X.comap f) m := by
  intro S' hS'
  rw [isIndep_comap] at hS'
  have hsub : S'.image f ⊆ Finset.univ.image f :=
    Finset.image_subset_image (Finset.subset_univ S')
  have := hα (S'.image f) hsub hS'
  rwa [Finset.card_image_of_injective _ f.injective] at this

/-- `ω ≤ m` transports across `comap`: if `X`-cliques inside the image have card `≤ m`,
then `X.comap f` is `(m+1)`-clique-free. -/
theorem cliqueFree_comap_of {s t m : ℕ} (X : SimpleGraph (Fin s)) (f : Fin t ↪ Fin s)
    (hω : ∀ S : Finset (Fin s), S ⊆ Finset.univ.image f → X.IsClique ↑S → S.card ≤ m) :
    (X.comap f).CliqueFree (m + 1) := by
  intro S' hS'
  obtain ⟨hclq, hcard⟩ := hS'
  have himg : X.IsClique ↑(S'.image f) := by
    rw [SimpleGraph.isClique_iff] at hclq ⊢
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_image] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    have hab' : a' ≠ b' := fun h => hab (by rw [h])
    have := hclq (Finset.mem_coe.mpr ha') (Finset.mem_coe.mpr hb') hab'
    rwa [SimpleGraph.comap_adj] at this
  have hle := hω (S'.image f) (Finset.image_subset_image (Finset.subset_univ S')) himg
  rw [Finset.card_image_of_injective _ f.injective, hcard] at hle
  omega

/-- **`α ≤ 3` floor on a subset.** If `X` restricted to `W` (`|W| ≤ 20`) has `α ≤ 3`,
`ω ≤ 4`, and `X` is cap-11, then `Lfloor |W| ≤ e(X[W])`. Transports `X[W]` onto
`Fin |W|` and applies `Lfloor_le_of_props`. -/
theorem edgeCountIn_ge_Lfloor (h : PrimFacts) {s : ℕ} (X : SimpleGraph (Fin s))
    (W : Finset (Fin s)) (hW : W.card ≤ 20)
    (hαW : ∀ S : Finset (Fin s), S ⊆ W → IsIndep X S → S.card ≤ 3)
    (hωW : ∀ S : Finset (Fin s), S ⊆ W → X.IsClique ↑S → S.card ≤ 4)
    (hcap : capAtMost11 X) :
    Lfloor W.card ≤ edgeCountIn X W := by
  obtain ⟨f, hf⟩ := exists_embedding_image_eq W (rfl : W.card = W.card)
  have hEC : edgeCountIn (X.comap f) Finset.univ = edgeCountIn X W := by
    rw [edgeCountIn_comap, hf]
  rw [← hEC]
  refine Lfloor_le_of_props h hW (X.comap f) (alphaAtMost_comap_gen X f ?_)
    (cliqueFree_comap_of X f ?_) (capAtMost11_comap X f hcap)
  · intro S hSsub hSindep; rw [hf] at hSsub; exact hαW S hSsub hSindep
  · intro S hSsub hSclq; rw [hf] at hSsub; exact hωW S hSsub hSclq

/-- A clique bound from `CliqueFree`: an `X`-clique has card `≤ n` when `X` is
`(n+1)`-clique-free. -/
theorem clique_card_le_of_cliqueFree {s n : ℕ} {X : SimpleGraph (Fin s)}
    (hω : X.CliqueFree (n + 1)) {S : Finset (Fin s)} (hclq : X.IsClique ↑S) : S.card ≤ n := by
  by_contra hgt
  push Not at hgt
  obtain ⟨S', hS'sub, hS'card⟩ := Finset.exists_subset_card_eq (show n + 1 ≤ S.card by omega)
  have hclq' : X.IsClique ↑S' := by
    rw [SimpleGraph.isClique_iff] at hclq ⊢
    intro a ha b hb hab
    exact hclq (Finset.mem_coe.mpr (hS'sub (Finset.mem_coe.mp ha)))
      (Finset.mem_coe.mpr (hS'sub (Finset.mem_coe.mp hb))) hab
  exact hω S' ⟨hclq', hS'card⟩

/-- Extending a `W_v`-independent set by `v` stays `X`-independent, so `α(X) ≤ m`
forces `α(X[W_v]) ≤ m − 1` (delivered as `|S| + 1 ≤ m`). -/
theorem card_complNbhd_indep_succ {s m : ℕ} {X : SimpleGraph (Fin s)} (hα : alphaAtMost X m)
    {v : Fin s} {S : Finset (Fin s)} (hSW : S ⊆ complClosedNbhd X v) (hindep : IsIndep X S) :
    S.card + 1 ≤ m := by
  have hvS : v ∉ S := by
    intro hv; have hm := hSW hv; rw [mem_complClosedNbhd] at hm; exact hm.1 rfl
  have hins : IsIndep X (insert v S) := by
    intro a ha b hb hab
    rw [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact absurd rfl hab
    · have hm := hSW hb; rw [mem_complClosedNbhd] at hm; exact hm.2
    · have hm := hSW ha; rw [mem_complClosedNbhd] at hm; exact fun hh => hm.2 hh.symm
    · exact hindep a ha b hb hab
  have := hα (insert v S) hins
  rwa [Finset.card_insert_of_notMem hvS] at this

/-- Inserting `x ∉ Q` adds at least `x`'s `G`-edges into `Q`:
`e(G[Q]) + #{q ∈ Q : G.Adj x q} ≤ e(G[insert x Q])`. -/
theorem edgeCountIn_insert_ge {s : ℕ} (G : SimpleGraph (Fin s)) {x : Fin s} {Q : Finset (Fin s)}
    (hx : x ∉ Q) :
    edgeCountIn G Q + (Q.filter (fun q => G.Adj x q)).card ≤ edgeCountIn G (insert x Q) := by
  rw [edgeCountIn_eq_filter_edgeFinset G (insert x Q), edgeCountIn_eq_filter_edgeFinset G Q]
  set A := G.edgeFinset.filter (fun e => e ∈ (insert x Q).sym2) with hA
  set B := G.edgeFinset.filter (fun e => e ∈ Q.sym2) with hB
  set C := (Q.filter (fun q => G.Adj x q)).image (fun q => s(x, q)) with hC
  have hinj : Function.Injective (fun q : Fin s => s(x, q)) := by
    intro a b hab
    rw [Sym2.eq_iff] at hab
    rcases hab with ⟨_, h⟩ | ⟨h1, h2⟩
    · exact h
    · exact h2.trans h1
  have hCcard : C.card = (Q.filter (fun q => G.Adj x q)).card :=
    Finset.card_image_of_injective _ hinj
  have hsubBC : B ∪ C ⊆ A := by
    intro e he
    rw [Finset.mem_union] at he
    rcases he with he | he
    · rw [hB, Finset.mem_filter] at he
      rw [hA, Finset.mem_filter]
      exact ⟨he.1, Finset.sym2_mono (Finset.subset_insert x Q) he.2⟩
    · rw [hC, Finset.mem_image] at he
      obtain ⟨q, hq, rfl⟩ := he
      rw [Finset.mem_filter] at hq
      rw [hA, Finset.mem_filter]
      refine ⟨G.mem_edgeFinset.mpr hq.2, ?_⟩
      rw [Finset.mk_mem_sym2_iff]
      exact ⟨Finset.mem_insert_self x Q, Finset.mem_insert_of_mem hq.1⟩
  have hdisjBC : Disjoint B C := by
    rw [Finset.disjoint_left]
    intro e heB heC
    rw [hB, Finset.mem_filter] at heB
    rw [hC, Finset.mem_image] at heC
    obtain ⟨q, hq, rfl⟩ := heC
    have hmem := heB.2
    rw [Finset.mk_mem_sym2_iff] at hmem
    exact hx hmem.1
  calc B.card + (Q.filter (fun q => G.Adj x q)).card
      = B.card + C.card := by rw [hCcard]
    _ = (B ∪ C).card := (Finset.card_union_of_disjoint hdisjBC).symm
    _ ≤ A.card := Finset.card_le_card hsubBC

/-- **Brouwer floor on a 16-subset.** If `F` restricted to `W` (`|W| = 16`) is `K₄`-free
(`ω ≤ 3`) with `α ≤ 5`, then `e(F[W]) ≥ 20` (`120 − t₅(16) + ⌊16/5⌋ − 1 = 120 − 100`). -/
theorem brouwer_Fi_on16 (bf : BrouwerFacts) {s : ℕ} (F : SimpleGraph (Fin s)) (W : Finset (Fin s))
    (hWcard : W.card = 16)
    (hω3 : ∀ S : Finset (Fin s), S ⊆ W → F.IsClique ↑S → S.card ≤ 3)
    (hα5 : ∀ S : Finset (Fin s), S ⊆ W → IsIndep F S → S.card ≤ 5) :
    20 ≤ edgeCountIn F W := by
  obtain ⟨g, hg⟩ := exists_embedding_image_eq W hWcard
  have hEC : edgeCountIn (F.comap g) Finset.univ = edgeCountIn F W := by rw [edgeCountIn_comap, hg]
  have hFWcf4 : (F.comap g).CliqueFree 4 :=
    cliqueFree_comap_of F g (fun S hS hclq => hω3 S (by rw [hg] at hS; exact hS) hclq)
  have hFWa5 : alphaAtMost (F.comap g) 5 :=
    alphaAtMost_comap_gen F g (fun S hS hind => hα5 S (by rw [hg] at hS; exact hS) hind)
  have hJcf6 : (F.comap g)ᶜ.CliqueFree 6 :=
    compl_cliqueFree_six_of_alphaAtMost_five (F.comap g) hFWa5
  have hJa3 : alphaAtMost (F.comap g)ᶜ 3 := by
    rw [alphaAtMost_iff_compl_cliqueFree, compl_compl]; exact hFWcf4
  have hJ100 := brouwer_bound_16 bf (F.comap g)ᶜ hJcf6 hJa3
  have hadd := edgeCountIn_add_compl (F.comap g)
  have h120 : (16 : ℕ).choose 2 = 120 := by decide
  omega

/-- A nonzero edge count yields an actual edge inside the set. -/
theorem exists_edge_of_edgeCountIn_pos {s : ℕ} (G : SimpleGraph (Fin s)) {S : Finset (Fin s)}
    (h : 1 ≤ edgeCountIn G S) : ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ G.Adj u v := by
  rw [edgeCountIn] at h
  obtain ⟨e, he⟩ := Finset.card_pos.mp h
  rw [Finset.mem_filter] at he
  obtain ⟨hemem, hedge⟩ := he
  revert hemem hedge
  induction e using Sym2.ind with
  | _ u v =>
    intro hemem hedge
    rw [Finset.mk_mem_sym2_iff] at hemem
    rw [SimpleGraph.mem_edgeSet] at hedge
    exact ⟨u, hemem.1, v, hemem.2, G.ne_of_adj hedge, hedge⟩

/-- **Edge count of a disjoint union, `≤` form.** Every edge inside `A ∪ B` is within `A`,
within `B`, or crossing; each crossing edge injects into an adjacent `A × B` pair. -/
theorem edgeCountIn_union_le_cross {s : ℕ} (G : SimpleGraph (Fin s)) {A B : Finset (Fin s)} :
    edgeCountIn G (A ∪ B) ≤ edgeCountIn G A + edgeCountIn G B
      + ((A ×ˢ B).filter (fun p => G.Adj p.1 p.2)).card := by
  rw [edgeCountIn_eq_filter_edgeFinset G (A ∪ B), edgeCountIn_eq_filter_edgeFinset G A,
    edgeCountIn_eq_filter_edgeFinset G B]
  set fA := G.edgeFinset.filter (fun e => e ∈ A.sym2) with hfA
  set fB := G.edgeFinset.filter (fun e => e ∈ B.sym2) with hfB
  set crossI := ((A ×ˢ B).filter (fun p => G.Adj p.1 p.2)).image (fun p => s(p.1, p.2)) with hcI
  have hsub : G.edgeFinset.filter (fun e => e ∈ (A ∪ B).sym2) ⊆ fA ∪ fB ∪ crossI := by
    intro e he
    revert he
    induction e using Sym2.ind with
    | _ u v =>
      intro he
      rw [Finset.mem_filter, Finset.mk_mem_sym2_iff] at he
      obtain ⟨heEdge, hu, hv⟩ := he
      have hadj : G.Adj u v := by rw [← SimpleGraph.mem_edgeSet]; exact G.mem_edgeFinset.mp heEdge
      rw [Finset.mem_union] at hu hv
      rw [Finset.mem_union, Finset.mem_union]
      rcases hu with hu | hu <;> rcases hv with hv | hv
      · exact Or.inl (Or.inl (Finset.mem_filter.mpr ⟨heEdge, Finset.mk_mem_sym2_iff.mpr ⟨hu, hv⟩⟩))
      · refine Or.inr ?_
        rw [hcI, Finset.mem_image]
        exact ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu, hv⟩, hadj⟩, rfl⟩
      · refine Or.inr ?_
        rw [hcI, Finset.mem_image]
        exact ⟨(v, u), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hv, hu⟩, G.symm hadj⟩,
          Sym2.eq_swap⟩
      · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨heEdge, Finset.mk_mem_sym2_iff.mpr ⟨hu, hv⟩⟩))
  calc (G.edgeFinset.filter (fun e => e ∈ (A ∪ B).sym2)).card
      ≤ (fA ∪ fB ∪ crossI).card := Finset.card_le_card hsub
    _ ≤ (fA ∪ fB).card + crossI.card := Finset.card_union_le _ _
    _ ≤ fA.card + fB.card + ((A ×ˢ B).filter (fun p => G.Adj p.1 p.2)).card := by
        have h1 := Finset.card_union_le fA fB
        have h2 : crossI.card ≤ ((A ×ˢ B).filter (fun p => G.Adj p.1 p.2)).card :=
          Finset.card_image_le
        omega

/-! ## The [MH″] context and the graph-theoretic contradiction

`MH2Ctx` packages the five colour graphs on `Fin 21` (the 21 non-`T` vertices)
together with the properties inherited from balancedness of the ambient `K₂₅` and the
`α(G_k − T) ≤ 4` assumption. §§3–7 prove `MH2Ctx → False`; §1 builds the context. -/

/-- The colour graphs on the 21 non-`T` vertices, with their inherited properties. -/
structure MH2Ctx where
  /-- The five colour graphs, relabelled onto `Fin 21`. -/
  Gc : Fin 5 → SimpleGraph (Fin 21)
  /-- The special colour (`H := Gc k`). -/
  k : Fin 5
  /-- The colour of the pair `{u,v}`. -/
  col : Fin 21 → Fin 21 → Fin 5
  /-- Adjacency in `Gc i` means `{u,v}` has colour `i`. -/
  adj_iff : ∀ (i : Fin 5) (u v : Fin 21), (Gc i).Adj u v ↔ u ≠ v ∧ col u v = i
  /-- Cap-11 on every colour graph (from balancedness). -/
  cap : ∀ i, capAtMost11 (Gc i)
  /-- Every colour graph has independence number ≤ 5 (from balancedness). -/
  alpha5 : ∀ i, alphaAtMost (Gc i) 5
  /-- `α(H) ≤ 4` (the `α(G_k − T) ≤ 4` assumption). -/
  alphaH : alphaAtMost (Gc k) 4
  /-- The five colours partition the pairs of every subset. -/
  edgeSumOn : ∀ W : Finset (Fin 21), ∑ i, edgeCountIn (Gc i) W = W.card.choose 2
  /-- Every 6-set sees every colour (the balanced property, on the 21 vertices). -/
  sees6 : ∀ (S : Finset (Fin 21)), S.card = 6 → ∀ c' : Fin 5, 1 ≤ edgeCountIn (Gc c') S

namespace MH2Ctx

variable (ctx : MH2Ctx)

/-- `H := Gc k`, the special colour graph. -/
abbrev H : SimpleGraph (Fin 21) := ctx.Gc ctx.k

/-- Colour is symmetric on distinct pairs. -/
theorem col_symm {u v : Fin 21} (huv : u ≠ v) : ctx.col u v = ctx.col v u := by
  have h1 : (ctx.Gc (ctx.col u v)).Adj u v := (ctx.adj_iff _ u v).mpr ⟨huv, rfl⟩
  have h2 := h1.symm
  exact ((ctx.adj_iff _ v u).mp h2).2.symm

/-- Distinct colour graphs are edge-disjoint. -/
theorem col_uniq {i j : Fin 5} {u v : Fin 21} (hi : (ctx.Gc i).Adj u v)
    (hj : (ctx.Gc j).Adj u v) : i = j := by
  rw [ctx.adj_iff] at hi hj; rw [← hi.2, ← hj.2]

/-- Cap-11 ⟹ every colour graph is `K₆`-free. -/
theorem cliqueFree6 (i : Fin 5) : (ctx.Gc i).CliqueFree 6 :=
  cliqueFree6_of_capAtMost11 (ctx.cap i)

/-- Every ordinary colour graph is `K₅`-free: a `Gc i`-`K₅` (`i ≠ k`) is `H`-independent. -/
theorem cliqueFree5_ordinary {i : Fin 5} (hik : i ≠ ctx.k) : (ctx.Gc i).CliqueFree 5 := by
  intro S hS
  obtain ⟨hclq, hcard⟩ := hS
  have hindep : IsIndep ctx.H S := by
    intro u hu v hv huv hHadj
    have hi : (ctx.Gc i).Adj u v :=
      hclq (Finset.mem_coe.mpr hu) (Finset.mem_coe.mpr hv) huv
    have hcoli : ctx.col u v = i := ((ctx.adj_iff i u v).mp hi).2
    have hk : ctx.col u v = ctx.k := ((ctx.adj_iff ctx.k u v).mp hHadj).2
    exact hik (hcoli ▸ hk ▸ rfl)
  have := ctx.alphaH S hindep
  omega

end MH2Ctx

/-! ## §4.3 → (4.10): `e(H) ≥ 58` for `K₅`-free `H`

A general `Fin 21` lemma: `α ≤ 4`, `K₅`-free, cap-11 ⟹ `e ≥ 58`, by the `Ψ` recursion
(F4 identity + per-vertex `Lfloor(20−d)`/`ufloor(d)` bounds + the affine bound
`Ψ(d) ≥ 52 − 19d/2`, verified pointwise for `d ∈ [0,20]`). -/

/-- Per-degree affine bound for the `Ψ` recursion (`twoA = 104, s = 21, twoB = 19`),
checked over `d ∈ [0,20]` by `decide` (scratchpad/check_f7_arith.py; equality at `d = 5,6`). -/
theorem affineBoundPsi (d : ℕ) (hhi : d ≤ 20) :
    104 + 21 * d + 2 * ufloor d ≤ 2 * Lfloor (20 - d) + 2 * d ^ 2 + 19 * d := by
  interval_cases d <;> decide

/-- **(4.10): `e(H) ≥ 58`.** Any `K₅`-free, `α ≤ 4`, cap-11 graph on `Fin 21` has
`≥ 58` edges. Applied to `H`. Assembly mirrors F5's `L20` with `Lfloor(20−d)` per-vertex
floors and the `Ψ` affine bound. -/
theorem edgeCount_ge_58 (h : PrimFacts) (X : SimpleGraph (Fin 21))
    (hα4 : alphaAtMost X 4) (hω : X.CliqueFree 5) (hcap : capAtMost11 X) :
    58 ≤ edgeCountIn X Finset.univ := by
  rw [edgeCountIn_univ_eq_card_edgeFinset]
  have hWcard : ∀ v, (complClosedNbhd X v).card = 20 - X.degree v := by
    intro v; rw [complNbhd_card X v]
  have hL_lb : ∀ v, Lfloor (20 - X.degree v) ≤ edgeCountIn X (complClosedNbhd X v) := by
    intro v
    rw [← hWcard v]
    refine edgeCountIn_ge_Lfloor h X (complClosedNbhd X v) (by rw [hWcard v]; omega) ?_ ?_ hcap
    · intro S hSsub hSindep
      have := card_complNbhd_indep_succ hα4 hSsub hSindep; omega
    · intro S _ hSclq
      exact clique_card_le_of_cliqueFree hω hSclq
  have hN_ub : ∀ v, edgeCountIn X (X.neighborFinset v) ≤ ufloor (X.degree v) :=
    fun v => edgeCountIn_nbhd_le_ufloor X hω hcap v
  have hAff : ∀ v, 104 + 21 * X.degree v + 2 * ufloor (X.degree v)
      ≤ 2 * Lfloor (20 - X.degree v) + 2 * (X.degree v) ^ 2 + 19 * X.degree v :=
    fun v => affineBoundPsi (X.degree v) (by have := degree_le_pred X v; omega)
  have hId := sum_edgeCountIn_compl_nbhd_add_sq_deg X
  have hDeg := X.sum_degrees_eq_twice_card_edges
  have hPL := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hL_lb v)
  have hSN := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hN_ub v)
  have hAffSum := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hAff v)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at hAffSum
  omega

/-! ## §3: `e(F_i) ≥ 38` for ordinary colours -/

/-- **(3.2): `e(F_i) ≥ 38`.** Brouwer gives `e(F_i) ≥ 37`; equality `= 37` forces the
`(4,4,4,4,4)` extremal `A/B` structure, and the six-sets `B ∪ {a,a'}` then carry
`4 (i) + 5 (H) + 3·4 (other ordinary) = 21 > 20` cross-edges, a contradiction. -/
theorem MH2Ctx.edgeCount_Fi_ge_38 (ctx : MH2Ctx) (bf : BrouwerFacts)
    {i : Fin 5} (hik : i ≠ ctx.k) : 38 ≤ edgeCountIn (ctx.Gc i) Finset.univ := by
  have hcf5 : (ctx.Gc i).CliqueFree 5 := ctx.cliqueFree5_ordinary hik
  have hJcf6 : (ctx.Gc i)ᶜ.CliqueFree 6 :=
    compl_cliqueFree_six_of_alphaAtMost_five (ctx.Gc i) (ctx.alpha5 i)
  have hJa4 : alphaAtMost (ctx.Gc i)ᶜ 4 :=
    alphaAtMost_compl_four_of_cliqueFree_five (ctx.Gc i) hcf5
  have hJ173 := brouwer_bound_21 bf (ctx.Gc i)ᶜ hJcf6 hJa4
  have hadd := edgeCountIn_add_compl (ctx.Gc i)
  have h210 : (21 : ℕ).choose 2 = 210 := by decide
  by_contra hlt
  push Not at hlt
  have he37 : edgeCountIn (ctx.Gc i) Finset.univ = 37 := by omega
  obtain ⟨A, B, hAB, hAcard, hBcard, ⟨x, hxA, y, hyA, hxy, hxynadj, hAstruct⟩,
    hBclique, hABedges⟩ := brouwer_21_equality bf (ctx.Gc i) (ctx.alpha5 i) hcf5 he37
  -- (a) the sole non-`i` edge `xy` of `A` is an `H`-edge
  have hxyH : ctx.col x y = ctx.k := by
    by_contra hne
    have hAindep : IsIndep ctx.H A := by
      intro u hu w hw huw hHadj
      have hcolk : ctx.col u w = ctx.k := ((ctx.adj_iff ctx.k u w).mp hHadj).2
      have hnadj : ¬ (ctx.Gc i).Adj u w := by
        intro hadj
        exact hik ((((ctx.adj_iff i u w).mp hadj).2) ▸ hcolk)
      rcases (hAstruct u hu w hw huw).mp hnadj with ⟨hux, hwy⟩ | ⟨huy, hwx⟩
      · rw [hux, hwy] at hcolk; exact hne hcolk
      · rw [huy, hwx, ← ctx.col_symm hxy] at hcolk; exact hne hcolk
    have := ctx.alphaH A hAindep; omega
  -- colours of `A`-pairs are `i` or `k`
  have hAcol : ∀ u ∈ A, ∀ w ∈ A, u ≠ w → ctx.col u w = i ∨ ctx.col u w = ctx.k := by
    intro u hu w hw huw
    by_cases hadj : (ctx.Gc i).Adj u w
    · exact Or.inl ((ctx.adj_iff i u w).mp hadj).2
    · rcases (hAstruct u hu w hw huw).mp hadj with ⟨hux, hwy⟩ | ⟨huy, hwx⟩
      · rw [hux, hwy]; exact Or.inr hxyH
      · rw [huy, hwx, ← ctx.col_symm hxy]; exact Or.inr hxyH
  -- cross-pair colour counts on `A × B`
  set cross : Fin 5 → ℕ :=
    fun c' => ((A ×ˢ B).filter (fun p => ctx.col p.1 p.2 = c')).card with hcrossdef
  have hsumcross : ∑ c' : Fin 5, cross c' = 20 := by
    have hcnt := Finset.card_eq_sum_card_fiberwise (s := A ×ˢ B)
      (f := fun p => ctx.col p.1 p.2) (t := (Finset.univ : Finset (Fin 5)))
      (fun p _ => Finset.mem_univ _)
    rw [Finset.card_product, hAcard, hBcard] at hcnt
    simp only [] at hcnt
    simp only [hcrossdef]; omega
  -- colour `i`: exactly 4 cross edges (≥ 4 suffices)
  have hkA1 : 1 ≤ edgeCountIn (ctx.Gc ctx.k) A := by
    rw [edgeCountIn]
    apply Finset.card_pos.mpr
    refine ⟨s(x, y), Finset.mem_filter.mpr ⟨Finset.mk_mem_sym2_iff.mpr ⟨hxA, hyA⟩, ?_⟩⟩
    rw [SimpleGraph.mem_edgeSet]; exact (ctx.adj_iff ctx.k x y).mpr ⟨hxy, hxyH⟩
  have heiA : edgeCountIn (ctx.Gc i) A ≤ 9 := by
    have hsumA := ctx.edgeSumOn A
    rw [hAcard] at hsumA
    have h5c : (5 : ℕ).choose 2 = 10 := by decide
    have htwo : edgeCountIn (ctx.Gc i) A + edgeCountIn (ctx.Gc ctx.k) A
        ≤ ∑ c', edgeCountIn (ctx.Gc c') A := by
      have hsub := Finset.sum_le_sum_of_subset (f := fun c' => edgeCountIn (ctx.Gc c') A)
        (Finset.subset_univ ({i, ctx.k} : Finset (Fin 5)))
      rwa [Finset.sum_pair hik] at hsub
    omega
  have heiB : edgeCountIn (ctx.Gc i) B ≤ 6 := by
    have hb := edgeCountIn_le_choose_two (ctx.Gc i) B
    rw [hBcard] at hb
    have h4c : (4 : ℕ).choose 2 = 6 := by decide
    omega
  have hcolAdj : (A ×ˢ B).filter (fun p => ctx.col p.1 p.2 = i)
      = (A ×ˢ B).filter (fun p => (ctx.Gc i).Adj p.1 p.2) := by
    apply Finset.filter_congr
    intro p hp
    rw [Finset.mem_product] at hp
    have hne : p.1 ≠ p.2 := fun heq => Finset.disjoint_left.mp hAB hp.1 (heq ▸ hp.2)
    rw [ctx.adj_iff]
    exact ⟨fun hc => ⟨hne, hc⟩, fun h => h.2⟩
  have hcrossi : 4 ≤ cross i := by
    simp only [hcrossdef]
    rw [hcolAdj]
    have huc := edgeCountIn_union_le_cross (ctx.Gc i) (A := A) (B := B)
    omega
  -- colour `k` (`H`): each `a ∈ A` has an `H`-neighbour in `B`
  have hcrossk : 5 ≤ cross ctx.k := by
    have hAsub : A ⊆ ((A ×ˢ B).filter (fun p => ctx.col p.1 p.2 = ctx.k)).image Prod.fst := by
      intro a ha
      have hb : ∃ b ∈ B, ctx.col a b = ctx.k := by
        by_contra hcon
        push Not at hcon
        have hanotB : a ∉ B := fun hb => Finset.disjoint_left.mp hAB ha hb
        have hindep : IsIndep ctx.H (insert a B) := by
          intro u hu w hw huw hHadj
          have hcolk : ctx.col u w = ctx.k := ((ctx.adj_iff ctx.k u w).mp hHadj).2
          rw [Finset.mem_insert] at hu hw
          rcases hu with rfl | hu <;> rcases hw with rfl | hw
          · exact absurd rfl huw
          · exact hcon w hw hcolk
          · rw [ctx.col_symm huw] at hcolk; exact hcon u hu hcolk
          · exact hik ((((ctx.adj_iff i u w).mp (hBclique u hu w hw huw)).2) ▸ hcolk)
        have hc5 : (insert a B).card = 5 := by rw [Finset.card_insert_of_notMem hanotB, hBcard]
        have := ctx.alphaH (insert a B) hindep; omega
      obtain ⟨b, hbB, hcolk⟩ := hb
      exact Finset.mem_image.mpr
        ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hbB⟩, hcolk⟩, rfl⟩
    calc 5 = A.card := hAcard.symm
      _ ≤ (((A ×ˢ B).filter (fun p => ctx.col p.1 p.2 = ctx.k)).image Prod.fst).card :=
          Finset.card_le_card hAsub
      _ ≤ cross ctx.k := by rw [hcrossdef]; exact Finset.card_image_le
  -- colour `j` (other ordinary): at most one `a ∈ A` lacks a `j`-neighbour in `B`
  have hcrossj : ∀ j : Fin 5, j ≠ i → j ≠ ctx.k → 4 ≤ cross j := by
    intro j hji hjk
    have hbad : (A.filter (fun a => ¬ ∃ b ∈ B, ctx.col a b = j)).card ≤ 1 := by
      by_contra hgt
      push Not at hgt
      obtain ⟨a1, ha1, a2, ha2, hne12⟩ := Finset.one_lt_card.mp (by omega)
      rw [Finset.mem_filter] at ha1 ha2
      have ha1A := ha1.1; have ha2A := ha2.1
      have ha1no := ha1.2; have ha2no := ha2.2
      have ha1B : a1 ∉ B := fun hb => Finset.disjoint_left.mp hAB ha1A hb
      have ha2B : a2 ∉ B := fun hb => Finset.disjoint_left.mp hAB ha2A hb
      have hset6 : (insert a1 (insert a2 B)).card = 6 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ha2B, hBcard]
        rw [Finset.mem_insert]; push Not; exact ⟨hne12, ha1B⟩
      obtain ⟨u, hu, v, hv, huv, hjadj⟩ :=
        exists_edge_of_edgeCountIn_pos (ctx.Gc j) (ctx.sees6 _ hset6 j)
      have hcolj : ctx.col u v = j := ((ctx.adj_iff j u v).mp hjadj).2
      -- no `j`-edge can exist in `B ∪ {a1,a2}`
      rw [Finset.mem_insert, Finset.mem_insert] at hu hv
      rcases hu with hua1 | hua2 | huB <;> rcases hv with hva1 | hva2 | hvB
      · exact huv (hua1.trans hva1.symm)
      · rw [hua1, hva2] at hcolj
        rcases hAcol a1 ha1A a2 ha2A hne12 with hc | hc
        · exact hji (hcolj.symm.trans hc)
        · exact hjk (hcolj.symm.trans hc)
      · rw [hua1] at hcolj; exact ha1no v hvB hcolj
      · rw [hua2, hva1] at hcolj
        rcases hAcol a2 ha2A a1 ha1A hne12.symm with hc | hc
        · exact hji (hcolj.symm.trans hc)
        · exact hjk (hcolj.symm.trans hc)
      · exact huv (hua2.trans hva2.symm)
      · rw [hua2] at hcolj; exact ha2no v hvB hcolj
      · have huna1 : u ≠ a1 := fun hh => huv (hh.trans hva1.symm)
        rw [hva1, ctx.col_symm huna1] at hcolj; exact ha1no u huB hcolj
      · have huna2 : u ≠ a2 := fun hh => huv (hh.trans hva2.symm)
        rw [hva2, ctx.col_symm huna2] at hcolj; exact ha2no u huB hcolj
      · exact hji (hcolj.symm.trans ((ctx.adj_iff i u v).mp (hBclique u huB v hvB huv)).2)
    have hAsub : (A \ A.filter (fun a => ¬ ∃ b ∈ B, ctx.col a b = j))
        ⊆ ((A ×ˢ B).filter (fun p => ctx.col p.1 p.2 = j)).image Prod.fst := by
      intro a ha
      rw [Finset.mem_sdiff, Finset.mem_filter] at ha
      have haA := ha.1
      have hex : ∃ b ∈ B, ctx.col a b = j := by
        by_contra hcon; exact ha.2 ⟨haA, hcon⟩
      obtain ⟨b, hbB, hcolj⟩ := hex
      exact Finset.mem_image.mpr
        ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨haA, hbB⟩, hcolj⟩, rfl⟩
    have hcard : 4 ≤ (A \ A.filter (fun a => ¬ ∃ b ∈ B, ctx.col a b = j)).card := by
      rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _), hAcard]; omega
    calc (4 : ℕ) ≤ (A \ A.filter (fun a => ¬ ∃ b ∈ B, ctx.col a b = j)).card := hcard
      _ ≤ (((A ×ˢ B).filter (fun p => ctx.col p.1 p.2 = j)).image Prod.fst).card :=
          Finset.card_le_card hAsub
      _ ≤ cross j := by rw [hcrossdef]; exact Finset.card_image_le
  -- the 20 cross edges carry ≥ 21 colour-weighted edges
  have hle : ∑ c' : Fin 5, (if c' = ctx.k then (5 : ℕ) else 4) ≤ ∑ c', cross c' :=
    Finset.sum_le_sum (fun c' _ => by
      by_cases hck : c' = ctx.k
      · rw [if_pos hck, hck]; exact hcrossk
      · rw [if_neg hck]
        by_cases hci : c' = i
        · rw [hci]; exact hcrossi
        · exact hcrossj c' hci hck)
  have hsumlb : ∑ c' : Fin 5, (if c' = ctx.k then (5 : ℕ) else 4) = 21 := by
    have hexp : ∀ c' : Fin 5, (if c' = ctx.k then (5 : ℕ) else 4)
        = 4 + (if c' = ctx.k then 1 else 0) := fun c' => by split <;> rfl
    simp_rw [hexp, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ ctx.k (fun _ => (1 : ℕ))]
    simp [Finset.sum_const, Finset.card_univ]
  rw [hsumlb, hsumcross] at hle
  omega

/-! ## §5: `H` is `K₅`-free -/

/-- **(5.4): `H` is `K₅`-free.** If `H` had a `K₅` `Q`, then on `X = V∖Q` (16 vertices)
every vertex has ≤ 1 `H`-neighbour in `Q` (5.1), so `α(H[X]) ≤ 3` (5.2); a second `K₅`
`R ⊆ X` would make `X∖R` an 11-vertex `α ≤ 2` cap-11 graph (`pf.nonex11`, vacuous), so
`H[X]` is `K₅`-free and `e(H[X]) ≥ L(16) = 46`, while each ordinary `e(F_i[X]) ≥ 20`;
`46 + 4·20 = 126 > 120 = C(16,2)`. -/
theorem MH2Ctx.H_cliqueFree5 (ctx : MH2Ctx) (h : PrimFacts) (bf : BrouwerFacts) :
    ctx.H.CliqueFree 5 := by
  intro Q hQ
  obtain ⟨hQclq, hQcard⟩ := hQ
  -- (5.1), for any H-K₅
  have h51 : ∀ K : Finset (Fin 21), ctx.H.IsNClique 5 K → ∀ x, x ∉ K →
      (K.filter (fun q => ctx.H.Adj x q)).card ≤ 1 := by
    intro K hK x hxK
    obtain ⟨hKclq, hKcard⟩ := hK
    have hc5 : (5 : ℕ).choose 2 = 10 := by decide
    have heK : edgeCountIn ctx.H K = 10 := by
      rw [edgeCountIn_clique ctx.H hKclq, hKcard, hc5]
    have hins_card : (insert x K).card = 6 := by rw [Finset.card_insert_of_notMem hxK, hKcard]
    have hcap : edgeCountIn ctx.H (insert x K) ≤ 11 := ctx.cap ctx.k (insert x K) hins_card
    have hge := edgeCountIn_insert_ge ctx.H hxK
    omega
  set X := Finset.univ \ Q with hXdef
  have hXcard : X.card = 16 := by
    rw [hXdef, Finset.card_sdiff_of_subset (Finset.subset_univ Q), Finset.card_univ,
      Fintype.card_fin, hQcard]
  have hmemX : ∀ x, x ∈ X ↔ x ∉ Q := by
    intro x; rw [hXdef, Finset.mem_sdiff]; simp only [Finset.mem_univ, true_and]
  -- (5.2): α(H[X]) ≤ 3
  have h52 : ∀ Y : Finset (Fin 21), Y ⊆ X → IsIndep ctx.H Y → Y.card ≤ 3 := by
    intro Y hYX hYindep
    by_contra hgt
    push Not at hgt
    obtain ⟨Y4, hY4sub, hY4card⟩ := Finset.exists_subset_card_eq (show 4 ≤ Y.card by omega)
    have hbound : (Q.filter (fun q => ∃ y ∈ Y4, ctx.H.Adj y q)).card ≤ 4 := by
      calc (Q.filter (fun q => ∃ y ∈ Y4, ctx.H.Adj y q)).card
          ≤ (Y4.biUnion (fun y => Q.filter (fun q => ctx.H.Adj y q))).card := by
            apply Finset.card_le_card
            intro q hq
            rw [Finset.mem_filter] at hq
            obtain ⟨hqQ, y, hy, hadj⟩ := hq
            rw [Finset.mem_biUnion]
            exact ⟨y, hy, Finset.mem_filter.mpr ⟨hqQ, hadj⟩⟩
        _ ≤ ∑ y ∈ Y4, (Q.filter (fun q => ctx.H.Adj y q)).card := Finset.card_biUnion_le
        _ ≤ ∑ _y ∈ Y4, 1 :=
            Finset.sum_le_sum (fun y hy =>
              h51 Q ⟨hQclq, hQcard⟩ y ((hmemX y).mp (hYX (hY4sub hy))))
        _ = 4 := by rw [Finset.sum_const, hY4card, smul_eq_mul, mul_one]
    have hex : ∃ q ∈ Q, ∀ y ∈ Y4, ¬ ctx.H.Adj y q := by
      by_contra hcon
      push Not at hcon
      have hQsub : Q ⊆ Q.filter (fun q => ∃ y ∈ Y4, ctx.H.Adj y q) :=
        fun q hq => Finset.mem_filter.mpr ⟨hq, hcon q hq⟩
      have := Finset.card_le_card hQsub
      rw [hQcard] at this; omega
    obtain ⟨q, hqQ, hqavoid⟩ := hex
    have hqnotY4 : q ∉ Y4 := fun hq => ((hmemX q).mp (hYX (hY4sub hq))) hqQ
    have hindep5 : IsIndep ctx.H (insert q Y4) := by
      intro a ha b hb hab
      rw [Finset.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact fun hadj => hqavoid b hb (ctx.H.symm hadj)
      · exact fun hadj => hqavoid a ha hadj
      · exact hYindep a (hY4sub ha) b (hY4sub hb) hab
    have hcard5 : (insert q Y4).card = 5 := by rw [Finset.card_insert_of_notMem hqnotY4, hY4card]
    have := ctx.alphaH (insert q Y4) hindep5
    omega
  -- Case B vacuous: no second H-K₅ in X
  have hnoR : ¬ ∃ R : Finset (Fin 21), R ⊆ X ∧ ctx.H.IsNClique 5 R := by
    rintro ⟨R, hRX, hRc, hRcard⟩
    set L := X \ R with hLdef
    have hLcard : L.card = 11 := by
      rw [hLdef, Finset.card_sdiff_of_subset hRX, hXcard, hRcard]
    have hLX : L ⊆ X := by rw [hLdef]; exact Finset.sdiff_subset
    -- α(H[L]) ≤ 2, via the triple-extension using q ∈ Q, r ∈ R
    have hαL2 : ∀ Z : Finset (Fin 21), Z ⊆ L → IsIndep ctx.H Z → Z.card ≤ 2 := by
      intro Z hZL hZindep
      by_contra hgt
      push Not at hgt
      obtain ⟨Z3, hZ3sub, hZ3card⟩ := Finset.exists_subset_card_eq (show 3 ≤ Z.card by omega)
      have hZ3indep : IsIndep ctx.H Z3 :=
        fun a ha b hb hab => hZindep a (hZ3sub ha) b (hZ3sub hb) hab
      have hZ3notQ : ∀ z ∈ Z3, z ∉ Q := fun z hz => (hmemX z).mp (hLX (hZL (hZ3sub hz)))
      have hZ3notR : ∀ z ∈ Z3, z ∉ R := fun z hz =>
        (Finset.mem_sdiff.mp (hZL (hZ3sub hz))).2
      -- helper: `Z3` sends ≤ 3 H-edges into any H-K₅ `K` disjoint from `Z3`
      have hZ3bad : ∀ (K : Finset (Fin 21)), ctx.H.IsNClique 5 K → (∀ z ∈ Z3, z ∉ K) →
          (K.filter (fun w => ∃ z ∈ Z3, ctx.H.Adj z w)).card ≤ 3 := by
        intro K hK hKZ
        calc (K.filter (fun w => ∃ z ∈ Z3, ctx.H.Adj z w)).card
            ≤ (Z3.biUnion (fun z => K.filter (fun w => ctx.H.Adj z w))).card := by
              apply Finset.card_le_card
              intro w hw
              rw [Finset.mem_filter] at hw
              obtain ⟨hwK, z, hz, hadj⟩ := hw
              exact Finset.mem_biUnion.mpr ⟨z, hz, Finset.mem_filter.mpr ⟨hwK, hadj⟩⟩
          _ ≤ ∑ z ∈ Z3, (K.filter (fun w => ctx.H.Adj z w)).card := Finset.card_biUnion_le
          _ ≤ ∑ _z ∈ Z3, 1 :=
              Finset.sum_le_sum (fun z hz => h51 K hK z (hKZ z hz))
          _ = 3 := by rw [Finset.sum_const, hZ3card, smul_eq_mul, mul_one]
      -- pick q ∈ Q avoiding Z3 (Q ∖ bad has ≥ 5 − 3 = 2 vertices)
      have hQbad := hZ3bad Q ⟨hQclq, hQcard⟩ hZ3notQ
      have hQgood : 0 < (Q \ Q.filter (fun q => ∃ z ∈ Z3, ctx.H.Adj z q)).card := by
        rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _), hQcard]; omega
      obtain ⟨q, hqmem⟩ := Finset.card_pos.mp hQgood
      rw [Finset.mem_sdiff, Finset.mem_filter] at hqmem
      have hqQ : q ∈ Q := hqmem.1
      have hqavoid : ∀ z ∈ Z3, ¬ ctx.H.Adj z q :=
        fun z hz hadj => hqmem.2 ⟨hqQ, z, hz, hadj⟩
      have hqR : q ∉ R := fun hqR => ((hmemX q).mp (hRX hqR)) hqQ
      -- pick r ∈ R avoiding Z3 and non-adjacent to q (R ∖ bad has ≥ 5 − 3 − 1 = 1)
      have hRbad := hZ3bad R ⟨hRc, hRcard⟩ hZ3notR
      have hRq : (R.filter (fun r => ctx.H.Adj q r)).card ≤ 1 := h51 R ⟨hRc, hRcard⟩ q hqR
      have hRgood : 0 < (R \ (R.filter (fun r => ∃ z ∈ Z3, ctx.H.Adj z r)
          ∪ R.filter (fun r => ctx.H.Adj q r))).card := by
        rw [Finset.card_sdiff_of_subset
          (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)), hRcard]
        have hunion := Finset.card_union_le (R.filter (fun r => ∃ z ∈ Z3, ctx.H.Adj z r))
          (R.filter (fun r => ctx.H.Adj q r))
        omega
      obtain ⟨r, hrmem⟩ := Finset.card_pos.mp hRgood
      rw [Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hrmem
      have hrR : r ∈ R := hrmem.1
      have hravoid : ∀ z ∈ Z3, ¬ ctx.H.Adj z r :=
        fun z hz hadj => hrmem.2 (Or.inl ⟨hrR, z, hz, hadj⟩)
      have hqr : ¬ ctx.H.Adj q r := fun hadj => hrmem.2 (Or.inr ⟨hrR, hadj⟩)
      -- {Z3, q, r} is an H-independent 5-set
      have hrnotZ3 : r ∉ Z3 := fun hz => hZ3notR r hz hrR
      have hqnotZ3 : q ∉ Z3 := fun hz => hZ3notQ q hz hqQ
      have hqr' : q ∉ insert r Z3 := by
        rw [Finset.mem_insert]
        push Not
        refine ⟨fun hh => ?_, hqnotZ3⟩
        exact hqR (hh ▸ hrR)
      have hindep5 : IsIndep ctx.H (insert q (insert r Z3)) := by
        intro a ha b hb hab
        rw [Finset.mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact absurd rfl hab
        · rw [Finset.mem_insert] at hb
          rcases hb with rfl | hb
          · exact hqr
          · exact fun hadj => hqavoid b hb (ctx.H.symm hadj)
        · rw [Finset.mem_insert] at ha
          rcases ha with rfl | ha
          · exact fun hadj => hqr (ctx.H.symm hadj)
          · exact fun hadj => hqavoid a ha hadj
        · rw [Finset.mem_insert] at ha hb
          rcases ha with rfl | ha <;> rcases hb with rfl | hb
          · exact absurd rfl hab
          · exact fun hadj => hravoid b hb (ctx.H.symm hadj)
          · exact fun hadj => hravoid a ha hadj
          · exact hZ3indep a ha b hb hab
      have hcard5 : (insert q (insert r Z3)).card = 5 := by
        rw [Finset.card_insert_of_notMem hqr', Finset.card_insert_of_notMem hrnotZ3, hZ3card]
      have := ctx.alphaH (insert q (insert r Z3)) hindep5
      omega
    -- transport H[L] onto Fin 11 and apply nonex11
    obtain ⟨gL, hgL⟩ := exists_embedding_image_eq L hLcard
    refine h.nonex11 (ctx.H.comap gL) (capAtMost11_comap ctx.H gL (ctx.cap ctx.k)) ?_
    refine alphaAtMost_comap_gen ctx.H gL (fun S hSsub hSindep => ?_)
    rw [hgL] at hSsub
    exact hαL2 S hSsub hSindep
  -- H[X] is K₅-free
  have hHXcf : ∀ S : Finset (Fin 21), S ⊆ X → ctx.H.IsClique ↑S → S.card ≤ 4 := by
    intro S hSX hSclq
    by_contra hgt
    push Not at hgt
    obtain ⟨R, hRS, hRcard⟩ := Finset.exists_subset_card_eq (show 5 ≤ S.card by omega)
    refine hnoR ⟨R, hRS.trans hSX, ?_, hRcard⟩
    intro a ha b hb hab
    exact hSclq (Finset.mem_coe.mpr (hRS (Finset.mem_coe.mp ha)))
      (Finset.mem_coe.mpr (hRS (Finset.mem_coe.mp hb))) hab
  -- e(H[X]) ≥ 46
  have heHX : 46 ≤ edgeCountIn ctx.H X := by
    have hle := edgeCountIn_ge_Lfloor h ctx.H X (by omega) h52 hHXcf (ctx.cap ctx.k)
    rw [hXcard] at hle
    exact le_trans (by decide) hle
  -- each ordinary e(F_i[X]) ≥ 20
  have heFiX : ∀ i : Fin 5, i ≠ ctx.k → 20 ≤ edgeCountIn (ctx.Gc i) X := by
    intro i hik
    refine brouwer_Fi_on16 bf (ctx.Gc i) X hXcard ?_ (fun S _ hind => ctx.alpha5 i S hind)
    intro S hSX hSclq
    by_contra hgt
    push Not at hgt
    obtain ⟨S4, hS4sub, hS4card⟩ := Finset.exists_subset_card_eq (show 4 ≤ S.card by omega)
    have hindep : IsIndep ctx.H S4 := by
      intro u hu v hv huv hHadj
      have hi : (ctx.Gc i).Adj u v :=
        hSclq (Finset.mem_coe.mpr (hS4sub hu)) (Finset.mem_coe.mpr (hS4sub hv)) huv
      have hcoli : ctx.col u v = i := ((ctx.adj_iff i u v).mp hi).2
      have hcolk : ctx.col u v = ctx.k := ((ctx.adj_iff ctx.k u v).mp hHadj).2
      exact hik (hcoli ▸ hcolk ▸ rfl)
    have := h52 S4 (hS4sub.trans hSX) hindep
    omega
  -- the count: 120 = C(16,2) ≥ 46 + 4·20 = 126
  have hpart := ctx.edgeSumOn X
  rw [hXcard] at hpart
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin 5))
    (fun i => edgeCountIn (ctx.Gc i) X) (Finset.mem_univ ctx.k)
  simp only [] at hsplit
  have hHXk : 46 ≤ edgeCountIn (ctx.Gc ctx.k) X := heHX
  have hrest : 80 ≤ ∑ i ∈ Finset.univ.erase ctx.k, edgeCountIn (ctx.Gc i) X := by
    have hle : ∑ _i ∈ Finset.univ.erase ctx.k, 20
        ≤ ∑ i ∈ Finset.univ.erase ctx.k, edgeCountIn (ctx.Gc i) X :=
      Finset.sum_le_sum (fun i hi => heFiX i (Finset.ne_of_mem_erase hi))
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ ctx.k),
      Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
    omega
  have h120 : (16 : ℕ).choose 2 = 120 := by decide
  omega

/-! ## §6 + §7: the endgame -/

/-- **The 16-set count contradiction** (used in §5 and §7.1). A 16-set `Y` with
`α(H[Y]) ≤ 3` and every ordinary `F_i[Y]` `K₄`-free is impossible: `e(H[Y]) ≥ L(16) = 46`
and each `e(F_i[Y]) ≥ 20`, so `46 + 4·20 = 126 > 120 = C(16,2)`. -/
theorem MH2Ctx.count16_false (ctx : MH2Ctx) (h : PrimFacts) (bf : BrouwerFacts)
    (hHcf5 : ctx.H.CliqueFree 5) (Y : Finset (Fin 21)) (hYcard : Y.card = 16)
    (hαY : ∀ S : Finset (Fin 21), S ⊆ Y → IsIndep ctx.H S → S.card ≤ 3)
    (hFiY : ∀ (i : Fin 5), i ≠ ctx.k → ∀ S : Finset (Fin 21), S ⊆ Y →
      (ctx.Gc i).IsClique ↑S → S.card ≤ 3) :
    False := by
  have hHYcf : ∀ S : Finset (Fin 21), S ⊆ Y → ctx.H.IsClique ↑S → S.card ≤ 4 :=
    fun S _ hSclq => clique_card_le_of_cliqueFree hHcf5 hSclq
  have heHY : 46 ≤ edgeCountIn ctx.H Y := by
    have hle := edgeCountIn_ge_Lfloor h ctx.H Y (by omega) hαY hHYcf (ctx.cap ctx.k)
    rw [hYcard] at hle
    exact le_trans (by decide) hle
  have heFiY : ∀ i : Fin 5, i ≠ ctx.k → 20 ≤ edgeCountIn (ctx.Gc i) Y :=
    fun i hik => brouwer_Fi_on16 bf (ctx.Gc i) Y hYcard (hFiY i hik)
      (fun S _ hind => ctx.alpha5 i S hind)
  have hpart := ctx.edgeSumOn Y
  rw [hYcard] at hpart
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin 5))
    (fun i => edgeCountIn (ctx.Gc i) Y) (Finset.mem_univ ctx.k)
  simp only [] at hsplit
  have hHYk : 46 ≤ edgeCountIn (ctx.Gc ctx.k) Y := heHY
  have hrest : 80 ≤ ∑ i ∈ Finset.univ.erase ctx.k, edgeCountIn (ctx.Gc i) Y := by
    have hle : ∑ _i ∈ Finset.univ.erase ctx.k, 20
        ≤ ∑ i ∈ Finset.univ.erase ctx.k, edgeCountIn (ctx.Gc i) Y :=
      Finset.sum_le_sum (fun i hi => heFiY i (Finset.ne_of_mem_erase hi))
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ ctx.k),
      Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
    omega
  have h120 : (16 : ℕ).choose 2 = 120 := by decide
  omega

/-- **(7.1): `δ(H) ≥ 5`.** A vertex `v` of `H`-degree `≤ 4` has `|W_v| ≥ 16`; any
16-subset `Y ⊆ W_v` has `α(H[Y]) ≤ 3` (add `v`) and every `F_i[Y]` `K₄`-free (an
`i`-`K₄` plus `v` is an `H`-independent 5-set), contradicting `count16_false`. -/
theorem MH2Ctx.delta_ge_5 (ctx : MH2Ctx) (h : PrimFacts) (bf : BrouwerFacts)
    (hHcf5 : ctx.H.CliqueFree 5) (v : Fin 21) : 5 ≤ ctx.H.degree v := by
  by_contra hlt
  push Not at hlt
  have hWge : 16 ≤ (complClosedNbhd ctx.H v).card := by
    rw [complNbhd_card ctx.H v]; omega
  obtain ⟨Y, hYsub, hYcard⟩ := Finset.exists_subset_card_eq hWge
  refine ctx.count16_false h bf hHcf5 Y hYcard ?_ ?_
  · intro S hSY hSindep
    have := card_complNbhd_indep_succ ctx.alphaH (hSY.trans hYsub) hSindep
    omega
  · intro i hik S hSY hSclq
    by_contra hgt
    push Not at hgt
    obtain ⟨S4, hS4sub, hS4card⟩ := Finset.exists_subset_card_eq (show 4 ≤ S.card by omega)
    have hvnotS4 : v ∉ S4 := by
      intro hv
      have hvW := hYsub (hSY (hS4sub hv))
      rw [mem_complClosedNbhd] at hvW
      exact hvW.1 rfl
    have hindep : IsIndep ctx.H (insert v S4) := by
      intro a ha b hb hab
      rw [Finset.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hab
      · intro hadj
        have hbW := hYsub (hSY (hS4sub hb))
        rw [mem_complClosedNbhd] at hbW; exact hbW.2 hadj
      · intro hadj
        have haW := hYsub (hSY (hS4sub ha))
        rw [mem_complClosedNbhd] at haW; exact haW.2 (ctx.H.symm hadj)
      · intro hHadj
        have hi : (ctx.Gc i).Adj a b :=
          hSclq (Finset.mem_coe.mpr (hS4sub ha)) (Finset.mem_coe.mpr (hS4sub hb)) hab
        have hcoli : ctx.col a b = i := ((ctx.adj_iff i a b).mp hi).2
        have hcolk : ctx.col a b = ctx.k := ((ctx.adj_iff ctx.k a b).mp hHadj).2
        exact hik (hcoli.symm.trans hcolk)
    have hc5 : (insert v S4).card = 5 := by rw [Finset.card_insert_of_notMem hvnotS4, hS4card]
    have := ctx.alphaH (insert v S4) hindep
    omega


/-! ## §7 endgame support: cross-count infrastructure, finite facts, clique-cover (F7e) -/

section Endgame7Infra
/-- Ordered adjacent pairs from `A` to `B`: `∑_{a∈A} #{b∈B : G.Adj a b}`. -/
noncomputable def crossE {s : ℕ} (G : SimpleGraph (Fin s)) (A B : Finset (Fin s)) : ℕ :=
  ∑ a ∈ A, (B.filter (fun b => G.Adj a b)).card

variable {s : ℕ} (G : SimpleGraph (Fin s))

/-- `crossE` splits over a disjoint union in its right argument. -/
theorem crossE_union_right (A : Finset (Fin s)) {B₁ B₂ : Finset (Fin s)}
    (hdisj : Disjoint B₁ B₂) :
    crossE G A (B₁ ∪ B₂) = crossE G A B₁ + crossE G A B₂ := by
  unfold crossE
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.filter_union, Finset.card_union_of_disjoint
    (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]

/-- `crossE` splits off an inserted left vertex. -/
theorem crossE_insert_left {v : Fin s} {A : Finset (Fin s)} (hv : v ∉ A) (B : Finset (Fin s)) :
    crossE G (insert v A) B = (B.filter (fun b => G.Adj v b)).card + crossE G A B := by
  unfold crossE
  rw [Finset.sum_insert hv]

/-- `crossE` into a singleton counts the left-neighbours of `b`. -/
theorem crossE_singleton_right (A : Finset (Fin s)) (b : Fin s) :
    crossE G A {b} = (A.filter (fun a => G.Adj a b)).card := by
  unfold crossE
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.filter_singleton]
  by_cases hab : G.Adj a b <;> simp [hab]

/-- `crossE` out of a singleton counts the right-neighbours of `x`. -/
theorem crossE_singleton_left (x : Fin s) (A : Finset (Fin s)) :
    crossE G {x} A = (A.filter (fun a => G.Adj x a)).card := by
  unfold crossE
  rw [Finset.sum_singleton]

/-- The degree sum over `A` is the cross count from `A` to all vertices. -/
theorem sum_degree_eq_crossE_univ (A : Finset (Fin s)) :
    ∑ x ∈ A, G.degree x = crossE G A Finset.univ := by
  unfold crossE
  apply Finset.sum_congr rfl
  intro a _
  rw [← G.card_neighborFinset_eq_degree]
  congr 1
  ext y
  rw [G.mem_neighborFinset, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

/-- `crossE` as a filtered product cardinality. -/
theorem crossE_eq_product (A B : Finset (Fin s)) :
    crossE G A B = ((A ×ˢ B).filter (fun p => G.Adj p.1 p.2)).card := by
  unfold crossE
  rw [Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.card_filter]

/-- **Handshake on an induced subgraph.** `crossE G A A = 2·e(G[A])`. -/
theorem crossE_self (A : Finset (Fin s)) : crossE G A A = 2 * edgeCountIn G A := by
  rw [crossE_eq_product]
  unfold edgeCountIn
  set P := (A ×ˢ A).filter (fun p => G.Adj p.1 p.2) with hP
  set E := A.sym2.filter (fun e => e ∈ G.edgeSet) with hE
  have hmap : ∀ p ∈ P, s(p.1, p.2) ∈ E := by
    intro p hp
    rw [hP, Finset.mem_filter, Finset.mem_product] at hp
    rw [hE, Finset.mem_filter, Finset.mk_mem_sym2_iff, SimpleGraph.mem_edgeSet]
    exact ⟨⟨hp.1.1, hp.1.2⟩, hp.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  have hfiber :
      ∀ e ∈ E, (P.filter (fun p => s(p.1, p.2) = e)).card = 2 := by
    intro e he
    revert he
    induction e using Sym2.ind with
    | _ u v =>
      intro he
      rw [hE, Finset.mem_filter, Finset.mk_mem_sym2_iff,
        SimpleGraph.mem_edgeSet] at he
      have huv : u ≠ v := he.2.ne
      have heq :
          P.filter (fun p => s(p.1, p.2) = s(u, v)) = {(u, v), (v, u)} := by
        ext p
        rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hp
          simp only [Sym2.eq_iff] at hp
          rcases hp.2 with h | h
          · exact Or.inl (Prod.ext_iff.mpr ⟨h.1, h.2⟩)
          · exact Or.inr (Prod.ext_iff.mpr ⟨h.1, h.2⟩)
        · intro hp
          rcases hp with rfl | rfl
          · refine ⟨?_, rfl⟩
            rw [hP, Finset.mem_filter, Finset.mem_product]
            exact ⟨⟨he.1.1, he.1.2⟩, he.2⟩
          · refine ⟨?_, Sym2.eq_swap⟩
            rw [hP, Finset.mem_filter, Finset.mem_product]
            exact ⟨⟨he.1.2, he.1.1⟩, G.symm he.2⟩
      rw [heq]
      exact Finset.card_pair (fun h => huv (Prod.ext_iff.mp h).1)
  have hsc : ∑ e ∈ E, (P.filter (fun p => s(p.1, p.2) = e)).card = ∑ _e ∈ E, 2 :=
    Finset.sum_congr rfl hfiber
  rw [hsc, Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- **Edge partition of a disjoint union (equality).** -/
theorem edgeCountIn_disjoint_union {A B : Finset (Fin s)} (hdisj : Disjoint A B) :
    edgeCountIn G (A ∪ B) = edgeCountIn G A + edgeCountIn G B + crossE G A B := by
  rw [edgeCountIn_eq_filter_edgeFinset G (A ∪ B), edgeCountIn_eq_filter_edgeFinset G A,
    edgeCountIn_eq_filter_edgeFinset G B, crossE_eq_product]
  set fA := G.edgeFinset.filter (fun e => e ∈ A.sym2) with hfA
  set fB := G.edgeFinset.filter (fun e => e ∈ B.sym2) with hfB
  set P := (A ×ˢ B).filter (fun p => G.Adj p.1 p.2) with hP
  set crossI := P.image (fun p => s(p.1, p.2)) with hcI
  have hdleft := Finset.disjoint_left.mp hdisj
  have hsub :
      G.edgeFinset.filter (fun e => e ∈ (A ∪ B).sym2) ⊆ fA ∪ fB ∪ crossI := by
    intro e he
    revert he
    induction e using Sym2.ind with
    | _ u v =>
      intro he
      rw [Finset.mem_filter, Finset.mk_mem_sym2_iff] at he
      obtain ⟨heEdge, hu, hv⟩ := he
      have hadj : G.Adj u v := by
        rw [← SimpleGraph.mem_edgeSet]
        exact G.mem_edgeFinset.mp heEdge
      rw [Finset.mem_union] at hu hv
      rw [Finset.mem_union, Finset.mem_union]
      rcases hu with hu | hu <;> rcases hv with hv | hv
      · exact Or.inl <| Or.inl <| Finset.mem_filter.mpr
          ⟨heEdge, Finset.mk_mem_sym2_iff.mpr ⟨hu, hv⟩⟩
      · refine Or.inr ?_
        rw [hcI, Finset.mem_image]
        exact ⟨(u, v),
          Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu, hv⟩, hadj⟩, rfl⟩
      · refine Or.inr ?_
        rw [hcI, Finset.mem_image]
        exact ⟨(v, u),
          Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hv, hu⟩, G.symm hadj⟩,
          Sym2.eq_swap⟩
      · exact Or.inl <| Or.inr <| Finset.mem_filter.mpr
          ⟨heEdge, Finset.mk_mem_sym2_iff.mpr ⟨hu, hv⟩⟩
  have hsup :
      fA ∪ fB ∪ crossI ⊆ G.edgeFinset.filter (fun e => e ∈ (A ∪ B).sym2) := by
    intro e he
    rw [Finset.mem_union, Finset.mem_union] at he
    rcases he with (he | he) | he
    · rw [hfA, Finset.mem_filter] at he
      exact Finset.mem_filter.mpr ⟨he.1,
        Finset.sym2_mono (fun _ hx => Finset.mem_union_left B hx) he.2⟩
    · rw [hfB, Finset.mem_filter] at he
      exact Finset.mem_filter.mpr ⟨he.1,
        Finset.sym2_mono (fun _ hx => Finset.mem_union_right A hx) he.2⟩
    · rw [hcI, Finset.mem_image] at he
      obtain ⟨p, hp, rfl⟩ := he
      rw [hP, Finset.mem_filter, Finset.mem_product] at hp
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · apply G.mem_edgeFinset.mpr
        rw [SimpleGraph.mem_edgeSet]
        exact hp.2
      · rw [Finset.mk_mem_sym2_iff]
        exact ⟨Finset.mem_union_left B hp.1.1, Finset.mem_union_right A hp.1.2⟩
  have heq :
      G.edgeFinset.filter (fun e => e ∈ (A ∪ B).sym2) = fA ∪ fB ∪ crossI :=
    Finset.Subset.antisymm hsub hsup
  have hdAB : Disjoint fA fB := by
    rw [Finset.disjoint_left]
    intro e heA heB
    revert heA heB
    induction e using Sym2.ind with
    | _ u v =>
      intro heA heB
      rw [hfA, Finset.mem_filter, Finset.mk_mem_sym2_iff] at heA
      rw [hfB, Finset.mem_filter, Finset.mk_mem_sym2_iff] at heB
      exact hdleft heA.2.1 heB.2.1
  have hdCross : Disjoint (fA ∪ fB) crossI := by
    rw [Finset.disjoint_left]
    intro e he heC
    rw [Finset.mem_union] at he
    rw [hcI, Finset.mem_image] at heC
    obtain ⟨p, hp, rfl⟩ := heC
    rw [hP, Finset.mem_filter, Finset.mem_product] at hp
    rcases he with he | he
    · rw [hfA, Finset.mem_filter, Finset.mk_mem_sym2_iff] at he
      exact hdleft he.2.2 hp.1.2
    · rw [hfB, Finset.mem_filter, Finset.mk_mem_sym2_iff] at he
      exact hdleft hp.1.1 he.2.1
  have hinj : Set.InjOn (fun p : Fin s × Fin s => s(p.1, p.2)) P := by
    intro p hp q hq he
    rw [hP, Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp hq
    simp only [Sym2.eq_iff] at he
    rcases he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Prod.ext h₁ h₂
    · exact False.elim (hdleft (h₁.symm ▸ hp.1.1) hq.1.2)
  rw [heq, Finset.card_union_of_disjoint hdCross,
    Finset.card_union_of_disjoint hdAB]
  rw [hcI, Finset.card_image_of_injOn hinj]

/-- **Edge count under insertion (equality).** (Named with a prime to avoid clashing
with `MMProof.edgeCountIn_insert_eq`; F9 may dedup.) -/
theorem edgeCountIn_insert_eq' {x : Fin s} {A : Finset (Fin s)} (hx : x ∉ A) :
    edgeCountIn G (insert x A) = edgeCountIn G A + (A.filter (fun a => G.Adj x a)).card := by
  rw [Finset.insert_eq, edgeCountIn_disjoint_union G (Finset.disjoint_singleton_left.mpr hx)]
  have hc : Nat.choose 1 2 = 0 := by decide
  have h0 : edgeCountIn G {x} = 0 := by
    have h := edgeCountIn_le_choose_two G {x}
    rw [Finset.card_singleton, hc] at h
    omega
  rw [h0, zero_add, crossE_singleton_left]

/-! ## The finite fact: five triangles covering five vertices need ≥ 6 edges -/

/-- **Finite fact (§7 finish).** A graph on `Fin 5` in which every vertex lies in a
triangle has at least `6` edges; equivalently `e = 5` is impossible. Proof: triangle
cover ⟹ `δ ≥ 2`; with `∑deg = 2·5 = 10` this forces `2`-regular; the triangle at any
vertex then closes a 3-set off from the rest, leaving a vertex of degree `≤ 1`. -/
theorem five_edge_no_triangle_cover (F : SimpleGraph (Fin 5))
    (hcov : ∀ x : Fin 5, ∃ y z : Fin 5, y ≠ x ∧ z ≠ x ∧ y ≠ z ∧
      F.Adj x y ∧ F.Adj x z ∧ F.Adj y z)
    (he : edgeCountIn F Finset.univ = 5) : False := by
  -- degree ≥ 2 everywhere from the cover
  have hdeg2 : ∀ x : Fin 5, 2 ≤ F.degree x := by
    intro x
    obtain ⟨y, z, hyx, hzx, hyz, hxy, hxz, _⟩ := hcov x
    have hsub : ({y, z} : Finset (Fin 5)) ⊆ F.neighborFinset x := by
      intro w hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [SimpleGraph.mem_neighborFinset]
      rcases hw with rfl | rfl
      · exact hxy
      · exact hxz
    have hcard : ({y, z} : Finset (Fin 5)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
    calc 2 = ({y, z} : Finset (Fin 5)).card := hcard.symm
      _ ≤ (F.neighborFinset x).card := Finset.card_le_card hsub
      _ = F.degree x := (F.card_neighborFinset_eq_degree x)
  -- total degree = 10
  have hsum : ∑ x : Fin 5, F.degree x = 10 := by
    rw [F.sum_degrees_eq_twice_card_edges, ← edgeCountIn_univ_eq_card_edgeFinset, he]
  -- hence every degree is exactly 2
  have hdegeq : ∀ x : Fin 5, F.degree x = 2 := by
    have hle : ∑ _x : Fin 5, (2 : ℕ) = ∑ x : Fin 5, F.degree x := by
      rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have hforall := (Finset.sum_eq_sum_iff_of_le (fun x _ => hdeg2 x)).mp hle
    intro x; exact (hforall x (Finset.mem_univ x)).symm
  -- exact neighbourhoods (2-regular): two known distinct neighbours ARE the whole nbhd
  have hNbhd : ∀ (p u w : Fin 5), u ≠ w → F.Adj p u → F.Adj p w →
      F.neighborFinset p = {u, w} := by
    intro p u w huw hpu hpw
    have hsub : ({u, w} : Finset (Fin 5)) ⊆ F.neighborFinset p := by
      intro t ht
      rw [Finset.mem_insert, Finset.mem_singleton] at ht
      rw [SimpleGraph.mem_neighborFinset]
      rcases ht with rfl | rfl
      · exact hpu
      · exact hpw
    have hc2 : ({u, w} : Finset (Fin 5)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [huw]), Finset.card_singleton]
    have h1 : (F.neighborFinset p).card = 2 := by rw [F.card_neighborFinset_eq_degree, hdegeq p]
    exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  -- fix the triangle at vertex 0; its neighbourhoods are exactly the other two
  obtain ⟨a, b, ha0, hb0, hab, h0a, h0b, hab'⟩ := hcov 0
  have hN0 : F.neighborFinset 0 = {a, b} := hNbhd 0 a b hab h0a h0b
  have hNa : F.neighborFinset a = {0, b} := hNbhd a 0 b (Ne.symm hb0) (F.symm h0a) hab'
  have hNb : F.neighborFinset b = {0, a} := hNbhd b 0 a (Ne.symm ha0) (F.symm h0b) (F.symm hab')
  -- S = {0,a,b} is closed under taking neighbours
  set S : Finset (Fin 5) := {0, a, b} with hSdef
  have hScard : S.card = 3 := by
    rw [hSdef, Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
        exact ⟨Ne.symm ha0, Ne.symm hb0⟩),
      Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact hab),
      Finset.card_singleton]
  have hclosed : ∀ s ∈ S, ∀ w, F.Adj s w → w ∈ S := by
    intro s hs w hsw
    rw [hSdef, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hs
    have hwN : w ∈ F.neighborFinset s := (SimpleGraph.mem_neighborFinset F s w).mpr hsw
    rcases hs with rfl | rfl | rfl
    · rw [hN0, Finset.mem_insert, Finset.mem_singleton] at hwN
      rw [hSdef]; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    · rw [hNa, Finset.mem_insert, Finset.mem_singleton] at hwN
      rw [hSdef]; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    · rw [hNb, Finset.mem_insert, Finset.mem_singleton] at hwN
      rw [hSdef]; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  -- some vertex c ∉ S; its neighbours all lie in univ∖S, forcing degree ≤ 1
  have hScompl : (Finset.univ \ S).card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin,
      hScard]
  have hne : (Finset.univ \ S).Nonempty := by rw [← Finset.card_pos, hScompl]; norm_num
  obtain ⟨c, hc⟩ := hne
  rw [Finset.mem_sdiff] at hc
  have hcS : c ∉ S := hc.2
  have hNc_sub : F.neighborFinset c ⊆ (Finset.univ \ S) \ {c} := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    rw [Finset.mem_sdiff, Finset.mem_sdiff, Finset.mem_singleton]
    refine ⟨⟨Finset.mem_univ w, ?_⟩, ?_⟩
    · intro hwS
      exact hcS (hclosed w hwS c (F.symm hw))
    · intro hwc; exact (F.ne_of_adj hw) hwc.symm
  have hcdeg : F.degree c ≤ 1 := by
    rw [← F.card_neighborFinset_eq_degree]
    calc (F.neighborFinset c).card ≤ ((Finset.univ \ S) \ {c}).card := Finset.card_le_card hNc_sub
      _ = 1 := by
          rw [Finset.card_sdiff_of_subset (by
            intro x hx; rw [Finset.mem_singleton] at hx; rw [hx]
            exact Finset.mem_sdiff.mpr ⟨hc.1, hc.2⟩),
            hScompl, Finset.card_singleton]
  rw [hdegeq c] at hcdeg
  omega

/-! ## Two more helpers for §7.2 -/

/-- If `∑_{i∈s} f i` equals the count of `i` with `f i ≥ 1`, then every `f i ≤ 1`. -/
theorem sum_le_one_of_sum_eq_card_filter {α : Type*} [DecidableEq α] {s : Finset α} {f : α → ℕ}
    (h : ∑ i ∈ s, f i = (s.filter (fun i => 1 ≤ f i)).card) : ∀ i ∈ s, f i ≤ 1 := by
  rw [Finset.card_filter] at h
  have hle : ∀ i ∈ s, (if 1 ≤ f i then 1 else 0) ≤ f i := by
    intro i _; split <;> omega
  have hforall := (Finset.sum_eq_sum_iff_of_le hle).mp h.symm
  intro i hi
  have hi' := hforall i hi
  split at hi' <;> omega

/-- The number of `i ∈ s` with `f i ≥ 1` is at most `∑_{i∈s} f i`. -/
theorem card_filter_one_le_sum {α : Type*} [DecidableEq α] {s : Finset α} {f : α → ℕ} :
    (s.filter (fun i => 1 ≤ f i)).card ≤ ∑ i ∈ s, f i := by
  rw [Finset.card_filter]
  apply Finset.sum_le_sum
  intro i _
  split <;> omega

/-- `crossE` distributes over a pairwise-disjoint indexed union in its right argument. -/
theorem crossE_biUnion_right {ι : Type*} [DecidableEq ι] (A : Finset (Fin s))
    (t : Finset ι) (C : ι → Finset (Fin s))
    (hdisj : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → Disjoint (C i) (C j)) :
    crossE G A (t.biUnion C) = ∑ j ∈ t, crossE G A (C j) := by
  unfold crossE
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.filter_biUnion, Finset.card_biUnion]
  intro i hi j hj hij
  exact (hdisj i hi j hj hij).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-- Clique-cover extraction on `Fin 15`. A `K₄`-free graph whose complement is
`5`-colourable partitions into five triangles. -/
theorem clique_cover_of_compl_colorable (Fi : SimpleGraph (Fin 15))
    (hcol : Fiᶜ.Colorable 5) (hK4 : Fi.CliqueFree 4) :
    ∃ C : Fin 5 → Finset (Fin 15), (∀ j, (C j).card = 3) ∧
      (∀ i j : Fin 5, i ≠ j → Disjoint (C i) (C j)) ∧
      Finset.univ.biUnion C = Finset.univ ∧
      (∀ j, Fi.IsClique ↑(C j)) := by
  obtain ⟨col⟩ := hcol
  let C : Fin 5 → Finset (Fin 15) :=
    fun j => Finset.univ.filter (fun x => col x = j)
  have hclique : ∀ j, Fi.IsClique ↑(C j) := by
    intro j
    rw [SimpleGraph.isClique_iff]
    intro x hx y hy hxy
    have hcx : col x = j := by simpa [C] using hx
    have hcy : col y = j := by simpa [C] using hy
    by_contra hnadj
    have hcomp : Fiᶜ.Adj x y := by rw [SimpleGraph.compl_adj]; exact ⟨hxy, hnadj⟩
    exact (col.valid hcomp) (hcx.trans hcy.symm)
  have hcard_le : ∀ j, (C j).card ≤ 3 := by
    intro j
    by_contra h
    have hfour : 4 ≤ (C j).card := by omega
    obtain ⟨S, hSC, hScard⟩ := Finset.exists_subset_card_eq hfour
    exact hK4 S ⟨(hclique j).subset hSC, hScard⟩
  have hdisj : ∀ i j : Fin 5, i ≠ j → Disjoint (C i) (C j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    have hxi' : col x = i := by simpa [C] using hxi
    have hxj' : col x = j := by simpa [C] using hxj
    exact hij (hxi'.symm.trans hxj')
  have hcover : (Finset.univ : Finset (Fin 5)).biUnion C =
      (Finset.univ : Finset (Fin 15)) := by
    ext x
    simp [C]
  have hsum : ∑ j ∈ (Finset.univ : Finset (Fin 5)), (C j).card = 15 := by
    rw [← Finset.card_biUnion (fun x _ y _ h => hdisj x y h), hcover, Finset.card_univ,
      Fintype.card_fin]
  have hsum3 : ∑ _j ∈ (Finset.univ : Finset (Fin 5)), 3 = 15 := by simp
  have hcards : ∀ j, (C j).card = 3 := by
    have hall : ∀ j ∈ (Finset.univ : Finset (Fin 5)), (C j).card = 3 :=
      (Finset.sum_eq_sum_iff_of_le (fun j _ => hcard_le j)).1 (hsum.trans hsum3.symm)
    intro j
    exact hall j (Finset.mem_univ j)
  exact ⟨C, hcards, hdisj, hcover, hclique⟩

end Endgame7Infra

/-- **§7 endgame.** Given the forced equalities `e(H) = 58`, `e(F_i) = 38`, and
`H` `K₅`-free, derive a contradiction (min-degree, degree-5 vertex, the `(r,w,c)`
system, the five `i`-triangles, and the five-triangles-need-six-edges finish). -/
theorem MH2Ctx.endgame (ctx : MH2Ctx) (h : PrimFacts) (bf : BrouwerFacts)
    (hHcf5 : ctx.H.CliqueFree 5)
    (hH58 : edgeCountIn ctx.H Finset.univ = 58)
    (hFi38 : ∀ i : Fin 5, i ≠ ctx.k → edgeCountIn (ctx.Gc i) Finset.univ = 38) :
    False := by
  -- (7.1) δ(H) ≥ 5, and a degree-exactly-5 vertex (2·58 = 116 < 6·21)
  have hdelta5 : ∀ v : Fin 21, 5 ≤ ctx.H.degree v := ctx.delta_ge_5 h bf hHcf5
  obtain ⟨v, hdeg5⟩ : ∃ v : Fin 21, ctx.H.degree v = 5 := by
    by_contra hcon
    push_neg at hcon
    have hge6 : ∀ v : Fin 21, 6 ≤ ctx.H.degree v :=
      fun v => by have := hdelta5 v; have := hcon v; omega
    have hsumdeg := ctx.H.sum_degrees_eq_twice_card_edges
    rw [edgeCountIn_univ_eq_card_edgeFinset] at hH58
    have hge : (6 * 21 : ℕ) ≤ ∑ v : Fin 21, ctx.H.degree v := by
      calc (6 * 21 : ℕ) = ∑ _v : Fin 21, 6 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        _ ≤ ∑ v, ctx.H.degree v := Finset.sum_le_sum (fun v _ => hge6 v)
    rw [hsumdeg, hH58] at hge
    omega
  -- setup: A = N_H(v), Q = A∪{v}, W = W_v
  set A := ctx.H.neighborFinset v with hAdef
  set Q := insert v A with hQdef
  set W := complClosedNbhd ctx.H v with hWdef
  have hvnotA : v ∉ A := by
    intro hv
    rw [hAdef, SimpleGraph.mem_neighborFinset] at hv
    exact ctx.H.ne_of_adj hv rfl
  have hAcard : A.card = 5 := by rw [hAdef, ctx.H.card_neighborFinset_eq_degree, hdeg5]
  have hQcard : Q.card = 6 := by rw [hQdef, Finset.card_insert_of_notMem hvnotA, hAcard]
  have hWcard : W.card = 15 := by rw [hWdef, complNbhd_card ctx.H v, hdeg5]
  have hWQ : W = Finset.univ \ Q := by rw [hWdef, hQdef, hAdef]; rfl
  have hdisjQW : Disjoint Q W := by rw [hWQ]; exact Finset.disjoint_sdiff
  have hunionQW : Q ∪ W = Finset.univ := by
    rw [hWQ, Finset.union_sdiff_of_subset (Finset.subset_univ Q)]
  -- every a ∈ A is H-adjacent to v (and vice versa)
  have hAadj : ∀ a ∈ A, ctx.H.Adj v a := by
    intro a ha; rw [hAdef, SimpleGraph.mem_neighborFinset] at ha; exact ha
  -- e_H(Q) = e_H(A) + 5
  have hfiltAv : (A.filter (fun a => ctx.H.Adj v a)).card = 5 := by
    rw [Finset.filter_true_of_mem (fun a ha => hAadj a ha), hAcard]
  have hQeq : edgeCountIn ctx.H Q = edgeCountIn ctx.H A + 5 := by
    rw [hQdef, edgeCountIn_insert_eq' ctx.H hvnotA, hfiltAv]
  -- e(H) partition: 58 = e_H(Q) + e_H(W) + crossE(Q,W)
  have hpart := edgeCountIn_disjoint_union ctx.H hdisjQW
  rw [hunionQW, hH58] at hpart
  -- crossE(Q,W) = crossE(A,W)  (v has no H-neighbour in W)
  have hWfilt : W.filter (fun b => ctx.H.Adj v b) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro b hb; rw [hWdef, mem_complClosedNbhd] at hb; exact hb.2
  have hcrossQW : crossE ctx.H Q W = crossE ctx.H A W := by
    rw [hQdef, crossE_insert_left ctx.H hvnotA, hWfilt, Finset.card_empty, zero_add]
  -- degree sum on A = 2·e_H(A) + 5 + crossE(A,W)
  have hAvadj : (A.filter (fun a => ctx.H.Adj a v)).card = 5 := by
    rw [Finset.filter_true_of_mem (fun a ha => (hAadj a ha).symm), hAcard]
  have hcrossAQ : crossE ctx.H A Q = 2 * edgeCountIn ctx.H A + 5 := by
    rw [hQdef, Finset.insert_eq,
      crossE_union_right ctx.H A (Finset.disjoint_singleton_left.mpr hvnotA),
      crossE_singleton_right, crossE_self, hAvadj]
    ring
  have hdegsum : ∑ x ∈ A, ctx.H.degree x = 2 * edgeCountIn ctx.H A + 5 + crossE ctx.H A W := by
    rw [sum_degree_eq_crossE_univ, ← hunionQW,
      crossE_union_right ctx.H A hdisjQW, hcrossAQ]
  have hdeg_ge : 25 ≤ ∑ x ∈ A, ctx.H.degree x := by
    calc (25 : ℕ) = ∑ _x ∈ A, 5 := by rw [Finset.sum_const, hAcard, smul_eq_mul]
      _ ≤ ∑ x ∈ A, ctx.H.degree x := Finset.sum_le_sum (fun x _ => hdelta5 x)
  -- w ≥ 38: L15 on W (α(H[W]) ≤ 3, ω ≤ 4, cap-11)
  have hαW : ∀ S : Finset (Fin 21), S ⊆ W → IsIndep ctx.H S → S.card ≤ 3 := by
    intro S hSW hSindep
    have := card_complNbhd_indep_succ ctx.alphaH (by rw [← hWdef]; exact hSW) hSindep
    omega
  have hωW : ∀ S : Finset (Fin 21), S ⊆ W → ctx.H.IsClique ↑S → S.card ≤ 4 :=
    fun S _ hSclq => clique_card_le_of_cliqueFree hHcf5 hSclq
  have hw38 : 38 ≤ edgeCountIn ctx.H W := by
    have hle := edgeCountIn_ge_Lfloor h ctx.H W (by omega) hαW hωW (ctx.cap ctx.k)
    rw [hWcard] at hle
    exact le_trans (by decide) hle
  -- §7.2 (a): some ordinary colour i has e(F_i[W]) ≤ 16
  have hsumW : ∑ i, edgeCountIn (ctx.Gc i) W = 105 := by
    have hh := ctx.edgeSumOn W
    rw [hWcard, show (15 : ℕ).choose 2 = 105 from by decide] at hh
    exact hh
  have hlow : ∃ i : Fin 5, i ≠ ctx.k ∧ edgeCountIn (ctx.Gc i) W ≤ 16 := by
    by_contra hcon
    push_neg at hcon
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin 5))
      (fun i => edgeCountIn (ctx.Gc i) W) (Finset.mem_univ ctx.k)
    simp only [] at hsplit
    have hrest : (4 * 17 : ℕ) ≤ ∑ i ∈ Finset.univ.erase ctx.k, edgeCountIn (ctx.Gc i) W := by
      have hle : ∑ _i ∈ Finset.univ.erase ctx.k, 17
          ≤ ∑ i ∈ Finset.univ.erase ctx.k, edgeCountIn (ctx.Gc i) W :=
        Finset.sum_le_sum (fun i hi => hcon i (Finset.ne_of_mem_erase hi))
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ ctx.k),
        Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
      omega
    have hwk : 38 ≤ edgeCountIn (ctx.Gc ctx.k) W := hw38
    rw [hsumW] at hsplit
    omega
  obtain ⟨i, hik, hilow⟩ := hlow
  -- F_i[W] is K₄-free (an i-K₄ ⊆ W is an H[W]-independent 4-set)
  have hFiK4 : ∀ S : Finset (Fin 21), S ⊆ W → (ctx.Gc i).IsClique ↑S → S.card ≤ 3 := by
    intro S hSW hSclq
    by_contra hgt
    push_neg at hgt
    obtain ⟨S4, hS4sub, hS4card⟩ := Finset.exists_subset_card_eq (show 4 ≤ S.card by omega)
    have hindep : IsIndep ctx.H S4 := by
      intro u hu w hw huw hHadj
      have hi : (ctx.Gc i).Adj u w :=
        hSclq (Finset.mem_coe.mpr (hS4sub hu)) (Finset.mem_coe.mpr (hS4sub hw)) huw
      have hcoli : ctx.col u w = i := ((ctx.adj_iff i u w).mp hi).2
      have hcolk : ctx.col u w = ctx.k := ((ctx.adj_iff ctx.k u w).mp hHadj).2
      exact hik (hcoli.symm.trans hcolk)
    have := hαW S4 (hS4sub.trans hSW) hindep
    omega
  -- transport F_i[W] onto Fin 15 and run Brouwer/colourability
  obtain ⟨g, hg⟩ := exists_embedding_image_eq W hWcard
  set Fi := (ctx.Gc i).comap g with hFidef
  have hFiEC : edgeCountIn Fi Finset.univ = edgeCountIn (ctx.Gc i) W := by
    rw [hFidef, edgeCountIn_comap, hg]
  have hFiK4' : Fi.CliqueFree 4 :=
    cliqueFree_comap_of (ctx.Gc i) g (fun S hS hclq => hFiK4 S (by rw [hg] at hS; exact hS) hclq)
  have hFia5 : alphaAtMost Fi 5 :=
    alphaAtMost_comap_gen (ctx.Gc i) g (fun S _ hind => ctx.alpha5 i S hind)
  have hFicompl6 : Fiᶜ.CliqueFree 6 := compl_cliqueFree_six_of_alphaAtMost_five Fi hFia5
  have hFicomplE : 89 ≤ edgeCountIn Fiᶜ Finset.univ := by
    have hadd := edgeCountIn_add_compl Fi
    rw [show (15 : ℕ).choose 2 = 105 from by decide, hFiEC] at hadd
    omega
  have hFicol : Fiᶜ.Colorable 5 := brouwer_15_colorable bf Fiᶜ hFicompl6 hFicomplE
  obtain ⟨C', hC'card, hC'disj, hC'cover, hC'clq⟩ :=
    clique_cover_of_compl_colorable Fi hFicol hFiK4'
  -- transport the triangles back to `W ⊆ Fin 21`
  set C := fun j => (C' j).image g with hCdef
  have hCcard : ∀ j, (C j).card = 3 := fun j => by
    rw [hCdef, Finset.card_image_of_injective _ g.injective, hC'card j]
  have hCsub : ∀ j, C j ⊆ W := fun j => by
    rw [hCdef, ← hg]; exact Finset.image_subset_image (Finset.subset_univ _)
  have hCdisj : ∀ a b : Fin 5, a ≠ b → Disjoint (C a) (C b) := by
    intro a b hab
    have hd := hC'disj a b hab
    rw [Finset.disjoint_left] at hd ⊢
    intro x hxa hxb
    simp only [hCdef, Finset.mem_image] at hxa hxb
    obtain ⟨a', ha', rfl⟩ := hxa
    obtain ⟨b', hb', hbeq⟩ := hxb
    exact hd ha' (g.injective hbeq ▸ hb')
  have hCcover : Finset.univ.biUnion C = W := by
    apply Finset.Subset.antisymm
    · intro x hx
      rw [Finset.mem_biUnion] at hx
      obtain ⟨j, _, hxj⟩ := hx
      exact hCsub j hxj
    · intro x hx
      rw [← hg, Finset.mem_image] at hx
      obtain ⟨x', _, rfl⟩ := hx
      have hx'b : x' ∈ Finset.univ.biUnion C' := by rw [hC'cover]; exact Finset.mem_univ x'
      rw [Finset.mem_biUnion] at hx'b
      obtain ⟨j, hj, hx'j⟩ := hx'b
      rw [Finset.mem_biUnion]
      exact ⟨j, hj, by simp only [hCdef]; exact Finset.mem_image_of_mem g hx'j⟩
  have hCindep : ∀ j, IsIndep ctx.H (C j) := by
    intro j u hu w hw huw hHadj
    rw [hCdef, Finset.mem_image] at hu hw
    obtain ⟨u', hu', rfl⟩ := hu
    obtain ⟨w', hw', rfl⟩ := hw
    have hu'w' : u' ≠ w' := fun heq => huw (by rw [heq])
    have hiadj : Fi.Adj u' w' := hC'clq j (Finset.mem_coe.mpr hu') (Finset.mem_coe.mpr hw') hu'w'
    rw [hFidef, SimpleGraph.comap_adj] at hiadj
    have hcoli : ctx.col (g u') (g w') = i := ((ctx.adj_iff i _ _).mp hiadj).2
    have hcolk : ctx.col (g u') (g w') = ctx.k := ((ctx.adj_iff ctx.k _ _).mp hHadj).2
    exact hik (hcoli.symm.trans hcolk)
  -- §7.2 (b): X_j analysis, c ≥ 10, equalities, ρ-count, finite fact
  -- Q partitions into X_j (no H-edge into C_j) and its complement, |Q| = 6
  have hcard6 : ∀ j : Fin 5,
      (Q.filter (fun q => 1 ≤ ((C j).filter (fun cc => ctx.H.Adj q cc)).card)).card
      + (Q.filter (fun q => ¬ (1 ≤ ((C j).filter (fun cc => ctx.H.Adj q cc)).card))).card = 6 := by
    intro j
    rw [Finset.filter_card_add_filter_neg_card_eq_card, hQcard]
  -- X_j is an H-clique (two nonadjacent + C_j = H-indep 5-set), so |X_j| ≤ 4
  have hXset_clique : ∀ j : Fin 5,
      ctx.H.IsClique ↑(Q.filter (fun q => ¬ (1 ≤ ((C j).filter (fun cc => ctx.H.Adj q cc)).card))) := by
    intro j
    rw [SimpleGraph.isClique_iff]
    intro q1 hq1 q2 hq2 hq12
    rw [Finset.mem_coe, Finset.mem_filter] at hq1 hq2
    have hq1no : ∀ cc ∈ C j, ¬ ctx.H.Adj q1 cc := fun cc hcc hadj =>
      hq1.2 (Finset.card_pos.mpr ⟨cc, Finset.mem_filter.mpr ⟨hcc, hadj⟩⟩)
    have hq2no : ∀ cc ∈ C j, ¬ ctx.H.Adj q2 cc := fun cc hcc hadj =>
      hq2.2 (Finset.card_pos.mpr ⟨cc, Finset.mem_filter.mpr ⟨hcc, hadj⟩⟩)
    by_contra hnadj
    have hq1notW : q1 ∉ C j := fun hw => Finset.disjoint_left.mp hdisjQW hq1.1 (hCsub j hw)
    have hq2notW : q2 ∉ C j := fun hw => Finset.disjoint_left.mp hdisjQW hq2.1 (hCsub j hw)
    have hindep : IsIndep ctx.H (insert q1 (insert q2 (C j))) := by
      intro a ha b hb hab
      simp only [Finset.mem_insert] at ha hb
      rcases ha with rfl | rfl | ha <;> rcases hb with rfl | rfl | hb
      · exact absurd rfl hab
      · exact hnadj
      · exact hq1no b hb
      · exact fun hadj => hnadj (ctx.H.symm hadj)
      · exact absurd rfl hab
      · exact hq2no b hb
      · exact fun hadj => hq1no a ha (ctx.H.symm hadj)
      · exact fun hadj => hq2no a ha (ctx.H.symm hadj)
      · exact hCindep j a ha b hb hab
    have hcard5 : (insert q1 (insert q2 (C j))).card = 5 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem hq2notW, hCcard j]
      rw [Finset.mem_insert]; push_neg; exact ⟨hq12, hq1notW⟩
    have := ctx.alphaH (insert q1 (insert q2 (C j))) hindep
    omega
  have hXclq : ∀ j : Fin 5,
      (Q.filter (fun q => ¬ (1 ≤ ((C j).filter (fun cc => ctx.H.Adj q cc)).card))).card ≤ 4 :=
    fun j => clique_card_le_of_cliqueFree hHcf5 (hXset_clique j)
  -- ≥ 2 of Q are adjacent to each C_j, and crossE Q (C j) ≥ that count
  have hAset2 : ∀ j : Fin 5,
      2 ≤ (Q.filter (fun q => 1 ≤ ((C j).filter (fun cc => ctx.H.Adj q cc)).card)).card :=
    fun j => by have := hcard6 j; have := hXclq j; omega
  have hcrossge : ∀ j : Fin 5,
      (Q.filter (fun q => 1 ≤ ((C j).filter (fun cc => ctx.H.Adj q cc)).card)).card
      ≤ crossE ctx.H Q (C j) := fun j => by
    rw [crossE]; exact card_filter_one_le_sum
  -- crossE Q W = ∑_j crossE Q (C j) since the C_j partition W
  have hcrosssum : crossE ctx.H Q W = ∑ j, crossE ctx.H Q (C j) := by
    rw [← hCcover, crossE_biUnion_right ctx.H Q Finset.univ C (fun a _ b _ hab => hCdisj a b hab)]
  -- c = crossE(A,W) = crossE(Q,W) ≥ 10
  have hc10 : 10 ≤ crossE ctx.H A W := by
    rw [← hcrossQW, hcrosssum]
    calc (10 : ℕ) = ∑ _j : Fin 5, 2 := by simp
      _ ≤ ∑ j, (Q.filter (fun q => 1 ≤ ((C j).filter (fun cc => ctx.H.Adj q cc)).card)).card :=
          Finset.sum_le_sum (fun j _ => hAset2 j)
      _ ≤ ∑ j, crossE ctx.H Q (C j) := Finset.sum_le_sum (fun j _ => hcrossge j)
  -- pin (r,w,c) = (5,38,10)
  rw [hQeq, hcrossQW] at hpart
  rw [hdegsum] at hdeg_ge
  have hr5 : edgeCountIn ctx.H A = 5 := by omega
  have hw38eq : edgeCountIn ctx.H W = 38 := by omega
  have hc10eq : crossE ctx.H A W = 10 := by omega
  -- §7.2 (b'): equality per j — each C_j receives exactly 2 H-edges from Q, one apiece
  have hsum10 : ∑ j, crossE ctx.H Q (C j) = 10 := by rw [← hcrosssum, hcrossQW, hc10eq]
  have hgeAset : ∀ j ∈ (Finset.univ : Finset (Fin 5)),
      (Q.filter (fun q => 1 ≤ ((C j).filter (fun cc => ctx.H.Adj q cc)).card)).card
      ≤ crossE ctx.H Q (C j) := fun j _ => hcrossge j
  have heqAset : ∀ j : Fin 5,
      crossE ctx.H Q (C j)
      = (Q.filter (fun q => 1 ≤ ((C j).filter (fun cc => ctx.H.Adj q cc)).card)).card := by
    have hle := Finset.sum_le_sum hgeAset
    have hsumAset : (10 : ℕ)
        ≤ ∑ j, (Q.filter (fun q => 1 ≤ ((C j).filter (fun cc => ctx.H.Adj q cc)).card)).card := by
      calc (10 : ℕ) = ∑ _j : Fin 5, 2 := by simp
        _ ≤ _ := Finset.sum_le_sum (fun j _ => hAset2 j)
    have hsumeq : ∑ j, (Q.filter (fun q => 1 ≤ ((C j).filter (fun cc => ctx.H.Adj q cc)).card)).card
        = ∑ j, crossE ctx.H Q (C j) := by omega
    exact fun j => ((Finset.sum_eq_sum_iff_of_le hgeAset).mp hsumeq j (Finset.mem_univ j)).symm
  have hAset2eq : ∀ j : Fin 5,
      (Q.filter (fun q => 1 ≤ ((C j).filter (fun cc => ctx.H.Adj q cc)).card)).card = 2 := by
    have hsumAset10 :
        ∑ j, (Q.filter (fun q => 1 ≤ ((C j).filter (fun cc => ctx.H.Adj q cc)).card)).card = 10 := by
      rw [← hsum10]; exact (Finset.sum_congr rfl (fun j _ => (heqAset j))).symm
    have hge2 : ∀ j ∈ (Finset.univ : Finset (Fin 5)),
        (2 : ℕ) ≤ (Q.filter (fun q => 1 ≤ ((C j).filter (fun cc => ctx.H.Adj q cc)).card)).card :=
      fun j _ => hAset2 j
    exact fun j => ((Finset.sum_eq_sum_iff_of_le hge2).mp
      (by rw [show ∑ _j : Fin 5, (2:ℕ) = 10 from by simp, hsumAset10]) j (Finset.mem_univ j)).symm
  -- each q ∈ Q sends ≤ 1 H-edge into C_j
  have hxCj1 : ∀ j : Fin 5, ∀ q ∈ Q, ((C j).filter (fun cc => ctx.H.Adj q cc)).card ≤ 1 :=
    fun j => sum_le_one_of_sum_eq_card_filter (heqAset j)
  -- |X_j| = 4, and v ∈ X_j
  have hXset4 : ∀ j : Fin 5,
      (Q.filter (fun q => ¬ (1 ≤ ((C j).filter (fun cc => ctx.H.Adj q cc)).card))).card = 4 :=
    fun j => by have := hcard6 j; have := hAset2eq j; omega
  have hvXset : ∀ j : Fin 5,
      v ∈ Q.filter (fun q => ¬ (1 ≤ ((C j).filter (fun cc => ctx.H.Adj q cc)).card)) := by
    intro j
    rw [Finset.mem_filter]
    refine ⟨by rw [hQdef]; exact Finset.mem_insert_self v A, ?_⟩
    have hemp : (C j).filter (fun cc => ctx.H.Adj v cc) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro cc hcc
      have hccW := hCsub j hcc
      rw [hWdef, mem_complClosedNbhd] at hccW
      exact hccW.2
    rw [hemp, Finset.card_empty]; omega
  -- degree decomposition for x ∈ A: d_H(x) = 1 + d_F(x) + e_H(x,W)
  have hdegx : ∀ x ∈ A, ctx.H.degree x =
      1 + (A.filter (fun a => ctx.H.Adj x a)).card + (W.filter (fun ww => ctx.H.Adj x ww)).card := by
    intro x hx
    have h1 : ctx.H.degree x = crossE ctx.H {x} Finset.univ := by
      have hh := sum_degree_eq_crossE_univ ctx.H {x}
      rwa [Finset.sum_singleton] at hh
    rw [h1, ← hunionQW, crossE_union_right ctx.H {x} hdisjQW, hQdef, Finset.insert_eq,
      crossE_union_right ctx.H {x} (Finset.disjoint_singleton_left.mpr hvnotA),
      crossE_singleton_left, crossE_singleton_left, crossE_singleton_left]
    have hv1 : (({v} : Finset (Fin 21)).filter (fun a => ctx.H.Adj x a)).card = 1 := by
      rw [Finset.filter_singleton, if_pos (hAadj x hx).symm, Finset.card_singleton]
    rw [hv1]
  -- e_H(x,W) as a sum over the triangles
  have heW_sum : ∀ x, (W.filter (fun ww => ctx.H.Adj x ww)).card
      = ∑ j, ((C j).filter (fun cc => ctx.H.Adj x cc)).card := by
    intro x
    rw [← hCcover, Finset.filter_biUnion, Finset.card_biUnion]
    intro a _ b _ hab
    exact (hCdisj a b hab).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  -- for x ∈ A, e_H(x,W) + ρ_x = 5, where ρ_x counts triangles with no H-edge from x
  have heWρ : ∀ x ∈ A,
      (W.filter (fun ww => ctx.H.Adj x ww)).card
      + (Finset.univ.filter (fun j => (C j).filter (fun cc => ctx.H.Adj x cc) = ∅)).card = 5 := by
    intro x hx
    have hxQ : x ∈ Q := by rw [hQdef]; exact Finset.mem_insert_of_mem hx
    have ht1 : ∀ j, ((C j).filter (fun cc => ctx.H.Adj x cc)).card ≤ 1 := fun j => hxCj1 j x hxQ
    have hρexp : (Finset.univ.filter (fun j => (C j).filter (fun cc => ctx.H.Adj x cc) = ∅)).card
        = ∑ j : Fin 5, (if (C j).filter (fun cc => ctx.H.Adj x cc) = ∅ then 1 else 0) :=
      Finset.card_filter _ _
    rw [heW_sum, hρexp, ← Finset.sum_add_distrib]
    have hone : ∀ j : Fin 5, ((C j).filter (fun cc => ctx.H.Adj x cc)).card
        + (if (C j).filter (fun cc => ctx.H.Adj x cc) = ∅ then 1 else 0) = 1 := by
      intro j
      have hle := ht1 j
      by_cases hz : (C j).filter (fun cc => ctx.H.Adj x cc) = ∅
      · rw [if_pos hz, hz, Finset.card_empty]
      · rw [if_neg hz]
        have hpos : 1 ≤ ((C j).filter (fun cc => ctx.H.Adj x cc)).card :=
          Finset.card_pos.mpr (Finset.nonempty_of_ne_empty hz)
        omega
    rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hone j)]
    simp
  -- ρ_x ≤ d_F(x) + 1 (from δ ≥ 5), and the two sums both equal 15
  have hρle : ∀ x ∈ A,
      (Finset.univ.filter (fun j => (C j).filter (fun cc => ctx.H.Adj x cc) = ∅)).card
      ≤ (A.filter (fun a => ctx.H.Adj x a)).card + 1 := by
    intro x hx
    have hd := hdegx x hx
    have he := heWρ x hx
    have h5 := hdelta5 x
    omega
  have hsumρ : ∑ x ∈ A,
      (Finset.univ.filter (fun j => (C j).filter (fun cc => ctx.H.Adj x cc) = ∅)).card = 15 := by
    have hsumeWρ : ∑ x ∈ A, ((W.filter (fun ww => ctx.H.Adj x ww)).card
        + (Finset.univ.filter (fun j => (C j).filter (fun cc => ctx.H.Adj x cc) = ∅)).card) = 25 := by
      rw [show (25 : ℕ) = ∑ _x ∈ A, 5 from by rw [Finset.sum_const, hAcard, smul_eq_mul]]
      exact Finset.sum_congr rfl (fun x hx => heWρ x hx)
    rw [Finset.sum_add_distrib] at hsumeWρ
    have hsumeW : ∑ x ∈ A, (W.filter (fun ww => ctx.H.Adj x ww)).card = crossE ctx.H A W := rfl
    rw [hsumeW, hc10eq] at hsumeWρ
    omega
  have hsumdF : ∑ x ∈ A, ((A.filter (fun a => ctx.H.Adj x a)).card + 1) = 15 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, hAcard, smul_eq_mul,
      show ∑ x ∈ A, (A.filter (fun a => ctx.H.Adj x a)).card = crossE ctx.H A A from rfl,
      crossE_self, hr5]
  have hρeq := (Finset.sum_eq_sum_iff_of_le (fun x hx => hρle x hx)).mp (by rw [hsumρ, hsumdF])
  -- every x ∈ A lies in an H-triangle inside A
  have hcover_tri : ∀ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, y ≠ x ∧ z ≠ x ∧ y ≠ z ∧
      ctx.H.Adj x y ∧ ctx.H.Adj x z ∧ ctx.H.Adj y z := by
    intro x hx
    have hρ1 : 1 ≤ (Finset.univ.filter (fun j => (C j).filter (fun cc => ctx.H.Adj x cc) = ∅)).card := by
      rw [hρeq x hx]; omega
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hρ1
    rw [Finset.mem_filter] at hj
    set Xj := Q.filter (fun q => ¬ (1 ≤ ((C j).filter (fun cc => ctx.H.Adj q cc)).card)) with hXjdef
    have hxXj : x ∈ Xj := by
      rw [hXjdef, Finset.mem_filter]
      exact ⟨by rw [hQdef]; exact Finset.mem_insert_of_mem hx, by rw [hj.2, Finset.card_empty]; omega⟩
    have hvXj : v ∈ Xj := hvXset j
    have hxv : x ≠ v := fun heq => hvnotA (heq ▸ hx)
    have hclq := hXset_clique j
    rw [SimpleGraph.isClique_iff] at hclq
    -- Xj \ {v} \ {x} has card 2
    have hc4 : Xj.card = 4 := hXset4 j
    have hsubv : ({v} : Finset (Fin 21)) ⊆ Xj := Finset.singleton_subset_iff.mpr hvXj
    have hxXjv : x ∈ Xj \ {v} :=
      Finset.mem_sdiff.mpr ⟨hxXj, mt Finset.mem_singleton.mp hxv⟩
    have hsubx : ({x} : Finset (Fin 21)) ⊆ Xj \ {v} := Finset.singleton_subset_iff.mpr hxXjv
    have hcard2 : ((Xj \ {v}) \ {x}).card = 2 := by
      rw [Finset.card_sdiff_of_subset hsubx, Finset.card_sdiff_of_subset hsubv, hc4,
        Finset.card_singleton, Finset.card_singleton]
    obtain ⟨y, z, hyz, hset⟩ := Finset.card_eq_two.mp hcard2
    have hymem : y ∈ (Xj \ {v}) \ {x} := by rw [hset]; exact Finset.mem_insert_self y {z}
    have hzmem : z ∈ (Xj \ {v}) \ {x} := by
      rw [hset]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self z)
    have hyXj : y ∈ Xj := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hymem).1).1
    have hzXj : z ∈ Xj := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hzmem).1).1
    have hyx : y ≠ x := mt Finset.mem_singleton.mpr (Finset.mem_sdiff.mp hymem).2
    have hzx : z ≠ x := mt Finset.mem_singleton.mpr (Finset.mem_sdiff.mp hzmem).2
    have hyA : y ∈ A := by
      have hyv : y ≠ v :=
        mt Finset.mem_singleton.mpr (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hymem).1).2
      rw [hXjdef, Finset.mem_filter, hQdef, Finset.mem_insert] at hyXj
      rcases hyXj.1 with rfl | hh
      · exact absurd rfl hyv
      · exact hh
    have hzA : z ∈ A := by
      have hzv : z ≠ v :=
        mt Finset.mem_singleton.mpr (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hzmem).1).2
      rw [hXjdef, Finset.mem_filter, hQdef, Finset.mem_insert] at hzXj
      rcases hzXj.1 with rfl | hh
      · exact absurd rfl hzv
      · exact hh
    exact ⟨y, hyA, z, hzA, hyx, hzx, hyz,
      hclq (Finset.mem_coe.mpr hxXj) (Finset.mem_coe.mpr hyXj) (Ne.symm hyx),
      hclq (Finset.mem_coe.mpr hxXj) (Finset.mem_coe.mpr hzXj) (Ne.symm hzx),
      hclq (Finset.mem_coe.mpr hyXj) (Finset.mem_coe.mpr hzXj) hyz⟩
  -- transport A to Fin 5 and invoke the finite fact
  obtain ⟨gA, hgA⟩ := exists_embedding_image_eq A hAcard
  apply five_edge_no_triangle_cover (ctx.H.comap gA)
  · intro x
    have hgAx : gA x ∈ A := by rw [← hgA]; exact Finset.mem_image_of_mem gA (Finset.mem_univ x)
    obtain ⟨y, hyA, z, hzA, hyx, hzx, hyz, hxy, hxz, hyz'⟩ := hcover_tri (gA x) hgAx
    rw [← hgA, Finset.mem_image] at hyA hzA
    obtain ⟨y', _, rfl⟩ := hyA
    obtain ⟨z', _, rfl⟩ := hzA
    refine ⟨y', z', fun heq => hyx (by rw [heq]), fun heq => hzx (by rw [heq]),
      fun heq => hyz (by rw [heq]), ?_, ?_, ?_⟩
    · rw [SimpleGraph.comap_adj]; exact hxy
    · rw [SimpleGraph.comap_adj]; exact hxz
    · rw [SimpleGraph.comap_adj]; exact hyz'
  · rw [edgeCountIn_comap, hgA]; exact hr5


/-- **§§3–7: `MH2Ctx → False`.** The graph-theoretic heart of [MH″]. -/
theorem MH2Ctx.false_of (ctx : MH2Ctx) (h : PrimFacts) (bf : BrouwerFacts) : False := by
  have hHcf5 : ctx.H.CliqueFree 5 := ctx.H_cliqueFree5 h bf
  -- §4.10: e(H) ≥ 58
  have hH58 : 58 ≤ edgeCountIn ctx.H Finset.univ :=
    edgeCount_ge_58 h ctx.H ctx.alphaH hHcf5 (ctx.cap ctx.k)
  -- §3: e(F_i) ≥ 38 for i ≠ k
  have hFi : ∀ i : Fin 5, i ≠ ctx.k → 38 ≤ edgeCountIn (ctx.Gc i) Finset.univ :=
    fun i hik => ctx.edgeCount_Fi_ge_38 bf hik
  -- §6: the five graphs partition C(21,2) = 210, so all bounds are tight
  have hsum : ∑ i, edgeCountIn (ctx.Gc i) Finset.univ = 210 := by
    have hh := ctx.edgeSumOn Finset.univ
    rwa [Finset.card_univ, Fintype.card_fin] at hh
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin 5))
    (fun i => edgeCountIn (ctx.Gc i) Finset.univ) (Finset.mem_univ ctx.k)
  simp only [] at hsplit
  have hH58' : 58 ≤ edgeCountIn (ctx.Gc ctx.k) Finset.univ := hH58
  have hrest : 152 ≤ ∑ i ∈ Finset.univ.erase ctx.k, edgeCountIn (ctx.Gc i) Finset.univ := by
    have hle : ∑ _i ∈ Finset.univ.erase ctx.k, 38
        ≤ ∑ i ∈ Finset.univ.erase ctx.k, edgeCountIn (ctx.Gc i) Finset.univ :=
      Finset.sum_le_sum (fun i hi => hFi i (Finset.ne_of_mem_erase hi))
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ ctx.k),
      Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
    omega
  -- e(H) = 58 exactly, and hence ∑_{i≠k} e(F_i) = 152
  have hgk58 : edgeCountIn (ctx.Gc ctx.k) Finset.univ = 58 := by omega
  have hsum152 : ∑ i ∈ Finset.univ.erase ctx.k, edgeCountIn (ctx.Gc i) Finset.univ = 152 := by omega
  have hH58eq : edgeCountIn ctx.H Finset.univ = 58 := hgk58
  -- each e(F_i) = 38 exactly (sum 152 over four classes each ≥ 38)
  have hFi38 : ∀ i : Fin 5, i ≠ ctx.k → edgeCountIn (ctx.Gc i) Finset.univ = 38 := by
    intro i hik
    have hmem : i ∈ Finset.univ.erase ctx.k := Finset.mem_erase.mpr ⟨hik, Finset.mem_univ i⟩
    have hdec := Finset.sum_erase_add (Finset.univ.erase ctx.k)
      (fun j => edgeCountIn (ctx.Gc j) Finset.univ) hmem
    simp only [] at hdec
    have hcard3 : ((Finset.univ.erase ctx.k).erase i).card = 3 := by
      rw [Finset.card_erase_of_mem hmem, Finset.card_erase_of_mem (Finset.mem_univ ctx.k),
        Finset.card_univ, Fintype.card_fin]
    have hge3 : 3 * 38 ≤ ∑ j ∈ (Finset.univ.erase ctx.k).erase i,
        edgeCountIn (ctx.Gc j) Finset.univ := by
      have hle : ∑ _j ∈ (Finset.univ.erase ctx.k).erase i, 38
          ≤ ∑ j ∈ (Finset.univ.erase ctx.k).erase i, edgeCountIn (ctx.Gc j) Finset.univ :=
        Finset.sum_le_sum (fun j hj =>
          hFi j (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)))
      rw [Finset.sum_const, hcard3, smul_eq_mul] at hle
      omega
    have hi38 := hFi i hik
    omega
  exact ctx.endgame h bf hHcf5 hH58eq hFi38

/-! ## §1: the reduction — building `MH2Ctx` from a balanced colouring -/

/-- Balanced ⟹ every 6-set spans ≥ 1 edge of each colour (sees every colour). -/
theorem sees_colour {n : ℕ} {c : Sym2 (Fin n) → Fin 5} (hbal : Balanced c) (k : Fin 5)
    {S : Finset (Fin n)} (hS : S.card = 6) : 1 ≤ edgeCountIn (colourClass c k) S := by
  have hnm := hbal S hS k
  rw [Misses] at hnm
  push Not at hnm
  obtain ⟨u, hu, v, hv, huv, hck⟩ := hnm
  rw [edgeCountIn_colourClass, Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
  refine ⟨s(u, v), Finset.mem_filter.mpr ⟨Finset.mk_mem_sym2_iff.mpr ⟨hu, hv⟩, ?_, hck⟩⟩
  rw [Sym2.mk_isDiag_iff]; exact huv

/-- **[MH″], conditional on `PrimFacts` and `BrouwerFacts`.** For every balanced
5-colouring of `K₂₅`, every colour `k`, and every 4-set `T`, some independent 5-set
of the colour-`k` class avoids `T`. Proved by contradiction: `¬∃` gives
`α(G_k − T) ≤ 4`; restricting to the 21 non-`T` vertices builds an `MH2Ctx`, whose
existence is refuted by `MH2Ctx.false_of` (§§3–7). -/
theorem lemma_MH2_of (pf : PrimFacts) (bf : BrouwerFacts) : MH2 := by
  intro c hbal k T hT
  by_contra hno
  push Not at hno
  -- hno : ∀ S, S.card = 5 → Disjoint S T → ¬ IsIndep (colourClass c k) S
  have hTc : (Finset.univ \ T).card = 21 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ T), Finset.card_univ, Fintype.card_fin, hT]
  obtain ⟨f, hf⟩ := exists_embedding_image_eq (Finset.univ \ T) hTc
  -- `f u ∉ T` for every `u : Fin 21`, since `f` lands in `univ \ T`
  have hfnotT : ∀ u : Fin 21, f u ∉ T := by
    intro u hu
    have hmem : f u ∈ Finset.univ \ T := by
      rw [← hf]; exact Finset.mem_image_of_mem f (Finset.mem_univ u)
    exact (Finset.mem_sdiff.mp hmem).2 hu
  refine MH2Ctx.false_of
    { Gc := fun i => (colourClass c i).comap f
      k := k
      col := fun u v => c s(f u, f v)
      adj_iff := ?_
      cap := ?_
      alpha5 := ?_
      alphaH := ?_
      edgeSumOn := ?_
      sees6 := ?_ } pf bf
  · -- adjacency ⟺ colour, transported
    intro i u v
    rw [SimpleGraph.comap_adj]
    constructor
    · rintro ⟨hne, hc⟩; exact ⟨fun h => hne (by rw [h]), hc⟩
    · rintro ⟨hne, hc⟩; exact ⟨fun h => hne (f.injective h), hc⟩
  · -- cap-11 (from balancedness), transported
    intro i
    exact capAtMost11_comap (colourClass c i) f (fun S hS => cap_eleven hbal i S hS)
  · -- α ≤ 5 (from balancedness), transported
    intro i
    exact alphaAtMost_comap_gen (colourClass c i) f
      (fun S _ hSindep => indep_le_five hbal i S hSindep)
  · -- α(H) ≤ 4 (the α(G_k − T) ≤ 4 assumption), transported
    refine alphaAtMost_comap_gen (colourClass c k) f (fun S hSsub hSindep => ?_)
    by_contra hgt
    push Not at hgt
    obtain ⟨S', hS'sub, hS'card⟩ := Finset.exists_subset_card_eq (show 5 ≤ S.card by omega)
    have hdisj : Disjoint S' T := by
      rw [Finset.disjoint_left]
      intro x hx hxT
      have hxmem : x ∈ Finset.univ \ T := by rw [← hf]; exact hSsub (hS'sub hx)
      exact (Finset.mem_sdiff.mp hxmem).2 hxT
    have hS'indep : IsIndep (colourClass c k) S' :=
      fun a ha b hb hab => hSindep a (hS'sub ha) b (hS'sub hb) hab
    exact hno S' hS'card hdisj hS'indep
  · -- colours partition each subset
    intro W
    have hcomap : ∀ i, edgeCountIn ((colourClass c i).comap f) W
        = edgeCountIn (colourClass c i) (W.image f) :=
      fun i => edgeCountIn_comap (colourClass c i) f W
    simp_rw [hcomap]
    rw [sum_edgeCountIn_colourClass, Finset.card_image_of_injective _ f.injective]
  · -- every 6-set sees every colour (from balancedness)
    intro S hS c'
    rw [edgeCountIn_comap]
    exact sees_colour hbal c' (by rw [Finset.card_image_of_injective _ f.injective, hS])

end Erdos617
