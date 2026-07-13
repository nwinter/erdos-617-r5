/-
D-CAMPAIGN development file (runner 17) — the (5,21) KP equality classification
`KPEqualityClassification`, proved by re-tracing KP Theorem 4's equality trace under `α ≤ 4`.

NON-AGGREGATED. This file is a WIP scaffold and MUST NOT be added to `Lean617.lean` (the
aggregator) until it is fully sorry-free — the aggregator is required to build sorry-free.

Roadmap (FORMAL.md "D-CAMPAIGN PROGRESS (2026-07-12, runner 17)", the forced-c=4 descent):
  D1  symmetrisation equality: extremal `J` (K₆-free, α≤4, e=173) is a CONE over a max-degree
      vertex `x` — `C = V∖Γx` is independent and `Γx–C` is complete.        [`d1_cone`, DONE]
  D2a top-level part size `c = |C| = 4` (i.e. `deg x = 17`), so `J[Γx]` is extremal at
      `(4,17)` (`e = 105 = p₄(17)`).                                         [`d2a_deg17`, DONE]
  D2b recurse the (D1,D2a) cone step at (4,17),(3,13),(2,9) — the descent 21→17→13→9.
      Generic helpers `cone_extremal_gen`/`eD_bound_gen`/`maxdeg_ge_gen`/`comap_nbhd_package`
      (level-independent structure) + per-level `descent_21_to_17`/`descent_17_to_13`/
      `descent_13_to_9` (the concrete `c=4` forcing). Each returns the next extremal PACKAGE
      (`K_r`-free, `α≤4`, `e = p_{r-1}(n-4)`) as a graph object, so the levels chain.    [DONE]
  Base (2,9): triangle-free, non-bipartite, `α≤4`, `e=17`. The 2 iso-classes are `base9A2`
      (`|A*|=2`, degseq `[3,3,4⁷]`) and `base9A1` (`|A*|=1`, degseq `[2,4⁸]`) — verified
      (`base9A{1,2}_{edgeCount,cliqueFree3,alpha}`; nauty `geng` confirms exactly these two).
      `base_maxdeg_le_four` (triangle-free ⇒ `Δ≤4`) is the sorry-free reduction that forces the
      degree sequence. `base_classification` (`≅ base9A2 ∨ base9A1`) is the remaining SORRY.  [PARTIAL]
  D3  apex freedom (`A*⊂N_s` proper) ⇒ `J ≅ kpG` (|A*|=2) or `kpG1` (|A*|=1).          [TODO]
  D4  transport (`equality21_transport`, DONE) + the 2 witnesses (`AB21_kpG_compl`,
      `AB21_kpG1_compl`, DONE) close `KPEqualityClassification`.

Research project: Mathlib style linters disabled.
-/
import Lean617.Brouwer
import Lean617.BrouwerInduction

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.multiGoal false
set_option linter.style.openClassical false
set_option maxHeartbeats 1000000

open Finset SimpleGraph
open scoped Classical

namespace Erdos617

/-! ## D1 — Symmetrisation equality (the cone extraction)

For an extremal `J` on `Fin 21` (`K₆`-free, `α ≤ 4`, `e(J) = 173`) and a maximum-degree vertex
`x`, the KP symmetrisation `H = symmG J x` satisfies `e(J) ≤ e(H)` (max degree) and `e(H) ≤ 173`
(it is `K₆`-free and non-5-colourable, so `kp_saving` applies). With `e(J) = 173` both are
equalities, so `e(J) = e(H)`. Since `d_J(v) ≤ d_H(v)` pointwise, the sum equality forces
`d_J(v) = d_H(v)` for EVERY `v`; reading this off `Γx` and `C = V∖Γx` gives the cone:
`Γx–C` complete and `C` independent. -/

/-- The max-degree of an extremal `J` (e = 173) on `Fin 21` is at least 17 (handshake:
`Σ deg = 346 > 21·16`). -/
theorem maxdeg_ge_17 (J : SimpleGraph (Fin 21)) (he : edgeCountIn J Finset.univ = 173)
    (x : Fin 21) (hmax : ∀ y, J.degree y ≤ J.degree x) : 17 ≤ J.degree x := by
  by_contra hlt
  push_neg at hlt
  have hsum : ∑ v, J.degree v = 2 * 173 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, ← edgeCountIn_univ_eq_card_edgeFinset, he]
  have hbound : ∑ v, J.degree v ≤ ∑ _v : Fin 21, 16 := by
    apply Finset.sum_le_sum; intro v _; have := hmax v; omega
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hbound
  omega

/-- In the symmetrisation, a vertex `v ∉ Γx` (i.e. `v ∈ C`) has neighbourhood exactly `Γx = D`. -/
theorem symmG_nbhd_of_notMem (J : SimpleGraph (Fin 21)) (x v : Fin 21)
    (hv : v ∉ J.neighborFinset x) :
    (symmG J x).neighborFinset v = J.neighborFinset x := by
  ext w
  rw [SimpleGraph.mem_neighborFinset, symmG_adj]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩)
    · exact absurd h hv
    · exact absurd h hv
    · exact h
  · intro hw; exact Or.inr (Or.inr ⟨hv, hw⟩)

/-- `α(symmG J x) ≤ 4` when `α(J) ≤ 4` and `|C| = |V∖Γx| ≤ 4`: an independent set of `symmG`
lies entirely in `D = Γx` (⇒ independent in `J`, `≤ 4`) or entirely in `C` (`≤ |C| ≤ 4`), because
`D–C` is complete in `symmG`. -/
theorem symmG_alpha_of (J : SimpleGraph (Fin 21)) (hα : alphaAtMost J 4) (x : Fin 21)
    (hc : (Finset.univ \ J.neighborFinset x).card ≤ 4) :
    alphaAtMost (symmG J x) 4 := by
  intro S hS
  by_cases hSD : ∀ v ∈ S, v ∈ J.neighborFinset x
  · -- S ⊆ D: independent in J
    apply hα
    intro u hu v hv huv
    have h := hS u hu v hv huv
    rwa [symmG_adj_of_mem_mem (hSD u hu) (hSD v hv)] at h
  · -- some vertex of S in C ⇒ S ⊆ C
    push_neg at hSD
    obtain ⟨w, hwS, hwC⟩ := hSD
    have hSsubC : S ⊆ Finset.univ \ J.neighborFinset x := by
      intro v hv
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hvD
      by_cases hvw : v = w
      · rw [hvw] at hvD; exact hwC hvD
      · exact hS v hv w hwS hvw (by rw [symmG_adj]; exact Or.inr (Or.inl ⟨hvD, hwC⟩))
    exact le_trans (Finset.card_le_card hSsubC) hc

/-- **D1: the cone structure.** For extremal `J` (`K₆`-free, `α ≤ 4`, `e = 173`) and a maximum
degree vertex `x`, with `D = Γx` and `C = V∖D`: `C` is independent and `D–C` is complete.
Equivalently `J = join(J[D], independent C)`. This is KP Theorem 4's Case-A equality claim,
specialised to `(5,21)`; it feeds D2. -/
theorem d1_cone (J : SimpleGraph (Fin 21)) (hK6 : J.CliqueFree 6) (hα : alphaAtMost J 4)
    (he : edgeCountIn J Finset.univ = 173) (x : Fin 21) (hmax : ∀ y, J.degree y ≤ J.degree x) :
    (∀ u ∈ Finset.univ \ J.neighborFinset x, ∀ v ∈ Finset.univ \ J.neighborFinset x, ¬ J.Adj u v)
    ∧ (∀ u ∈ J.neighborFinset x, ∀ v ∈ Finset.univ \ J.neighborFinset x, J.Adj u v) := by
  set D := J.neighborFinset x with hDdef
  -- d = |D| = deg x ≥ 17, so |C| = 21 − d ≤ 4
  have hd17 : 17 ≤ J.degree x := maxdeg_ge_17 J he x hmax
  have hdD : D.card = J.degree x := J.card_neighborFinset_eq_degree x
  have hCcard : (Finset.univ \ D).card = 21 - D.card := by
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin]
  have hc4 : (Finset.univ \ D).card ≤ 4 := by omega
  -- symmG is K₆-free and non-5-colourable, so kp_saving bounds e(H) ≤ 173
  have hαsymm : alphaAtMost (symmG J x) 4 := symmG_alpha_of J hα x hc4
  have hnc : ¬ (symmG J x).Colorable 5 := not_colorable_of_alphaAtMost _ hαsymm (by norm_num)
  have hsave := kp_saving (n := 21) (r := 5) (by norm_num) (by norm_num)
    (symmG J x) (symmG_cliqueFree hK6) hnc
  rw [turan_5_21] at hsave
  have hge : 173 ≤ edgeCountIn (symmG J x) Finset.univ := by
    have := symmG_edgeCount_ge (G := J) (x := x) hmax; rw [he] at this; exact this
  have hesymm : edgeCountIn (symmG J x) Finset.univ = 173 := by omega
  -- pointwise degree equality d_J(v) = d_H(v) for all v (from e(J) = e(H) + pointwise ≤)
  have hsumeq : ∑ v, J.degree v = ∑ v, (symmG J x).degree v := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, SimpleGraph.sum_degrees_eq_twice_card_edges,
      ← edgeCountIn_univ_eq_card_edgeFinset, ← edgeCountIn_univ_eq_card_edgeFinset, he, hesymm]
  have hpt : ∀ v, J.degree v = (symmG J x).degree v := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨w, hw⟩ := hcon
    have hstrict : J.degree w < (symmG J x).degree w :=
      lt_of_le_of_ne (symmG_degree_ge hmax w) hw
    have hlt : ∑ v, J.degree v < ∑ v, (symmG J x).degree v :=
      Finset.sum_lt_sum (fun v _ => symmG_degree_ge hmax v) ⟨w, Finset.mem_univ w, hstrict⟩
    omega
  -- For y ∈ D: N_J(y) = N_H(y) (subset + equal card), and N_H(y) ⊇ C ⇒ y adjacent to all C.
  have hDC : ∀ y ∈ D, ∀ v ∈ Finset.univ \ D, J.Adj y v := by
    intro y hyD v hv
    rw [Finset.mem_sdiff] at hv
    have hvC : v ∉ D := hv.2
    -- N_J(y) ⊆ N_H(y)
    have hsub : J.neighborFinset y ⊆ (symmG J x).neighborFinset y := by
      intro w hw
      rw [SimpleGraph.mem_neighborFinset] at hw ⊢
      by_cases hwD : w ∈ D
      · exact (symmG_adj_of_mem_mem hyD hwD).mpr hw
      · rw [symmG_adj]; exact Or.inr (Or.inl ⟨hyD, hwD⟩)
    -- equal cardinality (degree equality)
    have hcard : (J.neighborFinset y).card = ((symmG J x).neighborFinset y).card := by
      rw [J.card_neighborFinset_eq_degree, (symmG J x).card_neighborFinset_eq_degree, hpt y]
    have heqset : J.neighborFinset y = (symmG J x).neighborFinset y :=
      Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
    -- v ∈ N_H(y) since D–C complete in symmG
    have hvH : v ∈ (symmG J x).neighborFinset y := by
      rw [SimpleGraph.mem_neighborFinset, symmG_adj]; exact Or.inr (Or.inl ⟨hyD, hvC⟩)
    rw [← heqset, SimpleGraph.mem_neighborFinset] at hvH
    exact hvH
  refine ⟨?_, hDC⟩
  -- C independent: u ∈ C has degree d = |D|, is adjacent to all D (from hDC), so N_J(u) = D.
  intro u hu v hv hadj
  rw [Finset.mem_sdiff] at hu hv
  have huC : u ∉ D := hu.2
  have hvC : v ∉ D := hv.2
  -- D ⊆ N_J(u): every D-vertex is adjacent to u (D–C complete, symmetric)
  have hDsub : D ⊆ J.neighborFinset u := by
    intro y hyD
    rw [SimpleGraph.mem_neighborFinset]
    exact (hDC y hyD u (by rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, huC⟩)).symm
  -- |N_J(u)| = deg u = deg_H(u) = |D| (since u ∈ C)
  have hHu : (symmG J x).neighborFinset u = D := symmG_nbhd_of_notMem J x u huC
  have hdegu : J.degree u = D.card := by
    rw [hpt u, ← (symmG J x).card_neighborFinset_eq_degree, hHu]
  have hcardu : (J.neighborFinset u).card = D.card := by
    rw [J.card_neighborFinset_eq_degree, hdegu]
  -- N_J(u) = D (D ⊆ N_J(u) with equal card)
  have hNu : J.neighborFinset u = D := (Finset.eq_of_subset_of_card_le hDsub (le_of_eq hcardu)).symm
  -- but v ∈ N_J(u) (hadj) and v ∉ D — contradiction
  have : v ∈ J.neighborFinset u := by rw [SimpleGraph.mem_neighborFinset]; exact hadj
  rw [hNu] at this
  exact hvC this

/-! ## D2, step a — the top-level part size `c = 4` (equivalently `deg x = 17`)

The cone `J = join(J[D], C)` has `e(J[D]) = 173 − d·(21−d)` where `d = deg x = |D|`. `J[D]` (on
`Fin d`) is `K₅`-free (`D = Γx`) and `α ≤ 4`, hence non-4-partite (`d > 16`), so `kp_saving` at
`r = 4` bounds `e(J[D]) + (d/4 − 1) ≤ t₄(d)`. The numerics (scratchpad/eq21_descent.py) show this
is VIOLATED for `d ∈ {18,19,20}` (`c ∈ {1,2,3}`) and tight for `d = 17` (`c = 4`). So `d = 17`,
and `J[D]` is the next extremal graph, `e(J[D]) = 105 = p₄(17)` — continuing the descent. -/

/-- **The `(4,d)` Brouwer bound on `J[Γx]`**, expressed at the `Fin 21` level: for `K₆`-free `J`
with `α ≤ 4` and `d = |Γx| > 16`, `e(J[Γx]) + (d/4 − 1) ≤ t₄(d)`. (The induced subgraph is
transported to `Fin d` internally; `kp_saving` at `r = 4` applies since it is `K₅`-free,
`α ≤ 4`, and non-4-colourable.) -/
theorem eD_bound (J : SimpleGraph (Fin 21)) (hK6 : J.CliqueFree 6) (hα : alphaAtMost J 4)
    (x : Fin 21) (hd16 : 16 < (J.neighborFinset x).card) :
    edgeCountIn J (J.neighborFinset x) + ((J.neighborFinset x).card / 4 - 1)
      ≤ (turanGraph (J.neighborFinset x).card 4).edgeFinset.card := by
  obtain ⟨f, hf⟩ := exists_embedding_image_eq (J.neighborFinset x)
    (rfl : (J.neighborFinset x).card = (J.neighborFinset x).card)
  set X := J.comap f with hXdef
  have hXcount : edgeCountIn X Finset.univ = edgeCountIn J (J.neighborFinset x) := by
    rw [hXdef, edgeCountIn_comap J f Finset.univ, hf]
  have hXCF : X.CliqueFree 5 := by
    intro K hK
    rw [hXdef] at hK
    obtain ⟨hclq, hcard⟩ := hK
    have hSsub : K.image f ⊆ J.neighborFinset x := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨a, _, rfl⟩ := hy
      have hmem : f a ∈ Finset.univ.image f := Finset.mem_image_of_mem f (Finset.mem_univ a)
      rwa [hf] at hmem
    have hSclq : J.IsClique ↑(K.image f) := by
      intro u hu v hv huv
      rw [Finset.mem_coe, Finset.mem_image] at hu hv
      obtain ⟨a, ha, rfl⟩ := hu
      obtain ⟨b, hb, rfl⟩ := hv
      have hab : a ≠ b := fun h => huv (by rw [h])
      have hcc := hclq (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab
      rwa [SimpleGraph.comap_adj] at hcc
    have hScard : (K.image f).card = 5 := by
      rw [Finset.card_image_of_injective _ f.injective, hcard]
    have hle := no_clique_r_in_nbhd (r := 5) hK6 (K.image f) hSsub hSclq
    omega
  have hXα : alphaAtMost X 4 := alphaAtMost_comap_gen J f (fun S _ hind => hα S hind)
  have hXnc : ¬ X.Colorable 4 := not_colorable_of_alphaAtMost X hXα (by omega)
  have hsave := kp_saving (n := (J.neighborFinset x).card) (r := 4) (by norm_num) (by omega)
    X hXCF hXnc
  rw [hXcount] at hsave
  exact hsave

/-- **D2a: the top-level part size is `4`.** For extremal `J` (`K₆`-free, `α ≤ 4`, `e = 173`) and a
maximum degree vertex `x`, `deg x = 17` (so `|C| = |V∖Γx| = 4`). Ruling out `deg x ∈ {18,19,20}`
via `eD_bound` + the concrete Turán numbers `t₄(18)=121, t₄(19)=135, t₄(20)=150`. -/
theorem d2a_deg17 (J : SimpleGraph (Fin 21)) (hK6 : J.CliqueFree 6) (hα : alphaAtMost J 4)
    (he : edgeCountIn J Finset.univ = 173) (x : Fin 21) (hmax : ∀ y, J.degree y ≤ J.degree x) :
    (J.neighborFinset x).card = 17 := by
  have hcone := d1_cone J hK6 hα he x hmax
  -- e(J[D]) = 173 − d·(21−d) from the cone decomposition
  have hconeE : edgeCountIn J Finset.univ
      = edgeCountIn J (J.neighborFinset x)
        + (J.neighborFinset x).card * (21 - (J.neighborFinset x).card) := by
    apply edgeCountIn_univ_of_cone
    · intro u hu v hv
      exact hcone.1 u (by rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, hu⟩)
        v (by rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, hv⟩)
    · intro u hu v hv
      exact hcone.2 u hu v (by rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, hv⟩)
  rw [he] at hconeE
  -- d ≥ 17 and d ≤ 20
  have hd17 : 17 ≤ (J.neighborFinset x).card := by
    have := maxdeg_ge_17 J he x hmax; rw [J.card_neighborFinset_eq_degree x]; exact this
  have hd20 : (J.neighborFinset x).card ≤ 20 := by
    have hsub : J.neighborFinset x ⊆ Finset.univ.erase x := by
      intro y hy
      rw [Finset.mem_erase]
      exact ⟨(J.ne_of_adj ((J.mem_neighborFinset x y).mp hy)).symm, Finset.mem_univ _⟩
    calc (J.neighborFinset x).card ≤ (Finset.univ.erase x).card := Finset.card_le_card hsub
      _ = 20 := by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
                        Fintype.card_fin]
  -- the Brouwer bound on J[D]
  have hbound := eD_bound J hK6 hα x (by omega)
  -- case-split on d ∈ {17,18,19,20}; only 17 is consistent
  set d := (J.neighborFinset x).card with hddef
  interval_cases d
  · rfl
  · exfalso
    have ht : (turanGraph 18 4).edgeFinset.card = 121 := by rw [card_edgeFinset_turanGraph]; decide
    rw [ht] at hbound; omega
  · exfalso
    have ht : (turanGraph 19 4).edgeFinset.card = 135 := by rw [card_edgeFinset_turanGraph]; decide
    rw [ht] at hbound; omega
  · exfalso
    have ht : (turanGraph 20 4).edgeFinset.card = 150 := by rw [card_edgeFinset_turanGraph]; decide
    rw [ht] at hbound; omega

/-! ## Generic structural helpers for the descent (level-independent)

These generalize `maxdeg_ge_17`, `symmG_nbhd_of_notMem`, `symmG_alpha_of`, `d1_cone`, `eD_bound`
(all currently pinned to `(5,21)`) to arbitrary `(r,n)`. The cone extraction and α-bound have NO
small-margin arithmetic, so generalizing them is safe; the level-specific `c=4` forcing (the tight
part) stays concrete in the per-level descent lemmas below. -/

/-- Handshake max-degree bound: if `n·(k−1) < 2E`, a max-degree vertex has degree `≥ k`. -/
theorem maxdeg_ge_gen {n : ℕ} (J : SimpleGraph (Fin n)) (E k : ℕ)
    (he : edgeCountIn J Finset.univ = E) (x : Fin n) (hmax : ∀ y, J.degree y ≤ J.degree x)
    (hkE : n * (k - 1) < 2 * E) : k ≤ J.degree x := by
  by_contra hlt
  push_neg at hlt
  have hsum : ∑ v, J.degree v = 2 * E := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, ← edgeCountIn_univ_eq_card_edgeFinset, he]
  have hbound : ∑ v, J.degree v ≤ ∑ _v : Fin n, (k - 1) := by
    apply Finset.sum_le_sum; intro v _; have := hmax v; omega
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hbound
  omega

/-- In `symmG`, a vertex `v ∉ Γx` has neighbourhood exactly `Γx`. (Generic in `n`.) -/
theorem symmG_nbhd_of_notMem_gen {n : ℕ} (J : SimpleGraph (Fin n)) (x v : Fin n)
    (hv : v ∉ J.neighborFinset x) :
    (symmG J x).neighborFinset v = J.neighborFinset x := by
  ext w
  rw [SimpleGraph.mem_neighborFinset, symmG_adj]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩)
    · exact absurd h hv
    · exact absurd h hv
    · exact h
  · intro hw; exact Or.inr (Or.inr ⟨hv, hw⟩)

/-- `α(symmG J x) ≤ 4` when `α(J) ≤ 4` and `|C| ≤ 4`. (Generic in `n`.) -/
theorem symmG_alpha_of_gen {n : ℕ} (J : SimpleGraph (Fin n)) (hα : alphaAtMost J 4) (x : Fin n)
    (hc : (Finset.univ \ J.neighborFinset x).card ≤ 4) :
    alphaAtMost (symmG J x) 4 := by
  intro S hS
  by_cases hSD : ∀ v ∈ S, v ∈ J.neighborFinset x
  · apply hα
    intro u hu v hv huv
    have h := hS u hu v hv huv
    rwa [symmG_adj_of_mem_mem (hSD u hu) (hSD v hv)] at h
  · push_neg at hSD
    obtain ⟨w, hwS, hwC⟩ := hSD
    have hSsubC : S ⊆ Finset.univ \ J.neighborFinset x := by
      intro v hv
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hvD
      by_cases hvw : v = w
      · rw [hvw] at hvD; exact hwC hvD
      · exact hS v hv w hwS hvw (by rw [symmG_adj]; exact Or.inr (Or.inl ⟨hvD, hwC⟩))
    exact le_trans (Finset.card_le_card hSsubC) hc

/-- **Generic cone extraction (D1).** For extremal `J` at `(r,n)` (`K_{r+1}`-free, `α≤4`,
`e = E` with `E + (n/r−1) = t_r(n)`), a max-degree vertex `x` with `|C| = |V∖Γx| ≤ 4` yields the
cone: `C` independent and `Γx–C` complete. -/
theorem cone_extremal_gen {n r : ℕ} (J : SimpleGraph (Fin n)) (hr : 0 < r) (h2rn : 2 * r + 1 ≤ n)
    (hrn4 : r * 4 < n) (hK : J.CliqueFree (r + 1)) (hα : alphaAtMost J 4) (E : ℕ)
    (he : edgeCountIn J Finset.univ = E)
    (hp : E + (n / r - 1) = (turanGraph n r).edgeFinset.card) (x : Fin n)
    (hmax : ∀ y, J.degree y ≤ J.degree x)
    (hc4 : (Finset.univ \ J.neighborFinset x).card ≤ 4) :
    (∀ u ∈ Finset.univ \ J.neighborFinset x, ∀ v ∈ Finset.univ \ J.neighborFinset x, ¬ J.Adj u v)
    ∧ (∀ u ∈ J.neighborFinset x, ∀ v ∈ Finset.univ \ J.neighborFinset x, J.Adj u v) := by
  set D := J.neighborFinset x with hDdef
  have hαsymm : alphaAtMost (symmG J x) 4 := symmG_alpha_of_gen J hα x hc4
  have hnc : ¬ (symmG J x).Colorable r := not_colorable_of_alphaAtMost _ hαsymm (by omega)
  have hge : E ≤ edgeCountIn (symmG J x) Finset.univ := by
    have := symmG_edgeCount_ge (G := J) (x := x) hmax; rw [he] at this; exact this
  have hsave := kp_saving hr h2rn (symmG J x) (symmG_cliqueFree hK) hnc
  have hesymm : edgeCountIn (symmG J x) Finset.univ = E := by omega
  -- pointwise degree equality
  have hsumeq : ∑ v, J.degree v = ∑ v, (symmG J x).degree v := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, SimpleGraph.sum_degrees_eq_twice_card_edges,
      ← edgeCountIn_univ_eq_card_edgeFinset, ← edgeCountIn_univ_eq_card_edgeFinset, he, hesymm]
  have hpt : ∀ v, J.degree v = (symmG J x).degree v := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨w, hw⟩ := hcon
    have hstrict : J.degree w < (symmG J x).degree w :=
      lt_of_le_of_ne (symmG_degree_ge hmax w) hw
    have hlt : ∑ v, J.degree v < ∑ v, (symmG J x).degree v :=
      Finset.sum_lt_sum (fun v _ => symmG_degree_ge hmax v) ⟨w, Finset.mem_univ w, hstrict⟩
    omega
  have hDC : ∀ y ∈ D, ∀ v ∈ Finset.univ \ D, J.Adj y v := by
    intro y hyD v hv
    rw [Finset.mem_sdiff] at hv
    have hvC : v ∉ D := hv.2
    have hsub : J.neighborFinset y ⊆ (symmG J x).neighborFinset y := by
      intro w hw
      rw [SimpleGraph.mem_neighborFinset] at hw ⊢
      by_cases hwD : w ∈ D
      · exact (symmG_adj_of_mem_mem hyD hwD).mpr hw
      · rw [symmG_adj]; exact Or.inr (Or.inl ⟨hyD, hwD⟩)
    have hcard : (J.neighborFinset y).card = ((symmG J x).neighborFinset y).card := by
      rw [J.card_neighborFinset_eq_degree, (symmG J x).card_neighborFinset_eq_degree, hpt y]
    have heqset : J.neighborFinset y = (symmG J x).neighborFinset y :=
      Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
    have hvH : v ∈ (symmG J x).neighborFinset y := by
      rw [SimpleGraph.mem_neighborFinset, symmG_adj]; exact Or.inr (Or.inl ⟨hyD, hvC⟩)
    rw [← heqset, SimpleGraph.mem_neighborFinset] at hvH
    exact hvH
  refine ⟨?_, hDC⟩
  intro u hu v hv hadj
  rw [Finset.mem_sdiff] at hu hv
  have huC : u ∉ D := hu.2
  have hvC : v ∉ D := hv.2
  have hDsub : D ⊆ J.neighborFinset u := by
    intro y hyD
    rw [SimpleGraph.mem_neighborFinset]
    exact (hDC y hyD u (by rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, huC⟩)).symm
  have hHu : (symmG J x).neighborFinset u = D := symmG_nbhd_of_notMem_gen J x u huC
  have hdegu : J.degree u = D.card := by
    rw [hpt u, ← (symmG J x).card_neighborFinset_eq_degree, hHu]
  have hcardu : (J.neighborFinset u).card = D.card := by
    rw [J.card_neighborFinset_eq_degree, hdegu]
  have hNu : J.neighborFinset u = D := (Finset.eq_of_subset_of_card_le hDsub (le_of_eq hcardu)).symm
  have : v ∈ J.neighborFinset u := by rw [SimpleGraph.mem_neighborFinset]; exact hadj
  rw [hNu] at this
  exact hvC this

/-- **Generic Brouwer bound on `J[Γx]` (D2a input).** For `K_{r+1}`-free `J` with `α≤4` and
`(r−1)·4 < |Γx|`, the induced `J[Γx]` (`K_r`-free, `α≤4`, non-`(r−1)`-colourable) obeys
`e(J[Γx]) + (|Γx|/(r−1) − 1) ≤ t_{r−1}(|Γx|)`. -/
theorem eD_bound_gen {n r : ℕ} (J : SimpleGraph (Fin n)) (hr : 2 ≤ r) (hK : J.CliqueFree (r + 1))
    (hα : alphaAtMost J 4) (x : Fin n) (hd : (r - 1) * 4 < (J.neighborFinset x).card) :
    edgeCountIn J (J.neighborFinset x) + ((J.neighborFinset x).card / (r - 1) - 1)
      ≤ (turanGraph (J.neighborFinset x).card (r - 1)).edgeFinset.card := by
  obtain ⟨f, hf⟩ := exists_embedding_image_eq (J.neighborFinset x)
    (rfl : (J.neighborFinset x).card = (J.neighborFinset x).card)
  set X := J.comap f with hXdef
  have hXcount : edgeCountIn X Finset.univ = edgeCountIn J (J.neighborFinset x) := by
    rw [hXdef, edgeCountIn_comap J f Finset.univ, hf]
  have hXCF : X.CliqueFree r := by
    intro K hK'
    rw [hXdef] at hK'
    obtain ⟨hclq, hcard⟩ := hK'
    have hSsub : K.image f ⊆ J.neighborFinset x := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨a, _, rfl⟩ := hy
      have hmem : f a ∈ Finset.univ.image f := Finset.mem_image_of_mem f (Finset.mem_univ a)
      rwa [hf] at hmem
    have hSclq : J.IsClique ↑(K.image f) := by
      intro u hu v hv huv
      rw [Finset.mem_coe, Finset.mem_image] at hu hv
      obtain ⟨a, ha, rfl⟩ := hu
      obtain ⟨b, hb, rfl⟩ := hv
      have hab : a ≠ b := fun h => huv (by rw [h])
      have hcc := hclq (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab
      rwa [SimpleGraph.comap_adj] at hcc
    have hScard : (K.image f).card = r := by
      rw [Finset.card_image_of_injective _ f.injective, hcard]
    have hle := no_clique_r_in_nbhd (r := r) hK (K.image f) hSsub hSclq
    omega
  have hXα : alphaAtMost X 4 := alphaAtMost_comap_gen J f (fun S _ hind => hα S hind)
  have hXnc : ¬ X.Colorable (r - 1) := not_colorable_of_alphaAtMost X hXα (by omega)
  have hXCF' : X.CliqueFree (r - 1 + 1) := by
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ r)]
  have hsave := kp_saving (n := (J.neighborFinset x).card) (r := r - 1) (by omega) (by omega)
    X hXCF' hXnc
  rw [hXcount] at hsave
  exact hsave

/-- **The comap extremal package.** Transport `J[Γx]` to `Fin nc` (`nc = |Γx|`) as a graph object:
`K_r`-free, `α≤4`, with edge count equal to `e(J[Γx])`. This is what lets the descent levels chain
(each level's output is the next level's input graph). -/
theorem comap_nbhd_package {n r nc : ℕ} (J : SimpleGraph (Fin n)) (hr : 1 ≤ r)
    (hK : J.CliqueFree (r + 1)) (hα : alphaAtMost J 4) (x : Fin n) (f : Fin nc ↪ Fin n)
    (hf : Finset.univ.image f = J.neighborFinset x) :
    (J.comap f).CliqueFree r ∧ alphaAtMost (J.comap f) 4
      ∧ edgeCountIn (J.comap f) Finset.univ = edgeCountIn J (J.neighborFinset x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro K hK'
    obtain ⟨hclq, hcard⟩ := hK'
    have hSsub : K.image f ⊆ J.neighborFinset x := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨a, _, rfl⟩ := hy
      have hmem : f a ∈ Finset.univ.image f := Finset.mem_image_of_mem f (Finset.mem_univ a)
      rwa [hf] at hmem
    have hSclq : J.IsClique ↑(K.image f) := by
      intro u hu v hv huv
      rw [Finset.mem_coe, Finset.mem_image] at hu hv
      obtain ⟨a, ha, rfl⟩ := hu
      obtain ⟨b, hb, rfl⟩ := hv
      have hab : a ≠ b := fun h => huv (by rw [h])
      have hcc := hclq (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab
      rwa [SimpleGraph.comap_adj] at hcc
    have hScard : (K.image f).card = r := by
      rw [Finset.card_image_of_injective _ f.injective, hcard]
    have hle := no_clique_r_in_nbhd (r := r) hK (K.image f) hSsub hSclq
    omega
  · exact alphaAtMost_comap_gen J f (fun S _ hind => hα S hind)
  · rw [edgeCountIn_comap J f Finset.univ, hf]

/-! ## D2b — the per-level descent lemmas

Each takes the extremal package at `(r,n)` and returns the extremal package at `(r−1, n−4)` as a
concrete graph object. The `c = 4` forcing (ruling out `c ∈ {1,2,3}`, i.e. `deg x ∈ {n−1,n−2,n−3}`)
is done concretely per level via `interval_cases` + the concrete Turán numbers — this is the tight
step (margins 1–2), which is why it is not generalized. -/

/-- **Descent `(5,21) → (4,17)`.** Extremal `J` on `Fin 21` (`K₆`-free, `α≤4`, `e=173`) yields an
extremal `J'` on `Fin 17` (`K₅`-free, `α≤4`, `e=105 = p₄(17)`). ENRICHED (D3): also returns the
neighbourhood embedding `f` (with `J' = J.comap f`) and the cone data — `C = V∖Γx` independent and
`Γx–C` complete — so the reassembly can rebuild `J ≅ (4-set) * J'`. -/
theorem descent_21_to_17 (J : SimpleGraph (Fin 21)) (hK6 : J.CliqueFree 6)
    (hα : alphaAtMost J 4) (he : edgeCountIn J Finset.univ = 173) :
    ∃ (J' : SimpleGraph (Fin 17)) (f : Fin 17 ↪ Fin 21),
      J' = J.comap f ∧ J'.CliqueFree 5 ∧ alphaAtMost J' 4 ∧ edgeCountIn J' Finset.univ = 105 ∧
      (∀ u ∈ Finset.univ \ Finset.univ.image f, ∀ v ∈ Finset.univ \ Finset.univ.image f,
        ¬ J.Adj u v) ∧
      (∀ u ∈ Finset.univ.image f, ∀ v ∈ Finset.univ \ Finset.univ.image f, J.Adj u v) := by
  obtain ⟨x, hxmax⟩ := J.exists_maximal_degree_vertex
  have hmax : ∀ y, J.degree y ≤ J.degree x := fun y => hxmax ▸ J.degree_le_maxDegree y
  have hd17 : 17 ≤ J.degree x := maxdeg_ge_gen J 173 17 he x hmax (by norm_num)
  have hdD : (J.neighborFinset x).card = J.degree x := J.card_neighborFinset_eq_degree x
  have hc4 : (Finset.univ \ J.neighborFinset x).card ≤ 4 := by
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin]; omega
  have hp : (173 : ℕ) + (21 / 5 - 1) = (turanGraph 21 5).edgeFinset.card := by rw [turan_5_21]
  have hcone := cone_extremal_gen J (by norm_num) (by norm_num) (by norm_num) hK6 hα 173 he hp x
    hmax hc4
  have hconeE : edgeCountIn J Finset.univ = edgeCountIn J (J.neighborFinset x)
      + (J.neighborFinset x).card * (21 - (J.neighborFinset x).card) := by
    apply edgeCountIn_univ_of_cone
    · intro u hu v hv
      exact hcone.1 u (by rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, hu⟩)
        v (by rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, hv⟩)
    · intro u hu v hv
      exact hcone.2 u hu v (by rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, hv⟩)
  rw [he] at hconeE
  have hd20 : (J.neighborFinset x).card ≤ 20 := by
    have hsub : J.neighborFinset x ⊆ Finset.univ.erase x := by
      intro y hy; rw [Finset.mem_erase]
      exact ⟨(J.ne_of_adj ((J.mem_neighborFinset x y).mp hy)).symm, Finset.mem_univ _⟩
    calc (J.neighborFinset x).card ≤ (Finset.univ.erase x).card := Finset.card_le_card hsub
      _ = 20 := by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
                        Fintype.card_fin]
  have hd17' : 17 ≤ (J.neighborFinset x).card := by rw [hdD]; exact hd17
  have hbound := eD_bound_gen J (by norm_num) hK6 hα x (by omega)
  simp only [show (5 : ℕ) - 1 = 4 from rfl] at hbound
  have hcard17 : (J.neighborFinset x).card = 17 := by
    set d := (J.neighborFinset x).card with hddef
    interval_cases d
    · rfl
    · exfalso
      have ht : (turanGraph 18 4).edgeFinset.card = 121 := by rw [card_edgeFinset_turanGraph]; decide
      rw [ht] at hbound; omega
    · exfalso
      have ht : (turanGraph 19 4).edgeFinset.card = 135 := by rw [card_edgeFinset_turanGraph]; decide
      rw [ht] at hbound; omega
    · exfalso
      have ht : (turanGraph 20 4).edgeFinset.card = 150 := by rw [card_edgeFinset_turanGraph]; decide
      rw [ht] at hbound; omega
  obtain ⟨f, hf⟩ := exists_embedding_image_eq (J.neighborFinset x) hcard17
  obtain ⟨hCF, hα', hcnt⟩ := comap_nbhd_package J (by norm_num) hK6 hα x f hf
  refine ⟨J.comap f, f, rfl, hCF, hα', ?_, ?_, ?_⟩
  · rw [hcnt]; rw [hcard17] at hconeE; omega
  · rw [hf]; exact hcone.1
  · rw [hf]; exact hcone.2

/-- **Descent `(4,17) → (3,13)`.** Extremal `J` on `Fin 17` (`K₅`-free, `α≤4`, `e=105`) yields an
extremal `J'` on `Fin 13` (`K₄`-free, `α≤4`, `e=53 = p₃(13)`). ENRICHED (D3): neighbourhood
embedding `f` (`J' = J.comap f`) + cone data (`C = V∖Γx` independent, `Γx–C` complete). -/
theorem descent_17_to_13 (J : SimpleGraph (Fin 17)) (hK5 : J.CliqueFree 5)
    (hα : alphaAtMost J 4) (he : edgeCountIn J Finset.univ = 105) :
    ∃ (J' : SimpleGraph (Fin 13)) (f : Fin 13 ↪ Fin 17),
      J' = J.comap f ∧ J'.CliqueFree 4 ∧ alphaAtMost J' 4 ∧ edgeCountIn J' Finset.univ = 53 ∧
      (∀ u ∈ Finset.univ \ Finset.univ.image f, ∀ v ∈ Finset.univ \ Finset.univ.image f,
        ¬ J.Adj u v) ∧
      (∀ u ∈ Finset.univ.image f, ∀ v ∈ Finset.univ \ Finset.univ.image f, J.Adj u v) := by
  obtain ⟨x, hxmax⟩ := J.exists_maximal_degree_vertex
  have hmax : ∀ y, J.degree y ≤ J.degree x := fun y => hxmax ▸ J.degree_le_maxDegree y
  have hd13 : 13 ≤ J.degree x := maxdeg_ge_gen J 105 13 he x hmax (by norm_num)
  have hdD : (J.neighborFinset x).card = J.degree x := J.card_neighborFinset_eq_degree x
  have hc4 : (Finset.univ \ J.neighborFinset x).card ≤ 4 := by
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin]; omega
  have ht417 : (turanGraph 17 4).edgeFinset.card = 108 := by rw [card_edgeFinset_turanGraph]; decide
  have hp : (105 : ℕ) + (17 / 4 - 1) = (turanGraph 17 4).edgeFinset.card := by rw [ht417]
  have hcone := cone_extremal_gen J (by norm_num) (by norm_num) (by norm_num) hK5 hα 105 he hp x
    hmax hc4
  have hconeE : edgeCountIn J Finset.univ = edgeCountIn J (J.neighborFinset x)
      + (J.neighborFinset x).card * (17 - (J.neighborFinset x).card) := by
    apply edgeCountIn_univ_of_cone
    · intro u hu v hv
      exact hcone.1 u (by rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, hu⟩)
        v (by rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, hv⟩)
    · intro u hu v hv
      exact hcone.2 u hu v (by rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, hv⟩)
  rw [he] at hconeE
  have hd16 : (J.neighborFinset x).card ≤ 16 := by
    have hsub : J.neighborFinset x ⊆ Finset.univ.erase x := by
      intro y hy; rw [Finset.mem_erase]
      exact ⟨(J.ne_of_adj ((J.mem_neighborFinset x y).mp hy)).symm, Finset.mem_univ _⟩
    calc (J.neighborFinset x).card ≤ (Finset.univ.erase x).card := Finset.card_le_card hsub
      _ = 16 := by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
                        Fintype.card_fin]
  have hd13' : 13 ≤ (J.neighborFinset x).card := by rw [hdD]; exact hd13
  have hbound := eD_bound_gen J (by norm_num) hK5 hα x (by omega)
  simp only [show (4 : ℕ) - 1 = 3 from rfl] at hbound
  have hcard13 : (J.neighborFinset x).card = 13 := by
    set d := (J.neighborFinset x).card with hddef
    interval_cases d
    · rfl
    · exfalso
      have ht : (turanGraph 14 3).edgeFinset.card = 65 := by rw [card_edgeFinset_turanGraph]; decide
      rw [ht] at hbound; omega
    · exfalso
      have ht : (turanGraph 15 3).edgeFinset.card = 75 := by rw [card_edgeFinset_turanGraph]; decide
      rw [ht] at hbound; omega
    · exfalso
      have ht : (turanGraph 16 3).edgeFinset.card = 85 := by rw [card_edgeFinset_turanGraph]; decide
      rw [ht] at hbound; omega
  obtain ⟨f, hf⟩ := exists_embedding_image_eq (J.neighborFinset x) hcard13
  obtain ⟨hCF, hα', hcnt⟩ := comap_nbhd_package J (by norm_num) hK5 hα x f hf
  refine ⟨J.comap f, f, rfl, hCF, hα', ?_, ?_, ?_⟩
  · rw [hcnt]; rw [hcard13] at hconeE; omega
  · rw [hf]; exact hcone.1
  · rw [hf]; exact hcone.2

/-- **Descent `(3,13) → (2,9)`.** Extremal `J` on `Fin 13` (`K₄`-free, `α≤4`, `e=53`) yields an
extremal `J'` on `Fin 9` (`K₃`-free / triangle-free, `α≤4`, `e=17 = p₂(9)`) — the base. ENRICHED
(D3): neighbourhood embedding `f` (`J' = J.comap f`) + cone data (`C = V∖Γx` independent, `Γx–C`
complete). -/
theorem descent_13_to_9 (J : SimpleGraph (Fin 13)) (hK4 : J.CliqueFree 4)
    (hα : alphaAtMost J 4) (he : edgeCountIn J Finset.univ = 53) :
    ∃ (J' : SimpleGraph (Fin 9)) (f : Fin 9 ↪ Fin 13),
      J' = J.comap f ∧ J'.CliqueFree 3 ∧ alphaAtMost J' 4 ∧ edgeCountIn J' Finset.univ = 17 ∧
      (∀ u ∈ Finset.univ \ Finset.univ.image f, ∀ v ∈ Finset.univ \ Finset.univ.image f,
        ¬ J.Adj u v) ∧
      (∀ u ∈ Finset.univ.image f, ∀ v ∈ Finset.univ \ Finset.univ.image f, J.Adj u v) := by
  obtain ⟨x, hxmax⟩ := J.exists_maximal_degree_vertex
  have hmax : ∀ y, J.degree y ≤ J.degree x := fun y => hxmax ▸ J.degree_le_maxDegree y
  have hd9 : 9 ≤ J.degree x := maxdeg_ge_gen J 53 9 he x hmax (by norm_num)
  have hdD : (J.neighborFinset x).card = J.degree x := J.card_neighborFinset_eq_degree x
  have hc4 : (Finset.univ \ J.neighborFinset x).card ≤ 4 := by
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin]; omega
  have ht313 : (turanGraph 13 3).edgeFinset.card = 56 := by rw [card_edgeFinset_turanGraph]; decide
  have hp : (53 : ℕ) + (13 / 3 - 1) = (turanGraph 13 3).edgeFinset.card := by rw [ht313]
  have hcone := cone_extremal_gen J (by norm_num) (by norm_num) (by norm_num) hK4 hα 53 he hp x
    hmax hc4
  have hconeE : edgeCountIn J Finset.univ = edgeCountIn J (J.neighborFinset x)
      + (J.neighborFinset x).card * (13 - (J.neighborFinset x).card) := by
    apply edgeCountIn_univ_of_cone
    · intro u hu v hv
      exact hcone.1 u (by rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, hu⟩)
        v (by rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, hv⟩)
    · intro u hu v hv
      exact hcone.2 u hu v (by rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, hv⟩)
  rw [he] at hconeE
  have hd12 : (J.neighborFinset x).card ≤ 12 := by
    have hsub : J.neighborFinset x ⊆ Finset.univ.erase x := by
      intro y hy; rw [Finset.mem_erase]
      exact ⟨(J.ne_of_adj ((J.mem_neighborFinset x y).mp hy)).symm, Finset.mem_univ _⟩
    calc (J.neighborFinset x).card ≤ (Finset.univ.erase x).card := Finset.card_le_card hsub
      _ = 12 := by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
                        Fintype.card_fin]
  have hd9' : 9 ≤ (J.neighborFinset x).card := by rw [hdD]; exact hd9
  have hbound := eD_bound_gen J (by norm_num) hK4 hα x (by omega)
  simp only [show (3 : ℕ) - 1 = 2 from rfl] at hbound
  have hcard9 : (J.neighborFinset x).card = 9 := by
    set d := (J.neighborFinset x).card with hddef
    interval_cases d
    · rfl
    · exfalso
      have ht : (turanGraph 10 2).edgeFinset.card = 25 := by rw [card_edgeFinset_turanGraph]; decide
      rw [ht] at hbound; omega
    · exfalso
      have ht : (turanGraph 11 2).edgeFinset.card = 30 := by rw [card_edgeFinset_turanGraph]; decide
      rw [ht] at hbound; omega
    · exfalso
      have ht : (turanGraph 12 2).edgeFinset.card = 36 := by rw [card_edgeFinset_turanGraph]; decide
      rw [ht] at hbound; omega
  obtain ⟨f, hf⟩ := exists_embedding_image_eq (J.neighborFinset x) hcard9
  obtain ⟨hCF, hα', hcnt⟩ := comap_nbhd_package J (by norm_num) hK4 hα x f hf
  refine ⟨J.comap f, f, rfl, hCF, hα', ?_, ?_, ?_⟩
  · rw [hcnt]; rw [hcard9] at hconeE; omega
  · rw [hf]; exact hcone.1
  · rw [hf]; exact hcone.2

/-! ## The (2,9) base — the two extremal iso-classes and the max-degree reduction

The descent ends at a `J' : SimpleGraph (Fin 9)` that is triangle-free (`K₃`-free), `α ≤ 4`,
`e = 17 = p₂(9)`. Enumeration (nauty `geng -t 9 17:17` + α-filter, scratchpad) shows there are
EXACTLY TWO such graphs up to isomorphism — the bases of `kpG` (`|A*| = 2`) and `kpG1` (`|A*| = 1`),
with degree sequences `[3,3,4⁷]` and `[2,4⁸]`. Relabelled onto `Fin 9`:
`N₀ = {0,1,2,3}`, `N₁ = {4,5,6,7}`, apex `8`; `N₀–N₁` complete bipartite minus the `A*–y` edges
(`y = 4`), apex joined to `A* ∪ {y}`. -/

/-- Base witness, `|A*| = 2` (`A* = {0,1}`): apex `8` joined to `{0,1,4}`, `N₀–N₁` minus `{0,4},{1,4}`.
Degree sequence `[3,3,4⁷]` (the base of `kpG`). -/
def base9A2Rel (a b : Fin 9) : Bool :=
  if a = b then false
  else if a.val = 8 then (b.val = 0 || b.val = 1 || b.val = 4)
  else if b.val = 8 then (a.val = 0 || a.val = 1 || a.val = 4)
  else
    (a.val / 4 ≠ b.val / 4) &&
      !((a.val = 4 && (b.val = 0 || b.val = 1)) || (b.val = 4 && (a.val = 0 || a.val = 1)))

/-- Base witness, `|A*| = 1` (`A* = {0}`): apex `8` joined to `{0,4}`, `N₀–N₁` minus `{0,4}`.
Degree sequence `[2,4⁸]` (the base of `kpG1`). -/
def base9A1Rel (a b : Fin 9) : Bool :=
  if a = b then false
  else if a.val = 8 then (b.val = 0 || b.val = 4)
  else if b.val = 8 then (a.val = 0 || a.val = 4)
  else
    (a.val / 4 ≠ b.val / 4) && !((a.val = 4 && b.val = 0) || (b.val = 4 && a.val = 0))

def base9A2 : SimpleGraph (Fin 9) where
  Adj a b := base9A2Rel a b = true
  symm := by
    have h : ∀ a b : Fin 9, base9A2Rel a b = true → base9A2Rel b a = true := by decide
    exact fun a b => h a b
  loopless := by
    have h : ∀ a : Fin 9, ¬ (base9A2Rel a a = true) := by decide
    exact ⟨h⟩

def base9A1 : SimpleGraph (Fin 9) where
  Adj a b := base9A1Rel a b = true
  symm := by
    have h : ∀ a b : Fin 9, base9A1Rel a b = true → base9A1Rel b a = true := by decide
    exact fun a b => h a b
  loopless := by
    have h : ∀ a : Fin 9, ¬ (base9A1Rel a a = true) := by decide
    exact ⟨h⟩

instance base9A2_decRel : DecidableRel base9A2.Adj := fun a b => decEq (base9A2Rel a b) true
instance base9A1_decRel : DecidableRel base9A1.Adj := fun a b => decEq (base9A1Rel a b) true

/-- `e(base9A2) = 17`. Bridged past the noncomputable `edgeCountIn` (Classical filter) to the same
filter with the computable `base9A2_decRel` instance, then `native_decide` (mirrors `kpG_edgeCount`). -/
theorem base9A2_edgeCount : edgeCountIn base9A2 Finset.univ = 17 := by
  have key : ((Finset.univ : Finset (Fin 9)).sym2.filter (fun e => e ∈ base9A2.edgeSet)).card
      = 17 := by native_decide
  unfold edgeCountIn
  convert key using 2
  exact Finset.filter_congr_decidable _ _ _

/-- `e(base9A1) = 17`. -/
theorem base9A1_edgeCount : edgeCountIn base9A1 Finset.univ = 17 := by
  have key : ((Finset.univ : Finset (Fin 9)).sym2.filter (fun e => e ∈ base9A1.edgeSet)).card
      = 17 := by native_decide
  unfold edgeCountIn
  convert key using 2
  exact Finset.filter_congr_decidable _ _ _

theorem base9A2_cliqueFree3 : base9A2.CliqueFree 3 := by
  show ∀ t : Finset (Fin 9), ¬ base9A2.IsNClique 3 t
  native_decide

theorem base9A1_cliqueFree3 : base9A1.CliqueFree 3 := by
  show ∀ t : Finset (Fin 9), ¬ base9A1.IsNClique 3 t
  native_decide

theorem base9A2_alpha : alphaAtMost base9A2 4 := by
  show ∀ S : Finset (Fin 9), (∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ base9A2.Adj u v) → S.card ≤ 4
  native_decide

theorem base9A1_alpha : alphaAtMost base9A1 4 := by
  show ∀ S : Finset (Fin 9), (∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ base9A1.Adj u v) → S.card ≤ 4
  native_decide

/-! ## The max-degree reduction (sorry-free) -/

/-- In a triangle-free graph the neighbourhood of any vertex is independent (an edge inside `N(v)`
would form a triangle with `v`). -/
theorem nbhd_indep_of_cliqueFree3 {n : ℕ} (J : SimpleGraph (Fin n)) (hK3 : J.CliqueFree 3)
    (v : Fin n) :
    ∀ u ∈ J.neighborFinset v, ∀ w ∈ J.neighborFinset v, u ≠ w → ¬ J.Adj u w := by
  intro u hu w hw huw hadj
  rw [SimpleGraph.mem_neighborFinset] at hu hw
  exact hK3 {v, u, w} (by rw [SimpleGraph.is3Clique_iff]; exact ⟨v, u, w, hu, hw, hadj, rfl⟩)

/-- **Base max-degree bound.** A triangle-free graph with `α ≤ 4` has maximum degree `≤ 4`
(`N(v)` is independent, so `deg v = |N(v)| ≤ α ≤ 4`). This is the first structural handle for the
base classification: with `e = 17` (`Σ deg = 34`) it forces the degree sequence to `[2,4⁸]` or
`[3,3,4⁷]`. -/
theorem base_maxdeg_le_four {n : ℕ} (J : SimpleGraph (Fin n)) (hK3 : J.CliqueFree 3)
    (hα : alphaAtMost J 4) (v : Fin n) : J.degree v ≤ 4 := by
  rw [← J.card_neighborFinset_eq_degree]
  exact hα _ (nbhd_indep_of_cliqueFree3 J hK3 v)

/-! ## Sum of degrees and the degree-sequence dichotomy

`e = 17 ⇒ Σ deg = 34`. With `Δ ≤ 4` (`base_maxdeg_le_four`) over 9 vertices this forces the degree
sequence to `[2,4⁸]` (a unique min-degree-2 vertex, rest 4) or `[3,3,4⁷]` (two degree-3, rest 4). -/

/-- `Σ deg = 34` for the extremal base graph. -/
theorem base_sum_degrees (J : SimpleGraph (Fin 9)) (he : edgeCountIn J Finset.univ = 17) :
    ∑ v, J.degree v = 34 := by
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges, ← edgeCountIn_univ_eq_card_edgeFinset, he]

/-! ### The [2,4⁸] case — a unique degree-2 (apex) vertex, all others degree 4

Root at the apex `a` (`deg a = 2`, `N(a) = {p,q}`, `p ≁ q` by triangle-freeness). Every other
vertex `w` (`deg 4`) is adjacent to `p` or `q`: otherwise `N(w) ⊆ V∖{a,p,q}` with `a ≁ N(w)`, so
`{a}∪N(w)` is an independent 5-set, contradicting `α ≤ 4`. Cardinalities then force
`P₃ = N(p)∖{a}`, `Q₃ = N(q)∖{a}` to partition `W = V∖{a,p,q}` (each size 3), and each `P₃`-vertex is
joined to all of `Q₃` (complete bipartite). This is `base9A1` (`K_{4,4}` minus edge `{p,q}`, apex `a`
joined to `{p,q}`). -/

/-- **[2,4⁸] structural determination.** From the apex data, the graph is the concrete `base9A1`
shape: two independent triples `P₃, Q₃` partitioning `W = V∖{a,p,q}`, complete between them, with
`p` joined to `P₃`, `q` to `Q₃`, `a` to `{p,q}` only, and `p ≁ q`. Packaged as the full adjacency
determination the isomorphism consumes. -/
theorem base_deg2_structure (J : SimpleGraph (Fin 9)) (hK3 : J.CliqueFree 3)
    (hα : alphaAtMost J 4) (a p q : Fin 9)
    (hNa : J.neighborFinset a = {p, q}) (hpq_ne : p ≠ q)
    (hdeg4 : ∀ v, v ≠ a → J.degree v = 4) :
    ∃ P3 Q3 : Finset (Fin 9), P3.card = 3 ∧ Q3.card = 3 ∧ Disjoint P3 Q3 ∧
      insert a (insert p (insert q (P3 ∪ Q3))) = Finset.univ ∧
      a ∉ P3 ∧ a ∉ Q3 ∧ p ∉ P3 ∧ p ∉ Q3 ∧ q ∉ P3 ∧ q ∉ Q3 ∧
      J.Adj a p ∧ J.Adj a q ∧ ¬ J.Adj p q ∧
      (∀ r ∈ P3, J.Adj p r) ∧ (∀ s ∈ Q3, J.Adj q s) ∧
      (∀ r ∈ P3, ∀ s ∈ Q3, J.Adj r s) ∧
      (∀ r ∈ P3, ¬ J.Adj a r) ∧ (∀ s ∈ Q3, ¬ J.Adj a s) ∧
      (∀ r ∈ P3, ¬ J.Adj q r) ∧ (∀ s ∈ Q3, ¬ J.Adj p s) ∧
      (∀ r ∈ P3, ∀ r' ∈ P3, r ≠ r' → ¬ J.Adj r r') ∧
      (∀ s ∈ Q3, ∀ s' ∈ Q3, s ≠ s' → ¬ J.Adj s s') := by
  -- neighbour-membership shorthand
  have memN : ∀ v w : Fin 9, w ∈ J.neighborFinset v ↔ J.Adj v w := fun v w => J.mem_neighborFinset v w
  -- basic apex facts
  have hap : J.Adj a p := by rw [← SimpleGraph.mem_neighborFinset, hNa]; exact Finset.mem_insert_self _ _
  have haq : J.Adj a q := by
    rw [← SimpleGraph.mem_neighborFinset, hNa]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hane_p : a ≠ p := J.ne_of_adj hap
  have hane_q : a ≠ q := J.ne_of_adj haq
  have hpq : ¬ J.Adj p q := by
    intro hpqadj
    exact hK3 {a, p, q} (by rw [SimpleGraph.is3Clique_iff]; exact ⟨a, p, q, hap, haq, hpqadj, rfl⟩)
  -- nbhds independent
  have hindep : ∀ v : Fin 9, ∀ u ∈ J.neighborFinset v, ∀ w ∈ J.neighborFinset v, u ≠ w → ¬ J.Adj u w :=
    fun v => nbhd_indep_of_cliqueFree3 J hK3 v
  -- degree of p, q
  have hdp : J.degree p = 4 := hdeg4 p (Ne.symm hane_p)
  have hdq : J.degree q = 4 := hdeg4 q (Ne.symm hane_q)
  -- a is a neighbour of p and of q
  have haNp : a ∈ J.neighborFinset p := (memN _ _).mpr hap.symm
  have haNq : a ∈ J.neighborFinset q := (memN _ _).mpr haq.symm
  -- define the two triples
  set P3 := J.neighborFinset p \ {a} with hP3def
  set Q3 := J.neighborFinset q \ {a} with hQ3def
  have hP3card : P3.card = 3 := by
    rw [hP3def, ← Finset.erase_eq, Finset.card_erase_of_mem haNp,
      J.card_neighborFinset_eq_degree, hdp]
  have hQ3card : Q3.card = 3 := by
    rw [hQ3def, ← Finset.erase_eq, Finset.card_erase_of_mem haNq,
      J.card_neighborFinset_eq_degree, hdq]
  -- membership characterisations
  have hmemP3 : ∀ r, r ∈ P3 ↔ J.Adj p r ∧ r ≠ a := by
    intro r; rw [hP3def, Finset.mem_sdiff, SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
  have hmemQ3 : ∀ s, s ∈ Q3 ↔ J.Adj q s ∧ s ≠ a := by
    intro s; rw [hQ3def, Finset.mem_sdiff, SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
  -- r ∈ P3 ⇒ r ∉ {a,p,q}
  have hP3ne : ∀ r ∈ P3, r ≠ a ∧ r ≠ p ∧ r ≠ q := by
    intro r hr
    rw [hmemP3] at hr
    refine ⟨hr.2, ?_, ?_⟩
    · exact fun h => J.ne_of_adj hr.1 h.symm
    · exact fun h => hpq (h ▸ hr.1)
  have hQ3ne : ∀ s ∈ Q3, s ≠ a ∧ s ≠ p ∧ s ≠ q := by
    intro s hs
    rw [hmemQ3] at hs
    refine ⟨hs.2, ?_, ?_⟩
    · exact fun h => hpq (h ▸ hs.1).symm
    · exact fun h => J.ne_of_adj hs.1 h.symm
  -- basic non-memberships
  have haP3 : a ∉ P3 := fun h => ((hP3ne a h).1) rfl
  have haQ3 : a ∉ Q3 := fun h => ((hQ3ne a h).1) rfl
  have hpP3 : p ∉ P3 := fun h => ((hP3ne p h).2.1) rfl
  have hpQ3 : p ∉ Q3 := fun h => ((hQ3ne p h).2.1) rfl
  have hqP3 : q ∉ P3 := fun h => ((hP3ne q h).2.2) rfl
  have hqQ3 : q ∉ Q3 := fun h => ((hQ3ne q h).2.2) rfl
  -- STEP 6: every W-vertex is adjacent to p or q
  have hstep6 : ∀ w : Fin 9, w ≠ a → w ≠ p → w ≠ q → (J.Adj w p ∨ J.Adj w q) := by
    intro w hwa hwp hwq
    by_contra hcon
    push_neg at hcon
    obtain ⟨hwnp, hwnq⟩ := hcon
    -- a ∉ N(w)
    have hwna : ¬ J.Adj a w := by
      intro h
      have hmem : w ∈ J.neighborFinset a := (memN _ _).mpr h
      rw [hNa, Finset.mem_insert, Finset.mem_singleton] at hmem
      exact hmem.elim hwp hwq
    have haNw : a ∉ J.neighborFinset w := fun h =>
      hwna ((memN _ _).mp h).symm
    -- {a} ∪ N(w) is independent of size 5
    have hindepSet : IsIndep J (insert a (J.neighborFinset w)) := by
      intro u hu v hv huv
      rw [Finset.mem_insert] at hu hv
      rcases hu with hua | hu
      · rcases hv with hva | hv
        · exact absurd (hua.trans hva.symm) huv
        · -- u = a, v ∈ N(w): show ¬ J.Adj a v ; v ∉ {p,q}
          rw [hua]; intro hadj
          have hvmem : v ∈ J.neighborFinset a := (memN _ _).mpr hadj
          rw [hNa, Finset.mem_insert, Finset.mem_singleton] at hvmem
          have hwv : J.Adj w v := (memN _ _).mp hv
          rcases hvmem with hvp | hvq
          · exact hwnp (hvp ▸ hwv)
          · exact hwnq (hvq ▸ hwv)
      · rcases hv with hva | hv
        · -- v = a, u ∈ N(w)
          rw [hva]; intro hadj
          have humem : u ∈ J.neighborFinset a := (memN _ _).mpr hadj.symm
          rw [hNa, Finset.mem_insert, Finset.mem_singleton] at humem
          have hwu : J.Adj w u := (memN _ _).mp hu
          rcases humem with hup | huq
          · exact hwnp (hup ▸ hwu)
          · exact hwnq (huq ▸ hwu)
        · exact hindep w u hu v hv huv
    have hcard5 : (insert a (J.neighborFinset w)).card = 5 := by
      rw [Finset.card_insert_of_notMem haNw, J.card_neighborFinset_eq_degree, hdeg4 w hwa]
    have := hα _ hindepSet
    omega
  -- STEP 7: {a,p,q} ∪ P3 ∪ Q3 = univ
  have hcover : insert a (insert p (insert q (P3 ∪ Q3))) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    by_cases hva : v = a
    · exact hva ▸ Finset.mem_insert_self _ _
    by_cases hvp : v = p
    · exact hvp ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    by_cases hvq : v = q
    · exact hvq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    · have := hstep6 v hva hvp hvq
      refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_))
      rw [Finset.mem_union]
      rcases this with h | h
      · left; rw [hmemP3]; exact ⟨h.symm, hva⟩
      · right; rw [hmemQ3]; exact ⟨h.symm, hva⟩
  -- STEP 8: disjointness (via cardinalities)
  have hapqne : a ≠ p ∧ a ≠ q ∧ p ≠ q := ⟨hane_p, hane_q, hpq_ne⟩
  have hunioncard : (P3 ∪ Q3).card = 6 := by
    have h9 : (Finset.univ : Finset (Fin 9)).card = 9 := by decide
    have hqnotin : q ∉ (P3 ∪ Q3) := by rw [Finset.mem_union]; exact fun h => h.elim hqP3 hqQ3
    have hpnotin : p ∉ insert q (P3 ∪ Q3) := by
      rw [Finset.mem_insert]; push_neg
      exact ⟨hpq_ne, by rw [Finset.mem_union]; exact fun h => h.elim hpP3 hpQ3⟩
    have hanotin : a ∉ insert p (insert q (P3 ∪ Q3)) := by
      rw [Finset.mem_insert, Finset.mem_insert]; push_neg
      exact ⟨hane_p, hane_q, by rw [Finset.mem_union]; exact fun h => h.elim haP3 haQ3⟩
    have := hcover
    rw [← this, Finset.card_insert_of_notMem hanotin, Finset.card_insert_of_notMem hpnotin,
      Finset.card_insert_of_notMem hqnotin] at h9
    omega
  have hdisj : Disjoint P3 Q3 := by
    rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.card_eq_zero]
    have := Finset.card_union_add_card_inter P3 Q3
    rw [hunioncard, hP3card, hQ3card] at this
    omega
  -- adjacency facts derivable from the definitions
  have hpP3adj : ∀ r ∈ P3, J.Adj p r := fun r hr => ((hmemP3 r).mp hr).1
  have hqQ3adj : ∀ s ∈ Q3, J.Adj q s := fun s hs => ((hmemQ3 s).mp hs).1
  have hindepP3 : ∀ r ∈ P3, ∀ r' ∈ P3, r ≠ r' → ¬ J.Adj r r' := by
    intro r hr r' hr' hne
    exact hindep p r ((memN _ _).mpr ((hmemP3 r).mp hr).1)
      r' ((memN _ _).mpr ((hmemP3 r').mp hr').1) hne
  have hindepQ3 : ∀ s ∈ Q3, ∀ s' ∈ Q3, s ≠ s' → ¬ J.Adj s s' := by
    intro s hs s' hs' hne
    exact hindep q s ((memN _ _).mpr ((hmemQ3 s).mp hs).1)
      s' ((memN _ _).mpr ((hmemQ3 s').mp hs').1) hne
  -- non-adjacencies to a
  have hanaP3 : ∀ r ∈ P3, ¬ J.Adj a r := by
    intro r hr hadj
    have hmem : r ∈ J.neighborFinset a := (memN _ _).mpr hadj
    rw [hNa, Finset.mem_insert, Finset.mem_singleton] at hmem
    exact hmem.elim (fun h => ((hP3ne r hr).2.1) h) (fun h => ((hP3ne r hr).2.2) h)
  have hanaQ3 : ∀ s ∈ Q3, ¬ J.Adj a s := by
    intro s hs hadj
    have hmem : s ∈ J.neighborFinset a := (memN _ _).mpr hadj
    rw [hNa, Finset.mem_insert, Finset.mem_singleton] at hmem
    exact hmem.elim (fun h => ((hQ3ne s hs).2.1) h) (fun h => ((hQ3ne s hs).2.2) h)
  -- p ≁ Q3, q ≁ P3
  have hpnaQ3 : ∀ s ∈ Q3, ¬ J.Adj p s := by
    intro s hs hadj
    have hsP3 : s ∈ P3 := (hmemP3 s).mpr ⟨hadj, (hQ3ne s hs).1⟩
    exact (Finset.disjoint_left.mp hdisj hsP3) hs
  have hqnaP3 : ∀ r ∈ P3, ¬ J.Adj q r := by
    intro r hr hadj
    have hrQ3 : r ∈ Q3 := (hmemQ3 r).mpr ⟨hadj, (hP3ne r hr).1⟩
    exact (Finset.disjoint_left.mp hdisj hr) hrQ3
  -- STEP 9: complete bipartite P3–Q3
  have hbip : ∀ r ∈ P3, ∀ s ∈ Q3, J.Adj r s := by
    intro x hxP y hyQ
    have hxp : J.Adj p x := ((hmemP3 x).mp hxP).1
    have hxa : x ≠ a := (hP3ne x hxP).1
    have hxq_ne : x ≠ q := (hP3ne x hxP).2.2
    have hxp_ne : x ≠ p := (hP3ne x hxP).2.1
    -- x ≁ q (x ∉ Q3)
    have hxnq : ¬ J.Adj x q := by
      intro hadj
      exact (Finset.disjoint_left.mp hdisj hxP) ((hmemQ3 x).mpr ⟨hadj.symm, hxa⟩)
    -- x ≁ a
    have hxna : ¬ J.Adj x a := fun hadj => hanaP3 x hxP hadj.symm
    -- p ∈ N(x)
    have hpNx : p ∈ J.neighborFinset x := (memN _ _).mpr hxp.symm
    -- N(x) \ {p} ⊆ Q3
    have hsub : J.neighborFinset x \ {p} ⊆ Q3 := by
      intro z hz
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hz
      obtain ⟨hzN, hzp⟩ := hz
      have hxz : J.Adj x z := (memN _ _).mp hzN
      -- z ≠ a
      have hza : z ≠ a := fun h => hxna (h ▸ hxz)
      -- z ≠ q
      have hzq : z ≠ q := fun h => hxnq (h ▸ hxz)
      -- z ≠ x
      have hzx : z ≠ x := fun h => J.ne_of_adj hxz h.symm
      -- z ∉ P3: z ≁ p (independence of N(x) with p)
      have hznp : ¬ J.Adj p z := by
        intro hadj
        exact hindep x p hpNx z hzN (Ne.symm hzp) hadj
      have hzP3 : z ∉ P3 := fun h => hznp ((hmemP3 z).mp h).1
      -- z ∈ W ⇒ z ∈ P3 ∪ Q3 ⇒ z ∈ Q3
      have hzcover : z ∈ insert a (insert p (insert q (P3 ∪ Q3))) := by
        rw [hcover]; exact Finset.mem_univ z
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_union] at hzcover
      rcases hzcover with h | h | h | h | h
      · exact absurd h hza
      · exact absurd h hzp
      · exact absurd h hzq
      · exact absurd h hzP3
      · exact h
    have hcardNx : (J.neighborFinset x \ {p}).card = 3 := by
      rw [← Finset.erase_eq, Finset.card_erase_of_mem hpNx,
        J.card_neighborFinset_eq_degree, hdeg4 x hxa]
    have heq : J.neighborFinset x \ {p} = Q3 :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hQ3card, hcardNx])
    have hyNx : y ∈ J.neighborFinset x := by
      have hh : y ∈ J.neighborFinset x \ {p} := by rw [heq]; exact hyQ
      exact (Finset.mem_sdiff.mp hh).1
    exact (memN _ _).mp hyNx
  -- assemble
  exact ⟨P3, Q3, hP3card, hQ3card, hdisj, hcover, haP3, haQ3, hpP3, hpQ3, hqP3, hqQ3,
    hap, haq, hpq, hpP3adj, hqQ3adj, hbip, hanaP3, hanaQ3, hqnaP3, hpnaQ3, hindepP3, hindepQ3⟩

/-- **[2,4⁸] isomorphism.** The pinned structure is isomorphic to `base9A1` via
`a↦8, p↦0, q↦4, Q₃↦{1,2,3}, P₃↦{5,6,7}`. -/
theorem base_classification_deg2 (J : SimpleGraph (Fin 9)) (hK3 : J.CliqueFree 3)
    (hα : alphaAtMost J 4) (a p q : Fin 9)
    (hNa : J.neighborFinset a = {p, q}) (hpq_ne : p ≠ q)
    (hdeg4 : ∀ v, v ≠ a → J.degree v = 4) :
    ∃ σ : Fin 9 ≃ Fin 9, ∀ u v, J.Adj u v ↔ base9A1.Adj (σ u) (σ v) := by
  obtain ⟨P3, Q3, hP3card, hQ3card, hdisj, hcover, haP3, haQ3, hpP3, hpQ3, hqP3, hqQ3,
    hap, haq, hpq, hpP3adj, hqQ3adj, hbip, hanaP3, hanaQ3, hqnaP3, hpnaQ3, hindepP3, hindepQ3⟩ :=
    base_deg2_structure J hK3 hα a p q hNa hpq_ne hdeg4
  obtain ⟨r1, r2, r3, hr12, hr13, hr23, hP3eq⟩ := Finset.card_eq_three.mp hP3card
  obtain ⟨s1, s2, s3, hs12, hs13, hs23, hQ3eq⟩ := Finset.card_eq_three.mp hQ3card
  -- memberships
  have hr1 : r1 ∈ P3 := by rw [hP3eq]; simp
  have hr2 : r2 ∈ P3 := by rw [hP3eq]; simp
  have hr3 : r3 ∈ P3 := by rw [hP3eq]; simp
  have hsm1 : s1 ∈ Q3 := by rw [hQ3eq]; simp
  have hsm2 : s2 ∈ Q3 := by rw [hQ3eq]; simp
  have hsm3 : s3 ∈ Q3 := by rw [hQ3eq]; simp
  -- distinctness across roles
  have hrs : ∀ r ∈ P3, ∀ s ∈ Q3, r ≠ s := fun r hr s hs h => (Finset.disjoint_left.mp hdisj hr) (h ▸ hs)
  have hpr : ∀ r ∈ P3, p ≠ r := fun r hr h => hpP3 (h ▸ hr)
  have hqr : ∀ r ∈ P3, q ≠ r := fun r hr h => hqP3 (h ▸ hr)
  have har : ∀ r ∈ P3, a ≠ r := fun r hr h => haP3 (h ▸ hr)
  have hps : ∀ s ∈ Q3, p ≠ s := fun s hs h => hpQ3 (h ▸ hs)
  have hqs : ∀ s ∈ Q3, q ≠ s := fun s hs h => hqQ3 (h ▸ hs)
  have has : ∀ s ∈ Q3, a ≠ s := fun s hs h => haQ3 (h ▸ hs)
  have hapne : a ≠ p := J.ne_of_adj hap
  have haqne : a ≠ q := J.ne_of_adj haq
  -- the inverse map ψ : position ↦ vertex
  set f : Fin 9 → Fin 9 := fun i =>
    if i = 0 then p else if i = 1 then s1 else if i = 2 then s2 else if i = 3 then s3
    else if i = 4 then q else if i = 5 then r1 else if i = 6 then r2 else if i = 7 then r3 else a
    with hf
  have hinj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [hf, Fin.isValue, Fin.reduceEq, reduceIte, reduceCtorEq] at hij ⊢ <;>
      first
        | rfl
        | exact absurd hij hpq_ne | exact absurd hij hpq_ne.symm
        | exact absurd hij hapne | exact absurd hij hapne.symm
        | exact absurd hij haqne | exact absurd hij haqne.symm
        | exact absurd hij (hpr r1 hr1) | exact absurd hij (hpr r2 hr2) | exact absurd hij (hpr r3 hr3)
        | exact absurd hij (hpr r1 hr1).symm | exact absurd hij (hpr r2 hr2).symm | exact absurd hij (hpr r3 hr3).symm
        | exact absurd hij (hqr r1 hr1) | exact absurd hij (hqr r2 hr2) | exact absurd hij (hqr r3 hr3)
        | exact absurd hij (hqr r1 hr1).symm | exact absurd hij (hqr r2 hr2).symm | exact absurd hij (hqr r3 hr3).symm
        | exact absurd hij (har r1 hr1) | exact absurd hij (har r2 hr2) | exact absurd hij (har r3 hr3)
        | exact absurd hij (har r1 hr1).symm | exact absurd hij (har r2 hr2).symm | exact absurd hij (har r3 hr3).symm
        | exact absurd hij (hps s1 hsm1) | exact absurd hij (hps s2 hsm2) | exact absurd hij (hps s3 hsm3)
        | exact absurd hij (hps s1 hsm1).symm | exact absurd hij (hps s2 hsm2).symm | exact absurd hij (hps s3 hsm3).symm
        | exact absurd hij (hqs s1 hsm1) | exact absurd hij (hqs s2 hsm2) | exact absurd hij (hqs s3 hsm3)
        | exact absurd hij (hqs s1 hsm1).symm | exact absurd hij (hqs s2 hsm2).symm | exact absurd hij (hqs s3 hsm3).symm
        | exact absurd hij (has s1 hsm1) | exact absurd hij (has s2 hsm2) | exact absurd hij (has s3 hsm3)
        | exact absurd hij (has s1 hsm1).symm | exact absurd hij (has s2 hsm2).symm | exact absurd hij (has s3 hsm3).symm
        | exact absurd hij hr12 | exact absurd hij hr13 | exact absurd hij hr23
        | exact absurd hij hr12.symm | exact absurd hij hr13.symm | exact absurd hij hr23.symm
        | exact absurd hij hs12 | exact absurd hij hs13 | exact absurd hij hs23
        | exact absurd hij hs12.symm | exact absurd hij hs13.symm | exact absurd hij hs23.symm
        | exact absurd hij (hrs r1 hr1 s1 hsm1) | exact absurd hij (hrs r1 hr1 s2 hsm2) | exact absurd hij (hrs r1 hr1 s3 hsm3)
        | exact absurd hij (hrs r2 hr2 s1 hsm1) | exact absurd hij (hrs r2 hr2 s2 hsm2) | exact absurd hij (hrs r2 hr2 s3 hsm3)
        | exact absurd hij (hrs r3 hr3 s1 hsm1) | exact absurd hij (hrs r3 hr3 s2 hsm2) | exact absurd hij (hrs r3 hr3 s3 hsm3)
        | exact absurd hij (hrs r1 hr1 s1 hsm1).symm | exact absurd hij (hrs r1 hr1 s2 hsm2).symm | exact absurd hij (hrs r1 hr1 s3 hsm3).symm
        | exact absurd hij (hrs r2 hr2 s1 hsm1).symm | exact absurd hij (hrs r2 hr2 s2 hsm2).symm | exact absurd hij (hrs r2 hr2 s3 hsm3).symm
        | exact absurd hij (hrs r3 hr3 s1 hsm1).symm | exact absurd hij (hrs r3 hr3 s2 hsm2).symm | exact absurd hij (hrs r3 hr3 s3 hsm3).symm
  let e := Equiv.ofBijective f ((Finite.injective_iff_bijective).mp hinj)
  have hfe : ∀ i, e i = f i := fun i => rfl
  -- adjacency correspondence
  have hψ : ∀ i j : Fin 9, J.Adj (f i) (f j) ↔ base9A1.Adj i j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [hf, Fin.isValue, if_true, if_false, reduceIte, reduceCtorEq] <;>
      first
        | (refine iff_of_true ?_ (by decide); first
            | exact hap | exact haq | exact hap.symm | exact haq.symm
            | exact hpP3adj r1 hr1 | exact hpP3adj r2 hr2 | exact hpP3adj r3 hr3
            | exact (hpP3adj r1 hr1).symm | exact (hpP3adj r2 hr2).symm | exact (hpP3adj r3 hr3).symm
            | exact hqQ3adj s1 hsm1 | exact hqQ3adj s2 hsm2 | exact hqQ3adj s3 hsm3
            | exact (hqQ3adj s1 hsm1).symm | exact (hqQ3adj s2 hsm2).symm | exact (hqQ3adj s3 hsm3).symm
            | exact hbip r1 hr1 s1 hsm1 | exact hbip r1 hr1 s2 hsm2 | exact hbip r1 hr1 s3 hsm3
            | exact hbip r2 hr2 s1 hsm1 | exact hbip r2 hr2 s2 hsm2 | exact hbip r2 hr2 s3 hsm3
            | exact hbip r3 hr3 s1 hsm1 | exact hbip r3 hr3 s2 hsm2 | exact hbip r3 hr3 s3 hsm3
            | exact (hbip r1 hr1 s1 hsm1).symm | exact (hbip r1 hr1 s2 hsm2).symm | exact (hbip r1 hr1 s3 hsm3).symm
            | exact (hbip r2 hr2 s1 hsm1).symm | exact (hbip r2 hr2 s2 hsm2).symm | exact (hbip r2 hr2 s3 hsm3).symm
            | exact (hbip r3 hr3 s1 hsm1).symm | exact (hbip r3 hr3 s2 hsm2).symm | exact (hbip r3 hr3 s3 hsm3).symm)
        | (refine iff_of_false ?_ (by decide); first
            | exact fun h => (J.ne_of_adj h) rfl
            | exact hpq | exact fun h => hpq h.symm
            | exact hanaP3 r1 hr1 | exact hanaP3 r2 hr2 | exact hanaP3 r3 hr3
            | exact fun h => hanaP3 r1 hr1 h.symm | exact fun h => hanaP3 r2 hr2 h.symm | exact fun h => hanaP3 r3 hr3 h.symm
            | exact hanaQ3 s1 hsm1 | exact hanaQ3 s2 hsm2 | exact hanaQ3 s3 hsm3
            | exact fun h => hanaQ3 s1 hsm1 h.symm | exact fun h => hanaQ3 s2 hsm2 h.symm | exact fun h => hanaQ3 s3 hsm3 h.symm
            | exact hqnaP3 r1 hr1 | exact hqnaP3 r2 hr2 | exact hqnaP3 r3 hr3
            | exact fun h => hqnaP3 r1 hr1 h.symm | exact fun h => hqnaP3 r2 hr2 h.symm | exact fun h => hqnaP3 r3 hr3 h.symm
            | exact hpnaQ3 s1 hsm1 | exact hpnaQ3 s2 hsm2 | exact hpnaQ3 s3 hsm3
            | exact fun h => hpnaQ3 s1 hsm1 h.symm | exact fun h => hpnaQ3 s2 hsm2 h.symm | exact fun h => hpnaQ3 s3 hsm3 h.symm
            | exact hindepP3 r1 hr1 r2 hr2 hr12 | exact hindepP3 r1 hr1 r3 hr3 hr13 | exact hindepP3 r2 hr2 r3 hr3 hr23
            | exact hindepP3 r2 hr2 r1 hr1 hr12.symm | exact hindepP3 r3 hr3 r1 hr1 hr13.symm | exact hindepP3 r3 hr3 r2 hr2 hr23.symm
            | exact hindepQ3 s1 hsm1 s2 hsm2 hs12 | exact hindepQ3 s1 hsm1 s3 hsm3 hs13 | exact hindepQ3 s2 hsm2 s3 hsm3 hs23
            | exact hindepQ3 s2 hsm2 s1 hsm1 hs12.symm | exact hindepQ3 s3 hsm3 s1 hsm1 hs13.symm | exact hindepQ3 s3 hsm3 s2 hsm2 hs23.symm)
  refine ⟨e.symm, fun u v => ?_⟩
  have hu : f (e.symm u) = u := e.apply_symm_apply u
  have hv : f (e.symm v) = v := e.apply_symm_apply v
  have h := hψ (e.symm u) (e.symm v)
  rw [hu, hv] at h
  exact h

/-! ## The base classification (target statement)

Any triangle-free `α ≤ 4` `e = 17` graph on `Fin 9` is isomorphic to `base9A2` or `base9A1`.
`base_maxdeg_le_four` + `base_sum_degrees` reduce the degree sequence to `[2,4⁸]`/`[3,3,4⁷]`; the
[2,4⁸] shape is pinned by `base_deg2_structure` (the [3,3,4⁷] shape by `base_deg3_structure`). The
remaining work is the isomorphism assembly (mapping the pinned structure onto the concrete
`base9A1`/`base9A2` labelling). -/

/-! ### The `[3,3,4⁷]` case — the two degree-3 vertices are adjacent

The crux of the deg-3 base case. Suppose `s ≁ t`. `Rest` (the common non-neighbours of `s,t`) is
independent (two adjacent degree-4 `Rest` vertices would force 6 distinct vertices into the
5-vertex set `(V∖{s,t})∖{r₁,r₂}`), so `Rest ∪ {s,t}` is independent of size `3+k` (`k=|N(s)∩N(t)|`),
forcing `k ≤ 1` by `α ≤ 4`. Both `k∈{0,1}` then contradict via degree counting (verified,
`scratchpad/base_deg3_kcheck.py`). -/

/-- The common non-neighbours of `s` and `t` form an independent set (each is degree-4 with
neighbourhood in `V∖{s,t}`; two adjacent ones over-fill the 5-vertex remainder). -/
theorem base_deg3_rest_indep (J : SimpleGraph (Fin 9)) (hK3 : J.CliqueFree 3)
    (s t : Fin 9) (hst : s ≠ t) (hother : ∀ v, v ≠ s → v ≠ t → J.degree v = 4)
    (r1 r2 : Fin 9) (hr1s : r1 ≠ s) (hr1t : r1 ≠ t) (hr2s : r2 ≠ s) (hr2t : r2 ≠ t)
    (hr1ns : ¬ J.Adj r1 s) (hr1nt : ¬ J.Adj r1 t) (hr2ns : ¬ J.Adj r2 s) (hr2nt : ¬ J.Adj r2 t)
    (hne : r1 ≠ r2) : ¬ J.Adj r1 r2 := by
  intro hadj
  have memN : ∀ v w : Fin 9, w ∈ J.neighborFinset v ↔ J.Adj v w := fun v w => J.mem_neighborFinset v w
  have hd1 : J.degree r1 = 4 := hother r1 hr1s hr1t
  have hd2 : J.degree r2 = 4 := hother r2 hr2s hr2t
  have hr2N1 : r2 ∈ J.neighborFinset r1 := (memN _ _).mpr hadj
  have hr1N2 : r1 ∈ J.neighborFinset r2 := (memN _ _).mpr hadj.symm
  set U1 := J.neighborFinset r1 \ {r2} with hU1
  set U2 := J.neighborFinset r2 \ {r1} with hU2
  have hcard1 : U1.card = 3 := by
    rw [hU1, ← Finset.erase_eq, Finset.card_erase_of_mem hr2N1, J.card_neighborFinset_eq_degree, hd1]
  have hcard2 : U2.card = 3 := by
    rw [hU2, ← Finset.erase_eq, Finset.card_erase_of_mem hr1N2, J.card_neighborFinset_eq_degree, hd2]
  have hdisj : Disjoint U1 U2 := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    rw [hU1, Finset.mem_sdiff, memN] at hw1
    rw [hU2, Finset.mem_sdiff, memN] at hw2
    exact hK3 {r1, r2, w} (by
      rw [SimpleGraph.is3Clique_iff]; exact ⟨r1, r2, w, hadj, hw1.1, hw2.1, rfl⟩)
  -- every element of U1 (and U2) avoids {s,t,r1,r2}
  have hU1avoid : ∀ w ∈ U1, w ≠ s ∧ w ≠ t ∧ w ≠ r1 ∧ w ≠ r2 := by
    intro w hw; rw [hU1, Finset.mem_sdiff, memN, Finset.mem_singleton] at hw
    exact ⟨fun h => hr1ns (h ▸ hw.1), fun h => hr1nt (h ▸ hw.1),
      fun h => J.ne_of_adj hw.1 h.symm, hw.2⟩
  have hU2avoid : ∀ w ∈ U2, w ≠ s ∧ w ≠ t ∧ w ≠ r1 ∧ w ≠ r2 := by
    intro w hw; rw [hU2, Finset.mem_sdiff, memN, Finset.mem_singleton] at hw
    exact ⟨fun h => hr2ns (h ▸ hw.1), fun h => hr2nt (h ▸ hw.1),
      hw.2, fun h => J.ne_of_adj hw.1 h.symm⟩
  have hsub : U1 ∪ U2 ⊆ Finset.univ \ {s, t, r1, r2} := by
    intro w hw
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [Finset.mem_union] at hw
    have hav : w ≠ s ∧ w ≠ t ∧ w ≠ r1 ∧ w ≠ r2 := hw.elim (hU1avoid w) (hU2avoid w)
    rintro (rfl | rfl | rfl | rfl)
    exacts [hav.1 rfl, hav.2.1 rfl, hav.2.2.1 rfl, hav.2.2.2 rfl]
  have hcardU : (U1 ∪ U2).card = 6 := by
    rw [Finset.card_union_of_disjoint hdisj, hcard1, hcard2]
  have hcard4 : ({s, t, r1, r2} : Finset (Fin 9)).card = 4 := by
    have e1 : r1 ∉ ({r2} : Finset (Fin 9)) := by simp [hne]
    have e2 : t ∉ ({r1, r2} : Finset (Fin 9)) := by simp [Ne.symm hr1t, Ne.symm hr2t]
    have e3 : s ∉ ({t, r1, r2} : Finset (Fin 9)) := by simp [hst, Ne.symm hr1s, Ne.symm hr2s]
    rw [Finset.card_insert_of_notMem e3, Finset.card_insert_of_notMem e2,
      Finset.card_insert_of_notMem e1, Finset.card_singleton]
  have hcardV : (Finset.univ \ ({s, t, r1, r2} : Finset (Fin 9))).card = 5 := by
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin, hcard4]
  have := Finset.card_le_card hsub
  omega

/-- **The two degree-3 vertices are adjacent.** For a triangle-free `α ≤ 4` graph on `Fin 9` with
exactly two degree-3 vertices `s, t` (rest degree 4), `s ~ t`. Proof: if not, the common
non-neighbours `Rest` are independent (`base_deg3_rest_indep`), so `Rest ∪ {s,t}` is independent of
size `3 + k` (`k = |N(s)∩N(t)|`), forcing `k ≤ 1`; `k∈{0,1}` then contradict via degree counting. -/
theorem base_deg3_st_adjacent (J : SimpleGraph (Fin 9)) (hK3 : J.CliqueFree 3)
    (hα : alphaAtMost J 4) (s t : Fin 9) (hst : s ≠ t)
    (hs3 : J.degree s = 3) (ht3 : J.degree t = 3)
    (hother : ∀ v, v ≠ s → v ≠ t → J.degree v = 4) :
    J.Adj s t := by
  by_contra hnst
  have memN : ∀ v w : Fin 9, w ∈ J.neighborFinset v ↔ J.Adj v w := fun v w => J.mem_neighborFinset v w
  set A := J.neighborFinset s with hAdef
  set B := J.neighborFinset t with hBdef
  have hAcard : A.card = 3 := by rw [hAdef, J.card_neighborFinset_eq_degree, hs3]
  have hBcard : B.card = 3 := by rw [hBdef, J.card_neighborFinset_eq_degree, ht3]
  -- s,t ∉ A ∪ B
  have hsA : s ∉ A := by rw [hAdef, memN]; exact fun h => J.ne_of_adj h rfl
  have hsB : s ∉ B := by rw [hBdef, memN]; exact fun h => hnst h.symm
  have htA : t ∉ A := by rw [hAdef, memN]; exact hnst
  have htB : t ∉ B := by rw [hBdef, memN]; exact fun h => J.ne_of_adj h rfl
  set Rest := Finset.univ \ insert s (insert t (A ∪ B)) with hRestdef
  -- membership facts for Rest vertices
  have hRest : ∀ v ∈ Rest, v ≠ s ∧ v ≠ t ∧ ¬ J.Adj v s ∧ ¬ J.Adj v t := by
    intro v hv
    rw [hRestdef, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_insert, Finset.mem_union] at hv
    obtain ⟨_, hv2⟩ := hv
    push_neg at hv2
    refine ⟨hv2.1, hv2.2.1, ?_, ?_⟩
    · intro h; exact hv2.2.2.1 (by rw [hAdef, memN]; exact h.symm)
    · intro h; exact hv2.2.2.2 (by rw [hBdef, memN]; exact h.symm)
  -- Rest is independent
  have hRestIndep : ∀ r1 ∈ Rest, ∀ r2 ∈ Rest, r1 ≠ r2 → ¬ J.Adj r1 r2 := by
    intro r1 hr1 r2 hr2 hne
    obtain ⟨h1s, h1t, h1ns, h1nt⟩ := hRest r1 hr1
    obtain ⟨h2s, h2t, h2ns, h2nt⟩ := hRest r2 hr2
    exact base_deg3_rest_indep J hK3 s t hst hother r1 r2 h1s h1t h2s h2t h1ns h1nt h2ns h2nt hne
  -- s, t ∉ Rest
  have hsRest : s ∉ Rest := by rw [hRestdef, Finset.mem_sdiff]; push_neg; intro _; simp
  have htRest : t ∉ Rest := by
    rw [hRestdef, Finset.mem_sdiff]; push_neg; intro _
    simp [Finset.mem_insert]
  -- insert s (insert t Rest) is independent
  have hindepST : IsIndep J (insert s (insert t Rest)) := by
    intro u hu v hv huv
    simp only [Finset.mem_insert] at hu hv
    rcases hu with hus | hut | huR
    · rcases hv with hvs | hvt | hvR
      · exact absurd (hus.trans hvs.symm) huv
      · rw [hus, hvt]; exact hnst
      · rw [hus]; exact fun h => (hRest v hvR).2.2.1 h.symm
    · rcases hv with hvs | hvt | hvR
      · rw [hut, hvs]; exact fun h => hnst h.symm
      · exact absurd (hut.trans hvt.symm) huv
      · rw [hut]; exact fun h => (hRest v hvR).2.2.2 h.symm
    · rcases hv with hvs | hvt | hvR
      · rw [hvs]; exact (hRest u huR).2.2.1
      · rw [hvt]; exact (hRest u huR).2.2.2
      · exact hRestIndep u huR v hvR huv
  -- cardinalities
  have hcardIns : (insert s (insert t Rest)).card = Rest.card + 2 := by
    rw [Finset.card_insert_of_notMem (by simp [Finset.mem_insert, hst, hsRest]),
      Finset.card_insert_of_notMem htRest]
  have hle4 : Rest.card + 2 ≤ 4 := by rw [← hcardIns]; exact hα _ hindepST
  -- Rest.card = 1 + k
  set k := (A ∩ B).card with hkdef
  have hk3 : k ≤ 3 := by
    rw [hkdef]
    calc (A ∩ B).card ≤ A.card := Finset.card_le_card Finset.inter_subset_left
      _ = 3 := hAcard
  have hcardUnion : (A ∪ B).card = 6 - k := by
    have := Finset.card_union_add_card_inter A B
    rw [hAcard, hBcard, ← hkdef] at this; omega
  have hcardIns2 : (insert s (insert t (A ∪ B))).card = 8 - k := by
    have hstU : s ∉ insert t (A ∪ B) := by
      simp only [Finset.mem_insert, Finset.mem_union]; push_neg
      exact ⟨hst, hsA, hsB⟩
    have htU : t ∉ (A ∪ B) := by rw [Finset.mem_union]; push_neg; exact ⟨htA, htB⟩
    rw [Finset.card_insert_of_notMem hstU, Finset.card_insert_of_notMem htU, hcardUnion]
    omega
  have hcardRest : Rest.card = 1 + k := by
    rw [hRestdef, ← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin, hcardIns2]
    omega
  have hk1 : k ≤ 1 := by omega
  -- shared helpers (independent of k)
  have hAindep : ∀ u ∈ A, ∀ w ∈ A, u ≠ w → ¬ J.Adj u w := by
    rw [hAdef]; exact nbhd_indep_of_cliqueFree3 J hK3 s
  have hBindep : ∀ u ∈ B, ∀ w ∈ B, u ≠ w → ¬ J.Adj u w := by
    rw [hBdef]; exact nbhd_indep_of_cliqueFree3 J hK3 t
  -- cover: every vertex is s, t, in A ∪ B, or in Rest
  have hcov : ∀ x : Fin 9, x ∈ insert s (insert t (A ∪ B)) ∪ Rest := by
    intro x
    by_cases hx : x ∈ insert s (insert t (A ∪ B))
    · exact Finset.mem_union_left _ hx
    · refine Finset.mem_union_right _ ?_
      rw [hRestdef, Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, hx⟩
  -- squeeze: a degree-4 vertex whose neighbourhood lands in a ≤3-set is impossible
  have squeeze : ∀ (v : Fin 9) (S : Finset (Fin 9)),
      J.degree v = 4 → (∀ y, J.Adj v y → y ∈ S) → S.card ≤ 3 → False := by
    intro v S hvdeg hNv hSc
    have hsub : J.neighborFinset v ⊆ S := fun y hy => hNv y ((memN v y).mp hy)
    have hle := Finset.card_le_card hsub
    rw [J.card_neighborFinset_eq_degree, hvdeg] at hle
    omega
  -- case k = 0 or k = 1
  interval_cases k
  · -- k = 0: A ∩ B = ∅, so Rest = {r} with deg r = 4 and N(r) ⊆ A ∪ B (disjoint). Whichever of
    -- A, B holds ≥ 2 of N(r), a degree-4 vertex on the other side is squeezed into a 3-set.
    have hABdisj : Disjoint A B := by
      rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.card_eq_zero]; omega
    obtain ⟨r, hReq⟩ := Finset.card_eq_one.mp (show Rest.card = 1 by omega)
    have hrR : r ∈ Rest := by rw [hReq]; exact Finset.mem_singleton_self r
    obtain ⟨hrs, hrt, hrns, hrnt⟩ := hRest r hrR
    have hrdeg : J.degree r = 4 := hother r hrs hrt
    have hNrsub : J.neighborFinset r ⊆ A ∪ B := by
      intro x hx
      have hxadj : J.Adj r x := (memN r x).mp hx
      have hxs : x ≠ s := by rintro rfl; exact hrns hxadj
      have hxt : x ≠ t := by rintro rfl; exact hrnt hxadj
      have hxr : x ≠ r := fun h => (J.ne_of_adj hxadj) h.symm
      rcases Finset.mem_union.mp (hcov x) with hin | hin
      · rw [Finset.mem_insert, Finset.mem_insert] at hin
        rcases hin with h | h | h
        · exact absurd h hxs
        · exact absurd h hxt
        · exact h
      · rw [hReq, Finset.mem_singleton] at hin; exact absurd hin hxr
    have hpq4 : (J.neighborFinset r ∩ A).card + (J.neighborFinset r ∩ B).card = 4 := by
      have hd : Disjoint (J.neighborFinset r ∩ A) (J.neighborFinset r ∩ B) :=
        (hABdisj.mono_left Finset.inter_subset_right).mono_right Finset.inter_subset_right
      rw [← Finset.card_union_of_disjoint hd, ← Finset.inter_union_distrib_left,
        Finset.inter_eq_left.mpr hNrsub, J.card_neighborFinset_eq_degree, hrdeg]
    have hp3 : (J.neighborFinset r ∩ A).card ≤ 3 := by
      rw [← hAcard]; exact Finset.card_le_card Finset.inter_subset_right
    have hq3 : (J.neighborFinset r ∩ B).card ≤ 3 := by
      rw [← hBcard]; exact Finset.card_le_card Finset.inter_subset_right
    rcases (show 2 ≤ (J.neighborFinset r ∩ A).card ∨ 2 ≤ (J.neighborFinset r ∩ B).card by omega)
      with hp2 | hq2
    · -- p ≥ 2: squeeze b ∈ N(r) ∩ B into {t, r} ∪ (A \ (N(r) ∩ A))
      obtain ⟨b, hbmem⟩ := Finset.card_pos.mp (show 0 < (J.neighborFinset r ∩ B).card by omega)
      obtain ⟨hbNr, hbB⟩ := Finset.mem_inter.mp hbmem
      have hbnA : b ∉ A := fun h => (Finset.disjoint_left.mp hABdisj h) hbB
      have hbns : ¬ J.Adj b s := fun h => hbnA (by rw [hAdef]; exact (memN s b).mpr h.symm)
      have hbs : b ≠ s := fun h => hsB (by rw [← h]; exact hbB)
      have hbt : b ≠ t := fun h => htB (by rw [← h]; exact hbB)
      have hbdeg : J.degree b = 4 := hother b hbs hbt
      have hbnNrA : ∀ a ∈ J.neighborFinset r ∩ A, ¬ J.Adj b a := by
        intro a ha hba
        obtain ⟨haNr, haA⟩ := Finset.mem_inter.mp ha
        have hbnea : b ≠ a := fun h => hbnA (by rw [← h] at haA; exact haA)
        exact nbhd_indep_of_cliqueFree3 J hK3 r b hbNr a haNr hbnea hba
      refine squeeze b (insert t (insert r (A \ (J.neighborFinset r ∩ A)))) hbdeg ?_ ?_
      · intro y hyadj
        rcases Finset.mem_union.mp (hcov y) with hin | hin
        · rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_union] at hin
          rcases hin with hys | hyt | hyA | hyB
          · rw [hys] at hyadj; exact (hbns hyadj).elim
          · exact Finset.mem_insert.mpr (Or.inl hyt)
          · by_cases hyNr : y ∈ J.neighborFinset r ∩ A
            · exact absurd hyadj (hbnNrA y hyNr)
            · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                (Finset.mem_sdiff.mpr ⟨hyA, hyNr⟩))
          · exact absurd hyadj (hBindep b hbB y hyB (J.ne_of_adj hyadj))
        · rw [hReq, Finset.mem_singleton] at hin
          exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl hin))
      · have h1 := Finset.card_insert_le t (insert r (A \ (J.neighborFinset r ∩ A)))
        have h2 := Finset.card_insert_le r (A \ (J.neighborFinset r ∩ A))
        have h3 : (A \ (J.neighborFinset r ∩ A)).card = 3 - (J.neighborFinset r ∩ A).card := by
          rw [Finset.card_sdiff_of_subset Finset.inter_subset_right, hAcard]
        omega
    · -- q ≥ 2: symmetric, squeeze a ∈ N(r) ∩ A into {s, r} ∪ (B \ (N(r) ∩ B))
      obtain ⟨a, hamem⟩ := Finset.card_pos.mp (show 0 < (J.neighborFinset r ∩ A).card by omega)
      obtain ⟨haNr, haA⟩ := Finset.mem_inter.mp hamem
      have hanB : a ∉ B := fun h => (Finset.disjoint_left.mp hABdisj haA) h
      have hant : ¬ J.Adj a t := fun h => hanB (by rw [hBdef]; exact (memN t a).mpr h.symm)
      have haNs : a ≠ s := fun h => hsA (by rw [← h]; exact haA)
      have haNt : a ≠ t := fun h => htA (by rw [← h]; exact haA)
      have hadeg : J.degree a = 4 := hother a haNs haNt
      have hanNrB : ∀ b ∈ J.neighborFinset r ∩ B, ¬ J.Adj a b := by
        intro b hb hab
        obtain ⟨hbNr, hbB⟩ := Finset.mem_inter.mp hb
        have hanb : a ≠ b := fun h => hanB (by rw [← h] at hbB; exact hbB)
        exact nbhd_indep_of_cliqueFree3 J hK3 r a haNr b hbNr hanb hab
      refine squeeze a (insert s (insert r (B \ (J.neighborFinset r ∩ B)))) hadeg ?_ ?_
      · intro y hyadj
        rcases Finset.mem_union.mp (hcov y) with hin | hin
        · rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_union] at hin
          rcases hin with hys | hyt | hyA | hyB
          · exact Finset.mem_insert.mpr (Or.inl hys)
          · rw [hyt] at hyadj; exact (hant hyadj).elim
          · exact absurd hyadj (hAindep a haA y hyA (J.ne_of_adj hyadj))
          · by_cases hyNr : y ∈ J.neighborFinset r ∩ B
            · exact absurd hyadj (hanNrB y hyNr)
            · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                (Finset.mem_sdiff.mpr ⟨hyB, hyNr⟩))
        · rw [hReq, Finset.mem_singleton] at hin
          exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl hin))
      · have h1 := Finset.card_insert_le s (insert r (B \ (J.neighborFinset r ∩ B)))
        have h2 := Finset.card_insert_le r (B \ (J.neighborFinset r ∩ B))
        have h3 : (B \ (J.neighborFinset r ∩ B)).card = 3 - (J.neighborFinset r ∩ B).card := by
          rw [Finset.card_sdiff_of_subset Finset.inter_subset_right, hBcard]
        omega
  · -- k = 1: A ∩ B = {c}. With α = A \ {c}, β = B \ {c} (each card 2), any r ∈ Rest has N(r) ⊆ A ∪ B
    -- and |N(r)| = 4 forcing |N(r)∩α| = 2 or |N(r)∩β| = 2; the light-side degree-4 vertex is squeezed
    -- into {t}∪Rest / {s}∪Rest (card 3).
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (show (A ∩ B).card = 1 by omega)
    have hcAB : c ∈ A ∩ B := by rw [hc]; exact Finset.mem_singleton_self c
    obtain ⟨hcA, hcB⟩ := Finset.mem_inter.mp hcAB
    set α := A \ {c} with hαdef
    set β := B \ {c} with hβdef
    have hαsubA : α ⊆ A := by rw [hαdef]; exact Finset.sdiff_subset
    have hβsubB : β ⊆ B := by rw [hβdef]; exact Finset.sdiff_subset
    have hαcard : α.card = 2 := by
      rw [hαdef, Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hcA), hAcard,
        Finset.card_singleton]
    have hβcard : β.card = 2 := by
      rw [hβdef, Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hcB), hBcard,
        Finset.card_singleton]
    have hαβdisj : Disjoint α β := by
      rw [Finset.disjoint_left]
      intro x hxα hxβ
      rw [hαdef, Finset.mem_sdiff] at hxα
      rw [hβdef, Finset.mem_sdiff] at hxβ
      have hxAB : x ∈ A ∩ B := Finset.mem_inter.mpr ⟨hxα.1, hxβ.1⟩
      rw [hc, Finset.mem_singleton] at hxAB
      exact hxα.2 (Finset.mem_singleton.mpr hxAB)
    obtain ⟨r, hrR⟩ := Finset.card_pos.mp (show 0 < Rest.card by omega)
    obtain ⟨hrs, hrt, hrns, hrnt⟩ := hRest r hrR
    have hrdeg : J.degree r = 4 := hother r hrs hrt
    have hNrsub : J.neighborFinset r ⊆ A ∪ B := by
      intro x hx
      have hxadj : J.Adj r x := (memN r x).mp hx
      have hxs : x ≠ s := by rintro rfl; exact hrns hxadj
      have hxt : x ≠ t := by rintro rfl; exact hrnt hxadj
      have hxr : x ∉ Rest := by
        intro hxRest
        by_cases hxeqr : x = r
        · exact (J.ne_of_adj hxadj) hxeqr.symm
        · exact (hRestIndep r hrR x hxRest (fun h => hxeqr h.symm)) hxadj
      rcases Finset.mem_union.mp (hcov x) with hin | hin
      · rw [Finset.mem_insert, Finset.mem_insert] at hin
        rcases hin with h | h | h
        · exact absurd h hxs
        · exact absurd h hxt
        · exact h
      · exact absurd hin hxr
    have hun : (J.neighborFinset r ∩ α) ∪ (J.neighborFinset r ∩ β)
        = J.neighborFinset r ∩ (α ∪ β) := (Finset.inter_union_distrib_left _ _ _).symm
    have hdisj2 : Disjoint (J.neighborFinset r ∩ α) (J.neighborFinset r ∩ β) :=
      (hαβdisj.mono_left Finset.inter_subset_right).mono_right Finset.inter_subset_right
    have hsub2 : J.neighborFinset r ⊆ insert c (α ∪ β) := by
      intro x hx
      have hxAB := hNrsub hx
      rw [Finset.mem_union] at hxAB
      by_cases hxc : x = c
      · exact Finset.mem_insert.mpr (Or.inl hxc)
      · refine Finset.mem_insert_of_mem (Finset.mem_union.mpr ?_)
        rcases hxAB with hxA | hxB
        · left; rw [hαdef, Finset.mem_sdiff]
          exact ⟨hxA, fun h => hxc (Finset.mem_singleton.mp h)⟩
        · right; rw [hβdef, Finset.mem_sdiff]
          exact ⟨hxB, fun h => hxc (Finset.mem_singleton.mp h)⟩
    have hPQ3 : 3 ≤ (J.neighborFinset r ∩ α).card + (J.neighborFinset r ∩ β).card := by
      have h1 : J.neighborFinset r
          ⊆ insert c ((J.neighborFinset r ∩ α) ∪ (J.neighborFinset r ∩ β)) := by
        intro x hx
        by_cases hxc : x = c
        · exact Finset.mem_insert.mpr (Or.inl hxc)
        · have hx2 := hsub2 hx
          rw [Finset.mem_insert] at hx2
          rcases hx2 with h | h
          · exact absurd h hxc
          · refine Finset.mem_insert_of_mem ?_
            rw [hun]; exact Finset.mem_inter.mpr ⟨hx, h⟩
      have hc1 := Finset.card_le_card h1
      have hc2 := Finset.card_insert_le c ((J.neighborFinset r ∩ α) ∪ (J.neighborFinset r ∩ β))
      have hc3 : ((J.neighborFinset r ∩ α) ∪ (J.neighborFinset r ∩ β)).card
          = (J.neighborFinset r ∩ α).card + (J.neighborFinset r ∩ β).card :=
        Finset.card_union_of_disjoint hdisj2
      rw [J.card_neighborFinset_eq_degree, hrdeg] at hc1
      omega
    have hPle : (J.neighborFinset r ∩ α).card ≤ 2 := by
      rw [← hαcard]; exact Finset.card_le_card Finset.inter_subset_right
    have hQle : (J.neighborFinset r ∩ β).card ≤ 2 := by
      rw [← hβcard]; exact Finset.card_le_card Finset.inter_subset_right
    rcases (show 2 ≤ (J.neighborFinset r ∩ α).card ∨ 2 ≤ (J.neighborFinset r ∩ β).card by omega)
      with hp2 | hq2
    · -- α ⊆ N(r); squeeze b ∈ N(r) ∩ β into insert t Rest
      have hαNr : α ⊆ J.neighborFinset r := by
        have heq : J.neighborFinset r ∩ α = α :=
          Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [hαcard]; exact hp2)
        intro x hxα
        have hx2 : x ∈ J.neighborFinset r ∩ α := by rw [heq]; exact hxα
        exact (Finset.mem_inter.mp hx2).1
      obtain ⟨b, hbmem⟩ := Finset.card_pos.mp (show 0 < (J.neighborFinset r ∩ β).card by omega)
      obtain ⟨hbNr, hbβ⟩ := Finset.mem_inter.mp hbmem
      have hbB : b ∈ B := hβsubB hbβ
      have hbc : b ≠ c := by
        have hb' := hbβ; rw [hβdef, Finset.mem_sdiff] at hb'
        exact fun h => hb'.2 (Finset.mem_singleton.mpr h)
      have hbnc : ¬ J.Adj b c := hBindep b hbB c hcB hbc
      have hbnA : b ∉ A := by
        intro h
        have hbAB : b ∈ A ∩ B := Finset.mem_inter.mpr ⟨h, hbB⟩
        rw [hc, Finset.mem_singleton] at hbAB; exact hbc hbAB
      have hbns : ¬ J.Adj b s := fun h => hbnA (by rw [hAdef]; exact (memN s b).mpr h.symm)
      have hbs : b ≠ s := fun h => hsB (by rw [← h]; exact hbB)
      have hbt : b ≠ t := fun h => htB (by rw [← h]; exact hbB)
      have hbdeg : J.degree b = 4 := hother b hbs hbt
      have hbnα : ∀ a ∈ α, ¬ J.Adj b a := by
        intro a haα hba
        have haNr : a ∈ J.neighborFinset r := hαNr haα
        have hab : b ≠ a := fun h => (Finset.disjoint_left.mp hαβdisj haα) (by rw [← h]; exact hbβ)
        exact nbhd_indep_of_cliqueFree3 J hK3 r b hbNr a haNr hab hba
      refine squeeze b (insert t Rest) hbdeg ?_ ?_
      · intro y hyadj
        rcases Finset.mem_union.mp (hcov y) with hin | hin
        · rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_union] at hin
          rcases hin with hys | hyt | hyA | hyB
          · rw [hys] at hyadj; exact (hbns hyadj).elim
          · exact Finset.mem_insert.mpr (Or.inl hyt)
          · by_cases hyc : y = c
            · rw [hyc] at hyadj; exact (hbnc hyadj).elim
            · refine absurd hyadj (hbnα y ?_)
              rw [hαdef, Finset.mem_sdiff]
              exact ⟨hyA, fun h => hyc (Finset.mem_singleton.mp h)⟩
          · exact absurd hyadj (hBindep b hbB y hyB (J.ne_of_adj hyadj))
        · exact Finset.mem_insert_of_mem hin
      · have h1 := Finset.card_insert_le t Rest
        omega
    · -- β ⊆ N(r); squeeze a ∈ N(r) ∩ α into insert s Rest
      have hβNr : β ⊆ J.neighborFinset r := by
        have heq : J.neighborFinset r ∩ β = β :=
          Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [hβcard]; exact hq2)
        intro x hxβ
        have hx2 : x ∈ J.neighborFinset r ∩ β := by rw [heq]; exact hxβ
        exact (Finset.mem_inter.mp hx2).1
      obtain ⟨a, hamem⟩ := Finset.card_pos.mp (show 0 < (J.neighborFinset r ∩ α).card by omega)
      obtain ⟨haNr, haα⟩ := Finset.mem_inter.mp hamem
      have haA : a ∈ A := hαsubA haα
      have hac : a ≠ c := by
        have ha' := haα; rw [hαdef, Finset.mem_sdiff] at ha'
        exact fun h => ha'.2 (Finset.mem_singleton.mpr h)
      have hanc : ¬ J.Adj a c := hAindep a haA c hcA hac
      have hanB : a ∉ B := by
        intro h
        have haAB : a ∈ A ∩ B := Finset.mem_inter.mpr ⟨haA, h⟩
        rw [hc, Finset.mem_singleton] at haAB; exact hac haAB
      have hant : ¬ J.Adj a t := fun h => hanB (by rw [hBdef]; exact (memN t a).mpr h.symm)
      have has : a ≠ s := fun h => hsA (by rw [← h]; exact haA)
      have hat : a ≠ t := fun h => htA (by rw [← h]; exact haA)
      have hadeg : J.degree a = 4 := hother a has hat
      have hanβ : ∀ b ∈ β, ¬ J.Adj a b := by
        intro b hbβ hab
        have hbNr : b ∈ J.neighborFinset r := hβNr hbβ
        have hba : a ≠ b := fun h => (Finset.disjoint_left.mp hαβdisj haα) (by rw [h]; exact hbβ)
        exact nbhd_indep_of_cliqueFree3 J hK3 r a haNr b hbNr hba hab
      refine squeeze a (insert s Rest) hadeg ?_ ?_
      · intro y hyadj
        rcases Finset.mem_union.mp (hcov y) with hin | hin
        · rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_union] at hin
          rcases hin with hys | hyt | hyA | hyB
          · exact Finset.mem_insert.mpr (Or.inl hys)
          · rw [hyt] at hyadj; exact (hant hyadj).elim
          · exact absurd hyadj (hAindep a haA y hyA (J.ne_of_adj hyadj))
          · by_cases hyc : y = c
            · rw [hyc] at hyadj; exact (hanc hyadj).elim
            · refine absurd hyadj (hanβ y ?_)
              rw [hβdef, Finset.mem_sdiff]
              exact ⟨hyB, fun h => hyc (Finset.mem_singleton.mp h)⟩
        · exact Finset.mem_insert_of_mem hin
      · have h1 := Finset.card_insert_le s Rest
        omega

/-- **[3,3,4⁷] structural determination.** Given `s ~ t` (both degree 3, rest degree 4,
triangle-free), the graph is the concrete `base9A2` shape: `spokes = N(t)∖{s}`, `ys = N(s)∖{t}`
(each independent, card 2), `zs` the remaining 3 (independent), with `N₀ = spokes ∪ ys` and
`N₁ = {s} ∪ zs` independent, `zs` completely joined to `spokes ∪ ys`, apex `t ~ {spokes, s}`.
No `α` needed: `zs` independent (`base_deg3_rest_indep`) forces every `z` to have `N(z) = spokes∪ys`
(degree 4 into a 4-set), which forces `N(sp) = {t}∪zs` and `N(y) = {s}∪zs`. -/
theorem base_deg3_structure (J : SimpleGraph (Fin 9)) (hK3 : J.CliqueFree 3)
    (s t : Fin 9) (hst : s ≠ t) (hst_adj : J.Adj s t)
    (hs3 : J.degree s = 3) (ht3 : J.degree t = 3)
    (hother : ∀ v, v ≠ s → v ≠ t → J.degree v = 4) :
    ∃ spokes ys zs : Finset (Fin 9),
      spokes.card = 2 ∧ ys.card = 2 ∧ zs.card = 3 ∧
      insert s (insert t (spokes ∪ ys ∪ zs)) = Finset.univ ∧
      s ∉ spokes ∧ s ∉ ys ∧ s ∉ zs ∧ t ∉ spokes ∧ t ∉ ys ∧ t ∉ zs ∧
      Disjoint spokes ys ∧ Disjoint spokes zs ∧ Disjoint ys zs ∧
      (∀ sp ∈ spokes, J.Adj t sp) ∧ (∀ y ∈ ys, J.Adj s y) ∧
      (∀ sp ∈ spokes, ∀ z ∈ zs, J.Adj sp z) ∧ (∀ y ∈ ys, ∀ z ∈ zs, J.Adj y z) ∧
      (∀ sp ∈ spokes, ¬ J.Adj s sp) ∧ (∀ z ∈ zs, ¬ J.Adj s z) ∧
      (∀ y ∈ ys, ¬ J.Adj t y) ∧ (∀ z ∈ zs, ¬ J.Adj t z) ∧
      (∀ sp ∈ spokes, ∀ y ∈ ys, ¬ J.Adj sp y) ∧
      (∀ sp ∈ spokes, ∀ sp' ∈ spokes, sp ≠ sp' → ¬ J.Adj sp sp') ∧
      (∀ y ∈ ys, ∀ y' ∈ ys, y ≠ y' → ¬ J.Adj y y') ∧
      (∀ z ∈ zs, ∀ z' ∈ zs, z ≠ z' → ¬ J.Adj z z') := by
  have memN : ∀ v w : Fin 9, w ∈ J.neighborFinset v ↔ J.Adj v w := fun v w => J.mem_neighborFinset v w
  have hindepN : ∀ v : Fin 9, ∀ u ∈ J.neighborFinset v, ∀ w ∈ J.neighborFinset v, u ≠ w →
      ¬ J.Adj u w := fun v => nbhd_indep_of_cliqueFree3 J hK3 v
  have hsNt : s ∈ J.neighborFinset t := (memN t s).mpr hst_adj.symm
  have htNs : t ∈ J.neighborFinset s := (memN s t).mpr hst_adj
  set spokes := J.neighborFinset t \ {s} with hspdef
  set ys := J.neighborFinset s \ {t} with hydef
  have hspcard : spokes.card = 2 := by
    rw [hspdef, Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hsNt),
      J.card_neighborFinset_eq_degree, ht3, Finset.card_singleton]
  have hycard : ys.card = 2 := by
    rw [hydef, Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr htNs),
      J.card_neighborFinset_eq_degree, hs3, Finset.card_singleton]
  have hmemsp : ∀ w, w ∈ spokes ↔ J.Adj t w ∧ w ≠ s := by
    intro w; rw [hspdef, Finset.mem_sdiff, memN, Finset.mem_singleton]
  have hmemy : ∀ w, w ∈ ys ↔ J.Adj s w ∧ w ≠ t := by
    intro w; rw [hydef, Finset.mem_sdiff, memN, Finset.mem_singleton]
  have hsp_t : ∀ sp ∈ spokes, J.Adj t sp := fun sp h => ((hmemsp sp).mp h).1
  have hsp_ne_s : ∀ sp ∈ spokes, sp ≠ s := fun sp h => ((hmemsp sp).mp h).2
  have hsp_ne_t : ∀ sp ∈ spokes, sp ≠ t := fun sp h => (J.ne_of_adj (hsp_t sp h)).symm
  have hy_s : ∀ y ∈ ys, J.Adj s y := fun y h => ((hmemy y).mp h).1
  have hy_ne_t : ∀ y ∈ ys, y ≠ t := fun y h => ((hmemy y).mp h).2
  have hy_ne_s : ∀ y ∈ ys, y ≠ s := fun y h => (J.ne_of_adj (hy_s y h)).symm
  have hs_nsp : ∀ sp ∈ spokes, ¬ J.Adj s sp := by
    intro sp h
    exact hindepN t s hsNt sp ((memN t sp).mpr (hsp_t sp h)) (Ne.symm (hsp_ne_s sp h))
  have ht_ny : ∀ y ∈ ys, ¬ J.Adj t y := by
    intro y h
    exact hindepN s t htNs y ((memN s y).mpr (hy_s y h)) (Ne.symm (hy_ne_t y h))
  have hsp_indep : ∀ sp ∈ spokes, ∀ sp' ∈ spokes, sp ≠ sp' → ¬ J.Adj sp sp' := by
    intro sp h sp' h' hne
    exact hindepN t sp ((memN t sp).mpr (hsp_t sp h)) sp' ((memN t sp').mpr (hsp_t sp' h')) hne
  have hy_indep : ∀ y ∈ ys, ∀ y' ∈ ys, y ≠ y' → ¬ J.Adj y y' := by
    intro y h y' h' hne
    exact hindepN s y ((memN s y).mpr (hy_s y h)) y' ((memN s y').mpr (hy_s y' h')) hne
  have hsp_y_disj : Disjoint spokes ys := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    exact hK3 {s, t, w} (by rw [SimpleGraph.is3Clique_iff]
                            exact ⟨s, t, w, hst_adj, hy_s w hw', hsp_t w hw, rfl⟩)
  set zs := Finset.univ \ (insert s (insert t (spokes ∪ ys))) with hzdef
  have hs_nsp' : s ∉ spokes := fun h => (hsp_ne_s s h) rfl
  have hs_ny : s ∉ ys := fun h => (hy_ne_s s h) rfl
  have ht_nsp : t ∉ spokes := fun h => (hsp_ne_t t h) rfl
  have ht_ny' : t ∉ ys := fun h => (hy_ne_t t h) rfl
  have hmemz : ∀ w, w ∈ zs ↔ w ≠ s ∧ w ≠ t ∧ w ∉ spokes ∧ w ∉ ys := by
    intro w
    rw [hzdef, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_insert, Finset.mem_union]
    constructor
    · rintro ⟨-, hw⟩
      exact ⟨fun h => hw (Or.inl h), fun h => hw (Or.inr (Or.inl h)),
        fun h => hw (Or.inr (Or.inr (Or.inl h))), fun h => hw (Or.inr (Or.inr (Or.inr h)))⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨Finset.mem_univ _,
        fun h => h.elim h1 (fun h => h.elim h2 (fun h => h.elim h3 h4))⟩
  have hsz : s ∉ zs := fun h => ((hmemz s).mp h).1 rfl
  have htz : t ∉ zs := fun h => ((hmemz t).mp h).2.1 rfl
  have hzcard : zs.card = 3 := by
    have hunion_card : (spokes ∪ ys).card = 4 := by
      rw [Finset.card_union_of_disjoint hsp_y_disj, hspcard, hycard]
    have htnotin : t ∉ (spokes ∪ ys) := by
      rw [Finset.mem_union]; exact fun h => h.elim ht_nsp ht_ny'
    have hsnotin : s ∉ insert t (spokes ∪ ys) := by
      rw [Finset.mem_insert]; push_neg
      exact ⟨hst, by rw [Finset.mem_union]; exact fun h => h.elim hs_nsp' hs_ny⟩
    have h6 : (insert s (insert t (spokes ∪ ys))).card = 6 := by
      rw [Finset.card_insert_of_notMem hsnotin, Finset.card_insert_of_notMem htnotin, hunion_card]
    rw [hzdef, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, h6]
  have hcover : insert s (insert t (spokes ∪ ys ∪ zs)) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro w
    by_cases hz : w ∈ zs
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _ hz))
    · have hw : ¬ (w ≠ s ∧ w ≠ t ∧ w ∉ spokes ∧ w ∉ ys) := fun hh => hz ((hmemz w).mpr hh)
      by_cases h1 : w = s
      · rw [h1]; exact Finset.mem_insert_self _ _
      by_cases h2 : w = t
      · rw [h2]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      by_cases h3 : w ∈ spokes
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_union_left _ (Finset.mem_union_left _ h3)))
      · have h4 : w ∈ ys := by by_contra h4; exact hw ⟨h1, h2, h3, h4⟩
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_union_left _ (Finset.mem_union_right _ h4)))
  have hsp_z_disj : Disjoint spokes zs := by
    rw [Finset.disjoint_left]; intro w hw hz; exact ((hmemz w).mp hz).2.2.1 hw
  have hy_z_disj : Disjoint ys zs := by
    rw [Finset.disjoint_left]; intro w hw hz; exact ((hmemz w).mp hz).2.2.2 hw
  have hz_ns : ∀ z ∈ zs, ¬ J.Adj s z := by
    intro z hz hadj
    obtain ⟨_, hzt, _, hzy⟩ := (hmemz z).mp hz
    rw [hydef] at hzy
    exact hzy (Finset.mem_sdiff.mpr ⟨(memN s z).mpr hadj, fun h => hzt (Finset.mem_singleton.mp h)⟩)
  have hz_nt : ∀ z ∈ zs, ¬ J.Adj t z := by
    intro z hz hadj
    obtain ⟨hzs, _, hzsp, _⟩ := (hmemz z).mp hz
    rw [hspdef] at hzsp
    exact hzsp (Finset.mem_sdiff.mpr ⟨(memN t z).mpr hadj, fun h => hzs (Finset.mem_singleton.mp h)⟩)
  have hz_indep : ∀ z ∈ zs, ∀ z' ∈ zs, z ≠ z' → ¬ J.Adj z z' := by
    intro z hz z' hz' hne
    obtain ⟨hzs, hzt, _, _⟩ := (hmemz z).mp hz
    obtain ⟨hz's, hz't, _, _⟩ := (hmemz z').mp hz'
    exact base_deg3_rest_indep J hK3 s t hst hother z z' hzs hzt hz's hz't
      (fun h => (hz_ns z hz) h.symm) (fun h => (hz_nt z hz) h.symm)
      (fun h => (hz_ns z' hz') h.symm) (fun h => (hz_nt z' hz') h.symm) hne
  have hzN : ∀ z ∈ zs, J.neighborFinset z = spokes ∪ ys := by
    intro z hz
    obtain ⟨hzs, hzt, _, _⟩ := (hmemz z).mp hz
    have hdz : J.degree z = 4 := hother z hzs hzt
    have hsub : J.neighborFinset z ⊆ spokes ∪ ys := by
      intro w hw
      have hzw : J.Adj z w := (memN z w).mp hw
      have hws : w ≠ s := fun h => (hz_ns z hz) ((show J.Adj z s by rw [← h]; exact hzw).symm)
      have hwt : w ≠ t := fun h => (hz_nt z hz) ((show J.Adj z t by rw [← h]; exact hzw).symm)
      have hwz : w ∉ zs := fun hwzs =>
        (hz_indep z hz w hwzs (J.ne_of_adj hzw)) hzw
      have hwuniv : w ∈ insert s (insert t (spokes ∪ ys ∪ zs)) := by
        rw [hcover]; exact Finset.mem_univ w
      rw [Finset.mem_insert, Finset.mem_insert] at hwuniv
      rcases hwuniv with h | h | h
      · exact absurd h hws
      · exact absurd h hwt
      · rw [Finset.mem_union] at h; exact h.elim id (fun h => absurd h hwz)
    have hcardeq : (spokes ∪ ys).card ≤ (J.neighborFinset z).card := by
      have h1 : (spokes ∪ ys).card = 4 := by
        rw [Finset.card_union_of_disjoint hsp_y_disj, hspcard, hycard]
      have h2 : (J.neighborFinset z).card = 4 := by rw [J.card_neighborFinset_eq_degree, hdz]
      omega
    exact Finset.eq_of_subset_of_card_le hsub hcardeq
  have hspN : ∀ sp ∈ spokes, J.neighborFinset sp = insert t zs := by
    intro sp hsp
    have hdsp : J.degree sp = 4 := hother sp (hsp_ne_s sp hsp) (hsp_ne_t sp hsp)
    have hsub : insert t zs ⊆ J.neighborFinset sp := by
      intro w hw
      rw [Finset.mem_insert] at hw
      rcases hw with h | h
      · rw [h]; exact (memN sp t).mpr (hsp_t sp hsp).symm
      · have hmem : sp ∈ J.neighborFinset w := by rw [hzN w h]; exact Finset.mem_union_left _ hsp
        exact (memN sp w).mpr ((memN w sp).mp hmem).symm
    have hcardeq : (J.neighborFinset sp).card ≤ (insert t zs).card := by
      have h1 : (insert t zs).card = 4 := by rw [Finset.card_insert_of_notMem htz, hzcard]
      have h2 : (J.neighborFinset sp).card = 4 := by rw [J.card_neighborFinset_eq_degree, hdsp]
      omega
    exact (Finset.eq_of_subset_of_card_le hsub hcardeq).symm
  have hyN : ∀ y ∈ ys, J.neighborFinset y = insert s zs := by
    intro y hy
    have hdy : J.degree y = 4 := hother y (hy_ne_s y hy) (hy_ne_t y hy)
    have hsub : insert s zs ⊆ J.neighborFinset y := by
      intro w hw
      rw [Finset.mem_insert] at hw
      rcases hw with h | h
      · rw [h]; exact (memN y s).mpr (hy_s y hy).symm
      · have hmem : y ∈ J.neighborFinset w := by rw [hzN w h]; exact Finset.mem_union_right _ hy
        exact (memN y w).mpr ((memN w y).mp hmem).symm
    have hcardeq : (J.neighborFinset y).card ≤ (insert s zs).card := by
      have h1 : (insert s zs).card = 4 := by rw [Finset.card_insert_of_notMem hsz, hzcard]
      have h2 : (J.neighborFinset y).card = 4 := by rw [J.card_neighborFinset_eq_degree, hdy]
      omega
    exact (Finset.eq_of_subset_of_card_le hsub hcardeq).symm
  have hspz : ∀ sp ∈ spokes, ∀ z ∈ zs, J.Adj sp z := by
    intro sp hsp z hz
    exact (memN sp z).mp (by rw [hspN sp hsp]; exact Finset.mem_insert_of_mem hz)
  have hyz : ∀ y ∈ ys, ∀ z ∈ zs, J.Adj y z := by
    intro y hy z hz
    exact (memN y z).mp (by rw [hyN y hy]; exact Finset.mem_insert_of_mem hz)
  have hspny : ∀ sp ∈ spokes, ∀ y ∈ ys, ¬ J.Adj sp y := by
    intro sp hsp y hy hadj
    have hmem : y ∈ J.neighborFinset sp := (memN sp y).mpr hadj
    rw [hspN sp hsp, Finset.mem_insert] at hmem
    exact hmem.elim (hy_ne_t y hy) (fun h => (Finset.disjoint_left.mp hy_z_disj hy) h)
  exact ⟨spokes, ys, zs, hspcard, hycard, hzcard, hcover,
    hs_nsp', hs_ny, hsz, ht_nsp, ht_ny', htz,
    hsp_y_disj, hsp_z_disj, hy_z_disj,
    hsp_t, hy_s, hspz, hyz,
    hs_nsp, hz_ns, ht_ny, hz_nt,
    hspny, hsp_indep, hy_indep, hz_indep⟩

/-- **[3,3,4⁷] isomorphism** (the second base class). Any triangle-free `α ≤ 4` `e = 17` graph on
`Fin 9` with exactly two degree-3 vertices `s, t` (rest degree 4) is isomorphic to `base9A2`.
(At `e = 17` the two degree-3 vertices are forced adjacent — nauty confirms no `e = 17` witness with
two non-adjacent degree-3 vertices; the structure is `base9A1` with a second removed cross-edge and
the apex also joined to that spoke.) -/
theorem base_classification_deg3 (J : SimpleGraph (Fin 9)) (hK3 : J.CliqueFree 3)
    (hα : alphaAtMost J 4) (he : edgeCountIn J Finset.univ = 17) (s t : Fin 9) (hst : s ≠ t)
    (hs3 : J.degree s = 3) (ht3 : J.degree t = 3)
    (hother : ∀ v, v ≠ s → v ≠ t → J.degree v = 4) :
    ∃ σ : Fin 9 ≃ Fin 9, ∀ u v, J.Adj u v ↔ base9A2.Adj (σ u) (σ v) := by
  have hst_adj : J.Adj s t := base_deg3_st_adjacent J hK3 hα s t hst hs3 ht3 hother
  obtain ⟨spokes, ys, zs, hspcard, hycard, hzcard, hcover, hsnsp, hsny, hsnz,
    htnsp, htny, htnz, hspydisj, hspzdisj, hyzdisj, htsp, hsy, hspz, hyz,
    hnssp, hnsz, hnty, hntz, hnspy, hspindep, hyindep, hzindep⟩ :=
    base_deg3_structure J hK3 s t hst hst_adj hs3 ht3 hother
  obtain ⟨sp1, sp2, hsp12, hspeq⟩ := Finset.card_eq_two.mp hspcard
  obtain ⟨y1, y2, hy12, hyeq⟩ := Finset.card_eq_two.mp hycard
  obtain ⟨z1, z2, z3, hz12, hz13, hz23, hzeq⟩ := Finset.card_eq_three.mp hzcard
  have hsp1 : sp1 ∈ spokes := by rw [hspeq]; exact Finset.mem_insert_self _ _
  have hsp2 : sp2 ∈ spokes := by rw [hspeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hym1 : y1 ∈ ys := by rw [hyeq]; exact Finset.mem_insert_self _ _
  have hym2 : y2 ∈ ys := by rw [hyeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hzm1 : z1 ∈ zs := by rw [hzeq]; exact Finset.mem_insert_self _ _
  have hzm2 : z2 ∈ zs := by rw [hzeq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hzm3 : z3 ∈ zs := by rw [hzeq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hs_sp : ∀ w ∈ spokes, s ≠ w := fun w h he => hsnsp (he ▸ h)
  have hs_y : ∀ w ∈ ys, s ≠ w := fun w h he => hsny (he ▸ h)
  have hs_z : ∀ w ∈ zs, s ≠ w := fun w h he => hsnz (he ▸ h)
  have ht_sp : ∀ w ∈ spokes, t ≠ w := fun w h he => htnsp (he ▸ h)
  have ht_y : ∀ w ∈ ys, t ≠ w := fun w h he => htny (he ▸ h)
  have ht_z : ∀ w ∈ zs, t ≠ w := fun w h he => htnz (he ▸ h)
  have hsp_y : ∀ u ∈ spokes, ∀ w ∈ ys, u ≠ w := fun u hu w hw he => (Finset.disjoint_left.mp hspydisj hu) (he ▸ hw)
  have hsp_z : ∀ u ∈ spokes, ∀ w ∈ zs, u ≠ w := fun u hu w hw he => (Finset.disjoint_left.mp hspzdisj hu) (he ▸ hw)
  have hy_z : ∀ u ∈ ys, ∀ w ∈ zs, u ≠ w := fun u hu w hw he => (Finset.disjoint_left.mp hyzdisj hu) (he ▸ hw)
  set f : Fin 9 → Fin 9 := fun i =>
    if i = 0 then sp1 else if i = 1 then sp2 else if i = 2 then y1 else if i = 3 then y2
    else if i = 4 then s else if i = 5 then z1 else if i = 6 then z2 else if i = 7 then z3 else t
    with hf
  have hinj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [hf, Fin.isValue, Fin.reduceEq, reduceIte, reduceCtorEq] at hij ⊢ <;>
      first
        | rfl
        | exact absurd hij (hsp12)
        | exact absurd hij (hsp12).symm
        | exact absurd hij (hsp_y sp1 hsp1 y1 hym1)
        | exact absurd hij (hsp_y sp1 hsp1 y1 hym1).symm
        | exact absurd hij (hsp_y sp1 hsp1 y2 hym2)
        | exact absurd hij (hsp_y sp1 hsp1 y2 hym2).symm
        | exact absurd hij ((hs_sp sp1 hsp1).symm)
        | exact absurd hij ((hs_sp sp1 hsp1).symm).symm
        | exact absurd hij (hsp_z sp1 hsp1 z1 hzm1)
        | exact absurd hij (hsp_z sp1 hsp1 z1 hzm1).symm
        | exact absurd hij (hsp_z sp1 hsp1 z2 hzm2)
        | exact absurd hij (hsp_z sp1 hsp1 z2 hzm2).symm
        | exact absurd hij (hsp_z sp1 hsp1 z3 hzm3)
        | exact absurd hij (hsp_z sp1 hsp1 z3 hzm3).symm
        | exact absurd hij ((ht_sp sp1 hsp1).symm)
        | exact absurd hij ((ht_sp sp1 hsp1).symm).symm
        | exact absurd hij (hsp12.symm)
        | exact absurd hij (hsp12.symm).symm
        | exact absurd hij (hsp_y sp2 hsp2 y1 hym1)
        | exact absurd hij (hsp_y sp2 hsp2 y1 hym1).symm
        | exact absurd hij (hsp_y sp2 hsp2 y2 hym2)
        | exact absurd hij (hsp_y sp2 hsp2 y2 hym2).symm
        | exact absurd hij ((hs_sp sp2 hsp2).symm)
        | exact absurd hij ((hs_sp sp2 hsp2).symm).symm
        | exact absurd hij (hsp_z sp2 hsp2 z1 hzm1)
        | exact absurd hij (hsp_z sp2 hsp2 z1 hzm1).symm
        | exact absurd hij (hsp_z sp2 hsp2 z2 hzm2)
        | exact absurd hij (hsp_z sp2 hsp2 z2 hzm2).symm
        | exact absurd hij (hsp_z sp2 hsp2 z3 hzm3)
        | exact absurd hij (hsp_z sp2 hsp2 z3 hzm3).symm
        | exact absurd hij ((ht_sp sp2 hsp2).symm)
        | exact absurd hij ((ht_sp sp2 hsp2).symm).symm
        | exact absurd hij ((hsp_y sp1 hsp1 y1 hym1).symm)
        | exact absurd hij ((hsp_y sp1 hsp1 y1 hym1).symm).symm
        | exact absurd hij ((hsp_y sp2 hsp2 y1 hym1).symm)
        | exact absurd hij ((hsp_y sp2 hsp2 y1 hym1).symm).symm
        | exact absurd hij (hy12)
        | exact absurd hij (hy12).symm
        | exact absurd hij ((hs_y y1 hym1).symm)
        | exact absurd hij ((hs_y y1 hym1).symm).symm
        | exact absurd hij (hy_z y1 hym1 z1 hzm1)
        | exact absurd hij (hy_z y1 hym1 z1 hzm1).symm
        | exact absurd hij (hy_z y1 hym1 z2 hzm2)
        | exact absurd hij (hy_z y1 hym1 z2 hzm2).symm
        | exact absurd hij (hy_z y1 hym1 z3 hzm3)
        | exact absurd hij (hy_z y1 hym1 z3 hzm3).symm
        | exact absurd hij ((ht_y y1 hym1).symm)
        | exact absurd hij ((ht_y y1 hym1).symm).symm
        | exact absurd hij ((hsp_y sp1 hsp1 y2 hym2).symm)
        | exact absurd hij ((hsp_y sp1 hsp1 y2 hym2).symm).symm
        | exact absurd hij ((hsp_y sp2 hsp2 y2 hym2).symm)
        | exact absurd hij ((hsp_y sp2 hsp2 y2 hym2).symm).symm
        | exact absurd hij (hy12.symm)
        | exact absurd hij (hy12.symm).symm
        | exact absurd hij ((hs_y y2 hym2).symm)
        | exact absurd hij ((hs_y y2 hym2).symm).symm
        | exact absurd hij (hy_z y2 hym2 z1 hzm1)
        | exact absurd hij (hy_z y2 hym2 z1 hzm1).symm
        | exact absurd hij (hy_z y2 hym2 z2 hzm2)
        | exact absurd hij (hy_z y2 hym2 z2 hzm2).symm
        | exact absurd hij (hy_z y2 hym2 z3 hzm3)
        | exact absurd hij (hy_z y2 hym2 z3 hzm3).symm
        | exact absurd hij ((ht_y y2 hym2).symm)
        | exact absurd hij ((ht_y y2 hym2).symm).symm
        | exact absurd hij (hs_sp sp1 hsp1)
        | exact absurd hij (hs_sp sp1 hsp1).symm
        | exact absurd hij (hs_sp sp2 hsp2)
        | exact absurd hij (hs_sp sp2 hsp2).symm
        | exact absurd hij (hs_y y1 hym1)
        | exact absurd hij (hs_y y1 hym1).symm
        | exact absurd hij (hs_y y2 hym2)
        | exact absurd hij (hs_y y2 hym2).symm
        | exact absurd hij (hs_z z1 hzm1)
        | exact absurd hij (hs_z z1 hzm1).symm
        | exact absurd hij (hs_z z2 hzm2)
        | exact absurd hij (hs_z z2 hzm2).symm
        | exact absurd hij (hs_z z3 hzm3)
        | exact absurd hij (hs_z z3 hzm3).symm
        | exact absurd hij (hst)
        | exact absurd hij (hst).symm
        | exact absurd hij ((hsp_z sp1 hsp1 z1 hzm1).symm)
        | exact absurd hij ((hsp_z sp1 hsp1 z1 hzm1).symm).symm
        | exact absurd hij ((hsp_z sp2 hsp2 z1 hzm1).symm)
        | exact absurd hij ((hsp_z sp2 hsp2 z1 hzm1).symm).symm
        | exact absurd hij ((hy_z y1 hym1 z1 hzm1).symm)
        | exact absurd hij ((hy_z y1 hym1 z1 hzm1).symm).symm
        | exact absurd hij ((hy_z y2 hym2 z1 hzm1).symm)
        | exact absurd hij ((hy_z y2 hym2 z1 hzm1).symm).symm
        | exact absurd hij ((hs_z z1 hzm1).symm)
        | exact absurd hij ((hs_z z1 hzm1).symm).symm
        | exact absurd hij (hz12)
        | exact absurd hij (hz12).symm
        | exact absurd hij (hz13)
        | exact absurd hij (hz13).symm
        | exact absurd hij ((ht_z z1 hzm1).symm)
        | exact absurd hij ((ht_z z1 hzm1).symm).symm
        | exact absurd hij ((hsp_z sp1 hsp1 z2 hzm2).symm)
        | exact absurd hij ((hsp_z sp1 hsp1 z2 hzm2).symm).symm
        | exact absurd hij ((hsp_z sp2 hsp2 z2 hzm2).symm)
        | exact absurd hij ((hsp_z sp2 hsp2 z2 hzm2).symm).symm
        | exact absurd hij ((hy_z y1 hym1 z2 hzm2).symm)
        | exact absurd hij ((hy_z y1 hym1 z2 hzm2).symm).symm
        | exact absurd hij ((hy_z y2 hym2 z2 hzm2).symm)
        | exact absurd hij ((hy_z y2 hym2 z2 hzm2).symm).symm
        | exact absurd hij ((hs_z z2 hzm2).symm)
        | exact absurd hij ((hs_z z2 hzm2).symm).symm
        | exact absurd hij (hz12.symm)
        | exact absurd hij (hz12.symm).symm
        | exact absurd hij (hz23)
        | exact absurd hij (hz23).symm
        | exact absurd hij ((ht_z z2 hzm2).symm)
        | exact absurd hij ((ht_z z2 hzm2).symm).symm
        | exact absurd hij ((hsp_z sp1 hsp1 z3 hzm3).symm)
        | exact absurd hij ((hsp_z sp1 hsp1 z3 hzm3).symm).symm
        | exact absurd hij ((hsp_z sp2 hsp2 z3 hzm3).symm)
        | exact absurd hij ((hsp_z sp2 hsp2 z3 hzm3).symm).symm
        | exact absurd hij ((hy_z y1 hym1 z3 hzm3).symm)
        | exact absurd hij ((hy_z y1 hym1 z3 hzm3).symm).symm
        | exact absurd hij ((hy_z y2 hym2 z3 hzm3).symm)
        | exact absurd hij ((hy_z y2 hym2 z3 hzm3).symm).symm
        | exact absurd hij ((hs_z z3 hzm3).symm)
        | exact absurd hij ((hs_z z3 hzm3).symm).symm
        | exact absurd hij (hz13.symm)
        | exact absurd hij (hz13.symm).symm
        | exact absurd hij (hz23.symm)
        | exact absurd hij (hz23.symm).symm
        | exact absurd hij ((ht_z z3 hzm3).symm)
        | exact absurd hij ((ht_z z3 hzm3).symm).symm
        | exact absurd hij (ht_sp sp1 hsp1)
        | exact absurd hij (ht_sp sp1 hsp1).symm
        | exact absurd hij (ht_sp sp2 hsp2)
        | exact absurd hij (ht_sp sp2 hsp2).symm
        | exact absurd hij (ht_y y1 hym1)
        | exact absurd hij (ht_y y1 hym1).symm
        | exact absurd hij (ht_y y2 hym2)
        | exact absurd hij (ht_y y2 hym2).symm
        | exact absurd hij (hst.symm)
        | exact absurd hij (hst.symm).symm
        | exact absurd hij (ht_z z1 hzm1)
        | exact absurd hij (ht_z z1 hzm1).symm
        | exact absurd hij (ht_z z2 hzm2)
        | exact absurd hij (ht_z z2 hzm2).symm
        | exact absurd hij (ht_z z3 hzm3)
        | exact absurd hij (ht_z z3 hzm3).symm
  let e := Equiv.ofBijective f ((Finite.injective_iff_bijective).mp hinj)
  have hψ : ∀ i j : Fin 9, J.Adj (f i) (f j) ↔ base9A2.Adj i j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [hf, Fin.isValue, if_true, if_false, reduceIte, reduceCtorEq] <;>
      first
        | (refine iff_of_true ?_ (by decide); first
            | exact hspz sp1 hsp1 z1 hzm1
            | exact hspz sp1 hsp1 z2 hzm2
            | exact hspz sp1 hsp1 z3 hzm3
            | exact (htsp sp1 hsp1).symm
            | exact hspz sp2 hsp2 z1 hzm1
            | exact hspz sp2 hsp2 z2 hzm2
            | exact hspz sp2 hsp2 z3 hzm3
            | exact (htsp sp2 hsp2).symm
            | exact (hsy y1 hym1).symm
            | exact hyz y1 hym1 z1 hzm1
            | exact hyz y1 hym1 z2 hzm2
            | exact hyz y1 hym1 z3 hzm3
            | exact (hsy y2 hym2).symm
            | exact hyz y2 hym2 z1 hzm1
            | exact hyz y2 hym2 z2 hzm2
            | exact hyz y2 hym2 z3 hzm3
            | exact hsy y1 hym1
            | exact hsy y2 hym2
            | exact hst_adj
            | exact (hspz sp1 hsp1 z1 hzm1).symm
            | exact (hspz sp2 hsp2 z1 hzm1).symm
            | exact (hyz y1 hym1 z1 hzm1).symm
            | exact (hyz y2 hym2 z1 hzm1).symm
            | exact (hspz sp1 hsp1 z2 hzm2).symm
            | exact (hspz sp2 hsp2 z2 hzm2).symm
            | exact (hyz y1 hym1 z2 hzm2).symm
            | exact (hyz y2 hym2 z2 hzm2).symm
            | exact (hspz sp1 hsp1 z3 hzm3).symm
            | exact (hspz sp2 hsp2 z3 hzm3).symm
            | exact (hyz y1 hym1 z3 hzm3).symm
            | exact (hyz y2 hym2 z3 hzm3).symm
            | exact htsp sp1 hsp1
            | exact htsp sp2 hsp2
            | exact hst_adj.symm)
        | (refine iff_of_false ?_ (by decide); first
            | exact (fun h => (J.ne_of_adj h) rfl)
            | exact hspindep sp1 hsp1 sp2 hsp2 hsp12
            | exact hnspy sp1 hsp1 y1 hym1
            | exact hnspy sp1 hsp1 y2 hym2
            | exact (fun h => hnssp sp1 hsp1 h.symm)
            | exact hspindep sp2 hsp2 sp1 hsp1 hsp12.symm
            | exact hnspy sp2 hsp2 y1 hym1
            | exact hnspy sp2 hsp2 y2 hym2
            | exact (fun h => hnssp sp2 hsp2 h.symm)
            | exact (fun h => hnspy sp1 hsp1 y1 hym1 h.symm)
            | exact (fun h => hnspy sp2 hsp2 y1 hym1 h.symm)
            | exact hyindep y1 hym1 y2 hym2 hy12
            | exact (fun h => hnty y1 hym1 h.symm)
            | exact (fun h => hnspy sp1 hsp1 y2 hym2 h.symm)
            | exact (fun h => hnspy sp2 hsp2 y2 hym2 h.symm)
            | exact hyindep y2 hym2 y1 hym1 hy12.symm
            | exact (fun h => hnty y2 hym2 h.symm)
            | exact hnssp sp1 hsp1
            | exact hnssp sp2 hsp2
            | exact hnsz z1 hzm1
            | exact hnsz z2 hzm2
            | exact hnsz z3 hzm3
            | exact (fun h => hnsz z1 hzm1 h.symm)
            | exact hzindep z1 hzm1 z2 hzm2 hz12
            | exact hzindep z1 hzm1 z3 hzm3 hz13
            | exact (fun h => hntz z1 hzm1 h.symm)
            | exact (fun h => hnsz z2 hzm2 h.symm)
            | exact hzindep z2 hzm2 z1 hzm1 hz12.symm
            | exact hzindep z2 hzm2 z3 hzm3 hz23
            | exact (fun h => hntz z2 hzm2 h.symm)
            | exact (fun h => hnsz z3 hzm3 h.symm)
            | exact hzindep z3 hzm3 z1 hzm1 hz13.symm
            | exact hzindep z3 hzm3 z2 hzm2 hz23.symm
            | exact (fun h => hntz z3 hzm3 h.symm)
            | exact hnty y1 hym1
            | exact hnty y2 hym2
            | exact hntz z1 hzm1
            | exact hntz z2 hzm2
            | exact hntz z3 hzm3)
  refine ⟨e.symm, fun u v => ?_⟩
  have hu : f (e.symm u) = u := e.apply_symm_apply u
  have hv : f (e.symm v) = v := e.apply_symm_apply v
  have h := hψ (e.symm u) (e.symm v)
  rw [hu, hv] at h
  exact h

/-- **The (2,9) base classification** (TARGET — the last base step). The degree sequence is forced
to `[2,4⁸]` or `[3,3,4⁷]` (`base_maxdeg_le_four` + `base_sum_degrees`); the two shapes are pinned by
`base_classification_deg2`/`base_classification_deg3`. -/
theorem base_classification (J : SimpleGraph (Fin 9)) (hK3 : J.CliqueFree 3)
    (hα : alphaAtMost J 4) (he : edgeCountIn J Finset.univ = 17) :
    ∃ σ : Fin 9 ≃ Fin 9,
      (∀ a b, J.Adj a b ↔ base9A2.Adj (σ a) (σ b)) ∨
      (∀ a b, J.Adj a b ↔ base9A1.Adj (σ a) (σ b)) := by
  have hsum : ∑ v, J.degree v = 34 := base_sum_degrees J he
  have hmax : ∀ v, J.degree v ≤ 4 := fun v => base_maxdeg_le_four J hK3 hα v
  -- minimum degree ≥ 2
  have hmin : ∀ v, 2 ≤ J.degree v := by
    intro v0
    by_contra hlt; push_neg at hlt
    have hrest : ∑ v ∈ Finset.univ.erase v0, J.degree v ≤ 32 := by
      calc ∑ v ∈ Finset.univ.erase v0, J.degree v ≤ ∑ _v ∈ Finset.univ.erase v0, 4 :=
            Finset.sum_le_sum (fun v _ => hmax v)
        _ = 32 := by
            rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
              Fintype.card_fin, smul_eq_mul]
    have hae : J.degree v0 + ∑ v ∈ Finset.univ.erase v0, J.degree v = ∑ v, J.degree v :=
      Finset.add_sum_erase Finset.univ (fun v => J.degree v) (Finset.mem_univ v0)
    omega
  by_cases hdeg2 : ∃ a, J.degree a = 2
  · -- [2,4⁸] case
    obtain ⟨a, ha2⟩ := hdeg2
    have hother : ∀ v, v ≠ a → J.degree v = 4 := by
      have hsum_erase : ∑ v ∈ Finset.univ.erase a, J.degree v = 32 := by
        have hae : J.degree a + ∑ v ∈ Finset.univ.erase a, J.degree v = ∑ v, J.degree v :=
          Finset.add_sum_erase Finset.univ (fun v => J.degree v) (Finset.mem_univ a)
        omega
      intro v0 hv0
      by_contra hne
      have hlt4 : J.degree v0 < 4 := lt_of_le_of_ne (hmax v0) hne
      have hv0mem : v0 ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hv0, Finset.mem_univ _⟩
      have hlt : ∑ v ∈ Finset.univ.erase a, J.degree v < ∑ _v ∈ Finset.univ.erase a, 4 :=
        Finset.sum_lt_sum (fun v _ => hmax v) ⟨v0, hv0mem, hlt4⟩
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin, smul_eq_mul] at hlt
      omega
    obtain ⟨p, q, hpq_ne, hNa⟩ := Finset.card_eq_two.mp
      (by rw [J.card_neighborFinset_eq_degree]; exact ha2)
    obtain ⟨σ, hσ⟩ := base_classification_deg2 J hK3 hα a p q hNa hpq_ne hother
    exact ⟨σ, Or.inr hσ⟩
  · -- [3,3,4⁷] case
    push_neg at hdeg2
    -- every degree ∈ {3,4}
    have hdeg34 : ∀ v, J.degree v = 3 ∨ J.degree v = 4 := by
      intro v; have := hmin v; have := hmax v; have := hdeg2 v; omega
    -- count degree-3 vertices = 2
    set three := Finset.univ.filter (fun v => J.degree v = 3) with hthreedef
    have hthree : three.card = 2 := by
      have hdefic : ∑ v, (4 - J.degree v) = 2 := by
        have h1 : ∑ v, ((4 - J.degree v) + J.degree v) = ∑ _v : Fin 9, 4 :=
          Finset.sum_congr rfl (fun v _ => by have := hmax v; omega)
        rw [Finset.sum_add_distrib, hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul] at h1
        omega
      have hind : ∀ v, (4 - J.degree v) = if J.degree v = 3 then 1 else 0 := by
        intro v; rcases hdeg34 v with h | h <;> simp [h]
      rw [Finset.sum_congr rfl (fun v _ => hind v), Finset.sum_boole] at hdefic
      rw [hthreedef]; exact_mod_cast hdefic
    obtain ⟨s, t, hst, hthreeeq⟩ := Finset.card_eq_two.mp hthree
    have hs3 : J.degree s = 3 := by
      have : s ∈ three := by rw [hthreeeq]; exact Finset.mem_insert_self _ _
      rw [hthreedef, Finset.mem_filter] at this; exact this.2
    have ht3 : J.degree t = 3 := by
      have : t ∈ three := by rw [hthreeeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      rw [hthreedef, Finset.mem_filter] at this; exact this.2
    have hother : ∀ v, v ≠ s → v ≠ t → J.degree v = 4 := by
      intro v hvs hvt
      rcases hdeg34 v with h | h
      · exfalso
        have hvthree : v ∈ three := by rw [hthreedef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩
        rw [hthreeeq, Finset.mem_insert, Finset.mem_singleton] at hvthree
        exact hvthree.elim hvs hvt
      · exact h
    obtain ⟨σ, hσ⟩ := base_classification_deg3 J hK3 hα he s t hst hs3 ht3 hother
    exact ⟨σ, Or.inl hσ⟩

end Erdos617
