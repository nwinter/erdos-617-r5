/-
Erdős Problem 617, r = 5 — milestone F4: the counting machinery of
review_queue/mh2-gpt56-candidate.md §4.

We formalize, for a graph `G` on `Fin q`:

* the double-counting identity (4.1)/(4.2):
    `(∑ v, e(G[W_v])) + ∑ v, (deg v)^2 = q * e(G) + ∑ v, e(G[N(v)])`,
  where `W_v = univ \ (insert v (N v))`, together with its triangle form
    `... = q * e(G) + 3 * #(triangles)`;
* the cap-11 neighbourhood bound (4.3):
    every 6-set spanning ≤ 11 edges forces `10 * e(G[N v]) ≤ 3 * d * (d-1)`
  for a vertex of degree `d ≥ 5`;
* two elementary facts about `edgeCountIn` used throughout the campaign.

`edgeCountIn` and `card_offdiag` are imported from `Lean617.Statements`; see
FORMAL.md for the elimination plan (this is F4).

Research project: Mathlib style linters disabled.
-/
import Lean617.Statements

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.style.multiGoal false
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false

open Finset
open scoped Classical

namespace Erdos617

variable {q : ℕ} (G : SimpleGraph (Fin q))

/-! ## Elementary facts about `edgeCountIn` -/

/-- Edge count is monotone in the vertex set. -/
theorem edgeCountIn_mono {S S' : Finset (Fin q)} (h : S ⊆ S') :
    edgeCountIn G S ≤ edgeCountIn G S' := by
  unfold edgeCountIn
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact Finset.sym2_mono h

/-- Trivial upper bound: at most `C(|S|, 2)` edges inside `S`. -/
theorem edgeCountIn_le_choose_two (S : Finset (Fin q)) :
    edgeCountIn G S ≤ S.card.choose 2 := by
  rw [← card_offdiag S]
  unfold edgeCountIn
  apply Finset.card_le_card
  intro e he
  rw [Finset.mem_filter] at he ⊢
  refine ⟨he.1, ?_⟩
  exact G.not_isDiag_of_mem_edgeSet he.2

/-- `edgeCountIn` counted from the edge side: the `G`-edges lying inside `S`. -/
theorem edgeCountIn_eq_filter_edgeFinset (S : Finset (Fin q)) :
    edgeCountIn G S = (G.edgeFinset.filter (fun e => e ∈ S.sym2)).card := by
  unfold edgeCountIn
  apply Finset.card_bij (fun e _ => e)
  · intro e he
    rw [Finset.mem_filter] at he ⊢
    exact ⟨G.mem_edgeFinset.mpr he.2, he.1⟩
  · intro a _ b _ hab; exact hab
  · intro e he
    rw [Finset.mem_filter] at he
    exact ⟨e, by rw [Finset.mem_filter]; exact ⟨he.2, G.mem_edgeFinset.mp he.1⟩, rfl⟩

/-- Total edge count via `edgeFinset`. -/
theorem edgeCountIn_univ_eq_card_edgeFinset :
    edgeCountIn G Finset.univ = G.edgeFinset.card := by
  unfold edgeCountIn
  rw [Finset.sym2_univ]
  congr 1
  ext e
  simp [G.mem_edgeFinset]

/-! ## The complementary-closed-neighbourhood set `W_v`

`W_v = V \ (N[v]) = univ \ (insert v (N v))`, the vertices that are neither `v`
nor adjacent to `v`. This is the set `W_v` of §4 of the informal proof. -/

/-- `W_v`: the vertices that are neither `v` nor adjacent to `v`. -/
noncomputable def complClosedNbhd (v : Fin q) : Finset (Fin q) :=
  Finset.univ \ insert v (G.neighborFinset v)

@[simp] theorem mem_complClosedNbhd {v x : Fin q} :
    x ∈ complClosedNbhd G v ↔ x ≠ v ∧ ¬ G.Adj v x := by
  unfold complClosedNbhd
  rw [Finset.mem_sdiff, Finset.mem_insert, G.mem_neighborFinset]
  simp only [Finset.mem_univ, true_and, not_or]

/-! ## The double-counting swap

For any vertex-indexed family `T`, the total `∑_v e(G[T v])` can be reorganised
as a sum over the edges of `G` of the number of vertices `v` whose set `T v`
contains that edge. Applying this to `T = W` and `T = N` is the heart of (4.1). -/

/-- Swap the order of summation: sum an edge count over all vertices by counting,
for each edge, how many vertices `v` have both endpoints in `T v`. -/
theorem sum_edgeCountIn_swap (T : Fin q → Finset (Fin q)) :
    ∑ v, edgeCountIn G (T v)
      = ∑ e ∈ G.edgeFinset, (Finset.univ.filter (fun v => e ∈ (T v).sym2)).card := by
  simp_rw [edgeCountIn_eq_filter_edgeFinset, Finset.card_filter]
  exact Finset.sum_comm

/-- For an edge `s(x,y)`, both endpoints lie in `W_v` iff `v` is adjacent to
neither `x` nor `y` (the endpoint-`≠`-`v` conditions are automatic for an edge). -/
theorem mem_sym2_complClosedNbhd_edge {x y v : Fin q} (hadj : G.Adj x y) :
    s(x, y) ∈ (complClosedNbhd G v).sym2 ↔ ¬ G.Adj v x ∧ ¬ G.Adj v y := by
  rw [Finset.mk_mem_sym2_iff, mem_complClosedNbhd, mem_complClosedNbhd]
  constructor
  · rintro ⟨⟨_, h1⟩, _, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun h => h2 (h ▸ hadj), h1⟩, fun h => h1 (G.symm (h ▸ hadj)), h2⟩

/-- For an edge `s(x,y)`, both endpoints lie in `N v` iff `v` is adjacent to both. -/
theorem mem_sym2_neighborFinset {x y v : Fin q} :
    s(x, y) ∈ (G.neighborFinset v).sym2 ↔ G.Adj v x ∧ G.Adj v y := by
  rw [Finset.mk_mem_sym2_iff, G.mem_neighborFinset, G.mem_neighborFinset]

/-- Per-edge count (inclusion–exclusion on neighbourhoods): for any `x, y`, the
number of `v` adjacent to neither, plus the two degrees, equals `q` plus the
number of common neighbours. (No edge hypothesis is needed.) -/
theorem per_edge_count (x y : Fin q) :
    (Finset.univ.filter (fun v => ¬ G.Adj v x ∧ ¬ G.Adj v y)).card + G.degree x + G.degree y
      = q + (Finset.univ.filter (fun v => G.Adj v x ∧ G.Adj v y)).card := by
  have hneither : (Finset.univ.filter (fun v => ¬ G.Adj v x ∧ ¬ G.Adj v y))
      = Finset.univ \ (G.neighborFinset x ∪ G.neighborFinset y) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
      Finset.mem_union, G.mem_neighborFinset, not_or, G.adj_comm x v, G.adj_comm y v]
  have hboth : (Finset.univ.filter (fun v => G.Adj v x ∧ G.Adj v y))
      = G.neighborFinset x ∩ G.neighborFinset y := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
      G.mem_neighborFinset, G.adj_comm x v, G.adj_comm y v]
  rw [hneither, hboth]
  have h1 := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (G.neighborFinset x ∪ G.neighborFinset y))
  rw [Finset.card_univ, Fintype.card_fin] at h1
  have h2 := Finset.card_union_add_card_inter (G.neighborFinset x) (G.neighborFinset y)
  rw [G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at h2
  omega

/-- Number of `G`-edges incident to `w` equals the degree of `w`. -/
theorem card_edgeFinset_filter_mem (w : Fin q) :
    (G.edgeFinset.filter (fun e => w ∈ e)).card = G.degree w := by
  rw [← G.card_incidenceFinset_eq_degree, G.incidenceFinset_eq_filter]

/-- Handshake-type identity: summing `deg x + deg y` over all edges `xy` gives
`∑_v (deg v)^2`. Phrased with `∑_w [w ∈ e] deg w` so the endpoint sum is
well-defined on `Sym2`. -/
theorem sum_endpointDeg_eq_sum_sq_degree :
    ∑ e ∈ G.edgeFinset, (∑ w, if w ∈ e then G.degree w else 0)
      = ∑ v, (G.degree v) ^ 2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul,
    card_edgeFinset_filter_mem G w, pow_two]

/-! ## The main counting identity (4.1)/(4.2)

The key double count of §4, in the triangle-free form used by F5:
`(∑ v, e(G[W_v])) + ∑ v, (deg v)^2 = q * e(G) + ∑ v, e(G[N v])`. Rearranged
this is `∑ v, (e(W_v) − e(N v)) = q·e(G) − ∑ v (deg v)^2`. -/

/-- **Identity (4.1)/(4.2), triangle-free form.** This is the version F5 consumes
(no triangle count appears; `∑ v, e(G[N v])` plays the role of `3τ`). -/
theorem sum_edgeCountIn_compl_nbhd_add_sq_deg :
    (∑ v, edgeCountIn G (complClosedNbhd G v)) + ∑ v, (G.degree v) ^ 2
      = q * G.edgeFinset.card + ∑ v, edgeCountIn G (G.neighborFinset v) := by
  rw [sum_edgeCountIn_swap G (complClosedNbhd G),
    sum_edgeCountIn_swap G (fun v => G.neighborFinset v),
    ← sum_endpointDeg_eq_sum_sq_degree G]
  rw [show q * G.edgeFinset.card = ∑ _e ∈ G.edgeFinset, q from by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e he => ?_
  revert he
  induction e using Sym2.ind with
  | _ x y =>
    intro he
    have hadj : G.Adj x y := by
      rw [← SimpleGraph.mem_edgeSet]; exact G.mem_edgeFinset.mp he
    have hxy : x ≠ y := G.ne_of_adj hadj
    rw [Finset.filter_congr (fun v (_ : v ∈ univ) => mem_sym2_complClosedNbhd_edge G hadj),
      Finset.filter_congr (fun v (_ : v ∈ univ) => mem_sym2_neighborFinset G)]
    have hcD : (∑ w, if w ∈ (s(x, y) : Sym2 (Fin q)) then G.degree w else 0)
        = G.degree x + G.degree y := by
      rw [← Finset.sum_filter]
      have hpair : (univ.filter (fun w => w ∈ (s(x, y) : Sym2 (Fin q)))) = {x, y} := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mem_iff,
          Finset.mem_insert, Finset.mem_singleton]
      rw [hpair, Finset.sum_pair hxy]
    rw [hcD]
    have := per_edge_count G x y
    omega

/-- **Identity (4.2).** Summing the neighbourhood edge counts is three times the
number of triangles. Proof by double counting incidences between edges and
triangles (`Finset.bipartiteAbove`/`bipartiteBelow`): each triangle contains 3
edges, and each edge `e` lies in the neighbourhood of exactly the vertices `v`
that complete `e` to a triangle. -/
theorem three_mul_card_cliqueFinset_three :
    3 * (G.cliqueFinset 3).card = ∑ v, edgeCountIn G (G.neighborFinset v) := by
  rw [sum_edgeCountIn_swap G (fun v => G.neighborFinset v)]
  let r : Finset (Fin q) → Sym2 (Fin q) → Prop := fun t e => e ∈ t.sym2
  calc
    3 * (G.cliqueFinset 3).card =
        ∑ t ∈ G.cliqueFinset 3, #(G.edgeFinset.bipartiteAbove r t) := by
          rw [show 3 * (G.cliqueFinset 3).card =
            ∑ _t ∈ G.cliqueFinset 3, 3 by
              rw [Finset.sum_const, smul_eq_mul, mul_comm]]
          apply Finset.sum_congr rfl
          intro t ht
          rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.is3Clique_iff] at ht
          obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ht
          have hset : G.edgeFinset.bipartiteAbove r ({a,b,c} : Finset (Fin q))
              = {s(a,b), s(a,c), s(b,c)} := by
            ext e
            induction e using Sym2.ind with
            | _ x y =>
              simp only [Finset.mem_bipartiteAbove, SimpleGraph.mem_edgeFinset,
                SimpleGraph.mem_edgeSet, r, Finset.mk_mem_sym2_iff,
                Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
              constructor
              · rintro ⟨hxy, hx, hy⟩
                rcases hx with rfl | rfl | rfl <;>
                  rcases hy with rfl | rfl | rfl
                all_goals simp_all [G.adj_comm]
              · intro h
                rcases h with hab' | hac' | hbc' | hcb'
                · rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                  · exact ⟨hab, by simp, by simp⟩
                  · exact ⟨G.symm hab, by simp, by simp⟩
                · rcases hac' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                  · exact ⟨hac, by simp, by simp⟩
                  · exact ⟨G.symm hac, by simp, by simp⟩
                · rcases hbc' with ⟨rfl, rfl⟩
                  exact ⟨hbc, by simp, by simp⟩
                · rcases hcb' with ⟨rfl, rfl⟩
                  exact ⟨G.symm hbc, by simp, by simp⟩
          rw [hset, eq_comm]
          refine Finset.card_eq_three.2 ⟨_, _, _, ?_, ?_, ?_, rfl⟩ <;>
            simp [hab.ne, hac.ne, hbc.ne]
    _ = ∑ e ∈ G.edgeFinset, #((G.cliqueFinset 3).bipartiteBelow r e) :=
      Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow r
    _ = ∑ e ∈ G.edgeFinset,
        #(Finset.univ.filter (fun v => e ∈ (G.neighborFinset v).sym2)) := by
          apply Finset.sum_congr rfl
          intro e he
          induction e using Sym2.ind with
          | _ x y =>
            have hadj : G.Adj x y := by
              rw [← SimpleGraph.mem_edgeSet]
              exact G.mem_edgeFinset.mp he
            symm
            apply Finset.card_bij (fun v _ => ({v,x,y} : Finset (Fin q)))
            · intro v hv
              rw [Finset.mem_filter] at hv
              rw [Finset.mem_bipartiteBelow]
              refine ⟨SimpleGraph.mem_cliqueFinset_iff.mpr
                (SimpleGraph.is3Clique_triple_iff.mpr ?_), ?_⟩
              · exact ⟨(mem_sym2_neighborFinset G).mp hv.2 |>.1,
                  (mem_sym2_neighborFinset G).mp hv.2 |>.2, hadj⟩
              · simp [r]
            · intro v hv w hw hvw
              rw [Finset.mem_filter] at hv
              have hvadj := (mem_sym2_neighborFinset G).mp hv.2
              have hvmem : v ∈ ({w,x,y} : Finset (Fin q)) := by
                rw [← hvw]
                simp
              simpa [hvadj.1.ne, hvadj.2.ne] using hvmem
            · intro t ht
              rw [Finset.mem_bipartiteBelow] at ht
              rcases ht with ⟨hcl, hxy⟩
              rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.is3Clique_iff] at hcl
              obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := hcl
              simp only [r, Finset.mk_mem_sym2_iff] at hxy
              simp only [Finset.mem_insert, Finset.mem_singleton] at hxy
              rcases hxy.1 with rfl | rfl | rfl <;>
                rcases hxy.2 with rfl | rfl | rfl
              all_goals simp_all [SimpleGraph.adj_comm]
              all_goals aesop

/-- **Identity (4.1), triangle form.** Immediate from the triangle-free identity
and (4.2). -/
theorem sum_edgeCountIn_compl_nbhd :
    (∑ v, edgeCountIn G (complClosedNbhd G v)) + ∑ v, (G.degree v) ^ 2
      = q * G.edgeFinset.card + 3 * (G.cliqueFinset 3).card := by
  rw [sum_edgeCountIn_compl_nbhd_add_sq_deg, three_mul_card_cliqueFinset_three]

/-! ## The cap-11 neighbourhood bound (4.3) -/

/-- Counting 5-subsets of `s` that contain a fixed pair `{x,y} ⊆ s`: there are
`C(|s|-2, 3)` of them (choose the other three vertices). Bijection with the
3-subsets of `s \ {x,y}`. -/
theorem card_powersetCard_five_filter_pair {s : Finset (Fin q)} {x y : Fin q}
    (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) :
    ((s.powersetCard 5).filter (fun A => x ∈ A ∧ y ∈ A)).card = (s.card - 2).choose 3 := by
  have hpair_sub : ({x, y} : Finset (Fin q)) ⊆ s := by
    intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have hcard2 : (s \ ({x, y} : Finset (Fin q))).card = s.card - 2 := by
    rw [Finset.card_sdiff_of_subset hpair_sub, Finset.card_pair hxy]
  rw [← hcard2, ← Finset.card_powersetCard]
  apply Finset.card_bij'
    (fun A _ => A \ ({x, y} : Finset (Fin q)))
    (fun B _ => insert x (insert y B))
  · intro A hA
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hA ⊢
    obtain ⟨⟨hAsub, hAcard⟩, hxA, hyA⟩ := hA
    have hpair_subA : ({x, y} : Finset (Fin q)) ⊆ A := by
      intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hxA
      · exact hyA
    refine ⟨Finset.sdiff_subset_sdiff hAsub subset_rfl, ?_⟩
    rw [Finset.card_sdiff_of_subset hpair_subA, Finset.card_pair hxy, hAcard]
  · intro B hB
    simp only [Finset.mem_powersetCard] at hB
    obtain ⟨hBsub, hBcard⟩ := hB
    have hxB : x ∉ B := fun h => (Finset.mem_sdiff.mp (hBsub h)).2 (by simp)
    have hyB : y ∉ B := fun h => (Finset.mem_sdiff.mp (hBsub h)).2 (by simp)
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨?_, ?_⟩, Finset.mem_insert_self x _,
      Finset.mem_insert_of_mem (Finset.mem_insert_self y B)⟩
    · intro z hz
      simp only [Finset.mem_insert] at hz
      rcases hz with rfl | rfl | hz
      · exact hx
      · exact hy
      · exact (Finset.mem_sdiff.mp (hBsub hz)).1
    · rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, not_or]; exact ⟨hxy, hxB⟩),
        Finset.card_insert_of_notMem hyB, hBcard]
  · intro A hA
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hA
    obtain ⟨⟨_, _⟩, hxA, hyA⟩ := hA
    ext z
    simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl | ⟨hz, _⟩)
      · exact hxA
      · exact hyA
      · exact hz
    · intro hz
      by_cases h1 : z = x
      · exact Or.inl h1
      · by_cases h2 : z = y
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr ⟨hz, by simp [h1, h2]⟩)
  · intro B hB
    simp only [Finset.mem_powersetCard] at hB
    have hxB : x ∉ B := fun h => (Finset.mem_sdiff.mp (hB.1 h)).2 (by simp)
    have hyB : y ∉ B := fun h => (Finset.mem_sdiff.mp (hB.1 h)).2 (by simp)
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · rintro ⟨rfl | rfl | hz, hnot⟩
      · exact absurd rfl hnot.1
      · exact absurd rfl hnot.2
      · exact hz
    · intro hz
      exact ⟨Or.inr (Or.inr hz), fun h => hxB (h ▸ hz), fun h => hyB (h ▸ hz)⟩

/-- Step 1 of (4.3): adding `v` to a set `A ⊆ N v` adds exactly `|A|` spoke edges,
so `e(G[A]) + |A| ≤ e(G[A ∪ {v}])`. -/
theorem edgeCountIn_add_card_le_insert {v : Fin q} {A : Finset (Fin q)}
    (hA : A ⊆ G.neighborFinset v) (hvA : v ∉ A) :
    edgeCountIn G A + A.card ≤ edgeCountIn G (insert v A) := by
  set spokes := A.image (fun w => s(v, w)) with hsp
  have hinj : Set.InjOn (fun w => s(v, w)) A := by
    intro a ha b hb hab
    simp only [Sym2.eq_iff] at hab
    rcases hab with ⟨_, h⟩ | ⟨_, hav⟩
    · exact h
    · exact absurd (hav ▸ (Finset.mem_coe.mp ha)) hvA
  have hspoke_card : spokes.card = A.card := by
    rw [hsp, Finset.card_image_of_injOn hinj]
  have hsub : (A.sym2.filter (fun e => e ∈ G.edgeSet)) ∪ spokes
      ⊆ (insert v A).sym2.filter (fun e => e ∈ G.edgeSet) := by
    intro e he
    rw [Finset.mem_union] at he
    rw [Finset.mem_filter]
    rcases he with he | he
    · rw [Finset.mem_filter] at he
      exact ⟨Finset.sym2_mono (Finset.subset_insert v A) he.1, he.2⟩
    · rw [hsp, Finset.mem_image] at he
      obtain ⟨w, hw, rfl⟩ := he
      refine ⟨?_, ?_⟩
      · rw [Finset.mk_mem_sym2_iff]
        exact ⟨Finset.mem_insert_self v A, Finset.mem_insert_of_mem hw⟩
      · rw [SimpleGraph.mem_edgeSet]
        exact (G.mem_neighborFinset v w).mp (hA hw)
  have hdisj : Disjoint (A.sym2.filter (fun e => e ∈ G.edgeSet)) spokes := by
    rw [Finset.disjoint_left]
    intro e he hesp
    rw [Finset.mem_filter] at he
    rw [hsp, Finset.mem_image] at hesp
    obtain ⟨w, hw, hwe⟩ := hesp
    have := he.1
    rw [← hwe, Finset.mk_mem_sym2_iff] at this
    exact hvA this.1
  calc edgeCountIn G A + A.card
      = (A.sym2.filter (fun e => e ∈ G.edgeSet)).card + spokes.card := by
        unfold edgeCountIn; rw [hspoke_card]
    _ = ((A.sym2.filter (fun e => e ∈ G.edgeSet)) ∪ spokes).card :=
        (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ ((insert v A).sym2.filter (fun e => e ∈ G.edgeSet)).card := Finset.card_le_card hsub
    _ = edgeCountIn G (insert v A) := rfl

/-- Step 2 of (4.3): double count over the 5-subsets of `N v`. Each edge of
`G[N v]` lies in exactly `C(d-2,3)` of them. -/
theorem sum_powersetCard_edgeCountIn {v : Fin q} {d : ℕ}
    (hNv : (G.neighborFinset v).card = d) :
    ∑ A ∈ (G.neighborFinset v).powersetCard 5, edgeCountIn G A
      = edgeCountIn G (G.neighborFinset v) * (d - 2).choose 3 := by
  have hstep : ∀ e ∈ G.edgeFinset,
      (((G.neighborFinset v).powersetCard 5).filter (fun A => e ∈ A.sym2)).card
        = if e ∈ (G.neighborFinset v).sym2 then (d - 2).choose 3 else 0 := by
    intro e
    induction e using Sym2.ind with
    | _ x y =>
      intro he
      have hadj : G.Adj x y := by rw [← SimpleGraph.mem_edgeSet]; exact G.mem_edgeFinset.mp he
      have hxy : x ≠ y := G.ne_of_adj hadj
      by_cases hmem : s(x, y) ∈ (G.neighborFinset v).sym2
      · rw [if_pos hmem]
        rw [Finset.mk_mem_sym2_iff] at hmem
        rw [show (((G.neighborFinset v).powersetCard 5).filter (fun A => s(x, y) ∈ A.sym2))
              = ((G.neighborFinset v).powersetCard 5).filter (fun A => x ∈ A ∧ y ∈ A) from
            Finset.filter_congr (fun A _ => Finset.mk_mem_sym2_iff)]
        rw [← hNv]
        exact card_powersetCard_five_filter_pair hmem.1 hmem.2 hxy
      · rw [if_neg hmem, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro A hA hcontra
        rw [Finset.mk_mem_sym2_iff] at hcontra
        rw [Finset.mem_powersetCard] at hA
        exact hmem (Finset.mk_mem_sym2_iff.mpr ⟨hA.1 hcontra.1, hA.1 hcontra.2⟩)
  calc ∑ A ∈ (G.neighborFinset v).powersetCard 5, edgeCountIn G A
      = ∑ e ∈ G.edgeFinset,
          (((G.neighborFinset v).powersetCard 5).filter (fun A => e ∈ A.sym2)).card := by
        simp_rw [edgeCountIn_eq_filter_edgeFinset, Finset.card_filter]
        rw [Finset.sum_comm]
    _ = ∑ e ∈ G.edgeFinset, if e ∈ (G.neighborFinset v).sym2 then (d - 2).choose 3 else 0 :=
        Finset.sum_congr rfl hstep
    _ = edgeCountIn G (G.neighborFinset v) * (d - 2).choose 3 := by
        rw [edgeCountIn_eq_filter_edgeFinset, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]

/-- **Neighbourhood bound (4.3).** If every 6-set spans at most 11 edges, then a
vertex of degree `d ≥ 5` has at most `⌊3d(d-1)/10⌋` edges among its neighbours;
stated in the floor-free form `10 * e(G[N v]) ≤ 3d(d-1)`. -/
theorem nbhd_bound_cap11
    (hcap : ∀ S : Finset (Fin q), S.card = 6 → edgeCountIn G S ≤ 11)
    {v : Fin q} {d : ℕ} (hd : G.degree v = d) (hd5 : 5 ≤ d) :
    10 * edgeCountIn G (G.neighborFinset v) ≤ 3 * d * (d - 1) := by
  have hNv : (G.neighborFinset v).card = d := by rw [G.card_neighborFinset_eq_degree, hd]
  set e := edgeCountIn G (G.neighborFinset v) with he_def
  have hvNv : v ∉ G.neighborFinset v := by simp [SimpleGraph.mem_neighborFinset]
  -- Step 1: every 5-subset A of N v has edgeCountIn G A ≤ 6.
  have hstep1 : ∀ A ∈ (G.neighborFinset v).powersetCard 5, edgeCountIn G A ≤ 6 := by
    intro A hA
    rw [Finset.mem_powersetCard] at hA
    obtain ⟨hAsub, hAcard⟩ := hA
    have hvA : v ∉ A := fun h => hvNv (hAsub h)
    have hins_card : (insert v A).card = 6 := by
      rw [Finset.card_insert_of_notMem hvA, hAcard]
    have hb := edgeCountIn_add_card_le_insert G hAsub hvA
    rw [hAcard] at hb
    have := hcap (insert v A) hins_card
    omega
  -- Steps 2–3: double count and bound.
  have hsum : ∑ A ∈ (G.neighborFinset v).powersetCard 5, edgeCountIn G A = e * (d - 2).choose 3 :=
    sum_powersetCard_edgeCountIn G hNv
  have hsum_le : ∑ A ∈ (G.neighborFinset v).powersetCard 5, edgeCountIn G A ≤ 6 * d.choose 5 := by
    calc ∑ A ∈ (G.neighborFinset v).powersetCard 5, edgeCountIn G A
        ≤ ∑ _A ∈ (G.neighborFinset v).powersetCard 5, 6 := Finset.sum_le_sum hstep1
      _ = ((G.neighborFinset v).powersetCard 5).card * 6 := by rw [Finset.sum_const, smul_eq_mul]
      _ = d.choose 5 * 6 := by rw [Finset.card_powersetCard, hNv]
      _ = 6 * d.choose 5 := by ring
  have hkey : e * (d - 2).choose 3 ≤ 6 * d.choose 5 := by rw [← hsum]; exact hsum_le
  -- Arithmetic: 60·C(d,5) = 3d(d-1)·C(d-2,3), and C(d-2,3) > 0.
  have hpos : 0 < (d - 2).choose 3 := Nat.choose_pos (by omega)
  have hcm : d.choose 5 * 10 = d.choose 2 * (d - 2).choose 3 := by
    have := Nat.choose_mul (n := d) (k := 5) (s := 2) (by norm_num)
    norm_num at this; exact this
  have hc2 : 2 * d.choose 2 = d * (d - 1) := by
    have h := Nat.descFactorial_eq_factorial_mul_choose d 2
    have hdf : d.descFactorial 2 = d * (d - 1) := by
      rw [Nat.descFactorial, Nat.descFactorial, Nat.descFactorial, Nat.sub_zero]; ring
    rw [hdf] at h; simp only [Nat.factorial] at h; omega
  have hchain : (10 * e) * (d - 2).choose 3 ≤ (3 * d * (d - 1)) * (d - 2).choose 3 := by
    have h1 : (10 * e) * (d - 2).choose 3 ≤ 60 * d.choose 5 := by
      calc (10 * e) * (d - 2).choose 3 = 10 * (e * (d - 2).choose 3) := by ring
        _ ≤ 10 * (6 * d.choose 5) := Nat.mul_le_mul (le_refl 10) hkey
        _ = 60 * d.choose 5 := by ring
    have h2 : (60 : ℕ) * d.choose 5 = (3 * d * (d - 1)) * (d - 2).choose 3 := by
      calc (60 : ℕ) * d.choose 5 = 6 * (d.choose 5 * 10) := by ring
        _ = 6 * (d.choose 2 * (d - 2).choose 3) := by rw [hcm]
        _ = 3 * (2 * d.choose 2) * (d - 2).choose 3 := by ring
        _ = 3 * (d * (d - 1)) * (d - 2).choose 3 := by rw [hc2]
        _ = (3 * d * (d - 1)) * (d - 2).choose 3 := by ring
    rw [h2] at h1; exact h1
  exact Nat.le_of_mul_le_mul_right hchain hpos

end Erdos617
