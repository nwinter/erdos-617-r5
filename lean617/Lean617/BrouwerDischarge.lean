/-
F6 discharge (WIP) — the Kang–Pikhurko upper-bound induction that inhabits
`BrouwerFacts` (Brouwer.lean). Built on the `symmG` symmetrisation engine
(BrouwerProof.lean) and the `crossE` edge-decomposition (reused from MH2Proof).

Roadmap (FORMAL.md F6):
  1. symmG edge decomposition  e(symmG G x) = e(G[Γx]) + d·(n−d)      [foundations]
  2. Turán recursion            t_r(d) + d·(n−d) ≤ t_{r+1}(n)          [foundations]
  3. Case A of KP Thm 4         (H[D] not (r−1)-partite ⇒ IH)
  4. Lemma 3                    (χ(G−y)=r ⇒ e(G) ≤ B(n,r))            [HARD]
  5. Case B                     (H[D] (r−1)-partite, good/bad split)   [HARD]
  6. assemble general `saving`, specialise to `Fin n`
  7. `equality21`

Research project: Mathlib style linters disabled.
-/
import Lean617.BrouwerProof
import Lean617.MH2Proof

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.multiGoal false
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false

open Finset SimpleGraph
open scoped Classical

namespace Erdos617

variable {n : ℕ}

/-! ## Foundations: edge-count helpers

Two graphs that agree on adjacency over `S` have the same `edgeCountIn S`; an
independent `S` has no internal edges; a complete bipartite `A–B` has `|A|·|B|`
cross edges. -/

/-- If `G` and `G'` agree on adjacency for all pairs inside `S`, they have the
same edge count on `S`. -/
theorem edgeCountIn_congr (G G' : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (h : ∀ u ∈ S, ∀ v ∈ S, (G.Adj u v ↔ G'.Adj u v)) :
    edgeCountIn G S = edgeCountIn G' S := by
  unfold edgeCountIn
  congr 1
  apply Finset.filter_congr
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
    rw [Finset.mk_mem_sym2_iff] at he
    simp only [SimpleGraph.mem_edgeSet]
    exact h u he.1 v he.2

/-- A set with no internal edges has edge count `0`. -/
theorem edgeCountIn_eq_zero_of_indep (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (h : ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v) : edgeCountIn G S = 0 := by
  unfold edgeCountIn
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
    rw [Finset.mk_mem_sym2_iff] at he
    rw [SimpleGraph.mem_edgeSet]
    exact h u he.1 v he.2

/-- Cross edges of a complete bipartite `A–B`: every `a∈A, b∈B` adjacent gives
`crossE = |A|·|B|`. -/
theorem crossE_complete (G : SimpleGraph (Fin n)) (A B : Finset (Fin n))
    (h : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) : crossE G A B = A.card * B.card := by
  unfold crossE
  have hb : ∀ a ∈ A, (B.filter (fun b => G.Adj a b)).card = B.card := by
    intro a ha
    rw [Finset.filter_true_of_mem (fun b hb => h a ha b hb)]
  rw [Finset.sum_congr rfl hb, Finset.sum_const, smul_eq_mul]

/-! ## The "cone" edge decomposition

If `K` makes `D–Dᶜ` complete and `Dᶜ` independent, then
`e(K) = e(K[D]) + |D|·(n−|D|)`. Both the symmetrisation `symmG` and the join
graph `joinTuran` below are cones over their `D`. -/

/-- **Cone edge count.** `Dᶜ` independent + `D–Dᶜ` complete ⇒
`e(K) = e(K[D]) + |D|·(n−|D|)`. -/
theorem edgeCountIn_univ_of_cone (K : SimpleGraph (Fin n)) (D : Finset (Fin n))
    (hindep : ∀ u, u ∉ D → ∀ v, v ∉ D → ¬ K.Adj u v)
    (hcomplete : ∀ u, u ∈ D → ∀ v, v ∉ D → K.Adj u v) :
    edgeCountIn K Finset.univ = edgeCountIn K D + D.card * (n - D.card) := by
  set C := (Finset.univ : Finset (Fin n)) \ D with hC
  have hdisj : Disjoint D C := by
    rw [Finset.disjoint_left]
    intro a haD haC
    rw [hC, Finset.mem_sdiff] at haC
    exact haC.2 haD
  have huniv : (Finset.univ : Finset (Fin n)) = D ∪ C := by
    rw [hC, Finset.union_sdiff_of_subset (Finset.subset_univ D)]
  have hCnotD : ∀ v, v ∈ C → v ∉ D := by
    intro v hv; rw [hC, Finset.mem_sdiff] at hv; exact hv.2
  rw [huniv, edgeCountIn_disjoint_union K hdisj]
  have hCzero : edgeCountIn K C = 0 :=
    edgeCountIn_eq_zero_of_indep K C
      (fun u hu v hv => hindep u (hCnotD u hu) v (hCnotD v hv))
  have hcross : crossE K D C = D.card * C.card :=
    crossE_complete K D C (fun a ha b hb => hcomplete a ha b (hCnotD b hb))
  have hCcard : C.card = n - D.card := by
    rw [hC, ← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin]
  rw [hCzero, hcross, hCcard, add_zero]

/-- **symmetrisation edge count** (Case-A identity `e(H) = e(H[D]) + |D|·|C|`). -/
theorem symmG_edgeCount_eq (G : SimpleGraph (Fin n)) (x : Fin n) :
    edgeCountIn (symmG G x) Finset.univ
      = edgeCountIn G (G.neighborFinset x)
        + (G.neighborFinset x).card * (n - (G.neighborFinset x).card) := by
  rw [edgeCountIn_univ_of_cone (symmG G x) (G.neighborFinset x)
      (fun u hu v hv => symmG_not_adj_of_notMem hu hv)
      (fun u hu v hv => by rw [symmG_adj]; exact Or.inr (Or.inl ⟨hu, hv⟩))]
  congr 1
  apply edgeCountIn_congr
  intro u hu v hv
  exact symmG_adj_of_mem_mem hu hv

/-! ## The Turán recursion `t_r(d) + d·(n−d) ≤ t_{r+1}(n)`

Realised by the join graph `joinTuran n r d`: `turanGraph n r` on the first `d`
vertices (`= T_r(d)`), the last `n−d` vertices independent and completely joined
to the first `d`. It is `(r+1)`-partite hence `K_{r+2}`-free, with
`e = t_r(d) + d·(n−d)`; Turán maximality then gives the recursion. -/

/-- The join graph: `turanGraph n r` on `{v : v < d}`, coned with an independent
`{v : v ≥ d}` completely joined to it. -/
def joinTuran (n r d : ℕ) : SimpleGraph (Fin n) where
  Adj u v :=
    ((u : ℕ) < d ∧ (v : ℕ) < d ∧ (turanGraph n r).Adj u v) ∨
    ((u : ℕ) < d ∧ ¬ (v : ℕ) < d) ∨ (¬ (u : ℕ) < d ∧ (v : ℕ) < d)
  symm := by
    intro u v h
    rcases h with ⟨hu, hv, ha⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact Or.inl ⟨hv, hu, ha.symm⟩
    · exact Or.inr (Or.inr ⟨hv, hu⟩)
    · exact Or.inr (Or.inl ⟨hv, hu⟩)
  loopless := ⟨by
    intro u h
    rcases h with ⟨_, _, ha⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact (turanGraph n r).ne_of_adj ha rfl
    · exact hv hu
    · exact hu hv⟩

@[simp] theorem joinTuran_adj {n r d : ℕ} {u v : Fin n} :
    (joinTuran n r d).Adj u v ↔
      ((u : ℕ) < d ∧ (v : ℕ) < d ∧ (turanGraph n r).Adj u v) ∨
      ((u : ℕ) < d ∧ ¬ (v : ℕ) < d) ∨ (¬ (u : ℕ) < d ∧ (v : ℕ) < d) := Iff.rfl

/-- The finset of "first `d`" vertices of `Fin n`. -/
def firstFin (n d : ℕ) : Finset (Fin n) := Finset.univ.filter (fun v => (v : ℕ) < d)

theorem mem_firstFin {n d : ℕ} {v : Fin n} : v ∈ firstFin n d ↔ (v : ℕ) < d := by
  rw [firstFin, Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- `firstFin n d` is the image of the first-`d` embedding `Fin d ↪ Fin n`. -/
theorem firstFin_eq_image {n d : ℕ} (hd : d ≤ n) :
    Finset.univ.image (Fin.castLEEmb hd) = firstFin n d := by
  ext v
  rw [Finset.mem_image, mem_firstFin]
  constructor
  · rintro ⟨i, _, rfl⟩; simpa using i.isLt
  · intro hv; exact ⟨⟨v, hv⟩, Finset.mem_univ _, by apply Fin.ext; rfl⟩

/-- `|firstFin n d| = d` when `d ≤ n`. -/
theorem card_firstFin {n d : ℕ} (hd : d ≤ n) : (firstFin n d).card = d := by
  rw [← firstFin_eq_image hd, Finset.card_image_of_injective _ (Fin.castLEEmb hd).injective,
    Finset.card_univ, Fintype.card_fin]

/-- Inside `firstFin`, `joinTuran` agrees with `turanGraph n r`. -/
theorem joinTuran_adj_of_mem_firstFin {n r d : ℕ} {u v : Fin n}
    (hu : u ∈ firstFin n d) (hv : v ∈ firstFin n d) :
    (joinTuran n r d).Adj u v ↔ (turanGraph n r).Adj u v := by
  rw [mem_firstFin] at hu hv
  rw [joinTuran_adj]
  constructor
  · rintro (⟨_, _, h⟩ | ⟨_, h⟩ | ⟨h, _⟩)
    · exact h
    · exact absurd hv h
    · exact absurd hu h
  · intro h; exact Or.inl ⟨hu, hv, h⟩

/-- The induced count of `turanGraph n r` on `firstFin n d` is `t_r(d)`. -/
theorem edgeCountIn_turanGraph_firstFin {n r d : ℕ} (hd : d ≤ n) :
    edgeCountIn (turanGraph n r) (firstFin n d) = (turanGraph d r).edgeFinset.card := by
  have hcomap : (turanGraph n r).comap (Fin.castLEEmb hd) = turanGraph d r := by
    ext u v
    simp only [SimpleGraph.comap_adj, turanGraph_adj, Fin.coe_castLEEmb, Fin.val_castLE]
  rw [← firstFin_eq_image hd, ← edgeCountIn_comap, hcomap]
  exact (card_edgeFinset_eq_edgeCountIn _).symm

/-- **join graph edge count.** `e(joinTuran n r d) = t_r(d) + d·(n−d)` (`d ≤ n`). -/
theorem joinTuran_edgeCount {n r d : ℕ} (hd : d ≤ n) :
    edgeCountIn (joinTuran n r d) Finset.univ
      = (turanGraph d r).edgeFinset.card + d * (n - d) := by
  rw [edgeCountIn_univ_of_cone (joinTuran n r d) (firstFin n d)
      (fun u hu v hv => by
        rw [joinTuran_adj, mem_firstFin] at *
        push_neg at hu hv
        rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩) <;> omega)
      (fun u hu v hv => by
        rw [mem_firstFin] at hu; rw [mem_firstFin] at hv; push_neg at hv
        rw [joinTuran_adj]; exact Or.inr (Or.inl ⟨hu, by omega⟩))]
  rw [card_firstFin hd]
  congr 1
  · rw [← edgeCountIn_turanGraph_firstFin hd]
    apply edgeCountIn_congr
    intro u hu v hv
    exact joinTuran_adj_of_mem_firstFin hu hv

/-- **`joinTuran` is `K_{r+2}`-free** (it is `(r+1)`-partite). -/
theorem joinTuran_cliqueFree {n r d : ℕ} (hr : 0 < r) :
    (joinTuran n r d).CliqueFree (r + 2) := by
  intro K hK
  obtain ⟨hclq, hcard⟩ := hK
  -- at most one vertex of K lies outside `firstFin` (its complement is independent)
  have hC1 : (K.filter (fun z => z ∉ firstFin n d)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    by_contra hab
    have haC : ¬ (a : ℕ) < d := fun h => ha.2 (mem_firstFin.mpr h)
    have hbC : ¬ (b : ℕ) < d := fun h => hb.2 (mem_firstFin.mpr h)
    have hadj := hclq (Finset.mem_coe.mpr ha.1) (Finset.mem_coe.mpr hb.1) hab
    rw [joinTuran_adj] at hadj
    rcases hadj with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
    · exact haC h
    · exact haC h
    · exact hbC h
  set KD := K.filter (fun z => z ∈ firstFin n d) with hKD
  have hsplit : KD.card + (K.filter (fun z => z ∉ firstFin n d)).card = K.card :=
    Finset.card_filter_add_card_filter_not (s := K) (fun z => z ∈ firstFin n d)
  have hKDcard : r + 1 ≤ KD.card := by omega
  -- `KD` is a `turanGraph n r`-clique (join agrees with the Turán graph inside `firstFin`)
  have hKDclq : (turanGraph n r).IsClique ↑KD := by
    intro u hu v hv huv
    rw [Finset.mem_coe, hKD, Finset.mem_filter] at hu hv
    exact (joinTuran_adj_of_mem_firstFin hu.2 hv.2).mp
      (hclq (Finset.mem_coe.mpr hu.1) (Finset.mem_coe.mpr hv.1) huv)
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hKDcard
  exact (turanGraph_cliqueFree (n := n) (r := r) hr) T
    ⟨hKDclq.subset (Finset.coe_subset.mpr hTsub), hTcard⟩

/-- **Turán recursion.** `t_r(d) + d·(n−d) ≤ t_{r+1}(n)` for `d ≤ n`, `0 < r`. -/
theorem turan_step {n r d : ℕ} (hr : 0 < r) (hd : d ≤ n) :
    (turanGraph d r).edgeFinset.card + d * (n - d)
      ≤ (turanGraph n (r + 1)).edgeFinset.card := by
  rw [← joinTuran_edgeCount hd]
  have := cliqueFree_edgeCountIn_le_turan (n := n) (r := r + 1) (by omega)
    (joinTuran n r d) (joinTuran_cliqueFree hr)
  simpa using this

