/-
F6 discharge (WIP, sorry-free so far) — the Zykov-type symmetrisation engine of the
Kang–Pikhurko upper-bound induction (scratchpad/kp_proof.txt, Theorem 4 proof).

This is the FIRST reusable step toward discharging `BrouwerFacts.saving`. Every lemma
here is proved sorry-free; they are the "engine" KP's induction runs on:
`symmG G x` clones every non-neighbour of `x` onto `x` (delete edges in `C = V∖Γ(x)`,
join `Γ(x)` to `C` completely). The two load-bearing facts —
`symmG_cliqueFree` (preserves `K_{r+1}`-freeness) and `symmG_edgeCount_ge`
(`e(G) ≤ e(symmG G x)` when `x` has max degree) — are complete.

REMAINING for the full discharge (see FORMAL.md F6 stuck-list): Lemma 3 (the
`χ(G−y)=r` case), the `H[D]` (r−1)-partite case split (good/bad parts), the
induction-on-r wrapper (over an arbitrary vertex type, applying the IH to `H[D]`),
and the `e(G(n)) → t_r(n)−⌊n/r⌋+1` arithmetic (Lemma 5 / Thm 1).
-/
import Lean617.LTable

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.multiGoal false
set_option linter.style.openClassical false

open Finset SimpleGraph
open scoped Classical

namespace Erdos617

variable {n : ℕ}

/-- The KP symmetrisation of `G` at a vertex `x` (write `D = Γ(x)`, `C = V∖D ∋ x`):
keep `G`-edges inside `D`, delete every edge inside `C`, and join `D` to `C`
completely. Equivalently, every vertex of `C` becomes a "clone" of `x`. -/
def symmG (G : SimpleGraph (Fin n)) (x : Fin n) : SimpleGraph (Fin n) where
  Adj u v :=
    (u ∈ G.neighborFinset x ∧ v ∈ G.neighborFinset x ∧ G.Adj u v) ∨
    (u ∈ G.neighborFinset x ∧ v ∉ G.neighborFinset x) ∨
    (u ∉ G.neighborFinset x ∧ v ∈ G.neighborFinset x)
  symm := by
    intro u v h
    rcases h with ⟨hu, hv, hadj⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact Or.inl ⟨hv, hu, hadj.symm⟩
    · exact Or.inr (Or.inr ⟨hv, hu⟩)
    · exact Or.inr (Or.inl ⟨hv, hu⟩)
  loopless := ⟨by
    intro u h
    rcases h with ⟨_, _, hadj⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact G.ne_of_adj hadj rfl
    · exact hv hu
    · exact hu hv⟩

@[simp] theorem symmG_adj {G : SimpleGraph (Fin n)} {x u v : Fin n} :
    (symmG G x).Adj u v ↔
      (u ∈ G.neighborFinset x ∧ v ∈ G.neighborFinset x ∧ G.Adj u v) ∨
      (u ∈ G.neighborFinset x ∧ v ∉ G.neighborFinset x) ∨
      (u ∉ G.neighborFinset x ∧ v ∈ G.neighborFinset x) := Iff.rfl

/-- Within `D = Γ(x)` the symmetrisation agrees with `G`. -/
theorem symmG_adj_of_mem_mem {G : SimpleGraph (Fin n)} {x u v : Fin n}
    (hu : u ∈ G.neighborFinset x) (hv : v ∈ G.neighborFinset x) :
    (symmG G x).Adj u v ↔ G.Adj u v := by
  rw [symmG_adj]
  constructor
  · rintro (⟨_, _, h⟩ | ⟨_, h⟩ | ⟨h, _⟩)
    · exact h
    · exact absurd hv h
    · exact absurd hu h
  · intro h; exact Or.inl ⟨hu, hv, h⟩

/-- `C = V∖D` is independent in the symmetrisation. -/
theorem symmG_not_adj_of_notMem {G : SimpleGraph (Fin n)} {x u v : Fin n}
    (hu : u ∉ G.neighborFinset x) (hv : v ∉ G.neighborFinset x) :
    ¬ (symmG G x).Adj u v := by
  rw [symmG_adj]
  rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩)
  · exact hu h
  · exact hu h
  · exact hv h

/-- **Symmetrisation preserves `K_{r+1}`-freeness.** (KP Thm 4 proof, first claim.) -/
theorem symmG_cliqueFree {G : SimpleGraph (Fin n)} {x : Fin n} {r : ℕ}
    (hG : G.CliqueFree (r + 1)) : (symmG G x).CliqueFree (r + 1) := by
  intro K hK
  obtain ⟨hclq, hcard⟩ := hK
  set D := G.neighborFinset x with hD
  have hxD : x ∉ D := by rw [hD]; simp [SimpleGraph.mem_neighborFinset]
  -- at most one vertex of K lies outside D (else two non-D vertices are non-adjacent)
  have hC1 : (K.filter (fun z => z ∉ D)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    by_contra hab
    exact symmG_not_adj_of_notMem ha.2 hb.2
      (hclq (Finset.mem_coe.mpr ha.1) (Finset.mem_coe.mpr hb.1) hab)
  set KD := K.filter (fun z => z ∈ D) with hKD
  have hsplit : KD.card + (K.filter (fun z => z ∉ D)).card = K.card :=
    Finset.card_filter_add_card_filter_not (s := K) (fun z => z ∈ D)
  have hKDcard : r ≤ KD.card := by omega
  -- KD is a G-clique (symmetrisation agrees with G inside D)
  have hKDclq : G.IsClique ↑KD := by
    intro u hu v hv huv
    rw [Finset.mem_coe, hKD, Finset.mem_filter] at hu hv
    exact (symmG_adj_of_mem_mem hu.2 hv.2).mp
      (hclq (Finset.mem_coe.mpr hu.1) (Finset.mem_coe.mpr hv.1) huv)
  -- x ∪ KD is a G-clique of size ≥ r+1
  have hxKD : x ∉ KD := by rw [hKD, Finset.mem_filter]; rintro ⟨_, h⟩; exact hxD h
  have hins : G.IsClique ↑(insert x KD) := by
    intro u hu v hv huv
    rw [Finset.coe_insert, Set.mem_insert_iff] at hu hv
    rcases hu with rfl | hu <;> rcases hv with rfl | hv
    · exact absurd rfl huv
    · rw [Finset.mem_coe, hKD, Finset.mem_filter, hD, SimpleGraph.mem_neighborFinset] at hv
      exact hv.2
    · rw [Finset.mem_coe, hKD, Finset.mem_filter, hD, SimpleGraph.mem_neighborFinset] at hu
      exact (hu.2).symm
    · exact hKDclq (Finset.mem_coe.mpr hu) (Finset.mem_coe.mpr hv) huv
  have hcardins : r + 1 ≤ (insert x KD).card := by
    rw [Finset.card_insert_of_notMem hxKD]; omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcardins
  exact hG T ⟨hins.subset (Finset.coe_subset.mpr hTsub), hTcard⟩

/-- **The neighbourhood of `x` induces a `K_r`-free graph** (a `K_r ⊆ Γ(x)` plus `x`
would be a `K_{r+1}`). Used for the Case-A induction on `H[D] = G[Γ(x)]`. -/
theorem no_clique_r_in_nbhd {G : SimpleGraph (Fin n)} {x : Fin n} {r : ℕ}
    (hG : G.CliqueFree (r + 1)) (S : Finset (Fin n)) (hS : S ⊆ G.neighborFinset x)
    (hSc : G.IsClique ↑S) : S.card ≤ r - 1 := by
  by_contra hgt
  push Not at hgt
  have hxS : x ∉ S := by
    intro hx
    have := hS hx
    rw [SimpleGraph.mem_neighborFinset] at this
    exact G.ne_of_adj this rfl
  have hxadj : ∀ w ∈ S, G.Adj x w := fun w hw => (G.mem_neighborFinset x w).mp (hS hw)
  have hins : G.IsClique ↑(insert x S) := by
    intro u hu v hv huv
    rw [Finset.coe_insert, Set.mem_insert_iff] at hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact absurd (hu.trans hv.symm) huv
    · rw [hu]; exact hxadj v (Finset.mem_coe.mp hv)
    · rw [hv]; exact (hxadj u (Finset.mem_coe.mp hu)).symm
    · exact hSc (Finset.mem_coe.mpr hu) (Finset.mem_coe.mpr hv) huv
  have hcard : r + 1 ≤ (insert x S).card := by
    rw [Finset.card_insert_of_notMem hxS]; omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcard
  exact hG T ⟨hins.subset (Finset.coe_subset.mpr hTsub), hTcard⟩

/-- **Symmetrisation does not decrease any degree** (given `x` has maximum degree):
inside `D`, `Γ_G(y) ⊆ Γ_H(y)`; for `y ∈ C`, `d_H(y) = |D| = Δ(G) ≥ d_G(y)`. -/
theorem symmG_degree_ge {G : SimpleGraph (Fin n)} {x : Fin n}
    (hmax : ∀ y, G.degree y ≤ G.degree x) (y : Fin n) :
    G.degree y ≤ (symmG G x).degree y := by
  by_cases hy : y ∈ G.neighborFinset x
  · rw [← G.card_neighborFinset_eq_degree, ← (symmG G x).card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw ⊢
    by_cases hwD : w ∈ G.neighborFinset x
    · exact (symmG_adj_of_mem_mem hy hwD).mpr hw
    · rw [symmG_adj]; exact Or.inr (Or.inl ⟨hy, hwD⟩)
  · have hnbhd : (symmG G x).neighborFinset y = G.neighborFinset x := by
      ext w
      rw [SimpleGraph.mem_neighborFinset, symmG_adj]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩)
        · exact absurd h hy
        · exact absurd h hy
        · exact h
      · intro hw; exact Or.inr (Or.inr ⟨hy, hw⟩)
    rw [← (symmG G x).card_neighborFinset_eq_degree, hnbhd, G.card_neighborFinset_eq_degree]
    exact hmax y

/-- **Symmetrisation does not decrease the edge count** (`e(G) ≤ e(H)`; KP Thm 4). -/
theorem symmG_edgeCount_ge {G : SimpleGraph (Fin n)} {x : Fin n}
    (hmax : ∀ y, G.degree y ≤ G.degree x) :
    edgeCountIn G Finset.univ ≤ edgeCountIn (symmG G x) Finset.univ := by
  rw [edgeCountIn_univ_eq_card_edgeFinset, edgeCountIn_univ_eq_card_edgeFinset]
  have h1 := G.sum_degrees_eq_twice_card_edges
  have h2 := (symmG G x).sum_degrees_eq_twice_card_edges
  have hle : ∑ y, G.degree y ≤ ∑ y, (symmG G x).degree y :=
    Finset.sum_le_sum (fun y _ => symmG_degree_ge hmax y)
  omega

end Erdos617
