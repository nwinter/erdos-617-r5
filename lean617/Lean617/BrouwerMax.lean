/-
F6 max-size (extremal) machinery for the KP induction. A maximum-edge counterexample
`G ∈ G(n,r) = {K_{r+1}-free, not r-colourable}` exists (finite class), and is *saturated*:
adding any non-edge creates a `K_{r+1}`, i.e. every non-edge `{u,v}` has an `(r−1)`-clique
adjacent to both. `kp_caseB_impl`'s `some-part ≤ 1` guard consumes `max_size_saturated`.

Research project: Mathlib style linters disabled.
-/
import Lean617.BrouwerDischarge

set_option linter.style.header false
set_option linter.style.longLine false
set_option maxHeartbeats 2000000

open Finset SimpleGraph
open scoped Classical

namespace Erdos617

/-- **Extremal choice.** The class `G(n,r)` (`K_{r+1}`-free, not `r`-colourable) is finite;
if it is nonempty (a witness `G`), it has a maximum-edge member `Gmax`. -/
theorem exists_max_counterexample {n r : ℕ} (G : SimpleGraph (Fin n))
    (hCF : G.CliqueFree (r + 1)) (hchi : ¬ G.Colorable r) :
    ∃ Gmax : SimpleGraph (Fin n), Gmax.CliqueFree (r + 1) ∧ ¬ Gmax.Colorable r ∧
      ∀ G' : SimpleGraph (Fin n), G'.CliqueFree (r + 1) → ¬ G'.Colorable r →
        edgeCountIn G' Finset.univ ≤ edgeCountIn Gmax Finset.univ := by
  classical
  set S := (Finset.univ : Finset (SimpleGraph (Fin n))).filter
    (fun G' => G'.CliqueFree (r + 1) ∧ ¬ G'.Colorable r) with hSdef
  have hne : S.Nonempty := ⟨G, by rw [hSdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hCF, hchi⟩⟩
  obtain ⟨Gmax, hmem, hmaxle⟩ := S.exists_max_image (fun G' => edgeCountIn G' Finset.univ) hne
  rw [hSdef, Finset.mem_filter] at hmem
  refine ⟨Gmax, hmem.2.1, hmem.2.2, ?_⟩
  intro G' hCF' hchi'
  exact hmaxle G' (by rw [hSdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hCF', hchi'⟩)

/-- **Saturation.** A maximum-edge counterexample `G` (given as the `hmaxE` maximality) is
saturated: for every non-edge `{u,v}`, there is an `(r−1)`-clique `K` (in `G`, avoiding `u,v`)
whose every vertex is `G`-adjacent to both `u` and `v`. (Adding `uv` would make `Y ∪ {u,v}` a
`K_{r+1}`; maximality forbids a bigger counterexample, so `G ⊔ uv` has a `K_{r+1}`, which must
use `uv`.) -/
theorem max_size_saturated {n r : ℕ} (hr : 1 ≤ r) (G : SimpleGraph (Fin n))
    (hCF : G.CliqueFree (r + 1)) (hchi : ¬ G.Colorable r)
    (hmaxE : ∀ G' : SimpleGraph (Fin n), G'.CliqueFree (r + 1) → ¬ G'.Colorable r →
      edgeCountIn G' Finset.univ ≤ edgeCountIn G Finset.univ)
    (u v : Fin n) (huv : u ≠ v) (hnadj : ¬ G.Adj u v) :
    ∃ K : Finset (Fin n), G.IsClique ↑K ∧ K.card = r - 1 ∧ u ∉ K ∧ v ∉ K ∧
      (∀ w ∈ K, G.Adj u w) ∧ (∀ w ∈ K, G.Adj v w) := by
  classical
  set G' := G ⊔ SimpleGraph.edge u v with hG'
  have hle : G ≤ G' := le_sup_left
  have hchi' : ¬ G'.Colorable r := fun hc => hchi (hc.mono_left hle)
  -- s(u,v) is a new edge
  have hmemG' : s(u, v) ∈ G'.edgeSet := by
    rw [hG', SimpleGraph.edgeSet_sup]
    exact Or.inr (by rw [SimpleGraph.edgeSet_edge_of_ne huv]; rfl)
  have hnmemG : s(u, v) ∉ G.edgeSet := by
    rw [SimpleGraph.mem_edgeSet]; exact hnadj
  have hlt : edgeCountIn G Finset.univ < edgeCountIn G' Finset.univ := by
    rw [edgeCountIn_univ_eq_card_edgeFinset, edgeCountIn_univ_eq_card_edgeFinset]
    apply Finset.card_lt_card
    refine (Finset.ssubset_iff_of_subset ?_).mpr ⟨s(u, v), ?_, ?_⟩
    · intro e he
      simp only [SimpleGraph.mem_edgeFinset] at he ⊢
      exact SimpleGraph.edgeSet_subset_edgeSet.mpr hle he
    · simp only [SimpleGraph.mem_edgeFinset]; exact hmemG'
    · simp only [SimpleGraph.mem_edgeFinset]; exact hnmemG
  have hG'CF : ¬ G'.CliqueFree (r + 1) := by
    intro hCF'; have := hmaxE G' hCF' hchi'; omega
  simp only [SimpleGraph.CliqueFree, not_forall, not_not] at hG'CF
  obtain ⟨K, hKclq, hKcard⟩ := hG'CF
  -- every G'-edge inside K is a G-edge unless it is exactly {u,v}
  have hedge : ∀ a ∈ K, ∀ b ∈ K, a ≠ b → ¬ (a = u ∧ b = v) → ¬ (a = v ∧ b = u) → G.Adj a b := by
    intro a ha b hb hab h1 h2
    have hG'ab := hKclq (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab
    rw [hG', SimpleGraph.sup_adj, SimpleGraph.edge_adj] at hG'ab
    rcases hG'ab with h | ⟨hor, _⟩
    · exact h
    · exfalso; rcases hor with h' | h'
      · exact h1 h'
      · exact h2 h'
  -- u, v ∈ K (else K is a G-clique of size r+1)
  have huK : u ∈ K := by
    by_contra huK
    apply hCF K
    refine ⟨fun a ha b hb hab => hedge a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hab
      (fun h => huK (h.1 ▸ Finset.mem_coe.mp ha)) (fun h => huK (h.2 ▸ Finset.mem_coe.mp hb)), hKcard⟩
  have hvK : v ∈ K := by
    by_contra hvK
    apply hCF K
    refine ⟨fun a ha b hb hab => hedge a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hab
      (fun h => hvK (h.2 ▸ Finset.mem_coe.mp hb)) (fun h => hvK (h.1 ▸ Finset.mem_coe.mp ha)), hKcard⟩
  refine ⟨(K.erase u).erase v, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- G-clique
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_erase, Finset.mem_erase] at ha hb
    exact hedge a ha.2.2 b hb.2.2 hab (fun h => ha.2.1 h.1) (fun h => ha.1 h.1)
  · rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨huv.symm, hvK⟩),
      Finset.card_erase_of_mem huK, hKcard]
    omega
  · exact fun h => (Finset.mem_erase.mp (Finset.mem_of_mem_erase h)).1 rfl
  · exact fun h => (Finset.mem_erase.mp h).1 rfl
  · intro w hw
    rw [Finset.mem_erase, Finset.mem_erase] at hw
    exact hedge u huK w hw.2.2 (Ne.symm hw.2.1) (fun h => hw.1 h.2) (fun h => huv h.1)
  · intro w hw
    rw [Finset.mem_erase, Finset.mem_erase] at hw
    exact hedge v hvK w hw.2.2 (Ne.symm hw.1) (fun h => hw.1 h.2) (fun h => hw.2.1 h.2)

end Erdos617
