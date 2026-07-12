/-
Guard scaffolding for kp_caseB_impl's `some-part ≤ 1` singleton sub-case (runner 14, lean-f6g).

The genuinely-new step, verified sorry-free: for a MAX-SIZE counterexample `G` in Case B
(`κ` a proper `(r−1)`-colouring of `Γx`), if a colour class `i0` is a SINGLETON `{w}`, then
`w` is adjacent to ALL of `C = V∖Γx`. Reason: for `v ∈ C∖{x}` (`¬Adj x v`), `max_size_saturated`
yields an `(r−1)`-clique `K ⊆ N(x)=Γx` adjacent to `v`; a size-`(r−1)` `G`-clique inside the
`(r−1)`-partite `Γx` is a TRANSVERSAL (one vertex per `κ`-class), so it hits the singleton class
`{w}`, forcing `w ∈ K` and hence `Adj w v`.

This REFRAMES f6f's "≥2 misses" crux to `W_C = ∅`. The remaining guard closure (from `w` adj all
`C` to `∃z, χ(G−z)≤r`) is still OPEN — see FORMAL.md "SINGLETON REDUCTION / RUNNER-14 UPDATE".

Standalone: does NOT touch BrouwerInduction (kp_lemma3 stays sorry-free). Research linters off.
-/
import Lean617.BrouwerInduction
import Lean617.BrouwerMax

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option maxHeartbeats 2000000

open Finset SimpleGraph
open scoped Classical

namespace Erdos617

/-- A size-`q` `G`-clique `K` inside a `q`-coloured (proper) set `D` is a transversal: it hits
every colour class exactly once. In particular, if class `i0` is the singleton `{w}`, then `w ∈ K`. -/
theorem clique_hits_singleton {n q : ℕ} (G : SimpleGraph (Fin n)) (κ : Fin n → Fin q)
    (D : Finset (Fin n))
    (hproper : ∀ u ∈ D, ∀ v ∈ D, G.Adj u v → κ u ≠ κ v)
    (K : Finset (Fin n)) (hKD : K ⊆ D) (hKclq : G.IsClique ↑K) (hKcard : K.card = q)
    (i0 : Fin q) (w : Fin n) (hw : D.filter (fun v => κ v = i0) = {w}) : w ∈ K := by
  classical
  -- κ is injective on K (proper clique)
  have hinj : Set.InjOn κ ↑K := by
    intro u hu v hv hκ
    by_contra huv
    exact hproper u (hKD (Finset.mem_coe.mp hu)) v (hKD (Finset.mem_coe.mp hv))
      (hKclq hu hv huv) hκ
  -- image has card q, hence is all of Fin q
  have himgcard : (K.image κ).card = q := by
    rw [Finset.card_image_of_injOn hinj, hKcard]
  have himgall : K.image κ = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [himgcard, Fintype.card_fin])
  -- i0 is hit
  have : i0 ∈ K.image κ := by rw [himgall]; exact Finset.mem_univ _
  rw [Finset.mem_image] at this
  obtain ⟨k, hkK, hki0⟩ := this
  -- k ∈ D with κ k = i0, so k ∈ {w}, so k = w
  have hkD : k ∈ D.filter (fun v => κ v = i0) := Finset.mem_filter.mpr ⟨hKD hkK, hki0⟩
  rw [hw, Finset.mem_singleton] at hkD
  rwa [← hkD]

/-- **Singleton part ⇒ adjacent to all `C`** (for a MAX-SIZE counterexample). `w` (the unique
vertex of a singleton colour class `i0` of `Γx`) is `G`-adjacent to every `v ∉ Γx`, `v ≠ x`. -/
theorem singleton_adj_all_C {n r : ℕ} (hr : 2 ≤ r) (G : SimpleGraph (Fin n))
    (hCF : G.CliqueFree (r + 1)) (hchi : ¬ G.Colorable r)
    (hmaxE : ∀ G' : SimpleGraph (Fin n), G'.CliqueFree (r + 1) → ¬ G'.Colorable r →
      edgeCountIn G' Finset.univ ≤ edgeCountIn G Finset.univ)
    (x : Fin n) (κ : Fin n → Fin (r - 1))
    (hproper : ∀ u ∈ G.neighborFinset x, ∀ v ∈ G.neighborFinset x, G.Adj u v → κ u ≠ κ v)
    (i0 : Fin (r - 1)) (w : Fin n)
    (hw : (G.neighborFinset x).filter (fun v => κ v = i0) = {w}) :
    ∀ v, v ∉ G.neighborFinset x → v ≠ x → G.Adj w v := by
  intro v hv hvx
  have hxv : ¬ G.Adj x v := fun h => hv ((G.mem_neighborFinset x v).mpr h)
  obtain ⟨K, hKclq, hKcard, _hxK, _hvK, hKx, hKv⟩ :=
    max_size_saturated (by omega) G hCF hchi hmaxE x v (Ne.symm hvx) hxv
  have hKD : K ⊆ G.neighborFinset x :=
    fun k hk => (G.mem_neighborFinset x k).mpr (hKx k hk)
  have hwK : w ∈ K :=
    clique_hits_singleton G κ (G.neighborFinset x) hproper K hKD hKclq hKcard i0 w hw
  exact (hKv w hwK).symm


/- **RETIRED (2026-07-12, F6aa).** `guard_singleton_closure_OPEN` — the former placeholder
singleton-closure obligation via the MAX-SIZE / Lemma-3 route — is no longer needed. The
`some-part ≤ 1` guard of `kp_caseB_impl` is now discharged sorry-free in `BrouwerInduction.lean`
(`guard_somepart_closure`) via ROUTE MI: `main_ineq` + `c ≥ 3`, using max-DEGREE only (no
max-size, no `z`-witness, no `BrouwerMax`). `singleton_adj_all_C` / `clique_hits_singleton`
above remain as standalone verified lemmas (banked machinery). -/

end Erdos617
