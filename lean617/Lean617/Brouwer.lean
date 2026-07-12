/-
Erdős Problem 617, r = 5 — milestone F6: Brouwer's non-r-partite Turán bound and
the Kang–Pikhurko extremal classification, packaged for the [MH″] assembly (F7).

The informal proof (review_queue/mh2-gpt56-candidate.md §2) *cites* the following
classical theorem as external input (papers/brouwer-kang-pikhurko.md, VERIFIED):

  Brouwer (1981) / Kang–Pikhurko (2005). If `Y` is an `n`-vertex `K_{r+1}`-free
  graph with `χ(Y) > r` and `n ≥ 2r+1`, then `e(Y) ≤ t_r(n) − ⌊n/r⌋ + 1`.
  Moreover the extremal graphs are classified.

Mathlib provides Turán's theorem (`isTuranMaximal_turanGraph`, giving
`e(Y) ≤ t_r(n)` for every `K_{r+1}`-free `Y`) and the closed form for `t_r(n)`
(`card_edgeFinset_turanGraph`). It does **not** provide the extra `⌊n/r⌋ − 1`
saving for non-r-partite graphs, nor the extremal classification: those are the
irreducible content of Brouwer/KP.

Following the F5 pattern (`PrimFacts`, discharged separately by SAT/F3), we bundle
that irreducible content into `BrouwerFacts` and thread it as a hypothesis. Every
export below is **sorry-free, conditional on `BrouwerFacts`**. The four things F7
consumes (C1–C4 of the F6 mandate) are the theorems

  `brouwer_bound_21`   : K₆-free, α ≤ 4 on Fin 21 ⟹ e ≤ 173         (§3)
  `brouwer_bound_16`   : K₆-free, α ≤ 3 on Fin 16 ⟹ e ≤ 100         (§5, §7.1)
  `brouwer_15_colorable`: K₆-free, e ≥ 89 on Fin 15 ⟹ 5-colorable   (§7.2, contrapositive)
  `brouwer_21_equality`: the KP (4,4,4,4,4) extremal structure at e = 173 (§3)

plus the reusable complement/independence bridges F7 needs to move between a
colour class `F_i` and its complement `J_i = F_iᶜ`.

DESIGN NOTE (route + equality decision, computationally locked; see FORMAL.md):
we take route (B)-as-(A): a single general `saving` field specialised to the three
concrete `(r,n)`. The "172-sharpening" shortcut (hoping α ≤ 4 alone forces
e ≤ 172, making §3's equality step free) is FALSE: the KP construction
`G((4,4,4,4,4))` is K₆-free on 21 vertices with α ≤ 4 and exactly 173 edges
(scratchpad/design_lock.py, |A*| ∈ {1,2,3} all give e=173, K₆-free, α≤4). So the
equality classification is genuinely required and is delivered as `equality21`.

Research project: Mathlib style linters disabled.
-/
import Lean617.LTable

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.style.multiGoal false
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false

open Finset SimpleGraph
open scoped Classical

namespace Erdos617

/-! ## Turán black box and the closed-form edge counts

Mathlib's `isTuranMaximal_turanGraph` gives the Turán bound; we phrase it in the
`edgeCountIn` idiom and record the three concrete `t_5(n)` values. -/

/-- **Turán bound**, in the `edgeCountIn` idiom: a `K_{r+1}`-free graph has at most
`e(turanGraph n r)` edges. -/
theorem cliqueFree_edgeCountIn_le_turan {n r : ℕ} (hr : 0 < r) (G : SimpleGraph (Fin n))
    (hCF : G.CliqueFree (r + 1)) :
    edgeCountIn G Finset.univ ≤ (turanGraph n r).edgeFinset.card := by
  have hmax := isTuranMaximal_turanGraph (n := n) (r := r) hr
  have hle := hmax.2 hCF
  rwa [card_edgeFinset_eq_edgeCountIn G] at hle

/-- `t_5(21) = 176`. -/
theorem turan_5_21 : (turanGraph 21 5).edgeFinset.card = 176 := by
  rw [card_edgeFinset_turanGraph]; decide

/-- `t_5(16) = 102`. -/
theorem turan_5_16 : (turanGraph 16 5).edgeFinset.card = 102 := by
  rw [card_edgeFinset_turanGraph]; decide

/-- `t_5(15) = 90`. -/
theorem turan_5_15 : (turanGraph 15 5).edgeFinset.card = 90 := by
  rw [card_edgeFinset_turanGraph]; decide

/-! ## Independence ⇄ complement-clique bridges

F7 works with a colour class `F_i` and its complement `J_i = F_iᶜ`. These translate
`alphaAtMost` (of `F_i`) into `CliqueFree` (of `J_i`) and back. Key facts:
`α(F) ≤ 5 ↔ Fᶜ` is `K₆`-free, and `F` is `K₅`-free `↔ α(Fᶜ) ≤ 4`. -/

/-- A set is `F`-independent iff it is a clique of the complement `Fᶜ`. -/
theorem isIndep_iff_compl_isClique {n : ℕ} (F : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    IsIndep F S ↔ Fᶜ.IsClique ↑S := by
  rw [SimpleGraph.isClique_iff]
  constructor
  · intro h u hu v hv huv
    rw [SimpleGraph.compl_adj]
    exact ⟨huv, h u (Finset.mem_coe.mp hu) v (Finset.mem_coe.mp hv) huv⟩
  · intro h u hu v hv huv hadj
    have hc := h (Finset.mem_coe.mpr hu) (Finset.mem_coe.mpr hv) huv
    rw [SimpleGraph.compl_adj] at hc
    exact hc.2 hadj

/-- **The α/complement-clique bridge.** `α(F) ≤ m` iff the complement `Fᶜ` is
`K_{m+1}`-free. -/
theorem alphaAtMost_iff_compl_cliqueFree {n : ℕ} (F : SimpleGraph (Fin n)) (m : ℕ) :
    alphaAtMost F m ↔ Fᶜ.CliqueFree (m + 1) := by
  constructor
  · intro hα t hnc
    obtain ⟨hclq, hcard⟩ := hnc
    have hindep : IsIndep F t := (isIndep_iff_compl_isClique F t).mpr hclq
    have := hα t hindep
    omega
  · intro hcf S hindep
    by_contra hgt
    push Not at hgt
    obtain ⟨S', hS'sub, hS'card⟩ :=
      Finset.exists_subset_card_eq (show m + 1 ≤ S.card by omega)
    have hindep' : IsIndep F S' :=
      fun u hu v hv huv => hindep u (hS'sub hu) v (hS'sub hv) huv
    exact hcf S' ⟨(isIndep_iff_compl_isClique F S').mp hindep', hS'card⟩

/-- `α(F) ≤ m ⟹ Fᶜ` is `K_{m+1}`-free. -/
theorem compl_cliqueFree_of_alphaAtMost {n : ℕ} (F : SimpleGraph (Fin n)) (m : ℕ)
    (hα : alphaAtMost F m) : Fᶜ.CliqueFree (m + 1) :=
  (alphaAtMost_iff_compl_cliqueFree F m).mp hα

/-- `F` is `K_{m+1}`-free `⟹ α(Fᶜ) ≤ m`. -/
theorem alphaAtMost_compl_of_cliqueFree {n : ℕ} (F : SimpleGraph (Fin n)) (m : ℕ)
    (hF : F.CliqueFree (m + 1)) : alphaAtMost Fᶜ m := by
  rw [alphaAtMost_iff_compl_cliqueFree, compl_compl]
  exact hF

/-- `α(F) ≤ 5 ⟹ Fᶜ` is `K₆`-free (i.e. `J_i = F_iᶜ` is `K₆`-free; §3, §5, §7). -/
theorem compl_cliqueFree_six_of_alphaAtMost_five {n : ℕ} (F : SimpleGraph (Fin n))
    (hα : alphaAtMost F 5) : Fᶜ.CliqueFree 6 :=
  compl_cliqueFree_of_alphaAtMost F 5 hα

/-- `F` is `K₅`-free `⟹ α(Fᶜ) ≤ 4` (i.e. `α(J_i) ≤ 4`; §3). -/
theorem alphaAtMost_compl_four_of_cliqueFree_five {n : ℕ} (F : SimpleGraph (Fin n))
    (hF : F.CliqueFree 5) : alphaAtMost Fᶜ 4 :=
  alphaAtMost_compl_of_cliqueFree F 4 hF

/-- `F` is `K₄`-free `⟹ α(Fᶜ) ≤ 3` (i.e. `α(J_i) ≤ 3`; §5, §7.1, §7.2, where each
`F_i[X]` is `K₄`-free). -/
theorem alphaAtMost_compl_three_of_cliqueFree_four {n : ℕ} (F : SimpleGraph (Fin n))
    (hF : F.CliqueFree 4) : alphaAtMost Fᶜ 3 :=
  alphaAtMost_compl_of_cliqueFree F 3 hF

/-! ## Covering lemma: `α ≤ k` with `r·k < n` forbids an `r`-colouring

The informal "not r-partite" is derived from the independence bound: an
`r`-colouring partitions the `n` vertices into `r` independent classes, each of
size `≤ α ≤ k`, covering at most `r·k` vertices. -/

/-- If `α(J) ≤ k` and `r·k < n`, then `J` is not `r`-colourable. -/
theorem not_colorable_of_alphaAtMost {n r k : ℕ} (J : SimpleGraph (Fin n))
    (hα : alphaAtMost J k) (hlt : r * k < n) : ¬ J.Colorable r := by
  rintro ⟨C⟩
  have hfib : ∀ i : Fin r, (Finset.univ.filter (fun v => C v = i)).card ≤ k := by
    intro i
    apply hα
    intro u hu v hv huv hadj
    rw [Finset.mem_filter] at hu hv
    exact C.valid hadj (hu.2.trans hv.2.symm)
  have hcard : (Finset.univ : Finset (Fin n)).card
      = ∑ i : Fin r, (Finset.univ.filter (fun v => C v = i)).card :=
    Finset.card_eq_sum_card_fiberwise (fun v _ => Finset.mem_univ (C v))
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  have hsum : ∑ i : Fin r, (Finset.univ.filter (fun v => C v = i)).card ≤ r * k := by
    calc ∑ i : Fin r, (Finset.univ.filter (fun v => C v = i)).card
        ≤ ∑ _i : Fin r, k := Finset.sum_le_sum (fun i _ => hfib i)
      _ = r * k := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

/-! ## The Brouwer/Kang–Pikhurko facts, bundled

This is the irreducible external input (cf. `PrimFacts` for F3). `saving` is
Brouwer's bound in additive-saving form; `equality21` is the KP extremal structure
at `(r,n) = (5,21)`, in colour-class `F` = `F_i` terms (`Fᶜ = J_i`). -/

/-- **The Brouwer/Kang–Pikhurko facts** (external classical theorem; to be
discharged separately). Both fields are literature-verified (papers/brouwer-kang-pikhurko.md). -/
structure BrouwerFacts : Prop where
  /-- **Brouwer's bound (saving form).** A `K_{r+1}`-free graph on `n ≥ 2r+1`
  vertices that is not `r`-colourable loses at least `⌊n/r⌋ − 1` edges off the
  Turán maximum: `e(G) + (⌊n/r⌋ − 1) ≤ t_r(n)`. -/
  saving : ∀ {n r : ℕ}, 0 < r → 2 * r + 1 ≤ n → ∀ G : SimpleGraph (Fin n),
    G.CliqueFree (r + 1) → ¬ G.Colorable r →
    edgeCountIn G Finset.univ + (n / r - 1) ≤ (turanGraph n r).edgeFinset.card
  /-- **KP equality classification at `(r,n) = (5,21)`.** If a colour class `F`
  (on 21 vertices) has `α(F) ≤ 5`, is `K₅`-free, and has exactly `37` edges (so its
  complement `J = Fᶜ` attains Brouwer's maximum `173`), then `F` realises the unique
  surviving extremal shape `G((4,4,4,4,4))`: there are disjoint `A` (`|A|=5`) and
  `B` (`|B|=4`) with `F[A] = K₅ − xy` (a single non-edge `xy`), `F[B] = K₄`, and
  `e_F(A) + e_F(B) + e_F(A,B) = 9 + 6 + 4 = 19` (so exactly four `F`-edges cross). -/
  equality21 : ∀ F : SimpleGraph (Fin 21), alphaAtMost F 5 → F.CliqueFree 5 →
    edgeCountIn F Finset.univ = 37 →
    ∃ A B : Finset (Fin 21), Disjoint A B ∧ A.card = 5 ∧ B.card = 4 ∧
      (∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ ¬ F.Adj x y ∧
        (∀ u ∈ A, ∀ w ∈ A, u ≠ w →
          (¬ F.Adj u w ↔ (u = x ∧ w = y) ∨ (u = y ∧ w = x)))) ∧
      (∀ u ∈ B, ∀ w ∈ B, u ≠ w → F.Adj u w) ∧
      edgeCountIn F (A ∪ B) = 19

/-! ## The four exports F7 consumes (C1–C4)

Each is proved sorry-free from `BrouwerFacts`. -/

/-- **C1 (§3): `n = 21` edge bound.** A `K₆`-free graph on 21 vertices with `α ≤ 4`
has at most `173` edges. (`t_5(21) − ⌊21/5⌋ + 1 = 176 − 3 = 173`.) -/
theorem brouwer_bound_21 (bf : BrouwerFacts) (J : SimpleGraph (Fin 21))
    (hω : J.CliqueFree 6) (hα : alphaAtMost J 4) :
    edgeCountIn J Finset.univ ≤ 173 := by
  have hnc : ¬ J.Colorable 5 := not_colorable_of_alphaAtMost J hα (by norm_num)
  have hsave := bf.saving (n := 21) (r := 5) (by norm_num) (by norm_num) J hω hnc
  rw [turan_5_21] at hsave
  omega

/-- **C2/C3 (§5, §7.1): `n = 16` edge bound.** A `K₆`-free graph on 16 vertices with
`α ≤ 3` has at most `100` edges. (`t_5(16) − ⌊16/5⌋ + 1 = 102 − 2 = 100`.) -/
theorem brouwer_bound_16 (bf : BrouwerFacts) (J : SimpleGraph (Fin 16))
    (hω : J.CliqueFree 6) (hα : alphaAtMost J 3) :
    edgeCountIn J Finset.univ ≤ 100 := by
  have hnc : ¬ J.Colorable 5 := not_colorable_of_alphaAtMost J hα (by norm_num)
  have hsave := bf.saving (n := 16) (r := 5) (by norm_num) (by norm_num) J hω hnc
  rw [turan_5_16] at hsave
  omega

/-- **C4 (§7.2): `n = 15` contrapositive.** A `K₆`-free graph on 15 vertices with at
least `89` edges is `5`-colourable. (A non-`5`-partite `K₆`-free graph on 15
vertices has `≤ t_5(15) − ⌊15/5⌋ + 1 = 90 − 2 = 88` edges.) -/
theorem brouwer_15_colorable (bf : BrouwerFacts) (J : SimpleGraph (Fin 15))
    (hω : J.CliqueFree 6) (he : 89 ≤ edgeCountIn J Finset.univ) :
    J.Colorable 5 := by
  by_contra hnc
  have hsave := bf.saving (n := 15) (r := 5) (by norm_num) (by norm_num) J hω hnc
  rw [turan_5_15] at hsave
  omega

/-! ### Colour-class (`F_i`) forms

The same bounds phrased for a colour class `F` directly (`e(F_i) ≥ …`), matching what
§3/§5/§7.1 state. `J_i = Fᶜ` is `K₆`-free and the complement identity
`edgeCountIn_add_compl` (from LTable) turns the `J`-upper-bound into an `F`-lower-bound.
F7 applies these after transporting `F_i[X]` onto the relevant `Fin n`. -/

/-- **§3 colour form.** A colour class `F` on 21 vertices with `α(F) ≤ 5` and `K₅`-free
has `≥ 37` edges. (`C(21,2) − 173 = 210 − 173 = 37`.) -/
theorem brouwer_F_bound_21 (bf : BrouwerFacts) (F : SimpleGraph (Fin 21))
    (hα : alphaAtMost F 5) (hK5 : F.CliqueFree 5) : 37 ≤ edgeCountIn F Finset.univ := by
  have hJ : edgeCountIn Fᶜ Finset.univ ≤ 173 :=
    brouwer_bound_21 bf Fᶜ (compl_cliqueFree_six_of_alphaAtMost_five F hα)
      (alphaAtMost_compl_four_of_cliqueFree_five F hK5)
  have hid := edgeCountIn_add_compl F
  have hc : (21 : ℕ).choose 2 = 210 := by decide
  omega

/-- **§5, §7.1 colour form.** A colour class `F` on 16 vertices with `α(F) ≤ 5` and
`K₄`-free has `≥ 20` edges. (`C(16,2) − 100 = 120 − 100 = 20`.) -/
theorem brouwer_F_bound_16 (bf : BrouwerFacts) (F : SimpleGraph (Fin 16))
    (hα : alphaAtMost F 5) (hK4 : F.CliqueFree 4) : 20 ≤ edgeCountIn F Finset.univ := by
  have hJ : edgeCountIn Fᶜ Finset.univ ≤ 100 :=
    brouwer_bound_16 bf Fᶜ (compl_cliqueFree_six_of_alphaAtMost_five F hα)
      (alphaAtMost_compl_three_of_cliqueFree_four F hK4)
  have hid := edgeCountIn_add_compl F
  have hc : (16 : ℕ).choose 2 = 120 := by decide
  omega

/-- **C1 equality structure (§3).** The KP extremal structure at `e(F) = 37`;
delivered verbatim from `BrouwerFacts.equality21`. -/
theorem brouwer_21_equality (bf : BrouwerFacts) (F : SimpleGraph (Fin 21))
    (hα : alphaAtMost F 5) (hK5 : F.CliqueFree 5) (he : edgeCountIn F Finset.univ = 37) :
    ∃ A B : Finset (Fin 21), Disjoint A B ∧ A.card = 5 ∧ B.card = 4 ∧
      (∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ ¬ F.Adj x y ∧
        (∀ u ∈ A, ∀ w ∈ A, u ≠ w →
          (¬ F.Adj u w ↔ (u = x ∧ w = y) ∨ (u = y ∧ w = x)))) ∧
      (∀ u ∈ B, ∀ w ∈ B, u ≠ w → F.Adj u w) ∧
      edgeCountIn F (A ∪ B) = 19 :=
  bf.equality21 F hα hK5 he

end Erdos617
