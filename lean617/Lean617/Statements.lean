/-
Erdős Problem 617, r = 5: formal statements.

Main target matches google-deepmind/formal-conjectures `erdos_617` specialized
to r = 5 (see papers/ergy99.md §8 for the upstream statement): for every
5-colouring of the edges of K_26 there exist 6 vertices and a colour k such
that no edge among those vertices has colour k.

This file pins all definitions and states the three-link chain from the
informal proof (review_queue/: extension-chain.md, mh2-gpt56-candidate.md,
mm-gpt56-candidate.md):

  chain_deduction : MH2 → MM → Main
  lemma_MH2       : MH2
  lemma_MM        : MM

See FORMAL.md for the elimination plan.

This is a research project, not a Mathlib PR: Mathlib's style linters are
disabled below.
-/
import Mathlib

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.style.multiGoal false
set_option linter.style.openClassical false
-- `main_imp_upstream` keeps `[DecidableEq V]` to mirror the upstream signature
-- exactly, even though `open scoped Classical` makes it redundant.
set_option linter.unusedDecidableInType false

open Finset
open scoped Classical

namespace Erdos617

/-! ## Definitions -/

/-- The colour-`k` class of an edge colouring, as a simple graph. -/
def colourClass {n : ℕ} (c : Sym2 (Fin n) → Fin 5) (k : Fin 5) :
    SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ c s(u, v) = k
  symm := by
    intro u v ⟨huv, hc⟩
    exact ⟨huv.symm, by rwa [Sym2.eq_swap]⟩
  loopless := ⟨fun _ ⟨hn, _⟩ => hn rfl⟩

/-- `S` misses colour `k`: no edge inside `S` has colour `k`. -/
def Misses {n : ℕ} (c : Sym2 (Fin n) → Fin 5) (S : Finset (Fin n))
    (k : Fin 5) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u, v) ≠ k

/-- A colouring is balanced iff every 6-subset sees all 5 colours. -/
def Balanced {n : ℕ} (c : Sym2 (Fin n) → Fin 5) : Prop :=
  ∀ S : Finset (Fin n), S.card = 6 → ∀ k : Fin 5, ¬ Misses c S k

/-- `S` is an independent set of the graph `G` (no edge inside `S`). -/
def IsIndep {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ G.Adj u v

/-- Number of edges of `G` with both endpoints in the finset `S`. -/
noncomputable def edgeCountIn {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : ℕ :=
  (S.sym2.filter (fun e => e ∈ G.edgeSet)).card

/-! ## Basic structural lemmas (proved) -/

/-- Membership in the edge set of a colour class. -/
theorem mem_colourClass_edgeSet {n : ℕ} (c : Sym2 (Fin n) → Fin 5) (k : Fin 5)
    (e : Sym2 (Fin n)) :
    e ∈ (colourClass c k).edgeSet ↔ ¬ e.IsDiag ∧ c e = k := by
  induction e using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeSet, Sym2.mk_isDiag_iff]
    exact Iff.rfl

/-- The number of off-diagonal unordered pairs of a finset is `C(|S|, 2)`. -/
theorem card_offdiag {α : Type*} [DecidableEq α] (S : Finset α) :
    (S.sym2.filter (fun e => ¬ e.IsDiag)).card = S.card.choose 2 := by
  have hdiag : (S.sym2.filter (fun e => e.IsDiag)).card = S.card := by
    have himg : S.sym2.filter (fun e => e.IsDiag) = S.image Sym2.diag := by
      ext e
      induction e using Sym2.ind with
      | _ x y =>
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mk_mem_sym2_iff,
          Sym2.mk_isDiag_iff]
        constructor
        · rintro ⟨⟨hx, _⟩, rfl⟩
          exact ⟨x, hx, rfl⟩
        · rintro ⟨a, ha, hae⟩
          simp only [Sym2.diag] at hae
          rw [Sym2.eq_iff] at hae
          rcases hae with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨⟨ha, ha⟩, rfl⟩
          · exact ⟨⟨ha, ha⟩, rfl⟩
    rw [himg, Finset.card_image_of_injective _ Sym2.diag_injective]
  have hsplit := Finset.card_filter_add_card_filter_not (fun e : Sym2 α => e.IsDiag)
    (s := S.sym2)
  rw [Finset.card_sym2, hdiag] at hsplit
  have hchoose : (S.card + 1).choose 2 = S.card + S.card.choose 2 := by
    rw [Nat.choose_succ_succ' S.card 1, Nat.choose_one_right]
  omega

/-- Edges of a colour class inside `S`, as a colour-filter of the off-diagonal pairs. -/
theorem edgeCountIn_colourClass {n : ℕ} (c : Sym2 (Fin n) → Fin 5) (k : Fin 5)
    (S : Finset (Fin n)) :
    edgeCountIn (colourClass c k) S
      = (S.sym2.filter (fun e => ¬ e.IsDiag ∧ c e = k)).card := by
  unfold edgeCountIn
  congr 1
  apply Finset.filter_congr
  intro e _
  rw [mem_colourClass_edgeSet]

/-- The colour classes partition the off-diagonal pairs of `S`, so their edge
counts sum to `C(|S|, 2)`. -/
theorem sum_edgeCountIn_colourClass {n : ℕ} (c : Sym2 (Fin n) → Fin 5)
    (S : Finset (Fin n)) :
    ∑ k : Fin 5, edgeCountIn (colourClass c k) S = S.card.choose 2 := by
  have hP : ∀ k : Fin 5, edgeCountIn (colourClass c k) S
      = ((S.sym2.filter (fun e => ¬ e.IsDiag)).filter (fun e => c e = k)).card := by
    intro k
    rw [edgeCountIn_colourClass, Finset.filter_filter]
  simp_rw [hP]
  rw [← Finset.card_eq_sum_card_fiberwise
        (s := S.sym2.filter (fun e => ¬ e.IsDiag)) (f := c)
        (t := Finset.univ) (fun e _ => Finset.mem_univ _)]
  exact card_offdiag S

/-! ## The three-link chain -/

/-- [MH″] (proved informally, review_queue/mh2-gpt56-candidate.md):
for every balanced 5-colouring of K_25, every colour k and every 4-set T,
some independent 5-set of the colour-k class avoids T. Equivalently: no 4-set
kills all independent 5-sets of a colour class. -/
def MH2 : Prop :=
  ∀ c : Sym2 (Fin 25) → Fin 5, Balanced c →
    ∀ k : Fin 5, ∀ T : Finset (Fin 25), T.card = 4 →
      ∃ S : Finset (Fin 25), S.card = 5 ∧ Disjoint S T ∧ IsIndep (colourClass c k) S

/-- [MM] (proved informally, review_queue/mm-gpt56-candidate.md):
there is no graph G on 25 vertices with independence number ≤ 5, every 6-set
spanning ≤ 11 edges, ≤ 60 edges total, together with a 5-set T such that
α(G − T) ≤ 4 and T spans ≤ 6 edges of G. -/
def MM : Prop :=
  ∀ G : SimpleGraph (Fin 25),
    (∀ S : Finset (Fin 25), IsIndep G S → S.card ≤ 5) →
    (∀ S : Finset (Fin 25), S.card = 6 → edgeCountIn G S ≤ 11) →
    edgeCountIn G Finset.univ ≤ 60 →
    ∀ T : Finset (Fin 25), T.card = 5 →
      (∀ S : Finset (Fin 25), IsIndep G S → Disjoint S T → S.card ≤ 4) →
      edgeCountIn G T ≤ 6 →
      False

/-- The main theorem, r = 5 case of Erdős 617, in the upstream's shape. -/
def Main : Prop :=
  ∀ c : Sym2 (Fin 26) → Fin 5,
    ∃ (S : Finset (Fin 26)) (k : Fin 5), S.card = 6 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u, v) ≠ k

theorem main_iff_no_balanced :
    Main ↔ ∀ c : Sym2 (Fin 26) → Fin 5, ¬ Balanced c := by
  constructor
  · intro h c hbal
    obtain ⟨S, k, hcard, hmiss⟩ := h c
    exact hbal S hcard k hmiss
  · intro h c
    have hc := h c
    rw [Balanced] at hc
    push Not at hc
    obtain ⟨S, hcard, k, hmiss⟩ := hc
    exact ⟨S, k, hcard, hmiss⟩

/-- **Statement fidelity.** `Main` (stated over `Fin 26`) implies the upstream
`google-deepmind/formal-conjectures` `erdos_617` conclusion at `r = 5` for an
*arbitrary* finite vertex type `V` with `card V = 5^2 + 1`. Transport is via any
equivalence `V ≃ Fin 26`; this shows the `Fin 26` specialisation loses no
generality (see papers/ergy99.md §8 for the upstream text). -/
theorem main_imp_upstream (h : Main) {V : Type} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V = 5 ^ 2 + 1) (coloring : Sym2 V → Fin 5) :
    ∃ (S : Finset V) (k : Fin 5), S.card = 5 + 1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k := by
  have hcard : Fintype.card V = 26 := by rw [hV]; norm_num
  let e : V ≃ Fin 26 := Fintype.equivFinOfCardEq hcard
  obtain ⟨S', k, hcard', hmiss'⟩ := h (fun z => coloring (z.map e.symm))
  refine ⟨S'.image e.symm, k, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ e.symm.injective]; omega
  · intro u hu v hv huv
    rw [Finset.mem_image] at hu hv
    obtain ⟨a, ha, rfl⟩ := hu
    obtain ⟨b, hb, rfl⟩ := hv
    have hab : a ≠ b := fun hh => huv (by rw [hh])
    have hkey := hmiss' a ha b hb hab
    simp only [Sym2.map_mk] at hkey
    exact hkey

/-- Balanced ⇒ every colour class has independence number ≤ 5 (an independent
6-set would be a 6-set missing that colour). -/
theorem indep_le_five {n : ℕ} {c : Sym2 (Fin n) → Fin 5} (hbal : Balanced c)
    (k : Fin 5) (S : Finset (Fin n)) (hS : IsIndep (colourClass c k) S) :
    S.card ≤ 5 := by
  by_contra hgt
  push Not at hgt
  obtain ⟨S6, hsub, hcard6⟩ := Finset.exists_subset_card_eq (show 6 ≤ S.card by omega)
  apply hbal S6 hcard6 k
  intro u hu v hv huv hck
  exact hS u (hsub hu) v (hsub hv) huv ⟨huv, hck⟩

/-- Balanced ⇒ every 6-set spans at most 11 edges of any colour class
(≥ 12 of one colour leaves ≤ 3 for the other four, so some colour is missing). -/
theorem cap_eleven {n : ℕ} {c : Sym2 (Fin n) → Fin 5} (hbal : Balanced c)
    (k : Fin 5) (S : Finset (Fin n)) (hS : S.card = 6) :
    edgeCountIn (colourClass c k) S ≤ 11 := by
  -- each colour occurs at least once in S
  have hpos : ∀ j : Fin 5, 1 ≤ edgeCountIn (colourClass c j) S := by
    intro j
    have hnm := hbal S hS j
    rw [Misses] at hnm
    push Not at hnm
    obtain ⟨u, hu, v, hv, huv, hcj⟩ := hnm
    rw [edgeCountIn_colourClass, Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero,
      Finset.card_pos]
    refine ⟨s(u, v), ?_⟩
    rw [Finset.mem_filter]
    refine ⟨by rw [Finset.mk_mem_sym2_iff]; exact ⟨hu, hv⟩, ?_, hcj⟩
    rw [Sym2.mk_isDiag_iff]; exact huv
  -- the counts sum to 15
  have hsum : ∑ j : Fin 5, edgeCountIn (colourClass c j) S = 15 := by
    rw [sum_edgeCountIn_colourClass, hS]; decide
  have hk_mem : k ∈ (Finset.univ : Finset (Fin 5)) := Finset.mem_univ k
  rw [← Finset.sum_erase_add _ _ hk_mem] at hsum
  have hcard4 : (Finset.univ.erase k).card = 4 := by
    rw [Finset.card_erase_of_mem hk_mem, Finset.card_univ, Fintype.card_fin]
  have hrest : 4 ≤ ∑ j ∈ Finset.univ.erase k, edgeCountIn (colourClass c j) S := by
    have hle : (Finset.univ.erase k).card
        ≤ ∑ j ∈ Finset.univ.erase k, edgeCountIn (colourClass c j) S := by
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum (fun j _ => hpos j)
    omega
  omega

/-- Five naturals each ≥ 5 summing to 25 are all equal to 5. -/
theorem all_eq_five (g : Fin 5 → ℕ) (hge : ∀ i, 5 ≤ g i) (hsum : ∑ i, g i = 25)
    (k : Fin 5) : g k = 5 := by
  have hle : g k ≤ 5 := by
    by_contra h
    push Not at h
    have h2 := Finset.sum_erase_add (Finset.univ : Finset (Fin 5)) g (Finset.mem_univ k)
    have h1 : 20 ≤ ∑ x ∈ Finset.univ.erase k, g x := by
      calc (20 : ℕ) = ∑ _x ∈ Finset.univ.erase k, 5 := by
            simp [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ k)]
        _ ≤ _ := Finset.sum_le_sum (fun j _ => hge j)
    rw [hsum] at h2
    omega
  have := hge k
  omega

/-- A graph with no edges inside `S` is independent on `S`. -/
theorem isIndep_of_edgeCountIn_zero {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (h : edgeCountIn G S = 0) : IsIndep G S := by
  intro u hu v hv huv hadj
  rw [edgeCountIn, Finset.card_eq_zero] at h
  have hmem : s(u, v) ∈ S.sym2.filter (fun e => e ∈ G.edgeSet) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mk_mem_sym2_iff.mpr ⟨hu, hv⟩, G.mem_edgeSet.mpr hadj⟩
  rw [h] at hmem
  exact absurd hmem (Finset.notMem_empty _)

/-- The restriction of a balanced colouring of K_26 to the 25 vertices in the
image of `Fin.castSucc` is a balanced colouring of K_25. -/
theorem balanced_restrict {c : Sym2 (Fin 26) → Fin 5} (hbal : Balanced c) :
    Balanced (fun z => c (z.map (Fin.castSucc : Fin 25 → Fin 26))) := by
  intro S hcard k hmiss
  refine hbal (S.image Fin.castSucc) ?_ k ?_
  · rw [Finset.card_image_of_injective _ (Fin.castSucc_injective 25)]; exact hcard
  · intro u hu v hv huv
    rw [Finset.mem_image] at hu hv
    obtain ⟨a, ha, rfl⟩ := hu
    obtain ⟨b, hb, rfl⟩ := hv
    have hab : a ≠ b := fun h => huv (by rw [h])
    have hm := hmiss a ha b hb hab
    simp only [Sym2.map_mk] at hm
    exact hm

theorem chain_deduction (hMH2 : MH2) (hMM : MM) : Main := by
  rw [main_iff_no_balanced]
  intro c hbal
  set c' : Sym2 (Fin 25) → Fin 5 := fun z => c (z.map (Fin.castSucc : Fin 25 → Fin 26))
    with hc'def
  have hbal' : Balanced c' := balanced_restrict hbal
  set x : Fin 26 := Fin.last 25 with hxdef
  set T : Fin 5 → Finset (Fin 25) :=
    fun k => Finset.univ.filter (fun v => c s(x, Fin.castSucc v) = k) with hTdef
  have memT : ∀ (k : Fin 5) (v : Fin 25), v ∈ T k ↔ c s(x, Fin.castSucc v) = k := by
    intro k v
    simp only [hTdef, Finset.mem_filter, Finset.mem_univ, true_and]
  -- ∑ |T k| = 25 (fibres of the spoke-colour map partition the 25 vertices)
  have hTsum : ∑ k : Fin 5, (T k).card = 25 := by
    have hfib : ∀ k : Fin 5, (T k).card
        = (Finset.univ.filter (fun v => c s(x, Fin.castSucc v) = k)).card := by
      intro k; rw [hTdef]
    simp_rw [hfib]
    rw [← Finset.card_eq_sum_card_fiberwise
          (s := (Finset.univ : Finset (Fin 25)))
          (f := fun v => c s(x, Fin.castSucc v)) (t := Finset.univ)
          (fun v _ => Finset.mem_univ _)]
    rw [Finset.card_univ, Fintype.card_fin]
  -- Step 2: α(G_k − T_k) ≤ 4
  have step2 : ∀ (k : Fin 5) (S : Finset (Fin 25)),
      IsIndep (colourClass c' k) S → Disjoint S (T k) → S.card ≤ 4 := by
    intro k S hindep hdisj
    by_contra hgt
    push Not at hgt
    obtain ⟨F, hFsub, hFcard⟩ := Finset.exists_subset_card_eq (show 5 ≤ S.card by omega)
    have spoke : ∀ b ∈ F, c s(x, Fin.castSucc b) ≠ k := by
      intro b hb hh
      exact Finset.disjoint_left.mp hdisj (hFsub hb) ((memT k b).mpr hh)
    have hxnotin : x ∉ F.image Fin.castSucc := by
      rw [Finset.mem_image]; rintro ⟨b, _, hb⟩; exact (Fin.castSucc_lt_last b).ne hb
    have hWcard : (insert x (F.image Fin.castSucc)).card = 6 := by
      rw [Finset.card_insert_of_notMem hxnotin,
        Finset.card_image_of_injective _ (Fin.castSucc_injective 25), hFcard]
    apply hbal (insert x (F.image Fin.castSucc)) hWcard k
    intro u hu v hv huv
    rw [Finset.mem_insert] at hu hv
    rcases hu with rfl | hu <;> rcases hv with rfl | hv
    · exact absurd rfl huv
    · -- u = x, v = castSucc b
      rw [Finset.mem_image] at hv
      obtain ⟨b, hb, rfl⟩ := hv
      exact spoke b hb
    · -- u = castSucc a, v = x
      rw [Finset.mem_image] at hu
      obtain ⟨a, ha, rfl⟩ := hu
      rw [Sym2.eq_swap]
      exact spoke a ha
    · -- u = castSucc a, v = castSucc b
      rw [Finset.mem_image] at hu hv
      obtain ⟨a, ha, rfl⟩ := hu
      obtain ⟨b, hb, rfl⟩ := hv
      have hab : a ≠ b := fun h => huv (by rw [h])
      have := hindep a (hFsub ha) b (hFsub hb) hab
      intro hck
      apply this
      refine ⟨hab, ?_⟩
      rw [hc'def]
      simp only [Sym2.map_mk]
      exact hck
  -- Step 4: |T k| ≥ 5 (MH2 + monotonicity), hence = 5 (∑ = 25)
  have step4ge : ∀ k : Fin 5, 5 ≤ (T k).card := by
    intro k
    by_contra hlt
    push Not at hlt
    obtain ⟨Tp, hsub, hTpcard⟩ := Finset.exists_superset_card_eq
      (show (T k).card ≤ 4 by omega) (by rw [Fintype.card_fin]; omega)
    obtain ⟨S, hScard, hSdisj, hSindep⟩ := hMH2 c' hbal' k Tp hTpcard
    have hdisjTk : Disjoint S (T k) := Finset.disjoint_of_subset_right hsub hSdisj
    have := step2 k S hSindep hdisjTk
    omega
  have step4 : ∀ k : Fin 5, (T k).card = 5 :=
    fun k => all_eq_five (fun j => (T j).card) step4ge hTsum k
  -- disjointness of distinct fibres
  have hdisjT : ∀ i j : Fin 5, i ≠ j → Disjoint (T i) (T j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro v hvi hvj
    rw [memT] at hvi hvj
    exact hij (hvi.symm.trans hvj)
  -- Minority colour m: at most 60 edges total
  obtain ⟨m, -, hm_min⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin 5))
    (fun j => edgeCountIn (colourClass c' j) Finset.univ) ⟨0, Finset.mem_univ 0⟩
  have hsum300 : ∑ j : Fin 5, edgeCountIn (colourClass c' j) Finset.univ = 300 := by
    rw [sum_edgeCountIn_colourClass, Finset.card_univ, Fintype.card_fin]; decide
  have hmin60 : edgeCountIn (colourClass c' m) Finset.univ ≤ 60 := by
    have hle := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 5)))
      (f := fun _ => edgeCountIn (colourClass c' m) Finset.univ)
      (g := fun j => edgeCountIn (colourClass c' j) Finset.univ)
      (fun j _ => hm_min j (Finset.mem_univ j))
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hsum300] at hle
    omega
  -- Step 5: T_m spans ≤ 6 edges of colour m
  have hpos_j : ∀ j : Fin 5, j ≠ m → 1 ≤ edgeCountIn (colourClass c' j) (T m) := by
    intro j hjm
    by_contra h
    push Not at h
    have hzero : edgeCountIn (colourClass c' j) (T m) = 0 := by omega
    have hindep := isIndep_of_edgeCountIn_zero _ _ hzero
    have hdisj : Disjoint (T m) (T j) := hdisjT m j (fun hh => hjm hh.symm)
    have hcard4 := step2 j (T m) hindep hdisj
    have := step4 m
    omega
  have hsum10 : ∑ j : Fin 5, edgeCountIn (colourClass c' j) (T m) = 10 := by
    rw [sum_edgeCountIn_colourClass, step4 m]; decide
  have step5 : edgeCountIn (colourClass c' m) (T m) ≤ 6 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ m)] at hsum10
    have hrest : 4 ≤ ∑ j ∈ Finset.univ.erase m, edgeCountIn (colourClass c' j) (T m) := by
      have hle : (Finset.univ.erase m).card
          ≤ ∑ j ∈ Finset.univ.erase m, edgeCountIn (colourClass c' j) (T m) := by
        rw [Finset.card_eq_sum_ones]
        exact Finset.sum_le_sum (fun j hj => hpos_j j (Finset.ne_of_mem_erase hj))
      rw [Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ,
        Fintype.card_fin] at hle
      omega
    omega
  -- Step 6: instantiate MM at the minority class
  exact hMM (colourClass c' m)
    (fun S hS => indep_le_five hbal' m S hS)
    (fun S hS => cap_eleven hbal' m S hS)
    hmin60 (T m) (step4 m)
    (fun S hindep hdisj => step2 m S hindep hdisj)
    step5

/- `lemma_MH2` and `lemma_MM` are proved in `Lean617.MH2Proof` and
`Lean617.MMProof` (as `lemma_MH2_of` / `lemma_MM_of`, conditional on the
hypothesis structures `PrimFacts` — discharged in `Lean617.Primitives` — and
`BrouwerFacts`). The final assembly lives in `Lean617.Final` to avoid an
import cycle. -/

end Erdos617
