/-
D3 JOIN-TRANSPORT (D-campaign runner 20). The descent (`EqualityProof.lean`) peels three
independent 4-sets off an extremal `J : SimpleGraph (Fin 21)`, each joined completely to
everything below (a cone). This file bundles that into an iso `J ≅ kpG ∨ J ≅ kpG1`.

Canonical cone extension `coneExtend G : SimpleGraph (Fin (m+4))`: `G` on the low positions
`0..m-1`, 4 fresh independent vertices `m..m+3` joined to all of `0..m-1`. Iterating from the
9-vertex base:  `coneExtend^3 base9A2 = K_{4,4,4} * base9A2`  (numerically `= kpG`,
scratchpad/coneextend_iso.py, explicit σ v = if v<8 then v else if v=20 then 8 else v+1).

Route: (1) `coneExtend` + functoriality `coneExtend_congr`; (2) `GIso` refl/symm/trans/compl;
(3) `cone_to_coneExtend` — the abstract cone→iso from the enriched descent data; (4) the concrete
witnesses `GIso kpG (coneExtend^3 base9A2)` / `kpG1 …` by native_decide; (5) chain.

Research project: Mathlib style linters disabled.
-/
import Lean617.EqualityProof
import Lean617.KPConstruction
import Lean617.Equality21

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.multiGoal false
set_option linter.style.openClassical false
set_option linter.style.nativeDecide false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

open Finset SimpleGraph

namespace Erdos617

/-! ## `coneExtend`: add 4 independent vertices, joined to everything -/

/-- Cone extension: `G` on low positions `0..m-1` of `Fin (m+4)`, plus 4 fresh independent
vertices `m..m+3` each joined to all of `0..m-1`. -/
def coneExtend {m : ℕ} (G : SimpleGraph (Fin m)) : SimpleGraph (Fin (m + 4)) where
  Adj u v :=
    if hu : (u : ℕ) < m then
      if hv : (v : ℕ) < m then G.Adj ⟨u, hu⟩ ⟨v, hv⟩ else True
    else
      if _hv : (v : ℕ) < m then True else False
  symm := by
    intro u v h
    by_cases hu : (u : ℕ) < m <;> by_cases hv : (v : ℕ) < m <;>
      simp only [hu, hv, dif_pos, dif_neg] at h ⊢
    · exact h.symm
    · exact h
    · exact h
    · exact h
  loopless := ⟨fun u h => by
    by_cases hu : (u : ℕ) < m
    · simp only [dif_pos hu] at h; exact G.loopless.irrefl _ h
    · simp only [dif_neg hu] at h⟩

/-- `coneExtend`, both low: reduces to `G`. -/
theorem coneExtend_adj_ll {m : ℕ} (G : SimpleGraph (Fin m)) {u v : Fin (m + 4)}
    (hu : (u : ℕ) < m) (hv : (v : ℕ) < m) :
    (coneExtend G).Adj u v = G.Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
  simp only [coneExtend, dif_pos hu, dif_pos hv]

/-- `coneExtend`, low–high: adjacent. -/
theorem coneExtend_adj_lh {m : ℕ} (G : SimpleGraph (Fin m)) {u v : Fin (m + 4)}
    (hu : (u : ℕ) < m) (hv : ¬ (v : ℕ) < m) : (coneExtend G).Adj u v := by
  simp only [coneExtend, dif_pos hu, dif_neg hv]

/-- `coneExtend`, high–low: adjacent. -/
theorem coneExtend_adj_hl {m : ℕ} (G : SimpleGraph (Fin m)) {u v : Fin (m + 4)}
    (hu : ¬ (u : ℕ) < m) (hv : (v : ℕ) < m) : (coneExtend G).Adj u v := by
  simp only [coneExtend, dif_neg hu, dif_pos hv]

/-- `coneExtend`, both high: non-adjacent. -/
theorem coneExtend_adj_hh {m : ℕ} (G : SimpleGraph (Fin m)) {u v : Fin (m + 4)}
    (hu : ¬ (u : ℕ) < m) (hv : ¬ (v : ℕ) < m) : ¬ (coneExtend G).Adj u v := by
  simp only [coneExtend, dif_neg hu, dif_neg hv]; exact not_false

/-- Decidability of `coneExtend`, structured so `native_decide` can evaluate it on concrete
graphs. -/
instance coneExtend_decRel {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj] :
    DecidableRel (coneExtend G).Adj := fun u v =>
  if hu : (u : ℕ) < m then
    if hv : (v : ℕ) < m then
      decidable_of_iff (G.Adj ⟨u, hu⟩ ⟨v, hv⟩) (coneExtend_adj_ll G hu hv).symm.to_iff
    else isTrue (coneExtend_adj_lh G hu hv)
  else
    if hv : (v : ℕ) < m then isTrue (coneExtend_adj_hl G hu hv)
    else isFalse (coneExtend_adj_hh G hu hv)

/-! ## `GIso`: unbundled graph isomorphism (matches the codebase's `∃ σ, …` style) -/

/-- Graph isomorphism as a raw existential (the shape used throughout `EqualityProof`/`Equality21`):
`σ : Fin n ≃ Fin n` carrying `G` to `H`. -/
def GIso {n : ℕ} (G H : SimpleGraph (Fin n)) : Prop :=
  ∃ σ : Fin n ≃ Fin n, ∀ a b, G.Adj a b ↔ H.Adj (σ a) (σ b)

theorem GIso.refl {n : ℕ} (G : SimpleGraph (Fin n)) : GIso G G :=
  ⟨Equiv.refl _, fun _ _ => Iff.rfl⟩

theorem GIso.symm {n : ℕ} {G H : SimpleGraph (Fin n)} (h : GIso G H) : GIso H G := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨σ.symm, fun a b => ?_⟩
  rw [hσ (σ.symm a) (σ.symm b), σ.apply_symm_apply, σ.apply_symm_apply]

theorem GIso.trans {n : ℕ} {G H I : SimpleGraph (Fin n)} (h1 : GIso G H) (h2 : GIso H I) :
    GIso G I := by
  obtain ⟨σ, hσ⟩ := h1
  obtain ⟨τ, hτ⟩ := h2
  exact ⟨σ.trans τ, fun a b => (hσ a b).trans (hτ (σ a) (σ b))⟩

/-- Isomorphic graphs have isomorphic complements (same `σ`). -/
theorem GIso.compl {n : ℕ} {G H : SimpleGraph (Fin n)} (h : GIso G H) : GIso Gᶜ Hᶜ := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨σ, fun a b => ?_⟩
  rw [SimpleGraph.compl_adj, SimpleGraph.compl_adj]
  constructor
  · rintro ⟨hne, hnadj⟩
    exact ⟨fun heq => hne (σ.injective heq), fun hadj => hnadj ((hσ a b).mpr hadj)⟩
  · rintro ⟨hne, hnadj⟩
    exact ⟨fun heq => hne (congrArg σ heq), fun hadj => hnadj ((hσ a b).mp hadj)⟩

/-! ## Functoriality of `coneExtend` -/

/-- Extend `σ : Fin m ≃ Fin m` to `Fin (m+4)` by acting on the low part and fixing the high 4. -/
def coneExtendEquiv {m : ℕ} (σ : Fin m ≃ Fin m) : Fin (m + 4) ≃ Fin (m + 4) where
  toFun u := if h : (u : ℕ) < m then Fin.castAdd 4 (σ ⟨u, h⟩) else u
  invFun u := if h : (u : ℕ) < m then Fin.castAdd 4 (σ.symm ⟨u, h⟩) else u
  left_inv := fun u => by
    by_cases h : (u : ℕ) < m
    · have hlt : ((Fin.castAdd 4 (σ ⟨u, h⟩) : Fin (m + 4)) : ℕ) < m := by
        rw [Fin.val_castAdd]; exact (σ ⟨u, h⟩).isLt
      simp only [dif_pos h, dif_pos hlt]
      have he : (⟨↑(Fin.castAdd 4 (σ ⟨u, h⟩)), hlt⟩ : Fin m) = σ ⟨u, h⟩ :=
        Fin.ext (Fin.val_castAdd 4 (σ ⟨u, h⟩))
      rw [he, σ.symm_apply_apply]; apply Fin.ext; rw [Fin.val_castAdd]
    · simp only [dif_neg h]
  right_inv := fun u => by
    by_cases h : (u : ℕ) < m
    · have hlt : ((Fin.castAdd 4 (σ.symm ⟨u, h⟩) : Fin (m + 4)) : ℕ) < m := by
        rw [Fin.val_castAdd]; exact (σ.symm ⟨u, h⟩).isLt
      simp only [dif_pos h, dif_pos hlt]
      have he : (⟨↑(Fin.castAdd 4 (σ.symm ⟨u, h⟩)), hlt⟩ : Fin m) = σ.symm ⟨u, h⟩ :=
        Fin.ext (Fin.val_castAdd 4 (σ.symm ⟨u, h⟩))
      rw [he, σ.apply_symm_apply]; apply Fin.ext; rw [Fin.val_castAdd]
    · simp only [dif_neg h]

theorem coneExtendEquiv_low {m : ℕ} (σ : Fin m ≃ Fin m) {u : Fin (m + 4)} (h : (u : ℕ) < m) :
    coneExtendEquiv σ u = Fin.castAdd 4 (σ ⟨u, h⟩) := dif_pos h

theorem coneExtendEquiv_high {m : ℕ} (σ : Fin m ≃ Fin m) {u : Fin (m + 4)} (h : ¬ (u : ℕ) < m) :
    coneExtendEquiv σ u = u := dif_neg h

theorem coneExtendEquiv_val_eq {m : ℕ} (σ : Fin m ≃ Fin m) {u : Fin (m + 4)} (h : (u : ℕ) < m) :
    ((coneExtendEquiv σ u : Fin (m + 4)) : ℕ) = (σ ⟨u, h⟩ : Fin m) := by
  rw [coneExtendEquiv_low σ h, Fin.val_castAdd]

theorem coneExtendEquiv_val_low {m : ℕ} (σ : Fin m ≃ Fin m) {u : Fin (m + 4)} (h : (u : ℕ) < m) :
    ((coneExtendEquiv σ u : Fin (m + 4)) : ℕ) < m := by
  rw [coneExtendEquiv_val_eq σ h]; exact (σ ⟨u, h⟩).isLt

theorem coneExtendEquiv_val_high {m : ℕ} (σ : Fin m ≃ Fin m) {u : Fin (m + 4)}
    (h : ¬ (u : ℕ) < m) : ¬ ((coneExtendEquiv σ u : Fin (m + 4)) : ℕ) < m := by
  rw [coneExtendEquiv_high σ h]; exact h

/-- **Functoriality:** `coneExtend` preserves `GIso`. -/
theorem coneExtend_congr {m : ℕ} {G H : SimpleGraph (Fin m)} (h : GIso G H) :
    GIso (coneExtend G) (coneExtend H) := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨coneExtendEquiv σ, fun a b => ?_⟩
  by_cases ha : (a : ℕ) < m <;> by_cases hb : (b : ℕ) < m
  · -- both low
    rw [coneExtend_adj_ll G ha hb,
      coneExtend_adj_ll H (coneExtendEquiv_val_low σ ha) (coneExtendEquiv_val_low σ hb)]
    have hea : (⟨↑(coneExtendEquiv σ a), coneExtendEquiv_val_low σ ha⟩ : Fin m) = σ ⟨a, ha⟩ :=
      Fin.ext (coneExtendEquiv_val_eq σ ha)
    have heb : (⟨↑(coneExtendEquiv σ b), coneExtendEquiv_val_low σ hb⟩ : Fin m) = σ ⟨b, hb⟩ :=
      Fin.ext (coneExtendEquiv_val_eq σ hb)
    rw [hea, heb]; exact hσ ⟨a, ha⟩ ⟨b, hb⟩
  · -- low, high
    exact iff_of_true (coneExtend_adj_lh G ha hb)
      (coneExtend_adj_lh H (coneExtendEquiv_val_low σ ha) (coneExtendEquiv_val_high σ hb))
  · -- high, low
    exact iff_of_true (coneExtend_adj_hl G ha hb)
      (coneExtend_adj_hl H (coneExtendEquiv_val_high σ ha) (coneExtendEquiv_val_low σ hb))
  · -- both high
    exact iff_of_false (coneExtend_adj_hh G ha hb)
      (coneExtend_adj_hh H (coneExtendEquiv_val_high σ ha) (coneExtendEquiv_val_high σ hb))

/-! ## The abstract cone → `coneExtend` iso (consumes the enriched descent data) -/

/-- Reconstruction map: `f` (the neighbourhood embedding) on the low block, `cval` (a `Fin 4`
enumeration of the cone set `C = V∖Γx`) on the high block. -/
def coneRho {n m : ℕ} (f : Fin m ↪ Fin n) (cval : Fin 4 → Fin n) : Fin (m + 4) → Fin n :=
  Fin.addCases (fun a => f a) (fun b => cval b)

@[simp] theorem coneRho_castAdd {n m : ℕ} (f : Fin m ↪ Fin n) (cval : Fin 4 → Fin n) (a : Fin m) :
    coneRho f cval (Fin.castAdd 4 a) = f a := Fin.addCases_left a

@[simp] theorem coneRho_natAdd {n m : ℕ} (f : Fin m ↪ Fin n) (cval : Fin 4 → Fin n) (b : Fin 4) :
    coneRho f cval (Fin.natAdd m b) = cval b := Fin.addCases_right b

/-- **The cone → iso lemma (the heart of the reassembly).** If `J : SimpleGraph (Fin n)` is a cone
over the neighbourhood `Γx = image f` (`C = V∖Γx` independent, `Γx–C` complete) with `n = m + 4`,
then `J ≅ coneExtend (J.comap f)` — the induced graph on `Γx` with an independent 4-set joined to it.
This is exactly what the enriched descent returns, packaged as a `coneExtend`. -/
theorem cone_to_coneExtend {n m : ℕ} (hn : n = m + 4) (J : SimpleGraph (Fin n)) (f : Fin m ↪ Fin n)
    (hindep : ∀ u ∈ Finset.univ \ Finset.univ.image f, ∀ v ∈ Finset.univ \ Finset.univ.image f,
      ¬ J.Adj u v)
    (hcompl : ∀ u ∈ Finset.univ.image f, ∀ v ∈ Finset.univ \ Finset.univ.image f, J.Adj u v) :
    ∃ τ : Fin n ≃ Fin (m + 4), ∀ a b, J.Adj a b ↔ (coneExtend (J.comap f)).Adj (τ a) (τ b) := by
  classical
  set C := Finset.univ \ Finset.univ.image f with hCdef
  have hCcard : C.card = 4 := by
    have h1 : (Finset.univ.image f).card = m := by
      rw [Finset.card_image_of_injective Finset.univ f.injective, Finset.card_univ, Fintype.card_fin]
    rw [hCdef, ← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin, h1]
    omega
  set cval : Fin 4 → Fin n := ⇑(C.orderEmbOfFin hCcard) with hcvaldef
  have hfmem : ∀ a, f a ∈ Finset.univ.image f := fun a => Finset.mem_image_of_mem f (Finset.mem_univ a)
  have hcmem : ∀ b, cval b ∈ C := fun b => C.orderEmbOfFin_mem hCcard b
  have hcnotim : ∀ b, cval b ∉ Finset.univ.image f := fun b => (Finset.mem_sdiff.mp (hcmem b)).2
  have hcinj : Function.Injective cval := (C.orderEmbOfFin hCcard).injective
  have hlow : ∀ a : Fin m, ((Fin.castAdd 4 a : Fin (m + 4)) : ℕ) < m := fun a => by
    rw [Fin.val_castAdd]; exact a.isLt
  have hhigh : ∀ b : Fin 4, ¬ ((Fin.natAdd m b : Fin (m + 4)) : ℕ) < m := fun b => by
    rw [Fin.val_natAdd]; omega
  -- ρ is injective (f-block ⊆ image f, cval-block ⊆ C, disjoint; each injective)
  have hρinj : Function.Injective (coneRho f cval) := by
    intro i j hij
    induction i using Fin.addCases with
    | left a =>
      induction j using Fin.addCases with
      | left b => rw [coneRho_castAdd, coneRho_castAdd] at hij
                  exact congrArg (Fin.castAdd 4) (f.injective hij)
      | right b => rw [coneRho_castAdd, coneRho_natAdd] at hij
                   exact absurd (hij ▸ hfmem a) (hcnotim b)
    | right a =>
      induction j using Fin.addCases with
      | left b => rw [coneRho_natAdd, coneRho_castAdd] at hij
                  exact absurd (hij.symm ▸ hfmem b) (hcnotim a)
      | right b => rw [coneRho_natAdd, coneRho_natAdd] at hij
                   exact congrArg (Fin.natAdd m) (hcinj hij)
  have hbij : Function.Bijective (coneRho f cval) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨hρinj, by rw [Fintype.card_fin, Fintype.card_fin]; omega⟩
  -- adjacency transport along ρ
  have hρadj : ∀ i j, J.Adj (coneRho f cval i) (coneRho f cval j) ↔
      (coneExtend (J.comap f)).Adj i j := by
    intro i j
    induction i using Fin.addCases with
    | left a =>
      induction j using Fin.addCases with
      | left b =>
        rw [coneRho_castAdd, coneRho_castAdd, coneExtend_adj_ll (J.comap f) (hlow a) (hlow b),
          SimpleGraph.comap_adj]
        exact Iff.rfl
      | right b =>
        rw [coneRho_castAdd, coneRho_natAdd]
        exact iff_of_true (hcompl (f a) (hfmem a) (cval b) (hcmem b))
          (coneExtend_adj_lh (J.comap f) (hlow a) (hhigh b))
    | right a =>
      induction j using Fin.addCases with
      | left b =>
        rw [coneRho_natAdd, coneRho_castAdd]
        exact iff_of_true (hcompl (f b) (hfmem b) (cval a) (hcmem a)).symm
          (coneExtend_adj_hl (J.comap f) (hhigh a) (hlow b))
      | right b =>
        rw [coneRho_natAdd, coneRho_natAdd]
        exact iff_of_false (hindep (cval a) (hcmem a) (cval b) (hcmem b))
          (coneExtend_adj_hh (J.comap f) (hhigh a) (hhigh b))
  refine ⟨(Equiv.ofBijective (coneRho f cval) hbij).symm, fun a b => ?_⟩
  have hρa : coneRho f cval ((Equiv.ofBijective (coneRho f cval) hbij).symm a) = a :=
    (Equiv.ofBijective (coneRho f cval) hbij).apply_symm_apply a
  have hρb : coneRho f cval ((Equiv.ofBijective (coneRho f cval) hbij).symm b) = b :=
    (Equiv.ofBijective (coneRho f cval) hbij).apply_symm_apply b
  have h := hρadj ((Equiv.ofBijective (coneRho f cval) hbij).symm a)
    ((Equiv.ofBijective (coneRho f cval) hbij).symm b)
  rw [hρa, hρb] at h
  exact h

/-! ## The concrete witnesses `GIso kpG (coneExtend³ base9A2)` (and `kpG1`/`base9A1`)

Explicit σ from scratchpad/coneextend_iso.py: `σ v = if v<8 then v else if v=20 then 8 else v+1`
(the three parts `N₂,N₃,N₄` of `kpG` map to the three cone layers, the base `N₀∪N₁∪{apex}` to the
low 9). Both directions and the 441-pair adjacency identity are `native_decide`/`decide` checks on
concrete `Fin 21` graphs. -/

/-- The explicit descent-realizing permutation of `Fin 21`. -/
def sigmaW : Fin 21 ≃ Fin 21 where
  toFun v := if _h1 : (v : ℕ) < 8 then v
    else if _h2 : (v : ℕ) = 20 then ⟨8, by omega⟩
    else ⟨(v : ℕ) + 1, by have := v.isLt; omega⟩
  invFun w := if _h1 : (w : ℕ) < 8 then w
    else if _h2 : (w : ℕ) = 8 then ⟨20, by omega⟩
    else ⟨(w : ℕ) - 1, by have := w.isLt; omega⟩
  left_inv := by decide
  right_inv := by decide

/-- **Witness 1:** `kpG ≅ coneExtend³ base9A2` (the `|A*|=2` class). -/
theorem kpG_giso_cone3 : GIso kpG (coneExtend (coneExtend (coneExtend base9A2))) :=
  ⟨sigmaW, by native_decide⟩

/-- **Witness 2:** `kpG1 ≅ coneExtend³ base9A1` (the `|A*|=1` class). -/
theorem kpG1_giso_cone3 : GIso kpG1 (coneExtend (coneExtend (coneExtend base9A1))) :=
  ⟨sigmaW, by native_decide⟩

/-! ## The reassembly: `extremal21 J → J ≅ kpG ∨ J ≅ kpG1` -/

/-- **D3 reassembly.** An extremal `J` on `Fin 21` (`K₆`-free, `α≤4`, `e=173`) is isomorphic to `kpG`
or `kpG1`. Runs the three enriched descents (each peeling an independent 4-set as a `coneExtend`
layer), classifies the 9-vertex base, then transports the base iso up through the three cone layers
by functoriality and lands on the concrete witnesses. -/
theorem extremal21_giso (J : SimpleGraph (Fin 21)) (hK6 : J.CliqueFree 6)
    (hα : alphaAtMost J 4) (he : edgeCountIn J Finset.univ = 173) :
    GIso J kpG ∨ GIso J kpG1 := by
  obtain ⟨J1, f1, hJ1eq, hK5₁, hα₁, he₁, hindep₁, hcompl₁⟩ := descent_21_to_17 J hK6 hα he
  subst hJ1eq
  obtain ⟨J2, f2, hJ2eq, hK4₂, hα₂, he₂, hindep₂, hcompl₂⟩ := descent_17_to_13 _ hK5₁ hα₁ he₁
  subst hJ2eq
  obtain ⟨J3, f3, hJ3eq, hK3₃, hα₃, he₃, hindep₃, hcompl₃⟩ := descent_13_to_9 _ hK4₂ hα₂ he₂
  subst hJ3eq
  have g1 : GIso J (coneExtend (J.comap f1)) := cone_to_coneExtend rfl J f1 hindep₁ hcompl₁
  have g2 : GIso (J.comap f1) (coneExtend ((J.comap f1).comap f2)) :=
    cone_to_coneExtend rfl (J.comap f1) f2 hindep₂ hcompl₂
  have g3 : GIso ((J.comap f1).comap f2) (coneExtend (((J.comap f1).comap f2).comap f3)) :=
    cone_to_coneExtend rfl ((J.comap f1).comap f2) f3 hindep₃ hcompl₃
  obtain ⟨σ, hσ⟩ := base_classification (((J.comap f1).comap f2).comap f3) hK3₃ hα₃ he₃
  rcases hσ with hbase | hbase
  · left
    have gbase : GIso (((J.comap f1).comap f2).comap f3) base9A2 := ⟨σ, hbase⟩
    have G2 := g3.trans (coneExtend_congr gbase)
    have G1 := g2.trans (coneExtend_congr G2)
    have G0 := g1.trans (coneExtend_congr G1)
    exact G0.trans kpG_giso_cone3.symm
  · right
    have gbase : GIso (((J.comap f1).comap f2).comap f3) base9A1 := ⟨σ, hbase⟩
    have G2 := g3.trans (coneExtend_congr gbase)
    have G1 := g2.trans (coneExtend_congr G2)
    have G0 := g1.trans (coneExtend_congr G1)
    exact G0.trans kpG1_giso_cone3.symm

/-! ## D4 assembly: `KPEqualityClassification` is PROVEN -/

/-- **D4 — the (5,21) Kang–Pikhurko equality classification, PROVEN.** Every extremal colour class
`F` (`α≤5`, `K₅`-free, `e=37`) has `F ≅ kpGᶜ` or `F ≅ kpG1ᶜ`, both of which carry the extremal A/B
structure (`AB21_kpG_compl`/`AB21_kpG1_compl`). Chains `equality21_reduce` (F↦extremal complement)
→ `extremal21_giso` (the D3 reassembly) → complement transport. This discharges the sole classical
hypothesis the r=5 resolution was conditional on. -/
theorem kp_equality_classification_proven : KPEqualityClassification := by
  intro F hα hK5 he
  obtain ⟨hK6, hαc, hec⟩ := equality21_reduce F hα hK5 he
  rcases extremal21_giso Fᶜ hK6 hαc hec with h | h
  · obtain ⟨σ, hσ⟩ := h.compl
    refine ⟨kpGᶜ, σ, fun a b => ?_, AB21_kpG_compl⟩
    rw [show F = Fᶜᶜ from (compl_compl F).symm]; exact hσ a b
  · obtain ⟨σ, hσ⟩ := h.compl
    refine ⟨kpG1ᶜ, σ, fun a b => ?_, AB21_kpG1_compl⟩
    rw [show F = Fᶜᶜ from (compl_compl F).symm]; exact hσ a b

end Erdos617
