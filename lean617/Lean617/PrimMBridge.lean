import Lean617.PrimBridge

/-!
# Graph → SAT bridge for the M-instances (cardinality version).

`MCNF n k` adds a Sinz sequential-counter "at most k edges" to `alpha ++ omega ++ cap`. Given a
graph with the graph properties AND `≤ k` edges, we extend `assign` to the counter's auxiliary
variables by the partial-sum bits `sbit`, and show every clause is satisfied — contradicting
`(MCNF n k).Unsat`. Hence such a graph has `≥ k+1` edges (M9: 19, M10: 25).
-/

open Std.Sat Finset
open scoped Classical

namespace Erdos617

open Erdos617F3

/-! ## Partial sums over the fixed edge list and the extended assignment. -/

/-- Is the pair-list `P = [a,b]` an edge of `G`? -/
noncomputable def edgePresent {n : ℕ} (G : SimpleGraph (Fin n)) (P : List (Fin n)) : Bool :=
  match P with
  | [a, b] => decide (G.Adj a b)
  | _ => false

/-- Number of present edges among the first `m` entries of `edgeList n`. -/
noncomputable def psum {n : ℕ} (G : SimpleGraph (Fin n)) (m : ℕ) : ℕ :=
  ((edgeList n).take m).countP (edgePresent G)

/-- Intended value of the counter bit `s(i,j)`: "at least `j+1` of `e₀..eᵢ` are present". -/
noncomputable def sbit {n : ℕ} (G : SimpleGraph (Fin n)) (i j : ℕ) : Bool :=
  decide (j + 1 ≤ psum G (i + 1))

/-- The M-instance assignment: edge variables via `assign`, counter variables via `sbit`. -/
noncomputable def assignM (n k : ℕ) (G : SimpleGraph (Fin n)) (v : Nat) : Bool :=
  if v < n * n then assign G v else sbit G ((v - n * n) / k) ((v - n * n) % k)

/-- `edgeVarL` of any pair is a valid edge-variable index `< n²`. -/
theorem edgeVarL_lt {n : ℕ} (hn : 0 < n) (P : List (Fin n)) : edgeVarL P < n * n := by
  unfold edgeVarL
  split
  · rename_i a b
    calc a.val * n + b.val < (a.val + 1) * n := by rw [Nat.add_mul, Nat.one_mul]; omega
      _ ≤ n * n := Nat.mul_le_mul_right n (by omega)
  · exact Nat.mul_pos hn hn

/-- On edge variables, `assignM` agrees with `assign`. -/
theorem assignM_edge {n k : ℕ} (G : SimpleGraph (Fin n)) {v : Nat} (h : v < n * n) :
    assignM n k G v = assign G v := by simp [assignM, h]

/-- The counter variables decode correctly (needs `j < k`). -/
theorem assignM_aux {n k : ℕ} (G : SimpleGraph (Fin n)) (i j : ℕ) (hj : j < k) :
    assignM n k G (auxVar n k i j) = sbit G i j := by
  have hk : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le j) hj
  have hge : ¬ auxVar n k i j < n * n := by simp only [auxVar]; omega
  have hsub : auxVar n k i j - n * n = i * k + j := by simp only [auxVar]; omega
  have hik : (i * k + j) / k = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hj, Nat.zero_add]
  have hjk : (i * k + j) % k = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  simp only [assignM, hge, if_false, hsub, hik, hjk]

/-! ## Edge-list / partial-sum facts. -/

/-- `getD` at an in-range index is the `getElem`. -/
theorem eNth_getElem {n m : ℕ} (hm : m < (edgeList n).length) :
    (edgeList n).getD m [] = (edgeList n)[m] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]; rfl

/-- Every entry of `edgeList n` (within range) is a genuine pair `[a,b]`. -/
theorem eNth_pair {n m : ℕ} (hm : m < (edgeList n).length) :
    ∃ a b : Fin n, (edgeList n).getD m [] = [a, b] := by
  have hmem : (edgeList n)[m] ∈ pairsOf (List.finRange n) := List.getElem_mem hm
  obtain ⟨a, b, hab, _, _⟩ := mem_pairsOf_imp hmem
  exact ⟨a, b, (eNth_getElem hm).trans hab⟩

/-- `assign` reads the `m`-th edge variable back as "edge `m` present". -/
theorem assign_evar {n : ℕ} (G : SimpleGraph (Fin n)) {m : ℕ} (hm : m < (edgeList n).length) :
    assign G (evar n m) = edgePresent G ((edgeList n).getD m []) := by
  obtain ⟨a, b, hab⟩ := eNth_pair hm
  rw [evar, hab, assign_edgeVarL]
  rfl

/-- The running count increases by 1 exactly when edge `m` is present. -/
theorem psum_succ {n : ℕ} (G : SimpleGraph (Fin n)) {m : ℕ} (hm : m < (edgeList n).length) :
    psum G (m + 1) = psum G m + (if edgePresent G ((edgeList n).getD m []) then 1 else 0) := by
  rw [eNth_getElem hm]
  unfold psum
  rw [List.take_succ, List.getElem?_eq_getElem hm, List.countP_append]
  simp [List.countP_cons]

/-- Monotonicity of the running count. -/
theorem psum_mono {n : ℕ} (G : SimpleGraph (Fin n)) (m : ℕ) : psum G m ≤ psum G (m + 1) := by
  by_cases hm : m < (edgeList n).length
  · rw [psum_succ G hm]; omega
  · unfold psum
    rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

/-- After the first edge, the count is at most 1. -/
theorem psum_one_le {n : ℕ} (G : SimpleGraph (Fin n)) : psum G 1 ≤ 1 := by
  unfold psum
  calc ((edgeList n).take 1).countP (edgePresent G)
      ≤ ((edgeList n).take 1).length := List.countP_le_length
    _ ≤ 1 := by simpa using List.length_take_le 1 (edgeList n)

/-! ## Agreement of `assignM` with `assign` on edge-only clauses. -/

/-- On a clause all of whose variables are `< n²`, `assignM` and `assign` give the same value. -/
theorem eval_congr_lt {n k : ℕ} (G : SimpleGraph (Fin n)) (c : List (Nat × Bool))
    (h : ∀ l ∈ c, l.1 < n * n) :
    CNF.Clause.eval (assignM n k G) c = CNF.Clause.eval (assign G) c := by
  induction c with
  | nil => rfl
  | cons a t ih =>
    rw [CNF.Clause.eval_cons, CNF.Clause.eval_cons,
      assignM_edge G (h a List.mem_cons_self),
      ih (fun l hl => h l (List.mem_cons_of_mem _ hl))]

/-- Every literal of an `alpha`/`omega` clause, or a `cap` clause, is an edge variable. -/
theorem pairLits_lt {n : ℕ} (hn : 0 < n) (pos : Bool) (pairs : List (List (Fin n)))
    (l : Nat × Bool) (hl : l ∈ pairLits pos pairs) : l.1 < n * n := by
  simp only [pairLits, List.mem_map] at hl
  obtain ⟨P, _, rfl⟩ := hl
  exact edgeVarL_lt hn P

/-- The total running count is at most the edge count (injection into `univ.sym2 ∩ edges`). -/
theorem psum_total_le_edgeCount {n : ℕ} [NeZero n] (G : SimpleGraph (Fin n)) :
    psum G (edgeList n).length ≤ edgeCountIn G Finset.univ := by
  have hpsum : psum G (edgeList n).length = ((edgeList n).filter (edgePresent G)).length := by
    unfold psum
    rw [List.take_length, List.countP_eq_length_filter]
  set fl := (edgeList n).filter (edgePresent G) with hfl
  have hflsub : List.Sublist fl (edgeList n) := List.filter_sublist
  have hnodup : (fl.map s2).Nodup :=
    (pairsOf_map_s2_nodup (l := List.finRange n) (List.nodup_finRange n)).sublist (hflsub.map s2)
  have hsubE : (fl.map s2).toFinset ⊆ Finset.univ.sym2.filter (fun e => e ∈ G.edgeSet) := by
    intro e he
    rw [List.mem_toFinset, List.mem_map] at he
    obtain ⟨P, hP, rfl⟩ := he
    rw [hfl, List.mem_filter] at hP
    obtain ⟨hPmem, hPpres⟩ := hP
    obtain ⟨a, b, rfl, _, _⟩ := mem_pairsOf_imp hPmem
    have hadj : G.Adj a b := by simpa [edgePresent] using hPpres
    rw [s2_pair, Finset.mem_filter, Finset.mk_mem_sym2_iff]
    refine ⟨⟨Finset.mem_univ a, Finset.mem_univ b⟩, ?_⟩
    rw [SimpleGraph.mem_edgeSet]; exact hadj
  calc psum G (edgeList n).length = fl.length := hpsum
    _ = (fl.map s2).length := by rw [List.length_map]
    _ = (fl.map s2).toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
    _ ≤ edgeCountIn G Finset.univ := Finset.card_le_card hsubE

/-- Multi-step monotonicity of the running count. -/
theorem psum_le {n : ℕ} (G : SimpleGraph (Fin n)) {a b : ℕ} (h : a ≤ b) :
    psum G a ≤ psum G b := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (psum_mono G _)

/-- `assignM` on the `i`-th edge variable. -/
theorem assignM_evar {n k : ℕ} [NeZero n] (G : SimpleGraph (Fin n)) {i : ℕ}
    (hi : i < (edgeList n).length) :
    assignM n k G (evar n i) = edgePresent G ((edgeList n).getD i []) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  rw [assignM_edge G (show evar n i < n * n from edgeVarL_lt hn _), assign_evar G hi]

/-! ## The five Sinz clause families are satisfied. -/

variable {n k : ℕ}

theorem cardA_sat [NeZero n] (G : SimpleGraph (Fin n)) {i : ℕ}
    (hi : i < (edgeList n).length) (hk : 0 < k) :
    CNF.Clause.eval (assignM n k G) [(evar n i, false), (auxVar n k i 0, true)] = true := by
  simp only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false,
    assignM_evar G hi, assignM_aux G i 0 hk]
  by_cases hp : edgePresent G ((edgeList n).getD i []) = true
  · have hs : sbit G i 0 = true := by
      unfold sbit; rw [psum_succ G hi, hp]; simp
    rw [hs]; simp
  · rw [Bool.not_eq_true] at hp; rw [hp]; simp

theorem cardB_sat [NeZero n] (G : SimpleGraph (Fin n)) {i j : ℕ}
    (hi1 : 1 ≤ i) (hj : j < k) :
    CNF.Clause.eval (assignM n k G)
      [(auxVar n k (i - 1) j, false), (auxVar n k i j, true)] = true := by
  simp only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false,
    assignM_aux G (i - 1) j hj, assignM_aux G i j hj]
  have hii : i - 1 + 1 = i := by omega
  by_cases hb : sbit G (i - 1) j = true
  · have hs : sbit G i j = true := by
      unfold sbit at hb ⊢
      rw [hii] at hb
      have := psum_mono G i
      simp only [decide_eq_true_eq] at hb ⊢; omega
    simp [hs]
  · simp only [Bool.not_eq_true] at hb; simp [hb]

theorem cardC_sat [NeZero n] (G : SimpleGraph (Fin n)) {i j : ℕ}
    (hi : i < (edgeList n).length) (hi1 : 1 ≤ i) (hj1 : 1 ≤ j) (hj : j < k) :
    CNF.Clause.eval (assignM n k G)
      [(evar n i, false), (auxVar n k (i - 1) (j - 1), false), (auxVar n k i j, true)] = true := by
  have hjk : j - 1 < k := by omega
  simp only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false,
    assignM_evar G hi, assignM_aux G (i - 1) (j - 1) hjk, assignM_aux G i j hj]
  have hii : i - 1 + 1 = i := by omega
  by_cases hp : edgePresent G ((edgeList n).getD i []) = true
  · by_cases hb : sbit G (i - 1) (j - 1) = true
    · have hbb : j ≤ psum G i := by
        unfold sbit at hb; rw [hii, decide_eq_true_eq] at hb; omega
      have hstep : psum G (i + 1) = psum G i + 1 := by rw [psum_succ G hi, hp]; simp
      have hs : sbit G i j = true := by
        unfold sbit; rw [hstep, decide_eq_true_eq]; omega
      rw [hs]; simp
    · rw [Bool.not_eq_true] at hb; rw [hb]; simp
  · rw [Bool.not_eq_true] at hp; rw [hp]; simp

theorem cardD_sat [NeZero n] (G : SimpleGraph (Fin n)) {j : ℕ}
    (hj1 : 1 ≤ j) (hj : j < k) :
    CNF.Clause.eval (assignM n k G) [(auxVar n k 0 j, false)] = true := by
  simp only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false, assignM_aux G 0 j hj]
  have hs : sbit G 0 j = false := by
    unfold sbit
    rw [Nat.zero_add]
    have := psum_one_le (n := n) G
    simp only [decide_eq_false_iff_not]; omega
  rw [hs]; simp

theorem cardE_sat [NeZero n] (G : SimpleGraph (Fin n)) {i : ℕ}
    (hi : i < (edgeList n).length) (hi1 : 1 ≤ i) (hk : 1 ≤ k)
    (hpk : psum G (edgeList n).length ≤ k) :
    CNF.Clause.eval (assignM n k G)
      [(evar n i, false), (auxVar n k (i - 1) (k - 1), false)] = true := by
  have hk1 : k - 1 < k := by omega
  simp only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false,
    assignM_evar G hi, assignM_aux G (i - 1) (k - 1) hk1]
  have hii : i - 1 + 1 = i := by omega
  by_cases hp : edgePresent G ((edgeList n).getD i []) = true
  · have hb : sbit G (i - 1) (k - 1) = false := by
      unfold sbit
      rw [hii]
      have hmono : psum G (i + 1) ≤ psum G (edgeList n).length := psum_le G (by omega)
      have hstep : psum G (i + 1) = psum G i + 1 := by rw [psum_succ G hi, hp]; simp
      simp only [decide_eq_false_iff_not]; omega
    rw [hb]; simp
  · rw [Bool.not_eq_true] at hp; rw [hp]; simp

/-! ## Every cardinality clause is satisfied. -/

theorem mem_range'_bounds {i len : ℕ} (h : i ∈ List.range' 1 len) : 1 ≤ i ∧ i < 1 + len := by
  rw [List.mem_range'] at h
  obtain ⟨j, hj, rfl⟩ := h
  omega

theorem cardClauses_sat {n k : ℕ} [NeZero n] (G : SimpleGraph (Fin n)) (hk : 1 ≤ k)
    (hpk : psum G (edgeList n).length ≤ k) :
    ∀ c ∈ cardClauses n k, CNF.Clause.eval (assignM n k G) c = true := by
  intro c hc
  simp only [cardClauses, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range] at hc
  rcases hc with (((hA | hB) | hC) | hD) | hE
  · obtain ⟨i, hi, rfl⟩ := hA
    exact cardA_sat G hi hk
  · obtain ⟨i, hiR, j, hj, rfl⟩ := hB
    obtain ⟨hi1, _⟩ := mem_range'_bounds hiR
    exact cardB_sat G hi1 hj
  · obtain ⟨i, hiR, j, hjR, rfl⟩ := hC
    obtain ⟨hi1, hi2⟩ := mem_range'_bounds hiR
    obtain ⟨hj1, hj2⟩ := mem_range'_bounds hjR
    exact cardC_sat G (by omega) hi1 hj1 (by omega)
  · obtain ⟨j, hjR, rfl⟩ := hD
    obtain ⟨hj1, hj2⟩ := mem_range'_bounds hjR
    exact cardD_sat G hj1 (by omega)
  · obtain ⟨i, hiR, rfl⟩ := hE
    obtain ⟨hi1, hi2⟩ := mem_range'_bounds hiR
    exact cardE_sat G (by omega) hi1 hk hpk

/-! ## Edge-clause variable bounds, and the full assembly. -/

theorem alphaClause_lt {n : ℕ} (hn : 0 < n) {c : List (Nat × Bool)} (h : c ∈ alphaClauses n)
    (l : Nat × Bool) (hl : l ∈ c) : l.1 < n * n := by
  simp only [alphaClauses, List.mem_map] at h
  obtain ⟨T, _, rfl⟩ := h
  exact pairLits_lt hn true (pairsOf T) l hl

theorem omegaClause_lt {n : ℕ} (hn : 0 < n) {c : List (Nat × Bool)} (h : c ∈ omegaClauses n)
    (l : Nat × Bool) (hl : l ∈ c) : l.1 < n * n := by
  simp only [omegaClauses, List.mem_map] at h
  obtain ⟨Q, _, rfl⟩ := h
  exact pairLits_lt hn false (pairsOf Q) l hl

theorem capClause_lt {n : ℕ} (hn : 0 < n) {c : List (Nat × Bool)} (h : c ∈ capClauses n)
    (l : Nat × Bool) (hl : l ∈ c) : l.1 < n * n := by
  simp only [capClauses, List.mem_flatMap, List.mem_map] at h
  obtain ⟨A, _, W, _, rfl⟩ := h
  exact pairLits_lt hn false W l hl

/-- Every clause of `MCNF n k` is satisfied by `assignM`, given `≤ k` edges. -/
theorem MCNF_sat {n k : ℕ} [NeZero n] (G : SimpleGraph (Fin n)) (hcap : capAtMost11 G)
    (hα : alphaAtMost G 2) (hω : G.CliqueFree 5) (hk : 1 ≤ k) (hle : edgeCountIn G Finset.univ ≤ k) :
    CNF.eval (assignM n k G) (MCNF n k) = true := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hpk : psum G (edgeList n).length ≤ k := le_trans (psum_total_le_edgeCount G) hle
  simp only [CNF.eval, MCNF]
  rw [Array.all_eq_true_iff_forall_mem]
  intro c hc
  rw [List.mem_toArray] at hc
  simp only [List.mem_append] at hc
  rcases hc with ((h | h) | h) | h
  · rw [eval_congr_lt G c (alphaClause_lt hn h)]; exact alpha_clause_sat G hα h
  · rw [eval_congr_lt G c (omegaClause_lt hn h)]; exact omega_clause_sat G hω h
  · rw [eval_congr_lt G c (capClause_lt hn h)]; exact cap_clause_sat G hcap h
  · exact cardClauses_sat G hk hpk c h

/-- **M bridge.** If `MCNF n k` is unsatisfiable (from the LRAT certificate), then any
`α ≤ 2`, `ω ≤ 4`, cap-11 graph on `Fin n` has more than `k` edges. -/
theorem M_of_unsat {n k : ℕ} [NeZero n] (hU : (MCNF n k).Unsat) (G : SimpleGraph (Fin n))
    (hcap : capAtMost11 G) (hα : alphaAtMost G 2) (hω : G.CliqueFree 5) (hk : 1 ≤ k)
    (hle : edgeCountIn G Finset.univ ≤ k) : False := by
  have h := hU (assignM n k G)
  rw [MCNF_sat G hcap hα hω hk hle] at h
  exact Bool.noConfusion h

end Erdos617
