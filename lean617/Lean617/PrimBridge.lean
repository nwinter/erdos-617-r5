import Lean617.PrimEncoding
import Lean617.LTable
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Sym.Sym2

/-!
# Graph → SAT bridge for the four primitives.

We show: if `G : SimpleGraph (Fin n)` has the stated graph properties (and, for the M-instances,
`≤ k` edges), then the corresponding `CNF Nat` is *satisfiable* — via the assignment
`assign G v := G.Adj (decode v)`. Contraposed against `(theCNF).Unsat` (obtained by `verifyCert`
from the LRAT certificate), this discharges the `PrimFacts`.
-/

open Std.Sat Finset
open scoped Classical

namespace Erdos617

/-! `IsIndep`, `edgeCountIn` (from `Lean617.Statements`) and `capAtMost11`, `alphaAtMost`
(from `Lean617.LTable`) are reused here — this file no longer redefines them. -/

/-! ## The satisfying assignment. -/

open Erdos617F3

/-- The assignment reading edge variable `a*n+b` back as `G.Adj a b`. Noncomputable (classical
`decide`), used only inside the unsatisfiability contradiction. -/
noncomputable def assign {n : ℕ} (G : SimpleGraph (Fin n)) (v : Nat) : Bool :=
  if h : 0 < n then
    decide (G.Adj ⟨(v / n) % n, Nat.mod_lt _ h⟩ ⟨v % n, Nat.mod_lt _ h⟩)
  else false

/-- The decode is exact: `assign G (edgeVarL [a,b]) = decide (G.Adj a b)` for any `a b : Fin n`. -/
theorem assign_edgeVarL {n : ℕ} (G : SimpleGraph (Fin n)) (a b : Fin n) :
    assign G (edgeVarL [a, b]) = decide (G.Adj a b) := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) a.isLt
  have e1 : ((edgeVarL [a, b] / n) % n) = a.val := by
    show ((a.val * n + b.val) / n) % n = a.val
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt b.isLt, Nat.zero_add,
      Nat.mod_eq_of_lt a.isLt]
  have e2 : (edgeVarL [a, b] % n) = b.val := by
    show (a.val * n + b.val) % n = b.val
    rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add]
    simp [Nat.mod_eq_of_lt b.isLt]
  have fa : (⟨(edgeVarL [a, b] / n) % n, Nat.mod_lt _ hn⟩ : Fin n) = a := Fin.ext e1
  have fb : (⟨edgeVarL [a, b] % n, Nat.mod_lt _ hn⟩ : Fin n) = b := Fin.ext e2
  simp only [assign, dif_pos hn, fa, fb]

/-! ## `pairsOf` combinatorics. -/

/-- For distinct `u v ∈ l`, one of `[u,v]`, `[v,u]` is in `pairsOf l` (order-free). -/
theorem mem_pairsOf_of_distinct {α : Type*} [DecidableEq α] {l : List α} {u v : α}
    (hu : u ∈ l) (hv : v ∈ l) (huv : u ≠ v) :
    [u, v] ∈ pairsOf l ∨ [v, u] ∈ pairsOf l := by
  induction l with
  | nil => simp at hu
  | cons a t ih =>
    simp only [pairsOf, List.mem_append, List.mem_map]
    rw [List.mem_cons] at hu hv
    rcases hu with rfl | hu
    · rcases hv with rfl | hv
      · exact absurd rfl huv
      · exact Or.inl (Or.inl ⟨v, hv, rfl⟩)
    · rcases hv with rfl | hv
      · exact Or.inr (Or.inl ⟨u, hu, rfl⟩)
      · rcases ih hu hv with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inr h)

/-- Every member of `pairsOf l` is a 2-element list whose entries lie in `l`. -/
theorem mem_pairsOf_imp {α : Type*} {l : List α} {P : List α} (hP : P ∈ pairsOf l) :
    ∃ x y, P = [x, y] ∧ x ∈ l ∧ y ∈ l := by
  induction l with
  | nil => simp [pairsOf] at hP
  | cons a t ih =>
    simp only [pairsOf, List.mem_append, List.mem_map] at hP
    rcases hP with ⟨b, hb, rfl⟩ | hP
    · exact ⟨a, b, rfl, List.mem_cons_self, List.mem_cons_of_mem _ hb⟩
    · obtain ⟨x, y, rfl, hx, hy⟩ := ih hP
      exact ⟨x, y, rfl, List.mem_cons_of_mem _ hx, List.mem_cons_of_mem _ hy⟩

/-! ## Clause evaluation under `assign`. -/

/-- Evaluating a `pairLits` clause reduces to an `any` over the pairs. -/
theorem eval_pairLits {n : ℕ} (G : SimpleGraph (Fin n)) (pos : Bool)
    (pairs : List (List (Fin n))) :
    CNF.Clause.eval (assign G) (pairLits pos pairs)
      = pairs.any (fun P => assign G (edgeVarL P) == pos) := by
  simp only [pairLits, CNF.Clause.eval, List.any_map, Function.comp_def]

/-- An edge pair makes its positive literal true. -/
theorem edge_pos {n : ℕ} (G : SimpleGraph (Fin n)) {x y : Fin n} (h : G.Adj x y) :
    (assign G (edgeVarL [x, y]) == true) = true := by
  rw [assign_edgeVarL]; simpa using h

/-- A non-edge pair makes its negative literal true. -/
theorem nonedge_neg {n : ℕ} (G : SimpleGraph (Fin n)) {x y : Fin n} (h : ¬ G.Adj x y) :
    (assign G (edgeVarL [x, y]) == false) = true := by
  rw [assign_edgeVarL]; simpa using h

/-! ## α ≤ 2 : every 3-subset clause is satisfied. -/

theorem alpha_clause_sat {n : ℕ} (G : SimpleGraph (Fin n)) (hα : alphaAtMost G 2)
    {c : List (Nat × Bool)} (hc : c ∈ alphaClauses n) :
    CNF.Clause.eval (assign G) c = true := by
  simp only [alphaClauses, List.mem_map] at hc
  obtain ⟨T, hT, rfl⟩ := hc
  rw [List.mem_sublistsLen] at hT
  obtain ⟨hTsub, hTlen⟩ := hT
  have hTnodup : T.Nodup := (List.nodup_finRange n).sublist hTsub
  have hcard : T.toFinset.card = 3 := by rw [List.toFinset_card_of_nodup hTnodup, hTlen]
  rw [eval_pairLits]
  -- T is not independent (card 3 > 2), so some pair is an edge.
  have hni : ¬ IsIndep G T.toFinset := by
    intro hindep; have := hα _ hindep; omega
  rw [IsIndep] at hni
  push_neg at hni
  obtain ⟨u, hu, v, hv, huv, hadj⟩ := hni
  rw [List.mem_toFinset] at hu hv
  rw [List.any_eq_true]
  rcases mem_pairsOf_of_distinct hu hv huv with h | h
  · exact ⟨[u, v], h, edge_pos G hadj⟩
  · exact ⟨[v, u], h, edge_pos G hadj.symm⟩

/-! ## cap-11 : every 6-subset / 12-of-15 clause is satisfied.

The delicate part is a counting injection: 12 distinct edge-pairs would give
`edgeCountIn ≥ 12 > 11`. We map pairs to `Sym2` and show that map has nodup image. -/

/-- Pairs in `pairsOf` are of distinct vertices (when the list is nodup). -/
theorem pairsOf_pair_ne {α : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup) {x y : α}
    (h : [x, y] ∈ pairsOf l) : x ≠ y := by
  induction l with
  | nil => simp [pairsOf] at h
  | cons a t ih =>
    simp only [pairsOf, List.mem_append, List.mem_map] at h
    rw [List.nodup_cons] at hl
    rcases h with ⟨b, hb, hab⟩ | h
    · rw [List.cons.injEq, List.cons.injEq] at hab
      obtain ⟨rfl, rfl, _⟩ := hab
      exact fun hxy => hl.1 (hxy ▸ hb)
    · exact ih hl.2 h

/-- The `Sym2` of a pair-list (junk `s(0,0)` off 2-lists; only used on genuine pairs). -/
def s2 {n : ℕ} [NeZero n] (P : List (Fin n)) : Sym2 (Fin n) :=
  match P with
  | x :: y :: _ => s(x, y)
  | _ => s(0, 0)

@[simp] theorem s2_pair {n : ℕ} [NeZero n] (x y : Fin n) : s2 [x, y] = s(x, y) := rfl

/-- `s2` is injective on `pairsOf l` for nodup `l`: distinct ordered pairs give distinct `Sym2`. -/
theorem pairsOf_map_s2_nodup {n : ℕ} [NeZero n] {l : List (Fin n)} (hl : l.Nodup) :
    ((pairsOf l).map s2).Nodup := by
  induction l with
  | nil => simp [pairsOf]
  | cons a t ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hat, htnodup⟩ := hl
    simp only [pairsOf, List.map_append, List.map_map]
    rw [List.nodup_append]
    refine ⟨?_, ih htnodup, ?_⟩
    · -- `(t.map (fun b => s(a,b))).Nodup`
      refine List.Nodup.map_on ?_ htnodup
      intro b hb b' hb' hbb'
      simp only [Function.comp_apply, s2_pair] at hbb'
      rw [Sym2.eq_iff] at hbb'
      rcases hbb' with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact h2
      · exact absurd hb' (h1 ▸ hat)
    · -- disjointness of the two mapped parts
      intro e he he' hmem
      rw [List.mem_map] at he hmem
      obtain ⟨b, hb, hbe⟩ := he
      obtain ⟨Q, hQ, hQe⟩ := hmem
      obtain ⟨x, y, rfl, hx, hy⟩ := mem_pairsOf_imp hQ
      rw [Function.comp_apply, s2_pair] at hbe
      rw [s2_pair] at hQe
      intro heq
      rw [← hbe, ← hQe, Sym2.eq_iff] at heq
      rcases heq with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact hat hx
      · exact hat hy

theorem cap_clause_sat {n : ℕ} [NeZero n] (G : SimpleGraph (Fin n)) (hcap : capAtMost11 G)
    {c : List (Nat × Bool)} (hc : c ∈ capClauses n) :
    CNF.Clause.eval (assign G) c = true := by
  simp only [capClauses, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨A, hA, W, hW, rfl⟩ := hc
  rw [List.mem_sublistsLen] at hA hW
  obtain ⟨hAsub, hAlen⟩ := hA
  obtain ⟨hWsub, hWlen⟩ := hW
  have hAnodup : A.Nodup := (List.nodup_finRange n).sublist hAsub
  have hpairsNodup : (pairsOf A).Nodup := by
    have := pairsOf_map_s2_nodup (l := A) hAnodup
    exact this.of_map
  have hWnodup : W.Nodup := hpairsNodup.sublist hWsub
  rw [eval_pairLits]
  by_contra hcon
  rw [Bool.not_eq_true, List.any_eq_false] at hcon
  -- Every pair in W is an edge.
  have hEdge : ∀ P ∈ W, ∃ x y : Fin n, P = [x, y] ∧ x ∈ A ∧ y ∈ A ∧ G.Adj x y := by
    intro P hP
    have hPpair := hWsub.subset hP
    obtain ⟨x, y, rfl, hx, hy⟩ := mem_pairsOf_imp hPpair
    have := hcon _ hP
    rw [assign_edgeVarL] at this
    refine ⟨x, y, rfl, hx, hy, ?_⟩
    simpa using this
  -- The edge Finset E and its cardinality.
  set E : Finset (Sym2 (Fin n)) := A.toFinset.sym2.filter (fun e => e ∈ G.edgeSet) with hE
  have hAcard : A.toFinset.card = 6 := by rw [List.toFinset_card_of_nodup hAnodup, hAlen]
  have hEcard : E.card ≤ 11 := hcap A.toFinset hAcard
  -- The map `s2` sends `W` into `E`, nodup, length 12.
  have hmapNodup : (W.map s2).Nodup :=
    (pairsOf_map_s2_nodup hAnodup).sublist (hWsub.map s2)
  have hsub : (W.map s2).toFinset ⊆ E := by
    intro e he
    rw [List.mem_toFinset, List.mem_map] at he
    obtain ⟨P, hP, rfl⟩ := he
    obtain ⟨x, y, rfl, hx, hy, hadj⟩ := hEdge P hP
    rw [s2_pair, hE, Finset.mem_filter, Finset.mk_mem_sym2_iff]
    refine ⟨⟨List.mem_toFinset.mpr hx, List.mem_toFinset.mpr hy⟩, ?_⟩
    rw [SimpleGraph.mem_edgeSet]; exact hadj
  have h12 : 12 ≤ E.card := by
    calc 12 = W.length := hWlen.symm
      _ = (W.map s2).length := by rw [List.length_map]
      _ = (W.map s2).toFinset.card := (List.toFinset_card_of_nodup hmapNodup).symm
      _ ≤ E.card := Finset.card_le_card hsub
  omega

/-! ## ω ≤ 4 : every 5-subset clause is satisfied (needed for M9/M10). -/

theorem omega_clause_sat {n : ℕ} (G : SimpleGraph (Fin n)) (hω : G.CliqueFree 5)
    {c : List (Nat × Bool)} (hc : c ∈ omegaClauses n) :
    CNF.Clause.eval (assign G) c = true := by
  simp only [omegaClauses, List.mem_map] at hc
  obtain ⟨Q, hQ, rfl⟩ := hc
  rw [List.mem_sublistsLen] at hQ
  obtain ⟨hQsub, hQlen⟩ := hQ
  have hQnodup : Q.Nodup := (List.nodup_finRange n).sublist hQsub
  have hcard : Q.toFinset.card = 5 := by rw [List.toFinset_card_of_nodup hQnodup, hQlen]
  rw [eval_pairLits]
  -- `Q.toFinset` is not a clique, else it is a 5-clique.
  have hnotclique : ¬ (∀ u ∈ Q.toFinset, ∀ v ∈ Q.toFinset, u ≠ v → G.Adj u v) := by
    intro hclique
    refine hω Q.toFinset ⟨?_, hcard⟩
    intro u hu v hv huv
    exact hclique u (Finset.mem_coe.mp hu) v (Finset.mem_coe.mp hv) huv
  push_neg at hnotclique
  obtain ⟨u, hu, v, hv, huv, hnadj⟩ := hnotclique
  rw [List.mem_toFinset] at hu hv
  rw [List.any_eq_true]
  rcases mem_pairsOf_of_distinct hu hv huv with h | h
  · exact ⟨[u, v], h, nonedge_neg G hnadj⟩
  · exact ⟨[v, u], h, nonedge_neg G (fun hadj => hnadj hadj.symm)⟩

/-! ## Assembly: the graph gives a satisfying assignment, contradicting `Unsat`. -/

/-- Every clause of `nonexCNF n` is satisfied by `assign G`. -/
theorem nonexCNF_sat {n : ℕ} [NeZero n] (G : SimpleGraph (Fin n))
    (hcap : capAtMost11 G) (hα : alphaAtMost G 2) :
    CNF.eval (assign G) (nonexCNF n) = true := by
  simp only [CNF.eval, nonexCNF]
  rw [Array.all_eq_true_iff_forall_mem]
  intro c hc
  rw [List.mem_toArray, List.mem_append] at hc
  rcases hc with h | h
  · exact alpha_clause_sat G hα h
  · exact cap_clause_sat G hcap h

/-- **nonex bridge.** If `nonexCNF n` is unsatisfiable (from the LRAT certificate), then no
`α ≤ 2`, cap-11 graph exists on `Fin n`. -/
theorem nonex_of_unsat {n : ℕ} [NeZero n] (hU : (nonexCNF n).Unsat)
    (G : SimpleGraph (Fin n)) (hcap : capAtMost11 G) (hα : alphaAtMost G 2) : False := by
  have h := hU (assign G)
  rw [nonexCNF_sat G hcap hα] at h
  exact Bool.noConfusion h

end Erdos617
