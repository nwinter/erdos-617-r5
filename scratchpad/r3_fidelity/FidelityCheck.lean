import Lean617.Statements
import Lean617.Final

/-!
Statement-fidelity EXECUTABLE cross-check (R3).
We deliberately do NOT `open Classical`; `decide` uses genuine Decidable
instances, so the props really compute. `Misses`/`Balanced` are plain (non-reducible)
`def`s, so we `unfold` them before `decide`.
-/

open Finset
namespace Erdos617

/-! ### 1. Verbatim def bodies + statement shapes. -/
#print Misses
#print Balanced
#print Main
#print MH2
#print MM
#check @main_iff_no_balanced
#check @main_imp_upstream

/-! ### 2. Misses / Balanced on hand-crafted colourings where we KNOW the answer. -/

-- all edges colour 0 on a triangle: {0,1,2} MISSES colour 1, does NOT miss colour 0.
example : Misses (fun _ => (0 : Fin 5)) ({0,1,2} : Finset (Fin 3)) 1 := by
  unfold Misses; decide
example : ¬ Misses (fun _ => (0 : Fin 5)) ({0,1,2} : Finset (Fin 3)) 0 := by
  unfold Misses; decide

-- all edges colour 0 on K_6: NOT balanced (colours 1..4 missing from the unique 6-set).
example : ¬ Balanced (fun _ => (0 : Fin 5) : Sym2 (Fin 6) → Fin 5) := by
  unfold Balanced Misses; decide

-- c(s(i,j)) = (i+j) mod 5 hits all 5 colours on the 15 edges of K_6: BALANCED (non-vacuous).
def csum : Sym2 (Fin 6) → Fin 5 :=
  Sym2.lift ⟨fun i j => ⟨(i.val + j.val) % 5, by omega⟩,
             by intro a b; simp only [Fin.mk.injEq]; omega⟩
example : Balanced csum := by unfold Balanced Misses; decide

/-! ### 3. edgeCountIn counts each unordered edge exactly ONCE (no double count, no loops).
   Pentagon on K_5: 5 cycle edges colour 0, 5 diagonals colour 1. -/

def pentEdges : Finset (Sym2 (Fin 5)) := {s(0,1), s(1,2), s(2,3), s(3,4), s(4,0)}
def cpent : Sym2 (Fin 5) → Fin 5 := fun e => if e ∈ pentEdges then 0 else 1

-- direct filter-card:
#eval ((univ : Finset (Fin 5)).sym2.filter (fun e => ¬ e.IsDiag ∧ cpent e = 0)).card  -- 5
#eval ((univ : Finset (Fin 5)).sym2.filter (fun e => ¬ e.IsDiag ∧ cpent e = 1)).card  -- 5

-- the SAME through the actual (noncomputable) `edgeCountIn`, via kernel-proved rewrites:
example : edgeCountIn (colourClass cpent 0) univ = 5 := by
  rw [edgeCountIn_colourClass]; decide
example : edgeCountIn (colourClass cpent 1) univ = 5 := by
  rw [edgeCountIn_colourClass]; decide
-- sum over colours = C(5,2)=10 ⇒ each edge counted once, diagonals excluded:
example : (∑ k : Fin 5, edgeCountIn (colourClass cpent k) univ) = 10 := by
  rw [sum_edgeCountIn_colourClass]; decide

-- diagonals genuinely excluded (loopless): s(v,v) is never adjacent / counted.
example : ¬ (colourClass cpent 0).Adj 0 0 := fun h => h.1 rfl

/-! ### 4. Balanced on Fin 5 is vacuously true (no 6-subsets) — quantifier shape sanity. -/
example : Balanced cpent := by unfold Balanced Misses; decide

/-! ### 5. Threshold arithmetic behind the invariants. -/
#eval (6 : ℕ).choose 2          -- 15  (cap-11: >=4 left for other colours)
#eval (25 : ℕ).choose 2         -- 300 (minority <= 60)
#eval (5 : ℕ).choose 2          -- 10  (step-5: minority T spans <= 6)
#eval (26 : ℕ).choose 2         -- 325 (K_26 total)

/-! ### 6. Honesty / axiom profile of the final theorems. -/
#print axioms erdos_617_r5
#print axioms erdos_617_r5_upstream
#print axioms main_iff_no_balanced

end Erdos617
