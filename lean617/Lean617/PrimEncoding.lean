import Mathlib.Data.List.Sublists
import Mathlib.Data.List.FinRange
import Std.Tactic.BVDecide

/-!
# CNF encodings of the four SAT primitives, as `CNF Nat` data.

Everything is generated with computable `List` operations (`List.sublistsLen` over
`List.finRange n`) so the instances can be `#eval`-emitted to DIMACS.

Variables: an edge `[a,b]` (a<b over `Fin n`, as an ascending 2-sublist) is the boolean
`edgeVarL [a,b] = a*n+b`. Sparse but injective on pairs; unused indices are harmless.

Clause families (each an "OR over the pairs of a subset", single polarity):
* `alphaClauses n` : every 3-subset spans an edge   (⇒ α ≤ 2)
* `omegaClauses n` : every 5-subset omits an edge    (⇒ ω ≤ 4, i.e. `CliqueFree 5`)
* `capClauses n`   : every 6-subset, every 12 of its 15 pairs omits an edge (6-set ≤ 11 edges)

The `CNF Nat` uses 0-based Lean variables; `Std.Sat.CNF.dimacs`/`verifyCert` both shift by `+1`,
so our streaming DIMACS writer (same `+1`) and checking via `verifyCert` are consistent.
-/

open Std.Sat

namespace Erdos617F3

/-- Edge variable of an ascending 2-element vertex list `[a,b]`: value `a*n+b`. -/
def edgeVarL {n : ℕ} (P : List (Fin n)) : Nat :=
  match P with
  | [a, b] => a.val * n + b.val
  | _ => 0

/-- All ordered pairs `[a,b]` with `a` before `b` in `l`. For an ascending nodup `l`
this is exactly `{[a,b] | a,b ∈ l, a < b}`, with a clean membership lemma (see Bridge). -/
def pairsOf {α : Type*} : List α → List (List α)
  | [] => []
  | a :: t => t.map (fun b => [a, b]) ++ pairsOf t

/-- Turn a list of vertex-pairs into a clause: one literal `(edgeVarL P, pos)` per pair. -/
def pairLits {n : ℕ} (pos : Bool) (pairs : List (List (Fin n))) : List (Nat × Bool) :=
  pairs.map (fun P => (edgeVarL P, pos))

/-- α ≤ 2 : every 3-subset contains an edge (positive OR over its 3 pairs). -/
def alphaClauses (n : ℕ) : List (List (Nat × Bool)) :=
  ((List.finRange n).sublistsLen 3).map (fun T => pairLits true (pairsOf T))

/-- ω ≤ 4 : every 5-subset omits an edge (negative OR over its 10 pairs). -/
def omegaClauses (n : ℕ) : List (List (Nat × Bool)) :=
  ((List.finRange n).sublistsLen 5).map (fun Q => pairLits false (pairsOf Q))

/-- cap-11 : every 6-subset `A`, every 12 of its 15 pairs, at least one non-edge. -/
def capClauses (n : ℕ) : List (List (Nat × Bool)) :=
  ((List.finRange n).sublistsLen 6).flatMap (fun A =>
    ((pairsOf A).sublistsLen 12).map (fun W => pairLits false W))

/-- The nonexistence instance (α ≤ 2 + cap-11), for `n ∈ {11,12}`. -/
def nonexCNF (n : ℕ) : CNF Nat := ⟨(alphaClauses n ++ capClauses n).toArray⟩

/-! ## Cardinality "at most k" via a sequential (Sinz) counter, for the M-instances.

Over the fixed edge list `edgeList n = pairsOf (finRange n)` (all `[a,b]`, a<b), auxiliary
`s(i,j)` (`auxVar n k i j`) means "at least `j+1` of edges `e₀..eᵢ` are present". The clauses
force the running count never to exceed `k`; their COMPLETENESS (a ≤ k-edge graph admits the
partial-sum aux assignment) is what the M-bridge proves. -/

/-- The ordered edge list: all pairs `[a,b]`, a<b, in `pairsOf (finRange n)` order. -/
def edgeList (n : ℕ) : List (List (Fin n)) := pairsOf (List.finRange n)

/-- Edge variable at position `i` in `edgeList n`. -/
def evar (n : ℕ) (i : ℕ) : Nat := edgeVarL ((edgeList n).getD i [])

/-- Auxiliary counter variable `s(i,j)`, offset above all `n²` edge-variable indices. -/
def auxVar (n k i j : ℕ) : Nat := n * n + i * k + j

/-- Sinz sequential-counter clauses enforcing "at most `k`" of the `m = |edgeList n|` edges.
Uses `List.range'` (guard-free) to enumerate `i ∈ [1,m)`, `j ∈ [1,k)`. -/
def cardClauses (n k : ℕ) : List (List (Nat × Bool)) :=
  let m := (edgeList n).length
  -- (a) ¬xᵢ ∨ s(i,0)   for i ∈ [0,m)
  ((List.range m).map (fun i => [(evar n i, false), (auxVar n k i 0, true)]))
  -- (b) ¬s(i-1,j) ∨ s(i,j)   for i ∈ [1,m), j ∈ [0,k)
  ++ ((List.range' 1 (m - 1)).flatMap (fun i =>
        (List.range k).map (fun j => [(auxVar n k (i - 1) j, false), (auxVar n k i j, true)])))
  -- (c) ¬xᵢ ∨ ¬s(i-1,j-1) ∨ s(i,j)   for i ∈ [1,m), j ∈ [1,k)
  ++ ((List.range' 1 (m - 1)).flatMap (fun i =>
        (List.range' 1 (k - 1)).map (fun j =>
          [(evar n i, false), (auxVar n k (i - 1) (j - 1), false), (auxVar n k i j, true)])))
  -- (d) ¬s(0,j)   for j ∈ [1,k)
  ++ ((List.range' 1 (k - 1)).map (fun j => [(auxVar n k 0 j, false)]))
  -- (e) ¬xᵢ ∨ ¬s(i-1,k-1)   for i ∈ [1,m)  (can't reach a (k+1)-th)
  ++ ((List.range' 1 (m - 1)).map (fun i =>
        [(evar n i, false), (auxVar n k (i - 1) (k - 1), false)]))

/-- The M-instance (α ≤ 2, ω ≤ 4, cap-11, ≤ k edges), for `(n,k) ∈ {(9,18),(10,24)}`. -/
def MCNF (n k : ℕ) : CNF Nat :=
  ⟨(alphaClauses n ++ omegaClauses n ++ capClauses n ++ cardClauses n k).toArray⟩

/-! ## Streaming DIMACS emitter (same `+1` convention as `Std.Sat.CNF.dimacs`). -/

/-- Max 0-based variable appearing in the CNF (0 if none). -/
def maxVar (cnf : CNF Nat) : Nat :=
  cnf.clauses.foldl (fun m c => c.foldl (fun m l => Nat.max m l.1) m) 0

/-- Write `cnf` to `path` in DIMACS, shifting every variable by `+1` (0 is the terminator). -/
def emitDimacs (path : System.FilePath) (cnf : CNF Nat) : IO Unit := do
  let h ← IO.FS.Handle.mk path IO.FS.Mode.write
  h.putStrLn s!"p cnf {maxVar cnf + 1} {cnf.clauses.size}"
  for c in cnf.clauses do
    let mut line : String := ""
    for l in c do
      line := line ++ (if l.2 then s!"{l.1 + 1} " else s!"-{l.1 + 1} ")
    h.putStrLn (line ++ "0")

end Erdos617F3
