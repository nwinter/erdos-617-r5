/-
Challenge.lean — the comparator CHALLENGE for the four final theorems of the
r = 5 case of Erdős Problem 617.

WHAT THIS FILE IS.  The "Challenge" half of a leanprover/comparator run
(https://github.com/leanprover/comparator): it states the four theorems with
`sorry`; comparator then checks that our library (the "Solution", module
`Lean617.Final`) contains theorems of the SAME fully-qualified names whose
statements are ALPHA-EQUIVALENT to the ones here, are kernel-accepted, and depend
only on the permitted axioms in `erdos617_r5.json`.

WHY THIS IMPORTS `Lean617.Primitives` (and is NOT Mathlib-self-contained).
Comparator requires every permitted axiom to exist in BOTH the Challenge and the
Solution environments: it exports both modules with one shared target list that
includes the permitted axioms (comparator Main.lean:257-266, `LEAN_ABORT_ON_PANIC`),
and `compareAt` looks each axiom up on both sides (Compare.lean:70-83).  Our four
permitted SAT axioms are per-invocation `native_decide` reflection axioms
(`Erdos617.unsat_M9._native.native_decide.ax_1_1`, …) that (a) exist only in the
Solution and (b) have types that embed the entire multi-hundred-MB LRAT
certificate as a string literal and reference `Erdos617F3.MCNF`/`verifyCert`.
They cannot be hand-declared or vendored.  The only way to make them present in
the Challenge environment is to `import` the module that generates them —
`Lean617.Primitives`.  That import also transitively brings the canonical
`Main`/`edgeCountIn`/`IsIndep`/`alphaAtMost` (so those can NO LONGER be vendored
here — it would be a duplicate declaration), but it does NOT bring
`Erdos617.AB21`/`Erdos617.KPEqualityClassification` (they live in `Equality21`,
outside Primitives' import closure), so those two stay vendored below and remain
byte-checked by `check_challenge_fidelity.sh`.

WHAT THIS TRADE-OFF COSTS, EXACTLY.  Because `Main` is now the SAME imported
declaration on both sides, comparator's cross-check of the Solution's `Main`
against an independent Challenge copy devolves to import-identity (`Main == Main`);
likewise for `edgeCountIn`/`IsIndep`/`alphaAtMost`.  What comparator STILL verifies
is load-bearing: the four theorem STATEMENTS re-type against the Solution
(including that the vendored `KPEqualityClassification` hypothesis matches the
Solution's), the Solution's proofs use ONLY the exact permitted-axiom allow-list,
and the whole Solution replays through the kernel.  The claim that these `Prop`s
faithfully encode the informal conjecture is NOT comparator's job — it rests, as
before, on PROBLEM.md, the R3 statement-fidelity review (RELEASE.md), and
`check_challenge_fidelity.sh` reading the canonical `Statements.lean`/`Equality21.lean`.

NO DEFINITION HOLES.  `definition_names` is empty: a hole would let a Solution
redefine `Main := True` or the hypothesis `KPEqualityClassification := False` and
win vacuously (comparator does not compare hole bodies).  We keep every reachable
constant body-compared, so drift is a safe REJECTION.
-/
import Lean617.Primitives

-- Linter options below only silence warnings; they do not affect elaboration, so
-- they cannot change the ConstantInfo that comparator compares.
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.style.multiGoal false
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false

-- Mirror Equality21.lean's `open` context (the file the two vendored defs come
-- from) so `AB21`/`KPEqualityClassification` elaborate identically to canonical.
open Finset SimpleGraph
open scoped Classical

namespace Erdos617

/-! ## Vendored definitions

Only the two statement-reachable defs that are NOT in `Lean617.Primitives`' import
closure are vendored here (byte-for-byte from `Equality21.lean`).  `Main`,
`edgeCountIn`, `IsIndep`, `alphaAtMost` come in canonically through the import
above.  Do not edit by hand; if a canonical definition changes, re-copy it and
re-run `check_challenge_fidelity.sh`. -/

-- VENDORED FROM lean617/Lean617/Equality21.lean  (def AB21)
/-- **The equality21 A/B-structure predicate** on a graph over `Fin 21`. -/
def AB21 (H : SimpleGraph (Fin 21)) : Prop :=
  ∃ A B : Finset (Fin 21), Disjoint A B ∧ A.card = 5 ∧ B.card = 4 ∧
    (∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ ¬ H.Adj x y ∧
      (∀ u ∈ A, ∀ w ∈ A, u ≠ w →
        (¬ H.Adj u w ↔ (u = x ∧ w = y) ∨ (u = y ∧ w = x)))) ∧
    (∀ u ∈ B, ∀ w ∈ B, u ≠ w → H.Adj u w) ∧
    edgeCountIn H (A ∪ B) = 19

-- VENDORED FROM lean617/Lean617/Equality21.lean  (def KPEqualityClassification)
/-- **The (5,21) Kang–Pikhurko equality classification**, as a hypothesis-only `Prop`. -/
def KPEqualityClassification : Prop :=
  ∀ (F : SimpleGraph (Fin 21)), alphaAtMost F 5 → F.CliqueFree 5 →
    edgeCountIn F Finset.univ = 37 →
    ∃ (H : SimpleGraph (Fin 21)) (σ : Fin 21 ≃ Fin 21),
      (∀ a b, F.Adj a b ↔ H.Adj (σ a) (σ b)) ∧ AB21 H

/-! ## The four challenge theorems (statements only)

Signatures are byte-identical to `lean617/Lean617/Final.lean`; only the proofs
are replaced by `sorry`.  `Main` is the imported canonical def; `KPEqualityClassification`
is the vendored def above. -/

/-- **Erdős 617, r = 5 — UNCONDITIONAL.** -/
theorem erdos_617_r5_unconditional : Main := sorry

/-- The upstream-shaped corollary over an arbitrary 26-element vertex type, UNCONDITIONAL. -/
theorem erdos_617_r5_upstream_unconditional {V : Type} [Fintype V]
    [DecidableEq V] (hV : Fintype.card V = 5 ^ 2 + 1)
    (coloring : Sym2 V → Fin 5) :
    ∃ (S : Finset V) (k : Fin 5), S.card = 5 + 1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k := sorry

/-- **Erdős 617, r = 5**, conditional on the single classical hypothesis `KPEqualityClassification`. -/
theorem erdos_617_r5 (h : KPEqualityClassification) : Main := sorry

/-- The upstream-shaped corollary over an arbitrary 26-element vertex type, conditional on the same
single hypothesis `KPEqualityClassification`. -/
theorem erdos_617_r5_upstream (h : KPEqualityClassification) {V : Type} [Fintype V]
    [DecidableEq V] (hV : Fintype.card V = 5 ^ 2 + 1)
    (coloring : Sym2 V → Fin 5) :
    ∃ (S : Finset V) (k : Fin 5), S.card = 5 + 1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k := sorry

end Erdos617
