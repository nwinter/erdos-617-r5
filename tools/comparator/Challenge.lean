/-
Challenge.lean — the comparator CHALLENGE for the four final theorems of the
r = 5 case of Erdős Problem 617.

WHAT THIS FILE IS.  This is the "Challenge" half of a leanprover/comparator run
(https://github.com/leanprover/comparator).  A Challenge states theorems whose
proofs are `sorry`; comparator then checks that our library (the "Solution",
module `Lean617.Final`) contains theorems of the SAME fully-qualified names whose
statements are ALPHA-EQUIVALENT to the ones here, are accepted by the Lean
kernel, and depend only on the permitted axioms listed in `erdos617_r5.json`.

HOW COMPARATOR USES THIS FILE (why the definitions below matter).  Comparator
matches theorems BY NAME and compares statement TYPES up to alpha-equivalence
(no definitional unfolding).  For every constant reachable FROM a matched
statement — here `Erdos617.Main` and `Erdos617.KPEqualityClassification`, and
everything THEY unfold to — it compares the FULL definition (type AND body)
between this Challenge and the Solution, and rejects on any mismatch.  So the six
definitions below are not decoration: comparator forces each to be byte-for-byte
(alpha-)identical to the Solution's, which is exactly the fidelity we want.  We
deliberately use NO definition holes (`definition_names` is empty in the config):
a hole would let a Solution redefine `Main := True` or the hypothesis
`KPEqualityClassification := False` and trivially "win", because comparator does
not compare hole bodies.  Vendoring the bodies makes any drift a safe REJECTION.

VENDORED, NOT IMPORTED.  So that a third-party auditor can read the exact
statements without trusting anything in this repository beyond Mathlib, this file
imports only Mathlib and vendors the six statement-reachable definitions
byte-identically from their canonical sources (per-definition provenance
comments below).  `tools/comparator/check_challenge_fidelity.sh` re-verifies, on
every run, that each vendored block is textually identical to its canonical
source in `lean617/Lean617/{Statements,LTable,Equality21}.lean` and that the four
theorem SIGNATURES match `lean617/Lean617/Final.lean`.  Comparator itself is the
second, independent check of the same fidelity (it body-compares against the
built Solution); the shell script is the fast, Linux-free local guard.

WHAT COMPARATOR DOES NOT CHECK.  Comparator does not judge whether these
statements faithfully encode the informal Erdős–Gyárfás conjecture.  That is the
job of PROBLEM.md, the R3 statement-fidelity review (RELEASE.md), and the upstream
google-deepmind/formal-conjectures `erdos_617` token-identity audit — NOT of this
harness.  See tools/comparator/README.md.
-/
import Mathlib

-- Linter options below only silence warnings; they do not affect elaboration, so
-- they cannot change the ConstantInfo that comparator compares.  They mirror the
-- canonical source files.
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.style.multiGoal false
set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false

-- `open` context is the UNION of the canonical files' opens (Statements.lean:
-- `open Finset`; LTable.lean / Equality21.lean: `open Finset SimpleGraph`; all
-- with `open scoped Classical`).  Every vendored body below references the extra
-- `SimpleGraph` names only through dot-notation (`G.Adj`, `F.CliqueFree`, …) or
-- through in-namespace constants, so the wider `open` cannot change how any of
-- them elaborates.  Comparator is the arbiter: a stray resolution difference
-- would surface as a rejected constant, never as a false pass.
open Finset SimpleGraph
open scoped Classical

namespace Erdos617

/-! ## Vendored statement-reachable definitions

Each block below is copied byte-for-byte from the cited canonical file.  Do not
edit by hand; if a canonical definition changes, re-copy it and re-run
`check_challenge_fidelity.sh`. -/

-- VENDORED FROM lean617/Lean617/Statements.lean  (def edgeCountIn)
/-- Number of edges of `G` with both endpoints in the finset `S`. -/
noncomputable def edgeCountIn {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : ℕ :=
  (S.sym2.filter (fun e => e ∈ G.edgeSet)).card

-- VENDORED FROM lean617/Lean617/Statements.lean  (def IsIndep)
/-- `S` is an independent set of the graph `G` (no edge inside `S`). -/
def IsIndep {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ G.Adj u v

-- VENDORED FROM lean617/Lean617/Statements.lean  (def Main)
/-- The main theorem, r = 5 case of Erdős 617, in the upstream's shape. -/
def Main : Prop :=
  ∀ c : Sym2 (Fin 26) → Fin 5,
    ∃ (S : Finset (Fin 26)) (k : Fin 5), S.card = 6 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u, v) ≠ k

-- VENDORED FROM lean617/Lean617/LTable.lean  (def alphaAtMost)
/-- Independence number at most `m`. -/
def alphaAtMost {n : ℕ} (G : SimpleGraph (Fin n)) (m : ℕ) : Prop :=
  ∀ S : Finset (Fin n), IsIndep G S → S.card ≤ m

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
are replaced by `sorry`.  Comparator checks the Solution proves each of these. -/

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
