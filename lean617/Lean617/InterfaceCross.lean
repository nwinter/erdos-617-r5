/-
Interface-equivalence cross-check for Erdős Problem 617 at r = 5
(VERIFICATION-ROUND.md, Task 3).

This file does two things.

1. It transcribes VERBATIM the external Lean statement interface shipped as
   `review_queue/external-candidate-B/interface-B.lean.txt` — its definitions
   `SeesColor`, `Balanced`, `HasMissingColor`, `UpstreamStatement`,
   `NoBalancedFiveColoring`, `UpstreamStatementR5`, and its internal fidelity
   lemmas — into a fresh namespace `Erdos617.InterfaceB`, so it can sit beside
   our own `Erdos617` definitions. Only the namespace line is changed
   (`Erdos617` → `Erdos617.InterfaceB`); their docstrings are preserved. That
   the transcription — definitions AND their `Iff.rfl`/classical proofs —
   compiles unchanged in our toolchain is itself part of the fidelity check.

2. It proves, sorry-free, that the external interface's two final statement
   shapes are logically equivalent to OUR `Erdos617.Main`:

     interfaceB_upstreamR5_iff_main : InterfaceB.UpstreamStatementR5   ↔ Main
     interfaceB_noBalanced_iff_main : InterfaceB.NoBalancedFiveColoring ↔ Main

   The heavy lifting is our `main_imp_upstream` (Statements.lean; transports
   `Main` over `Fin 26` to the upstream shape over an arbitrary card-26 type)
   and the interface's own `upstreamStatementR5_iff_noBalancedFiveColoring`.

   Transported through those equivalences, the external targets are then
   THEOREMS given our completed proof `erdos_617_r5_unconditional`:

     interfaceB_upstreamR5_unconditional  : InterfaceB.UpstreamStatementR5
     interfaceB_noBalanced_unconditional  : InterfaceB.NoBalancedFiveColoring

See `verification/interface-equivalence.md` for the definition-by-definition
semantic comparison, the upstream-pinning comparison, and the verdict.
-/
import Lean617.Final

-- This is a research project, not a Mathlib PR: Mathlib's style linters are
-- disabled (matching Lean617.Statements). `linter.style.whitespace` and
-- `linter.unusedDecidableInType` are disabled so the VERBATIM transcription
-- below (which writes `5^2` and keeps `[DecidableEq V]` to mirror upstream)
-- builds warning-clean.
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.style.multiGoal false
set_option linter.unusedDecidableInType false
set_option autoImplicit false

/-!
## The external interface, transcribed verbatim

Everything in `namespace Erdos617.InterfaceB` below is transcribed VERBATIM from
`review_queue/external-candidate-B/interface-B.lean.txt` (its lines 13–127),
modulo only the namespace line so it does not clash with our own `Erdos617`
definitions. Their original docstrings are kept.
-/

namespace Erdos617.InterfaceB

/-- A set of vertices sees `k` when one of its unordered edges has color `k`. -/
def SeesColor {r : ℕ} {V : Type} (coloring : Sym2 V → Fin r)
    (S : Finset V) (k : Fin r) : Prop :=
  ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ coloring s(u, v) = k

/--
A coloring is balanced when every `(r + 1)`-set of vertices sees every one of
the `r` colors.  This is the working definition pinned by `PROBLEM.md`.
-/
def Balanced {r : ℕ} {V : Type} (coloring : Sym2 V → Fin r) : Prop :=
  ∀ S : Finset V, S.card = r + 1 → ∀ k : Fin r, SeesColor coloring S k

/-- Auditable expansion of the clean balanced definition. -/
theorem balanced_iff_every_set_sees_every_color {r : ℕ} {V : Type}
    (coloring : Sym2 V → Fin r) :
    Balanced coloring ↔
      ∀ S : Finset V, S.card = r + 1 → ∀ k : Fin r,
        ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ coloring s(u, v) = k :=
  Iff.rfl

/-- The missing-color conclusion used verbatim in the public upstream theorem. -/
def HasMissingColor {r : ℕ} {V : Type} (coloring : Sym2 V → Fin r) : Prop :=
  ∃ (S : Finset V) (k : Fin r),
    S.card = r + 1 ∧
    ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k

/--
The exact outer binder order and conclusion of the public
`Erdos617.erdos_617` declaration, represented as a proposition so that the
interface itself introduces no unproved theorem or axiom.  The hypothesis
`hr` is retained even though it does not occur in the conclusion, exactly as
in the upstream declaration.
-/
def UpstreamStatement (r : ℕ) (_hr : r ≥ 3) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V],
    Fintype.card V = r^2 + 1 →
    ∀ coloring : Sym2 V → Fin r,
      ∃ (S : Finset V) (k : Fin r),
        S.card = r + 1 ∧
        ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k

/--
Definitional audit of `UpstreamStatement`: the right side is the exact type of
the public upstream declaration after its theorem name.
-/
theorem upstreamStatement_iff_literal (r : ℕ) (hr : r ≥ 3) :
    UpstreamStatement r hr ↔
      ∀ {V : Type} [Fintype V] [DecidableEq V],
        Fintype.card V = r^2 + 1 →
        ∀ coloring : Sym2 V → Fin r,
          ∃ (S : Finset V) (k : Fin r),
            S.card = r + 1 ∧
            ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k :=
  Iff.rfl

/-- The clean working statement for the `r = 5`, `|V| = 26` target. -/
def NoBalancedFiveColoring : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V],
    Fintype.card V = 26 →
    ∀ coloring : Sym2 V → Fin 5, ¬Balanced coloring

/-- Missing a color is exactly the negation of the pinned balanced condition. -/
theorem hasMissingColor_iff_not_balanced {r : ℕ} {V : Type}
    (coloring : Sym2 V → Fin r) :
    HasMissingColor coloring ↔ ¬Balanced coloring := by
  classical
  constructor
  · rintro ⟨S, k, hcard, hmissing⟩ hbalanced
    obtain ⟨u, hu, v, hv, huv, hcolor⟩ := hbalanced S hcard k
    exact hmissing u hu v hv huv hcolor
  · intro hnot
    by_contra hnoMissing
    apply hnot
    intro S hcard k
    by_contra hnotSees
    apply hnoMissing
    refine ⟨S, k, hcard, ?_⟩
    intro u hu v hv huv hcolor
    exact hnotSees ⟨u, hu, v, hv, huv, hcolor⟩

/-- The public upstream statement instantiated at `r = 5`. -/
def UpstreamStatementR5 : Prop :=
  UpstreamStatement 5 (by norm_num)

/--
Fidelity theorem: the exact upstream `r = 5` interface is logically
equivalent to the clean working definition, including `26 = 5^2 + 1` and
`6 = 5 + 1`.
-/
theorem upstreamStatementR5_iff_noBalancedFiveColoring :
    UpstreamStatementR5 ↔ NoBalancedFiveColoring := by
  constructor
  · intro hupstream V instFintype instDecidableEq hcard coloring
    apply (hasMissingColor_iff_not_balanced coloring).mp
    apply hupstream (V := V)
    · norm_num at hcard ⊢
      exact hcard
  · intro hclean V instFintype instDecidableEq hcard coloring
    apply (hasMissingColor_iff_not_balanced coloring).mpr
    apply hclean (V := V)
    · norm_num at hcard ⊢
      exact hcard

/--
The intended outermost wrapper for an eventual proof of the clean target.
Its conclusion and binders after `hclean` are the literal upstream `r = 5`
specialization.
-/
theorem upstreamR5_of_clean (hclean : NoBalancedFiveColoring)
    {V : Type} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V = 5^2 + 1) (coloring : Sym2 V → Fin 5) :
    ∃ (S : Finset V) (k : Fin 5),
      S.card = 5 + 1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k := by
  exact (upstreamStatementR5_iff_noBalancedFiveColoring.mpr hclean) hV coloring

end Erdos617.InterfaceB

/-!
## Equivalence with our `Erdos617.Main`

The following are OUR theorems (not part of the verbatim transcription): the
external interface's two final statement shapes are logically equivalent to
`Erdos617.Main`, and — transported through those equivalences — are true given
our completed proof `Erdos617.erdos_617_r5_unconditional`.
-/

/-- The external interface's exact-upstream `r = 5` statement is logically
equivalent to our `Erdos617.Main`. Forward instantiates their arbitrary-`V`
statement at `V = Fin 26` (using `Fintype.card (Fin 26) = 5 ^ 2 + 1`) and reads
off `S.card = 5 + 1 = 6`; backward is exactly our `main_imp_upstream`
(the `Fin 26` ⟹ arbitrary card-26 `V` transport). -/
theorem interfaceB_upstreamR5_iff_main :
    Erdos617.InterfaceB.UpstreamStatementR5 ↔ Erdos617.Main := by
  unfold Erdos617.InterfaceB.UpstreamStatementR5 Erdos617.InterfaceB.UpstreamStatement
  constructor
  · intro hU c
    have hcard : Fintype.card (Fin 26) = 5 ^ 2 + 1 := by norm_num [Fintype.card_fin]
    obtain ⟨S, k, hScard, hmiss⟩ := hU (V := Fin 26) hcard c
    exact ⟨S, k, by omega, hmiss⟩
  · intro hMain V _ _ hV coloring
    exact Erdos617.main_imp_upstream hMain hV coloring

/-- The external interface's clean `NoBalancedFiveColoring` target is logically
equivalent to our `Erdos617.Main`, by composing the interface's own
`upstreamStatementR5_iff_noBalancedFiveColoring` with the equivalence above. -/
theorem interfaceB_noBalanced_iff_main :
    Erdos617.InterfaceB.NoBalancedFiveColoring ↔ Erdos617.Main :=
  Erdos617.InterfaceB.upstreamStatementR5_iff_noBalancedFiveColoring.symm.trans
    interfaceB_upstreamR5_iff_main

/-- **Corollary (transported).** The external interface's exact-upstream `r = 5`
statement holds — modulo the disclosed axioms of `erdos_617_r5_unconditional`
(the standard three + the native_decide reflection axioms) — obtained from our
completed proof through `interfaceB_upstreamR5_iff_main`. -/
theorem interfaceB_upstreamR5_unconditional :
    Erdos617.InterfaceB.UpstreamStatementR5 :=
  interfaceB_upstreamR5_iff_main.mpr Erdos617.erdos_617_r5_unconditional

/-- **Corollary (transported).** The external interface's clean
`NoBalancedFiveColoring` target holds — modulo the disclosed axioms of
`erdos_617_r5_unconditional` — obtained from our completed proof through
`interfaceB_noBalanced_iff_main`. -/
theorem interfaceB_noBalanced_unconditional :
    Erdos617.InterfaceB.NoBalancedFiveColoring :=
  interfaceB_noBalanced_iff_main.mpr Erdos617.erdos_617_r5_unconditional
