/-
F9: final assembly of the r = 5 case of Erdős Problem 617.

  erdos_617_r5 (h : KPEqualityClassification) : Main

Every link is sorry-free. The axiom profile (audited below via #print axioms):
  - propext, Classical.choice, Quot.sound  (standard),
  - the four SAT-reflection axioms entering through `primFacts`
    (Lean617.Primitives; per-computation native_decide axioms, the same trust base as
    Lean's `bv_decide`; underlying certificates: cadical + LRAT, checked by
    Lean's verified checker — regeneration recipe in FORMAL.md F3),
  - and the single explicit hypothesis `KPEqualityClassification` — the classical
    Kang–Pikhurko (2005) equality classification at (r,n) = (5,21)
    (literature-verified in papers/brouwer-kang-pikhurko.md; independently
    numerically validated, FORMAL.md EQUALITY21 analysis). NB Brouwer's bound
    itself is no longer assumed: its `saving` form is PROVEN (`kp_saving`,
    Lean617.BrouwerInduction, axiom-clean), and `brouwerFacts_of`
    (Lean617.Equality21) assembles the full `BrouwerFacts` from that proof plus
    this one hypothesis.

`main_imp_upstream` (Lean617.Statements) transports `Main` to the upstream
google-deepmind/formal-conjectures `erdos_617` statement shape at r = 5.
-/
import Lean617.Statements
import Lean617.Primitives
import Lean617.MH2Proof
import Lean617.MMProof
import Lean617.Equality21
import Lean617.JoinTransport

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.style.multiGoal false

namespace Erdos617

/-- [MM] unconditionally: the SAT primitives are discharged. -/
theorem lemma_MM : MM := lemma_MM_of primFacts

/-- [MH″], conditional on the single classical hypothesis `KPEqualityClassification`.
`brouwerFacts_of` assembles the full `BrouwerFacts` from the PROVEN Brouwer bound
(`kp_saving`) and this hypothesis. -/
theorem lemma_MH2 (h : KPEqualityClassification) : MH2 :=
  lemma_MH2_of primFacts (brouwerFacts_of h)

/-- **Erdős Problem 617, r = 5**, conditional on exactly one published classical result — the
Kang–Pikhurko equality classification at `(r,n) = (5,21)` (`KPEqualityClassification`;
literature-verified in papers/brouwer-kang-pikhurko.md, independently numerically validated,
FORMAL.md EQUALITY21 analysis). Everything else — including Brouwer's bound itself (`kp_saving`) —
is proven. Conclusion: every 5-colouring of the edges of `K₂₆` has six vertices whose induced `K₆`
misses a colour. -/
theorem erdos_617_r5 (h : KPEqualityClassification) : Main :=
  chain_deduction (lemma_MH2 h) lemma_MM

/-- The upstream-shaped corollary over an arbitrary 26-element vertex type, conditional on the same
single hypothesis `KPEqualityClassification`. -/
theorem erdos_617_r5_upstream (h : KPEqualityClassification) {V : Type} [Fintype V]
    [DecidableEq V] (hV : Fintype.card V = 5 ^ 2 + 1)
    (coloring : Sym2 V → Fin 5) :
    ∃ (S : Finset V) (k : Fin 5), S.card = 5 + 1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k :=
  main_imp_upstream (erdos_617_r5 h) hV coloring

/-- **Erdős Problem 617, r = 5 — UNCONDITIONAL** (modulo the standard Lean axioms and the
`native_decide` reflection axioms). The sole classical hypothesis `KPEqualityClassification` — the
Kang–Pikhurko (2005) equality classification at `(r,n) = (5,21)` — is now itself PROVEN in Lean
(`kp_equality_classification_proven`, Lean617.JoinTransport) via the D1–D4 cone descent
`(5,21)→(4,17)→(3,13)→(2,9)`, the join-transport reassembly, and the `(2,9)` base classification
(`base_classification`). Conclusion: every 5-colouring of the edges of `K₂₆` has six vertices whose
induced `K₆` misses a colour. Its `#print axioms` (audited in `AxiomAudit.lean`) is the three
standard axioms plus the SAT-reflection and KP-construction `native_decide` axioms — no `sorryAx`,
no remaining mathematical hypothesis. -/
theorem erdos_617_r5_unconditional : Main :=
  erdos_617_r5 kp_equality_classification_proven

/-- The upstream-shaped corollary over an arbitrary 26-element vertex type, UNCONDITIONAL. -/
theorem erdos_617_r5_upstream_unconditional {V : Type} [Fintype V]
    [DecidableEq V] (hV : Fintype.card V = 5 ^ 2 + 1)
    (coloring : Sym2 V → Fin 5) :
    ∃ (S : Finset V) (k : Fin 5), S.card = 5 + 1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k :=
  erdos_617_r5_upstream kp_equality_classification_proven hV coloring

end Erdos617
