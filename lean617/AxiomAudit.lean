/-
Axiom audit for the four final theorems of the r = 5 resolution.

Run with:  lake env lean AxiomAudit.lean

Expected axiom profile for every theorem below:
  - propext, Classical.choice, Quot.sound        (the three standard Lean axioms)
  - the four SAT-reflection native_decide axioms  (the same trust base as Lean's
                                                   bv_decide; via `primFacts`)
and — for the three that depend on it — the single explicit *mathematical*
hypothesis `Erdos617.KPEqualityClassification` (the (5,21) Kang–Pikhurko equality
classification), which is a hypothesis variable, not an axiom (it therefore does
NOT appear in `#print axioms`; it is discharged by the caller).

NB (F6i): the `saving` field of `BrouwerFacts` is now PROVEN (`kp_saving`,
axiom-clean), and `brouwerFacts_of` assembles `BrouwerFacts` from it plus the one
hypothesis; so `BrouwerFacts` itself no longer appears as an assumption of the
final theorems. The KP construction `kpG`'s native_decide facts (KPConstruction)
do NOT enter these theorems — the `equality21` field is discharged via the
hypothesis route (`equality21_final` ∘ `equality21_transport`), which never touches
`kpG` — so no new native_decide axioms appear beyond the four SAT ones.

There must be NO `sorryAx` anywhere. `tools/axiom_audit.sh` greps this file's
output for exactly that condition.
-/
import Lean617.Final

#print axioms Erdos617.lemma_MM
#print axioms Erdos617.lemma_MH2
#print axioms Erdos617.erdos_617_r5
#print axioms Erdos617.erdos_617_r5_upstream
