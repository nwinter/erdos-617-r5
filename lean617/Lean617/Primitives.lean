import Lean617.PrimMBridge

/-!
# F3: discharge of `PrimFacts` via verified SAT certificates.

The four SAT-primitive facts (`Lean617.LTable.PrimFacts`) are proved by kernel-checking
externally-generated LRAT certificates with `Std.Tactic.BVDecide`'s `verifyCert`, then bridging
the CNF (un)satisfiability to the graph statements (`PrimBridge`/`PrimMBridge`).

Pipeline for each instance (see FORMAL.md F3 and `lean617_f3/`):
`emitDimacs cnf` → `cadical … --lrat --shrink=0 --unsat --inprocessing=false` → `LRAT.trim` →
the trimmed `.lrat` embedded via `include_str` and checked by `native_decide`.

Axiom footprint of `primFacts`: propext, Classical.choice, Quot.sound, and the four
`native_decide` per-computation axioms — the standard, unavoidable cost of machine-scale
SAT reflection (this is exactly what `bv_decide` produces).

Certificates live in `Lean617/certs/` (git-ignored; regenerate via the pipeline above with
`lean617_f3/`'s `emit`/`trimtool`).
-/

open Erdos617 Erdos617F3 Std.Sat Std.Tactic.BVDecide.Reflect

namespace Erdos617

/-! ## The four unsatisfiability certificates. -/

theorem unsat_nonex11 : (nonexCNF 11).Unsat :=
  verifyCert_correct (nonexCNF 11) (include_str "certs/nonex11.lrat") (by native_decide)

theorem unsat_nonex12 : (nonexCNF 12).Unsat :=
  verifyCert_correct (nonexCNF 12) (include_str "certs/nonex12.lrat") (by native_decide)

theorem unsat_M9 : (MCNF 9 18).Unsat :=
  verifyCert_correct (MCNF 9 18) (include_str "certs/M9.lrat") (by native_decide)

theorem unsat_M10 : (MCNF 10 24).Unsat :=
  verifyCert_correct (MCNF 10 24) (include_str "certs/M10.lrat") (by native_decide)

/-! ## Discharging `PrimFacts`. -/

/-- **The four SAT-primitive facts, proved.** Feeds `Lean617.LTable`'s conditional L-table. -/
theorem primFacts : PrimFacts where
  nonex11 G hcap hα := nonex_of_unsat unsat_nonex11 G hcap hα
  nonex12 G hcap hα := nonex_of_unsat unsat_nonex12 G hcap hα
  M9 G hcap hα hω := by
    by_contra h
    push_neg at h
    exact M_of_unsat unsat_M9 G hcap hα hω (by omega) (by omega)
  M10 G hcap hα hω := by
    by_contra h
    push_neg at h
    exact M_of_unsat unsat_M10 G hcap hα hω (by omega) (by omega)

end Erdos617
