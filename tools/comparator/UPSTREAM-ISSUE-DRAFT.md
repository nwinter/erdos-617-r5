# DRAFT upstream issue for leanprover/comparator — DO NOT FILE without owner sign-off

> Filing posts publicly under the repo owner's GitHub account. This is a ready-to-post
> draft; the owner decides whether/when to file it against `leanprover/comparator`.
> Written against commit `c3903e1ed0148a32cd39510707c632dc4d265514` (default branch `master`, Lean v4.33.0-rc1).

---

**Title:** `permitted_axioms` are required to exist in the *Challenge* too, which breaks `native_decide`-style per-invocation axioms

**Summary.** Comparator requires every entry of `permitted_axioms` to exist in **both** the Challenge and the Solution environments. That is fine for universal axioms (`propext`, `Classical.choice`, `Quot.sound`, `Lean.ofReduceBool`), but it makes comparator unusable for Solutions whose axioms are **per-invocation `native_decide` reflection axioms** — these exist only in the Solution, and their types can be enormous. Semantically, `permitted_axioms` describes what the *Solution* may use; the axiom *check* is already Solution-only. Only the export and the statement-compare over-reach to the Challenge.

**Where it happens.**
- `Main.lean:257-258` builds one shared `exportTargets` that includes `getLegalAxioms`, and `Main.lean:262` / `:266` export **both** the Challenge and the Solution with it. `safeExport` runs `lean4export` with `LEAN_ABORT_ON_PANIC=1` (`Main.lean:135-147`), so an axiom absent from the Challenge aborts the export:
  `PANIC at dumpConstant: Constant <axiom> not found in environment`.
- `Main.lean:249` passes `getTheoremNames ++ getLegalAxioms` to `compareAt`, and `compareAt` (`Compare.lean:70-83`) looks each target up in **both** `challenge.constMap` and `solution.constMap`, throwing `Const not found in challenge` otherwise (and comparing the two as `axiomInfo`/`axiomInfo`).
- The tell that this is over-reach: the axiom **check**, `checkAxioms` (`Axioms.lean:52-70`), already walks only the **Solution**'s constants. It never needs the axioms in the Challenge.

**Use case / motivation.** A Solution proving finite facts by `native_decide` (e.g. SAT/`bv_decide`-style LRAT reflection). Depending on the Lean version, `native_decide` emits a per-declaration axiom named `<decl>._native.native_decide.ax_1_1` rather than depending on the global `Lean.ofReduceBool`. These axioms (a) are declared only in the module that ran the tactic (the Solution), and (b) can have very large types — in our project (Erdős-problem formalization, Lean v4.30.0) each such axiom's *type* embeds a 340–455 MB LRAT certificate string plus Solution-internal defs. They cannot be re-declared or vendored into a Challenge. Today the only workaround is to `import` the Solution's axiom-generating module into the Challenge, which forfeits a self-contained Challenge and makes the reachable-constant cross-check on those imports vacuous.

**Minimal repro sketch.**
```lean
-- Solution.lean
theorem foo : (decide (0 < 1) = true) := by native_decide   -- yields Solution-only axiom `foo._native.native_decide.ax_1_1`
-- Challenge.lean
theorem foo : (decide (0 < 1) = true) := sorry
```
```jsonc
// config.json
{ "challenge_module": "Challenge", "solution_module": "Solution",
  "theorem_names": ["foo"], "permitted_axioms":
  ["propext","Quot.sound","Classical.choice","foo._native.native_decide.ax_1_1"],
  "enable_nanoda": false }
```
Expected today: the Challenge export panics on `foo._native.native_decide.ax_1_1` (absent from the Challenge). Even with the export made lenient, `compareAt` throws `Const not found in challenge`.

**Proposed fix (small, semantics-preserving).**
1. Split the export targets so the permitted axioms are exported **Solution-side only**:
   - `challengeExportTargets := builtinTargets ++ theoremNames ++ primitiveTargets ++ definitionNames` (no `legalAxioms`);
   - `solutionExportTargets  := challengeExportTargets ++ legalAxioms`.
2. In `verifyMatch`, pass `compareAt` only `theoremNames` (drop `++ legalAxioms` at `Main.lean:249`). Statement-compare should range over the theorems/definitions, not the axioms.
3. Keep `checkAxioms` exactly as is (already Solution-only) — it remains the enforcement that the Solution uses no axiom outside `permitted_axioms`.

This preserves every guarantee (statement match, axiom conformance, kernel replay) while letting the Challenge stay independent of the Solution's axiom-generating modules.

**Note on intent.** If exporting/comparing axioms on the Challenge side was meant to *pin the axioms' types* via the trusted Challenge, that guarantee is (a) trivial for universal axioms and (b) infeasible for large per-invocation `native_decide` axioms. If type-pinning is desired, a Solution-side "record the type of each permitted axiom and surface it" step would achieve it without requiring the axiom in the Challenge.

**Alternative already usable today (no upstream change):** import the Solution's axiom-generating module into the Challenge so the axioms are present. Downsides: the Challenge is no longer self-contained, and the reachable-constant cross-check on the shared imports becomes `X == X`. We currently do this (`tools/comparator/Challenge.lean` imports `Lean617.Primitives`); the fix above would let us drop it.
