# comparator harness for the four final theorems (Erdős 617, r = 5)

This directory lets a third party verify our result with the **standard**
Lean-FRO tool [`leanprover/comparator`](https://github.com/leanprover/comparator)
instead of our bespoke scripts. Comparator is a "trustworthy judge for Lean
proofs": given a **Challenge** (theorems stated with `sorry`) and a **Solution**
(a library that proves them), it checks — kernel-accepted and landrun-sandboxed —
that the Solution proves the *same* statements using *only* permitted axioms.

## What this verifies

For the four final theorems of the r = 5 case:

| theorem (in `Lean617.Final`) | shape |
|---|---|
| `Erdos617.erdos_617_r5_unconditional` | `Main` (unconditional) |
| `Erdos617.erdos_617_r5_upstream_unconditional` | upstream shape over any 26-element `V`, unconditional |
| `Erdos617.erdos_617_r5` | `KPEqualityClassification → Main` (conditional) |
| `Erdos617.erdos_617_r5_upstream` | upstream shape, conditional |

a passing comparator run certifies exactly three things:

1. **Statement match** — the Solution's theorem of each name has a type
   **alpha-equivalent** to the Challenge's (`Challenge.lean`). No definitional
   unfolding is used, so this is a strict statement-fidelity check.
2. **Axiom conformance** — every axiom in each proof's transitive closure is on
   the exact allow-list in `erdos617_r5.json` (the three standard Lean axioms plus
   the four SAT-reflection axioms; see below). Any other axiom — or a stray
   `sorryAx` — fails the run.
3. **Kernel acceptance** — the entire Solution environment is re-exported and
   replayed through the Lean kernel (optionally a second kernel; see *nanoda*).

## What this does NOT verify

Comparator treats the **Challenge as trusted** — it never asks whether the
Challenge's `sorry`-statements faithfully encode the informal Erdős–Gyárfás
conjecture. That fidelity is argued elsewhere and is **not** part of this harness:

- `PROBLEM.md` — the pinned informal statement and worked examples.
- The **R3 statement-fidelity review** (`RELEASE.md`) and the token-identity audit
  against upstream `google-deepmind/formal-conjectures` `erdos_617` at r = 5.
- `check_challenge_fidelity.sh` (here) — proves the Challenge's vendored
  `AB21`/`KPEqualityClassification` are byte-identical to canonical, and that the
  four theorem signatures match `Final.lean`. (The other statement-reachable defs —
  `Main`, `edgeCountIn`, `IsIndep`, `alphaAtMost` — are the Solution's own imported
  declarations; see *Why the Challenge imports the Solution's SAT layer* below.)

In short: comparator answers *"does the Solution prove the Challenge, cleanly?"*;
the documents above answer *"is the Challenge the right theorem?"*.

## Files

- **`Challenge.lean`** — the four theorem **statements** with `sorry`. It
  `import`s `Lean617.Primitives` (required — see *Why the Challenge imports the
  Solution's SAT layer* below), which brings the four permitted SAT axioms and the
  canonical `Main`/`edgeCountIn`/`IsIndep`/`alphaAtMost`, and it **vendors** the two
  remaining statement-reachable defs (`AB21`, `KPEqualityClassification`, from
  `Equality21.lean`, outside that import closure) byte-identically. We use **no
  definition holes** (see *Why no holes* below).
- **`erdos617_r5.json`** — the comparator config (referenced by the repo's
  `formalization.yaml`). Names the Challenge/Solution modules, the four theorems,
  and the permitted axioms.
- **`check_challenge_fidelity.sh`** — fast, Linux-free guard that the vendored
  definitions and theorem signatures still match canonical. Run it anywhere; wire
  it into CI. It needs no Lean/Mathlib/build/network.
- **`run_comparator.sh`** — assembles the lake workspace and runs comparator on
  Linux. The single source of truth for the invocation (CI calls it).

## How comparator decides (so you can read the config)

- Theorems are matched **by fully-qualified name** — the Challenge declares
  `Erdos617.erdos_617_r5_unconditional` (etc.) in `namespace Erdos617`, matching
  the Solution's names.
- Statement equality is **alpha-equivalence of the exported kernel type**. For
  every constant reachable *from a statement* — `Main`, `KPEqualityClassification`,
  and everything they unfold to — comparator compares the **full definition (type
  and body)** between Challenge and Solution and rejects on any mismatch. For the
  vendored `AB21`/`KPEqualityClassification` this is a second, kernel-level check of
  what `check_challenge_fidelity.sh` checks textually; for `Main`/`edgeCountIn`/
  `IsIndep`/`alphaAtMost` (imported) it is a tautology — they are the same
  declaration on both sides.
- `permitted_axioms` is an **exact-string allow-list** (no globs). The four
  SAT-reflection axioms are listed literally:

  ```
  propext
  Classical.choice
  Quot.sound
  Erdos617.unsat_M9._native.native_decide.ax_1_1
  Erdos617.unsat_M10._native.native_decide.ax_1_1
  Erdos617.unsat_nonex11._native.native_decide.ax_1_1
  Erdos617.unsat_nonex12._native.native_decide.ax_1_1
  ```

  The four `native_decide` reflection axioms widen the trust base to include the
  Lean compiler's evaluation of the four LRAT-certified SAT facts — a deliberate,
  visible cost, identical to the profile audited by `tools/axiom_audit.sh` and
  declared in `formalization.yaml`. (This matches our repo's allow-list, whose
  globs are just a convenience; comparator needs the exact names, given here.)

### Why the Challenge imports the Solution's SAT layer

Comparator requires **every permitted axiom to exist in both the Challenge and the
Solution** environments (it exports both with one shared target list — comparator
`Main.lean:257-266`, with `LEAN_ABORT_ON_PANIC` — and `compareAt` looks each axiom
up on both sides, `Compare.lean:70-83`). Standard `native_decide` proofs use the
universal axiom `Lean.ofReduceBool`, which is present everywhere; but our Lean
v4.30.0 emits **per-invocation** axioms (`…unsat_M9._native.native_decide.ax_1_1`,
…) that live only in the Solution, and whose *types embed the full 340/455MB LRAT
certificates* plus internal defs (`Erdos617F3.MCNF`, `verifyCert`). They cannot be
hand-declared or vendored. The only way to satisfy comparator is to `import` the
module that generates them — `Lean617.Primitives` — so the Challenge does.

**What this costs (stated plainly):** the Challenge is no longer Mathlib-only
self-contained; it trusts `Lean617.Primitives` via import (a legitimate,
comparator-intended pattern — "the Challenge's imports are trusted"). Because that
import also supplies the canonical `Main`/`edgeCountIn`/`IsIndep`/`alphaAtMost`,
comparator's cross-check of those against an independent Challenge copy is lost
(they are the same declaration on both sides). What comparator still verifies is
the load-bearing part: the four theorem **statements** re-type against the Solution
(including that the vendored `KPEqualityClassification` hypothesis matches), the
Solution's proofs use **only** the exact axiom allow-list, and the whole Solution
**replays through the kernel**. The claim that these `Prop`s encode the informal
conjecture rests, as always, on `PROBLEM.md` + the R3 review +
`check_challenge_fidelity.sh` (which reads the canonical `Statements.lean`).

### Why no definition holes

Comparator can also leave definitions as *holes* (`definition_names`), comparing
only their type/universe/safety and **not** their body. We deliberately keep
`definition_names` empty: a hole would let a Solution redefine `Main := True` (or
the hypothesis `KPEqualityClassification := False`, making the conditional theorem
vacuous) and "win" trivially — comparator itself warns hole solutions need an
extra human check. Vendoring the bodies instead makes any drift a safe
**rejection**, not a false pass.

## Running it

### Linux (authoritative)

Comparator's sandbox uses **landrun** (Linux Landlock) and is **Linux-only**.

1. Build the three binaries once (versions matter — see *Toolchain* below):
   - `landrun` (github.com/Zouuup/landrun): `go build -o landrun cmd/landrun/main.go`
   - `lean4export` (github.com/leanprover/lean4export) at its **`v4.30.0` tag**
     (matches our Solution's toolchain), built with `lake build`.
   - `comparator` (github.com/leanprover/comparator, pinned commit): `lake build comparator`
2. Point the runner at them and go:
   ```bash
   export COMPARATOR_LANDRUN=/abs/landrun
   export COMPARATOR_LEAN4EXPORT=/abs/lean4export
   export COMPARATOR_COMPARATOR=/abs/comparator
   tools/comparator/run_comparator.sh
   ```
   The runner builds a throwaway lake workspace (our Lean v4.30.0 + Mathlib +
   `lean617` as a path dep, since the Challenge now imports `Lean617.Primitives`),
   fetches the Mathlib cache, ensures the SAT certificates exist, runs the
   standalone Solution-export feasibility probe (logs bytes/time/RSS), then runs
   `lake env comparator erdos617_r5.json`. Exit 0 = verified.

The canonical runner is **CI** (`.github/workflows/verify.yml`, job `comparator`,
`ubuntu-latest`), which does the builds and calls `run_comparator.sh`.

### macOS

There is **no real landrun on macOS**. Options:

- **Preferred:** run the CI job, or run `run_comparator.sh` inside a Linux
  container (e.g. `ubuntu:24.04` with elan + Go).
- **Dev only, unsandboxed:** point `COMPARATOR_LANDRUN` at upstream
  `scripts/fake-landrun.sh`. It runs comparator **without sandboxing** and prints a
  warning; the sandbox guarantee is void, so **do not treat a macOS pass as
  authoritative**.

Everything except the sandboxed run is macOS-friendly: `check_challenge_fidelity.sh`
and JSON validation run anywhere, and `Challenge.lean` elaborates against our
project with `lake env lean` (sorry warnings only).

## Open risks (why the CI job is `continue-on-error`)

Two things must still hold for a full run to pass; CI is the probe for both.

**1. Feasibility of exporting the huge axiom types (the binding risk).** The four
permitted axioms embed the full 340/455MB LRAT certificates in their *types*.
Comparator must export the Solution with those axioms, then parse and kernel-replay
a multi-GB export. This may exceed a hosted runner's memory/time regardless of
anything else. `run_comparator.sh` therefore runs a **standalone Solution-export
probe** first and logs bytes / wall-time / peak-RSS, so if this is what defeats
comparator, CI says so precisely. If it proves infeasible, the documented resting
state is **option C**: keep the harness artifacts and this README, leave the job
advisory, and rely on `tools/axiom_audit.sh` + R3 + `check_challenge_fidelity.sh`
(which already deliver the verification comparator was to cross-check).

**2. Toolchain (downstream, not yet exercised).** Our Solution is Lean **v4.30.0**;
comparator tracks **v4.33**. `lean4export` publishes a **`v4.30.0` tag** (CI pins
`LEAN4EXPORT_REV=v4.30.0`, so it reads our oleans natively); `comparator` has no
v4.30 line, so CI pins its master HEAD. The residual question — can a v4.33
comparator parse a v4.30.0 export — could not be reached earlier (the export
panicked first on the axiom issue, now fixed by importing `Lean617.Primitives`). If
it fails, pin comparator to a v4.30-compatible commit, or bump lean617 to v4.33.

**Upstream fix (the principled alternative).** Requiring permitted axioms on the
*challenge* side is arguably a comparator gap — the axioms are what the *Solution*
uses, and the axiom check (`Axioms.lean`) is already solution-only. A minimal
upstream change (don't export/compare `permitted_axioms` challenge-side) would let
the Challenge go back to Mathlib-only self-contained. See `UPSTREAM-ISSUE-DRAFT.md`.

## Trust statement

A passing run guarantees (1)–(3) above **given** comparator's own assumptions: the
Challenge's imports/lakefile are trusted (here: Mathlib + `Lean617.Primitives` +
the two vendored defs); no adversarial Solution was compiled in the environment
beforehand; landrun sandboxes correctly; and the Lean kernel is correct (or, with
nanoda enabled, Lean *or* nanoda is). It does **not** vouch for the informal-problem
encoding — that is `PROBLEM.md` + the fidelity reviews + `check_challenge_fidelity.sh`.
And it does not independently cross-check `Main`/`edgeCountIn`/`IsIndep`/`alphaAtMost`
(imported canonically), only the vendored `AB21`/`KPEqualityClassification`.

### Optional second kernel (nanoda)

Set `"enable_nanoda": true` in the config and provide the `nanoda_bin` binary
(build from `ammkrn/nanoda_lib`; point `COMPARATOR_NANODA` at it) to additionally
replay the Solution through the independent nanoda kernel — reducing the trust
assumption to "the Lean **or** the nanoda kernel is correct". We ship `false` by
default so the check needs no extra binary; enabling it is a pure hardening step.
