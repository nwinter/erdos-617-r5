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
- `check_challenge_fidelity.sh` (here) — proves the Challenge's *self-contained*
  definitions are byte-identical to the canonical ones the Solution uses, so that
  "the Challenge and the Solution talk about the same `Main`/`KPEqualityClassification`".

In short: comparator answers *"does the Solution prove the Challenge, cleanly?"*;
the documents above answer *"is the Challenge the right theorem?"*.

## Files

- **`Challenge.lean`** — the four theorem **statements** with `sorry`. To stay
  auditable without trusting this repo, it imports only Mathlib and **vendors** the
  six statement-reachable definitions (`edgeCountIn`, `IsIndep`, `Main`,
  `alphaAtMost`, `AB21`, `KPEqualityClassification`) byte-identically from
  `lean617/Lean617/{Statements,LTable,Equality21}.lean`, with per-definition
  provenance comments. We use **no definition holes** (see *Why no holes* below).
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
  every constant reachable *from a statement* — here `Main` and
  `KPEqualityClassification` and everything they unfold to — comparator compares
  the **full definition (type and body)** between Challenge and Solution and
  rejects on any mismatch. This is why the vendored bodies must be identical, and
  it is a second, kernel-level check of the same thing `check_challenge_fidelity.sh`
  checks textually.
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
   The runner builds a throwaway lake workspace (our Lean v4.30.0 + Mathlib),
   fetches the Mathlib cache, ensures the SAT certificates exist, then runs
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

## Toolchain (the load-bearing caveat)

Our Solution is **Lean v4.30.0** (Mathlib v4.30.0); upstream comparator/lean4export
track **v4.33**. `lean4export` reads our v4.30 oleans (olean format is
version-specific), and it conveniently publishes a **`v4.30.0` tag** — so CI pins
`LEAN4EXPORT_REV=v4.30.0`, giving an exporter that reads our oleans natively.
`comparator` has no v4.30 line, so CI pins its master HEAD commit for
reproducibility. The **only** residual unknown is whether a v4.33 `comparator` can
parse a **v4.30.0 export** (same tool, older format version) — this is the thing
to confirm before the CI job is promoted from `continue-on-error` to required. If
it does not interoperate, the fixes are to pin comparator to a v4.30-compatible
commit, or to bump lean617 to v4.33 (a Mathlib bump).

## Trust statement

A passing run guarantees (1)–(3) above **given** comparator's own assumptions: the
Challenge's imports/lakefile are trusted (here: Mathlib + this vendored file); no
adversarial Solution was compiled in the environment beforehand; landrun sandboxes
correctly; and the Lean kernel is correct (or, with nanoda enabled, Lean *or*
nanoda is). It does **not** vouch for the informal-problem encoding — that is
`PROBLEM.md` + the fidelity reviews + `check_challenge_fidelity.sh`.

### Optional second kernel (nanoda)

Set `"enable_nanoda": true` in the config and provide the `nanoda_bin` binary
(build from `ammkrn/nanoda_lib`; point `COMPARATOR_NANODA` at it) to additionally
replay the Solution through the independent nanoda kernel — reducing the trust
assumption to "the Lean **or** the nanoda kernel is correct". We ship `false` by
default so the check needs no extra binary; enabling it is a pure hardening step.
