# Kernel-pure SAT demonstration (ROUND-2026-07-14, Task A / WS2)

These files are **not part of the `Lean617` library** — `lake build` ignores them.
They stand as the end-to-end validation, and the precise infeasibility accounting,
for the kernel-pure migration of the four SAT primitives.

## What was migrated, what was not

The **10 KP-construction witnesses** were migrated from `native_decide` to kernel
`decide` (commit history "kernel-pure WS1"), removing 10 reflection axioms from
`Erdos617.erdos_617_r5_unconditional`. Its profile is now
`[propext, Classical.choice, Quot.sound]` + the **four SAT-primitive**
`native_decide` axioms (`unsat_nonex11/nonex12/M9/M10`) = 7 axioms (was 17).

The **four SAT primitives retain `native_decide`**. This directory shows both that
the kernel-pure route *works and is axiom-clean*, and *why it cannot currently be
wired into `primFacts`*.

## Files

| file | what it shows |
|---|---|
| `Demo.lean` | `lrat_proof m9_kernel_pure` on M9's DIMACS + drat-trim core LRAT. Kernel-checks the certificate (proof-term replay, no `ofReduceBool`). `#print axioms` = `[propext, Classical.choice, Quot.sound]` — **axiom-pure**. |
| `M9.cnf` | canonical M9 DIMACS (sha256 `596ffcf…`, matches `tools/certgen/checksums.txt`). |
| `M9.core.lrat` | fresh CaDiCaL 3.0.0 re-solve, backward-trimmed to the UNSAT core by `ext/drat-trim` (17010 core lemmas). |
| `BridgeInfeasibilityProbe.lean` | **expected to time out.** The minimal kernel reduction any bridge would need (`(MCNF 9 18).clauses.size = 39743 by rfl`) does not finish in >400s at `maxRecDepth 1e6`. |

## Reproduce

```
cd lean617
# (1) the axiom-pure kernel check — ~495s wall, ~14GB peak on a 64GB machine
lake env lean KernelPureDemo/Demo.lean
#   => 'm9_kernel_pure' depends on axioms: [propext, Classical.choice, Quot.sound]

# (2) regenerate the assets from scratch
lake env lean --run ../tools/certgen/emit_cnf.lean M 9 18 KernelPureDemo/M9.cnf
cadical KernelPureDemo/M9.cnf /tmp/M9.drat --binary=false --quiet --unsat --inprocessing=false
../ext/drat-trim/drat-trim KernelPureDemo/M9.cnf /tmp/M9.drat -L KernelPureDemo/M9.core.lrat  # "s VERIFIED"

# (3) watch the bridge obstruction time out
timeout 420 lake env lean KernelPureDemo/BridgeInfeasibilityProbe.lean   # expect: killed / no output
```

## The gap, precisely

`lrat_proof` produces a theorem about Mathlib's own `Sat.Fmla` (parsed from the DIMACS
string). `primFacts` needs `Std.Sat.CNF.Unsat (MCNF 9 18)`. Connecting the two makes the
kernel reduce `MCNF`/`nonexCNF` (built from `List.sublistsLen`), which does not terminate
in feasible time (`BridgeInfeasibilityProbe.lean`). Separately, the two nonexistence
primitives are out of reach on memory: nonex11/nonex12 certificates are 325MB/455MB
(hundreds of thousands of lemmas) while M9's 17010-lemma core already needs 14GB in
`lrat_proof`. A full kernel-pure SAT integration would require reimplementing
`PrimEncoding` in a kernel-reducible representation plus a proof-producing LRAT checker
over `Std.Sat.CNF` — a substantial project deferred to future work.
