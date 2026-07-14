# Reproducible rebuild audit — kernel-pure profile (ROUND-2026-07-14, Task A)

Everything here was produced by ONE scripted pipeline (`tools/rebuild_audit.sh`) run
against a **fresh `git clone`** of this repository in a scratch directory (no shared
build state with any working checkout; the Mathlib olean cache was fetched by
`lake exe cache get` as any third party would). The source commit is in
`source-commit.txt`. This audit certifies the **kernel-pure migration**: the 10
Kang–Pikhurko construction witnesses are now kernel `decide` (zero reflection axioms),
so the unconditional theorems dropped from a 17-axiom to a **7-axiom** profile.

Replay:

```
git clone <this-repo> fresh && cd fresh
# supply the 4 gitignored LRAT certificates into fresh/lean617/Lean617/certs/
#   (release bundle, or regenerate: tools/regen_certificates.sh)
tools/rebuild_audit.sh verification/rebuild-kernel-pure     # or inline the steps
```

**Memory note (important after the kernel-pure migration).** The three
kernel-`decide` modules (`KPConstruction`, `JoinTransport`, `EqualityProof`) each
peak at **~6 GB** during compilation (the price of kernel `decide` over
`native_decide`; a one-time build cost). They are dependency-chained so they never
compile concurrently, but a plain `lake build` can still stack a heavy module with
lighter workers. The memory-safe recipe (this Lake version has **no `-j` flag**) is
to build the heavy module first in its own invocation, then the rest:

```
lake build Lean617.KPConstruction && lake build
```

Reproducers on a busy or **< 32 GB** machine should also (owner directive on the
shared 64 GB box here): check `memory_pressure | grep 'free percentage'` and only
start a build with ≥ 25% free, and never run two Lean builds concurrently.

## Headline result

`#print axioms Erdos617.erdos_617_r5_unconditional` (and `_upstream_unconditional`)
now depend on **exactly 7 axioms**:

```
[propext, Classical.choice, Quot.sound,
 Erdos617.unsat_nonex11._native.native_decide.ax_1_1,
 Erdos617.unsat_nonex12._native.native_decide.ax_1_1,
 Erdos617.unsat_M9._native.native_decide.ax_1_1,
 Erdos617.unsat_M10._native.native_decide.ax_1_1]
```

**No `sorryAx`. No KP-construction `native_decide` axioms** (the ten
`kpG*`/`kpG1*` witnesses are gone — proved by kernel `decide`). The conditional
`erdos_617_r5`/`_upstream` carry the same 3 standard + 4 SAT profile.

## Artifacts

| file | what it is | expected content |
|---|---|---|
| `source-commit.txt` | commit the fresh clone was made at | the kernel-pure commit |
| `fingerprint.txt` | machine/OS/CPU + elan/lean/lake/cadical/drat-trim versions | Apple M1 Ultra, Lean 4.30.0, cadical 3.0.0 |
| `lean-toolchain`, `lake-manifest.json` | exact pins, copied from the clone | — |
| `cache-get.log` | Mathlib cache fetch | "Completed successfully" |
| `build.log.gz` | **complete** `lake build` output | "Build completed successfully", exit 0 |
| `axioms.txt` | verbatim `#print axioms` for all four exported theorems | conditional pair: 3 standard + 4 SAT; unconditional pair: **the same 7**, no KP `native_decide`, **no sorryAx** |
| `leanchecker.log` | toolchain-bundled `leanchecker` (external kernel re-check), one process per module, on Statements/Final/EqualityProof/JoinTransport/Primitives/**KPConstruction** | empty (leanchecker prints nothing on success); the **exit-0 verdicts are in `steps.log`** (`leanchecker Lean617.X: exit 0`, all six) |
| `cert-sha256.txt` | SHA-256 of the four LRAT certificates used | see caveat 1 |
| `sat-recheck.log` | all four CNFs **re-emitted from the Lean defs** and checksummed against `tools/certgen/checksums.txt` (encoding-drift check); fresh CaDiCaL re-solves of M9/M10 | 4× "sha256 OK"; 2× exit 20 (UNSAT) |
| `drattrim-M9.log`, `drattrim-M10.log` | **NEW: independent drat-trim re-verification** of the fresh re-solves | "s VERIFIED" |
| `m9-kernel-pure-demo.log` | the `KernelPureDemo/Demo.lean` run (kernel-pure `lrat_proof` on M9's core) | `'m9_kernel_pure' depends on axioms: [propext, Classical.choice, Quot.sound]` |
| `solve-logs/` | full CaDiCaL + drat-trim transcripts of the nonex11/nonex12 fresh re-solves | cadical exit 20; drat-trim "s VERIFIED" |
| `steps.log` | the pipeline's step-by-step transcript | ends "ALL DONE build=0 axioms=0" |

## Trust notes (read before citing this audit)

1. **Certificate provenance.** The four `*.lrat` files are gitignored (~815 MB); this run
   copied them from the working checkout and recorded SHA-256s (`cert-sha256.txt`). Their
   *validity* does not rest on provenance: the `lake build` in this run re-verified each with
   Lean's LRAT checker (`verifyCert`), and `sat-recheck.log` proves the CNFs are byte-identical
   to what the Lean definitions emit today.

2. **The "never re-solved" caveat from the 2026-07-13 audit is now CLOSED.** All four
   primitives were re-SOLVED from scratch this round with CaDiCaL 3.0.0 and, additionally,
   the fresh proofs were INDEPENDENTLY re-verified with `ext/drat-trim` (a different checker
   from Lean's) — M9/M10 inline here (`drattrim-*.log`), nonex11/nonex12 in `solve-logs/`
   (325MB/455MB DRAT proofs, drat-trim "s VERIFIED").

3. **Why four `native_decide` axioms remain.** The kernel-pure LRAT route (Mathlib
   `lrat_proof`) is demonstrated axiom-clean on M9 (`m9-kernel-pure-demo.log`), but it cannot
   be bridged to `primFacts`'s `CNF.Unsat` shape: that needs the kernel to reduce our
   `MCNF`/`nonexCNF` (`List.sublistsLen`-generated), which times out
   (`lean617/KernelPureDemo/BridgeInfeasibilityProbe.lean`), and nonex11/12 additionally
   exceed memory. Full accounting: `FORMAL.md` → "KERNEL-PURE MIGRATION".

4. **KP-purity is now regression-checked.** `tools/axiom_allowlist.txt` uses four TIGHT
   per-primitive SAT globs (not a blanket `*native_decide*`), so any construction witness
   regressing to `native_decide` fails `tools/axiom_audit.sh`.
