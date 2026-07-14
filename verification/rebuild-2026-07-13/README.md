# Reproducible rebuild audit — 2026-07-13 (VERIFICATION-ROUND.md Task 1)

Everything in this directory was produced by ONE scripted pipeline run against a
**fresh `git clone`** of this repository in a scratch directory (no shared build
state with any working checkout; the Mathlib olean cache was fetched by
`lake exe cache get` as any third party would). The source commit that was
cloned is in `source-commit.txt`. A third party replays this audit with:

```
git clone <this-repo> fresh && cd fresh
# supply the 4 gitignored LRAT certificates (release asset certs-v1.0.tgz, or
# regenerate: tools/regen_certificates.sh) into lean617/Lean617/certs/
cd lean617 && lake exe cache get && lake build          # expect: exit 0
echo 'import Lean617
#print axioms Erdos617.erdos_617_r5_unconditional' > A.lean && lake env lean A.lean
```

## Artifacts

| file | what it is | expected content |
|---|---|---|
| `source-commit.txt` | commit the fresh clone was made at | — |
| `fingerprint.txt` | machine/OS/CPU + elan/lean/lake versions + Mathlib rev | Lean 4.30.0; Mathlib rev in `lake-manifest.json` |
| `lean-toolchain`, `lake-manifest.json` | exact toolchain pins, copied verbatim from the clone | — |
| `cache-get.log.gz` | Mathlib cache fetch | "Completed successfully" |
| `build.log.gz` | **complete** `lake build` output | "Build completed successfully (8497 jobs)", exit 0 |
| `axioms.txt` | verbatim `#print axioms` for all four exported theorems | unconditional pair: 3 standard + 14 `native_decide` = 17, **no sorryAx**; conditional pair: 3 standard + 4 SAT |
| `leanchecker.log` | toolchain-bundled `leanchecker` (external kernel re-check), one process per module, on Statements/Final/EqualityProof/JoinTransport/Primitives | exit 0 ×5 |
| `cert-sha256.txt` | SHA-256 of the four LRAT certificates used | see caveat below |
| `sat-recheck.log` | (a) all four CNFs **re-emitted from the Lean definitions** and checksummed against the canonical `tools/certgen/checksums.txt` — the encoding-drift check; (b) full CaDiCaL re-solves of M9/M10 | 4× "sha256 OK"; 2× exit 20 (UNSAT) |
| `kp-witness-checks.log` | independent numeric cross-checks of the KP-construction witnesses (`scratchpad/coneextend_iso.py`, `eq21_*`) | all MATCH/True |
| `steps.log` | the pipeline's step-by-step transcript | ends "ALL DONE build=0 axioms=0" |

## Trust notes (read before citing this audit)

1. **Certificate provenance.** The four `*.lrat` files are gitignored (~815 MB);
   this run copied them from the working checkout and recorded their SHA-256s
   (`cert-sha256.txt`). Their *validity* does not rest on provenance: the
   `lake build` in this very run re-verified each of them with Lean's verified
   LRAT checker (`Primitives.lean`, `verifyCert` + `native_decide` — the four
   `unsat_*` axioms in `axioms.txt` are exactly that check), and `sat-recheck.log`
   proves the CNFs they certify are byte-identical to what the Lean definitions
   emit today. A maximally suspicious third party regenerates the certificates
   from scratch (`tools/regen_certificates.sh`; nonex11/12 take CaDiCaL hours)
   or downloads the release bundle and compares hashes.
2. **nonex11/nonex12 were not re-SOLVED here** (hours of CaDiCaL); they were
   kernel-REPLAYED by the build, which is the stronger check. M9/M10 were also
   fully re-solved as fault diversity (exit 20 = UNSAT).
3. **leanchecker invocation**: the first scripted attempt passed olean paths
   (wrong; see `steps.log`) and was re-run as `lake env leanchecker <Module>`
   per the official-validation convention; `leanchecker.log` is the re-run.
4. The machine also carried unrelated compute load during the build; this
   affects wall-clock only, not any verdict.
