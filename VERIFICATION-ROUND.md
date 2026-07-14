# Verification round on the completed r=5 result (human collaborator request, 2026-07-13)

Three tasks on the COMPLETED r=5 theorem. Task 1 is mechanical — run it first. Tasks 2 and 3 can proceed in parallel with it. Sequence around ongoing r=6 work however you judge best; this round takes priority. Ground rule for the whole round: work entirely inside this repository — do not read, search for, or open any other repository or directory on this machine, and do not try to identify the origin of the external candidate below.

## Task 1 — Reproducible rebuild + committed audit outputs

From a FRESH CLONE (or pristine worktree) of lean617/ in a scratch directory: fetch the Mathlib cache, run a full clean `lake build`, and capture the complete build log. Then run `#print axioms` for `Erdos617.erdos_617_r5_unconditional`, `Erdos617.erdos_617_r5_upstream`, and the conditional `erdos_617_r5` export, capturing exact outputs. Commit to this repo under `verification/rebuild-2026-07-13/`: the full build log, the verbatim axiom outputs, `lean-toolchain`, the Mathlib revision from the lake manifest, and a machine/OS fingerprint. Also re-run the DRAT/LRAT checks for the four SAT primitives and the KP-witness checks, and commit those logs alongside. Goal: a third party can replay the entire audit from the repo alone, with no reliance on claims in RESULTS.md.

## Task 2 — Adversarial review of an external candidate proof

`review_queue/external-candidate-B/candidate-proof.md` is an external candidate proof of the same theorem (no balanced 5-colouring of K_26). Its provenance is deliberately withheld; ignore any provenance hints and judge only the mathematics.

Protocol (your own review standard applies): adopt the working stance that it contains at least one fatal gap, and hunt for the single weakest inference. The candidate relies on machine-checked SAT/LRAT certificates for certain finite lemmas; treat each such certified lemma's STATEMENT as a given fact (certified in the candidate's own infrastructure — you are not asked to replay them) and review everything else: the top-level reduction, every inference between given facts, quantifier order and edge cases (K_25 vs K_26 off-by-ones, empty colour classes, the exact definition of balanced — check against PROBLEM.md), the counting arguments, and the faithfulness of its literature citations (retrieve the cited papers yourself; do not trust its paraphrases — you already hold verified notes on some of them in papers/).

Use fresh-eyes subagent reviewers per your protocol. Deliver `review_queue/external-candidate-B/review-by-team-A.md`: verdict FATAL (state the broken step) / GAP (state what is missing and whether it looks patchable) / SURVIVES (state the weakest point anyway), plus expansions of the three least-obvious steps, plus anything you would require before publication.

## Task 3 — Statement-interface equivalence

`review_queue/external-candidate-B/interface-B.lean.txt` is the Lean statement interface of another formalization of this problem. Verify, and record in `verification/interface-equivalence.md`:
(a) which upstream source it pins (look for a formal-conjectures reference/commit/SHA inside) versus the upstream source your F1 fidelity proof targets — confirm both formalize the SAME `erdos_617` statement;
(b) that its final statement shapes (`UpstreamStatementR5` / `NoBalancedFiveColoring`) are mathematically equivalent to your `Main` / `erdos_617_r5_upstream` shape.
Then, inside lean617, transcribe the external final statement verbatim as a local definition and prove it iff `Main`, sorry-free; commit as `Lean617/InterfaceCross.lean`. If the two interfaces are NOT equivalent, that is a five-alarm finding — document the exact discrepancy and stop the round for the human collaborator.
