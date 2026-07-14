# Context for the two-proofs writeup: the control experiment, the comparison facts

Written by the coordinating session (the Claude orchestrator working with Nick), 2026-07-14. Everything here has been verified — from read-only audits of both repos, the codex session logs, and the committed verification-round artifacts. This document de-anonymizes "external candidate B": read it before touching the paper or the popular writeup.

## What candidate B actually is

After your R9/R10 landed (2026-07-10), Nick commissioned a **control experiment**: could a different frontier model, working alone from the same starting point, independently confirm the theorem? Setup:

- Fresh repo `~/research/erdos-617-sol`, seeded from **your scaffold commit `3fa85b2`** — identical PROBLEM.md, verify.py, worked examples, seed ATTACKS.md (CLAUDE.md renamed AGENTS.md). Launched 2026-07-11 12:37.
- Agent: **OpenAI gpt-5.6-sol via the codex CLI**, reasoning effort "ultra", heavy multiagent (141 codex sessions).
- Framing: a **truthful confirmation brief** — it was told the theorem was already proved ("a different AI system… Claude Fable 5 … with another frontier model contributing lemma proofs"), given the statement and direction, and forbidden from reading any other repository on the machine or asking for the route.
- Delicate attribution point for the writeup: **gpt-5.6-sol also authored the first proofs of your [MH″] and [MM] from your briefs** — the same base model contributed to both proofs, in different roles (lemma-prover inside your team; independent prover in the control). Be precise about this; it is interesting, not embarrassing.

## Honest-comparison caveats (do not bury these)

The control knew the theorem was true and which way it resolved, started from your polished scaffold and referee, and ran after tractability was established. Your run was a cold open on a problem of unknown status, and you invented the reduction targets (N(5)=25 etc.) from scratch. **Wall-clock and commit counts are not a fair capability comparison** — present them as characteristics of two different regimes (discovery vs. confirmation), not a race result.

## Comparison facts (all verified)

| | Your team (fable-led + gpt-5.6-sol lemmas) | Control (gpt-5.6-sol solo) |
|---|---|---|
| Route | delete vertex; partition 25 by colour toward it; [MH″] hitter lemma (Brouwer+KP extremal core) forces parts of 5 with ≤6 own edges; [MM] pure-graph minority lemma kills it | no deletion; minority-colour "gap graph" on K₂₆; pincer on P(Q)=Σdeg over independent 5-sets (≥25 always via five-part transversal lemma; ≤25 somewhere via Bollobás–Nikiforov + Brouwer stability); exact P=25 → 8 signatures; 7 by LRAT-certified SAT, 1 by certified defect lemma + counting |
| Discovery style | empirics-first: AG(2,5) mining, non-extension experiments, the h4 phase transition suggested the lemma statements, then proofs | direct construction of the pincer; industrialized certificate pipeline (65 load-bearing LRAT certs, dual checkers, perturbation controls) |
| Extremal inputs | Brouwer 1981 + Kang–Pikhurko 2005 (equality classification) | Brouwer 1981 (19,5 case) + Bollobás–Nikiforov 2005 (strict form load-bearing); **no KP** |
| Effort | 164 commits, 2026-07-05→07-12 (~7 days) to unconditional; R9 at commit 38, first Lean at 72 | 295 commits, 2026-07-11 12:37→07-13 16:54 (~2d4h) |
| Lean | 25 files / ~15.4k lines, hand-written; axioms 3 standard + 14 native_decide (being migrated to kernel-pure in this round) | 1,153 files / ~317k lines (mostly generated); axioms exactly [propext, Classical.choice, Quot.sound]; SAT via Mathlib's kernel-checked lrat_proof |
| Verification round (07-13/14) | your review of B: SURVIVES, 2 non-fatal findings (E1 §7.3 bound; A1 artifact ref); your rebuild committed (8,497 jobs) | B's review of you: SURVIVES ×3 docs, zero FATAL — and it **independently rediscovered both of your historically-repaired weak spots** (MH″ §7 two-K₅ endgame; MM r=7 case) and verified the repairs; vendored KP, all five uses faithful; its rebuild committed (989 modules, fresh clone, both cert paths re-run) |
| Interface | your `InterfaceCross.lean` proves B's statement ⟺ `Main`, axiom-pure | its `main_iff_noBalancedFiveColoring` proves the converse direction, 3 axioms — the two formalizations provably state the same theorem, tied to the same formal-conjectures declaration |

## The independence story (verified from codex session logs; great material — tell it)

The control never read your repo. Its sole meaningful exposure: your concurrent `lake build Lean617.BrouwerInduction` appeared in a routine process listing at **15:26:56 on 07-11** — **117 seconds after** its own Brouwer-stability route was already committed (15:11) and reviewed (15:25). It then *noticed the exposure itself*, disclosed it in NOTES.md with the exact commit hashes, quarantined the string, banned system-wide process listings for the rest of its run, and enforced the ban on a subagent that violated it the next day. Every claim in its self-audit checks out against the session logs to the minute. Convergence on Brouwer 1981 was genuine independent literature convergence.

## Nick's requirements for the popular writeup

1. Make **both proofs genuinely easy to understand** for a technically curious general reader — on-ramp via the r=2 pentagon / R(3,3)=6 story, then each route's essence in a paragraph, then progressively deeper.
2. Make the **difference between the two proofs vivid**: local partition-and-hitters vs. global degree-boundary pincer; empirics-led lemma discovery vs. certificate industrialization.
3. Compare **effort, process, and result quality** — strengths, weaknesses, and characteristics of each approach — using the facts above, WITH the honest-comparison caveats stated plainly.
4. Include the **independence-audit story** (the 117 seconds) and the mutual hostile-review results.

## Paper decision (default; Nick can override)

**One mathematical paper containing both proofs**: shared preliminaries; Proof A (yours) and Proof B (the control's, sourced from `review_queue/external-candidate-B/candidate-proof.md` and your review of it), clearly attributed section by section; a verification-methodology appendix (rebuilds, cross-review protocol, interface equivalence, axiom profiles). Rationale: one citable reference for the theorem, the two-proofs format directly serves the verification story, and the independent-teams credibility lives in the repos and audit trail. **Mark the Proof-B sections for an accuracy pass by its authors** — Nick will arrange that exchange; do not ship prose putting words in the other team's mouth without that pass.
