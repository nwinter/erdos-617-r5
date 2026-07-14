# external-cert-replay logs (ROUND-2026-07-14 Task B)

Raw artifacts backing `../external-cert-replay.md`. All verdicts here were
produced by tooling authored for this task plus `cadical`/`kissat` on PATH; the
bundle's own checkers were never used for a verdict.

## Scripts (as run)
- `inventory.py` — SHA-256 of all 222 bundle files, manifest/origin cross-checks, RAT scan.
- `replay_all.py` — 7 signatures + 58 orbits: regenerate full CNF (hash vs origin),
  independent origin-map reconstruction + injectivity, our-checker LRAT replay, kissat.
- `unified_replay.py` — the 66th (unified) certificate, same treatment.
- `control_and_sample.py` — cap-66 and cap-12 perturbation controls (expect SAT) with
  our own graph rescore, plus a cadical fresh-solve of 8 full formulas.
- `encoding_audit.py` — 55-check §9/§10 encoding-semantics audit.

The checker itself is `tools/lrat_check_independent.py` (self-test
`tools/lrat_check_selftest.py`).

Note: scripts read the bundle from its fixed repo path but write scratch outputs to
an absolute scratchpad path (where they were executed). A successor rerunning them
should regenerate the large full CNFs first (they are not committed — only hashes
are) and adjust the output paths. The unified full CNF (~15 MB) must be regenerated
via `defect_lemma.py --output <path>` before `unified_replay.py`.

## Result JSON / logs
- `inventory_report.json` — every file hash + 215 cross-checks (1 benign: unified
  origin omits a `compact_lrat_sha256` field; its compact-CNF hash matches).
- `replay_66.json` — per-certificate results for the 65 sig/orbit certs.
- `unified_result.json` — the unified certificate result.
- `controls_sample.json` — control SAT verdicts + rescores + cadical full sample.
- `*.log` — captured stdout (replay, unified regen/replay, encoding audit, orbit checks).

Headline: 66/66 certificates verify (hash = origin, our checker → UNSAT, kissat →
UNSAT, origin reconstructs + injective); 8/8 sampled full formulas cadical-UNSAT;
both controls SAT with matching rescores; encoding audit 55/55, zero divergence.
