# Independent replay of external candidate B's certificate set

**Round:** ROUND-2026-07-14, Task B. **Date:** 2026-07-14.
**Closes:** requirement 5 of `review_queue/external-candidate-B/review-by-team-A.md`
("Independent certificate replay ... the one part of the trust chain nobody in
this round examined").

## Verdict

**The candidate's SAT certificate set is independently sound.** Every one of the
66 committed LRAT proofs replays to the empty clause under a checker written from
scratch for this task; every compact CNF re-solves UNSAT under a second solver
(kissat) we did not use to produce the proofs; every full formula regenerates
**byte-for-byte** from the bundle's `encode.py`/`defect_lemma.py` and matches the
SHA-256 recorded in its origin map; every compact→full origin map reconstructs
exactly and uses an **injective** variable renaming; both perturbation controls
flip to SAT with independently-recomputed scores matching the prose; and the
encoding faithfully implements the §9/§10 semantics on all 55 audited points with
**zero divergence**.

Scope note (per CLAUDE.md rule 6): this certifies the two *machine-checked*
lemmas of §9 (seven-signature) and §10 (three-K₃ defect) as genuine UNSAT facts
about the exact formulas the prose describes. It does **not** re-verify the human
mathematical chain §2–§8 (that was Reviewer α/β's job) and promotes nothing to a
"proof complete" claim. It removes the last "treated as given" black box.

### Trust boundary

No checker, solver verdict, or reconstruction routine from the bundle was used
for any verdict. The bundle's `lrat_core.py`, `check_lrat` (absent), and the
`certify_*.py` drivers were **read** for semantics and invocation only. Every
verdict came from: `tools/lrat_check_independent.py` (authored here),
`cadical 3.0.0` / `kissat 4.0.4` on PATH, and our own regeneration + origin/score
recomputation code. The bundle's `encode.py` and `defect_lemma.py` were *run* to
regenerate CNFs (the object under audit), then every clause they emit was checked
against an independent reconstruction of the prose.

## 1. Inventory and hashes

- 222 files under `cert-bundle/`, all SHA-256'd (`inventory_report.json`).
- **Manifest hash matches the record.** `full_p25_manifest.json` hashes to
  `028eefead2cb883ffd3f47e64ae5a3a005f3442417c9178f4b010c4e63626a75`, exactly the
  value candidate-proof §9 records. (Their caveat about timing-field nondeterminism
  concerns *newly generated* manifests; the committed file is stable and matches.)
- All committed compact CNF/LRAT hashes match both the manifest entries and the
  hashes recorded inside each `*.origin.json` (215 cross-checks, see below).
- Control/orbit-audit hashes recorded inside the manifests match the committed
  `full_p25_budget66_control.json`, `cap12_control.json`, `mask_orbits.json`.
- **No RAT steps** in any of the 66 LRAT files (all hints positive) — so a strict
  RUP-with-hints checker is complete for this bundle. (Scanned independently.)
- One benign gap: `p25_defect_unified/.../unified_unsym.origin.json` omits a
  `compact_lrat_sha256` field (its compact-CNF hash *is* present and matches). We
  replay that LRAT anyway and hash it ourselves, which is strictly stronger.

## 2. Independent LRAT checker

`tools/lrat_check_independent.py` (+ `tools/lrat_check_selftest.py`), ~170 lines,
no dependencies. Strict RUP-with-hints: for each addition it assigns the negation
of the new clause and walks the listed positive hints in order; each hint must be
unit under the running assignment (else reject: "not unit" / "already satisfied"),
and the chain must reach a conflict; deletions are tracked and a deleted/unknown
hint is rejected; clause ids must be fresh and monotone; the proof is accepted
only if the empty clause is derived. Negative (RAT) hints are rejected outright.

**Self-test** (`python3 tools/lrat_check_selftest.py` → `SELFTEST PASSED`):
(a) accepts a genuine `cadical --plain --lrat` proof of a 10-variable UNSAT
formula (pigeonhole PHP(5 pigeons, 2 holes)); rejects the same proof after
(b1) one hint removed, (b2) one clause literal flipped, (b3) the empty-clause
line deleted. Deletion bookkeeping is additionally exercised by the real bundle
proofs (4,268 deletions across the signature/orbit certs; the 38 MB unified proof
has 0 deletions and 144,704 additions).

## 3–5. Replay, origin audit, fault-diversity re-solve

For all 66 certificates: regenerated the full CNF via the bundle encoder →
SHA-256 vs origin; parsed it with our own reader; reconstructed each compact
clause from `selected_original_clause_ids` + `new_to_old_variable` and checked it
equals the recorded full clause; checked the renaming is injective and in range;
replayed the compact LRAT with our checker; re-solved the compact CNF with kissat.

| certificate class | n | full-CNF hash = origin | our checker → UNSAT | kissat compact → UNSAT | origin reconstructs + injective | cadical full-formula (sample) → UNSAT |
|---|---|---|---|---|---|---|
| §9 signatures        | 7  | 7/7  | 7/7  | 7/7  | 7/7  | 2/2 (`5`, `2222_23444`) |
| §10 defect orbits    | 58 | 58/58| 58/58| 58/58| 58/58| 6/6 (masks 0,4,10,20,30,50) |
| §10 unified (unsym)  | 1  | 1/1  | 1/1  | 1/1  | 1/1  | (subsumed by orbits) |
| **total**            | 66 | **66/66** | **66/66** | **66/66** | **66/66** | **8/8** |

- **Reproducibility.** Full CNFs are deterministic: the 26-vertex signature
  formulas, the 18-vertex orbit formulas, and the **746,314-clause / 294,008-var**
  unified formula all regenerate to the exact SHA-256 recorded in their origins,
  on Python 3.14.3. Our seven-signature aggregate (11,675 compact clauses, 17,054
  additions, largest 3,424) reproduces FULL_P25_REPORT's stated figures exactly.
- **Injectivity (review requirement 2).** For every certificate the compact→full
  renaming `new_to_old_variable` has all-distinct entries, so compact-UNSAT ⇒
  full-UNSAT is valid, not merely "each clause is reconstructable". Checked
  computationally on all 66, including the unified's 13,473-variable map.
- **Trivial orbits are sound.** 37 of 58 orbit cores are ≤4 clauses: for those,
  `defect_lemma.py`'s `remaining < 0` branch emits a `(v),(¬v)` contradiction pair.
  We independently confirmed a **perfect correspondence**: those are exactly the 37
  orbits whose fixed structure (anchored K₄s + masks + completion edges) already
  forces ≥12 edges into some 18-core six-set — a genuine violation of the ≤11 gap
  window. The 21 non-trivial orbits all have max fixed six-set = 11, so their UNSAT
  rests on the real proof. The contradiction branch never fires spuriously.

## 6. Perturbation controls (vacuousness guards)

| control | perturbation | cadical | our independent rescore of the committed model |
|---|---|---|---|
| `full_p25_budget66_control` | global edge cap 65 → 66 on `2222_23444` | **SAT** | e(G)=66, P=25, e(W)=41, min six-set=1, max anchored=11, min exchange margin=0, masks 01/04/01/01, max six=13 — matches §9 exactly |
| `cap12_control` | six-set cap 11 → 12 on defect orbit 4 | **SAT** | min=1, max=12, l=0, b=10, c=2, l+b+2c=14 — matches §10 exactly |

Both base formulas therefore are non-vacuously UNSAT: adding one unit of budget /
one unit of cap makes them satisfiable, and the witness graphs have precisely the
structure the prose reports (including the dense unanchored six-set of 13 edges
that demonstrates the relaxation genuinely omits unanchored caps). Rescoring used
our own graph scorer, not the bundle's `score()`/`validate_primary_graph()`.

## 7. Encoding-semantics audit — does the CNF say what §9/§10 claim?

`encoding_audit.py`: 55 independent checks, **0 divergence**. For each of the 8
signatures and the defect encoder we reconstructed the intended clauses from the
prose and/or truth-tabled the emitted clauses against their stated meaning.

**Primitives (exhaustive truth-table with our own DPLL):**
- `totalizer_at_most(lits, b)` is model-extendable iff `#true(lits) ≤ b` (n ≤ 6) —
  confirms the claimed safe model-extension property (assign each output by the
  number of true inputs below it).
- `direct_leq(L, R)` is satisfiable iff `ΣL ≤ ΣR` (exhaustive).
- A repeated literal is counted twice (`at_most([x,x],1)` SAT iff x false) —
  confirms the "X–X literal counted twice / repeated weighted literals" clause.

**§9 seven-signature encoder (all 8 rows, incl. the omitted `2222_33344`):**
- Fixed structure = Q–Q nonedges + each ordinary vertex's unique Q-edge and four
  Q-nonedges + within-group cliques (independent set-equality). ✓
- `exception_Q_degree` truth-tables to "exactly d of the 5 Q-edges" per exception. ✓
- `deficient_hit` = OR(edges to deficient indices) for degree-≤4 exceptions **only**
  (absent for the degree-5 exception). ✓
- `nonempty_six` = OR(variable edges) over exactly the six-sets with no fixed edge. ✓
- Upper caps (≤11) exist **only** on clique-anchored six-sets (105 / 315 / … per
  row); unanchored six-sets get no cap — the deliberate relaxation. ✓
- Residual W-edge budget = 65 − 25 − (internal clique edges), over the W–W
  variables. ✓

**§10 defect encoder (orbit 4 + unified):**
- Fixed = three anchored K₄s + exact per-orbit masks + mixed-mask completion edges
  (x∼q_deficient ∧ x∼q_large ⇒ x complete to that deficient S_i). ✓
- The 1..11 window is imposed on all C(18,6)=18,564 core six-sets. ✓
- Each X–X edge occurs exactly twice in the weighted `l+b+2c` list (coefficient 2
  on c). ✓
- Completion clauses equal the Horn implications for every (deficient i, large,
  w∈S_i). ✓
- **58 orbits independently reproduced** two ways (all 6,561 labelled mask
  assignments, and the 495 multisets, both canonicalize to 58 under S₃×S₂×S₄) —
  the eighth-signature case split is complete.

Every emitted clause is a valid *necessary* condition for a real gap graph of the
signature, and omitted constraints only weaken the formula: UNSAT is in the safe
direction, as the prose claims. No "harmless" divergence was found either.

## Missing from the bundle (reported, not improvised)

None load-bearing for this replay; listed for the human to fetch if a full
end-to-end rerun of the candidate's own documented commands is wanted:
- `check_lrat.py` and `tools/run_capped.py` — imported by the `certify_*.py`
  drivers and named in every "resource-capped" command in §9/§10. Not in the
  bundle; not needed here (we ran the encoders directly and used our own checker).
- `Erdos617/P25Certificates/Pattern*.lean` and `P25CertificatesAxiomAudit.lean` —
  the durable Mathlib `lrat_proof` replay files named in §9/§10. Only
  `MathlibReplay.lean` (the §10 defect one) is in the bundle. The Lean route is a
  separate trust path from the LRAT replay done here.
- `data/candidates/affine_k25_r5.json` — the §11 N(5)=25 lower-bound witness; not
  part of this SAT bundle and already tracked as finding A1/item 3 of the team-A
  review (the equivalent `ag25_merge_0_inf.json` referee-passes in this repo).

## How to reproduce

```
# checker + self-test
python3 tools/lrat_check_selftest.py

# from verification/external-cert-replay-logs/ (paths inside point at the bundle)
python3 inventory.py            # hashes + manifest cross-checks + RAT scan
python3 replay_all.py           # 7 sigs + 58 orbits: regen/hash/origin/replay/kissat
python3 unified_replay.py       # 66th cert (needs unified full CNF regenerated first)
python3 control_and_sample.py   # cap66 & cap12 controls + cadical full-formula sample
python3 encoding_audit.py       # §9/§10 encoding-semantics audit (55 checks)
```

Raw outputs: `verification/external-cert-replay-logs/*.json` and `*.log`.
Large regenerated CNFs (incl. the 15 MB unified full formula) are **not** committed;
only their hashes are, in the JSON logs.
