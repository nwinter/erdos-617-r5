# Cloud cube-and-conquer kit (for lemma certification)

Goal: DRAT-certified UNSAT for the machine lemmas of review_queue/extension-chain.md,
starting with [MH″] = `data/sat/r5_n25_h4b.cnf` (balanced K_25 + 4-set hitter; a sound
single symmetry cut included — see tools/probe_h4b.py for the soundness argument).

## Pipeline (validated locally before spending money)

1. **Canary first** (~$10, single box): `data/sat/chain_r4_mh_kissat.cnf` is the r=4
   analogue (480 vars) that stalled 68 CPU-hours un-split. Cube it and measure:
       python3 tools/cloud/make_cubes.py data/sat/chain_r4_mh_kissat.cnf /tmp/c4 \
           --colour-edges 0 1 2 3          # 4-colour instance: adapt (r=4 -> vars k*4+c+1)!
       # NB the r=4 instance is one-hot with r=4: --colour-edges assumes r=5 var layout;
       # for the canary use make_cubes with --icnf from march_cu, or edit the stride.
       bash tools/cloud/run_cubes.sh /tmp/c4 16
   Success criterion: total CPU across cubes << 68h (expect orders of magnitude if this
   family cubes well). This also validates kissat+drat-trim end-to-end.
2. **march_cu** (recommended over naive splitting): build from
   https://github.com/marijnheule/CnC (march_cu/). Generate ~10^3..10^5 cubes:
       march_cu BASE.cnf -o cubes.icnf -d 20
       python3 tools/cloud/make_cubes.py BASE.cnf CUBEDIR --icnf cubes.icnf
3. **Spot fleet**: any Linux x86 instances (c7a/c6i family, RAM >= 4 GB/worker).
   Sync CUBEDIR to S3; each worker: aws s3 sync down, `run_cubes.sh CUBEDIR $(nproc)`,
   s3 sync up on a cron/loop. The locks/verdicts protocol makes concurrent workers and
   preemptions safe (idempotent; a preempted cube is simply re-solved).
   Estimated cost at ~$0.03/vCPU-hr spot: 100 CPU-days ~= $75; 1000 CPU-days ~= $750.
   Kill criterion: if the canary scaling extrapolates above your budget, stop.
4. **Certificate**: keep (KEEP_PROOFS=1) or regenerate proofs for the final artifact.
   The claim "all 5^k / march cubes cover the space" is by construction (disjoint
   exhaustive assignments); record MANIFEST.tsv + base CNF hash + solver/checker
   versions alongside the verdicts.

## Soundness notes

- A SAT verdict on any cube = a model of the BASE instance (units only restrict).
  Decode with tools/sat_decode.py + the instance's .map.json, verify with
  tools/verify.py (referee) and the h4 condition before believing it.
- UNSAT of every cube in an exhaustive disjoint cube set = UNSAT of base. march_cu
  cube sets are exhaustive by construction; --colour-edges sets are exhaustive because
  each chosen edge has exactly one colour in any model (one-hot ALO clauses).
- The base instance's own WLOG/symmetry-cut soundness is documented in
  tools/probe_h4b.py and was adversarially reviewed (review_queue/extension-chain.md).

## After [MH″]: [MM]

`tools/monolith.py mm 25 60 mm_full.cnf` builds the full-cap [MM] instance (80.8M
clauses, ~4.3 GB): cube it the same way (memory: one worker per ~24 GB for this one),
or first re-pose [MM] with colouring context if its pure-graph form turns out SAT.
