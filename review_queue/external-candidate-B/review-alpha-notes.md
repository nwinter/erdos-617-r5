# Adversarial review — external candidate B (`candidate-proof.md`)

Reviewer: alpha (fresh-eyes, internal-math-chain scope).
Date: 2026-07-14.
Target: `review_queue/external-candidate-B/candidate-proof.md` (901 lines).
Pinned defs cross-checked against `PROBLEM.md`.

STATUS: **COMPLETE. Verdict = SURVIVES** (no fatal error / no genuine math gap in the
internal chain; 2 non-fatal findings E1, A1; correctness reduces to the given §9/§10 machine
lemmas + literature, all out of scope). See FINAL VERDICT + one-line index at bottom.

Scope taken as GIVEN (per assignment; verified by the parallel literature/cert reviewer):
- Literature theorems faithfully stated & conditioned (Bollobás–Nikiforov strict; Brouwer complement form; Turán values t_4(26)=253, t_5(26)=270, L_5 values, T(19,5)=27).
- §9 encodings are safe relaxations; 58-orbit count right; 8 signature degree-sums all =25.
- Certified seven-signature lemma (§9) and three-K_3 defect lemma (§10) exactly as stated.
- tools/verify.py verdicts.

Working stance: assume ≥1 fatal gap; hunt the weakest inference; recompute every number.

---

## Running verdict scratch (updated as I go)

§2 ✓ · §3 ✓ · §4 ✓ · §5 ✓ · §6 ✓ · §7+7.1/7.2/7.3 ✓(note E1) · §8 ✓ · §9 GIVEN ·
§10 ✓ · §11 ✓(note A1) · logic sweep ✓ ⇒ SURVIVES.

---

## §2 — minority-colour graph reduction (lines 52–69)

VERDICT: CORRECT.

- 325 edges / 5 colours ⇒ minority colour ≤ 65. ✓ (325/5 = 65 exactly.)
- ≥1 G-edge per 6-set: balanced ⇒ 6-set sees colour G ⇒ ≥1 edge. ✓
- ≤11 G-edges per 6-set: 6-set has C(6,2)=15 edges; if ≥12 are G, ≤3 remain for
  the other 4 colours ⇒ pigeonhole one absent ⇒ not balanced. ✓ (15−12=3<4.)
- Implication direction: "balanced 5-col of K_26 ⇒ gap graph exists", so
  "no gap graph ⇒ no balanced". Contrapositive is the right one. ✓
- No off-by-one: reduction is entirely on 26 vertices. No degenerate-class hole
  (empty colour class ⇒ some 6-set misses it ⇒ not balanced, so all 5 used).
- P(Q)=Σ_{q∈Q} d(q)=e(Q,V−Q) legit because Q independent (no internal edges). ✓

## §3 — α=5 and first boundary bounds (lines 71–102)

VERDICT: CORRECT.

- α≤5 from gap lower end (no independent 6-set). ✓
- α=5: α≤4 ⇒ complement K_5-free ⇒ e(H)≤t_4(26)=253 ⇒ e(G)≥325−253=72>65 ⊥. ✓
- P(Q)≥21: each of 21 W-vertices has ≥1 Q-neighbour (else independent 6-set). ✓
- (3.1) P(Q)≥22: equality P=21 ⇒ each w unique Q-neighbour ⇒ R_i partition;
  R_i clique via six-set {y,y'}∪(Q−q_i) (indep, size 6); |R_i|≤4 via
  {q_i}∪(5 members)=K_6, 15 edges >11; 5·4=20<21=|W| ⊥. Every six-set used is
  legitimate. ✓
- Upper: α(G[W])≤5 ⇒ e(W)≥ min-edge 5-clique cover of 21 = (5,4,4,4,4) =
  10+4·6=34; P(Q)=e(G)−e(W)≤65−34=31. ✓

Both sections airtight. Moving to the combinatorial eliminations §4–§6.

---

## §4 — Elimination of P=22 (lines 104–174)

VERDICT: CORRECT (all four lemma cases verified numerically + by hand).

Setup: P=22 ⇒ excess 1 ⇒ one exceptional x (Q-deg 2) + 20 ordinary (deg 1).
20 ordinary in 5 groups ≤4 ⇒ all five =K_4. ✓
- Pair graph R_i,R_j is a matching: six-set {q_i}∪R_i∪{y} has 10 fixed K_5 edges,
  cap 11 ⇒ y has ≤1 nb in R_i (y⊥q_i since y's Q-nb is q_j). Reverse ⇒ matching. ✓
- x meets q_i ⇒ x⊥R_i (10+1=11 cap). x⊥q_i ⇒ ≤1 nb (10+≤1). x has Q-deg 2, so
  ≤3 groups get a possible nb; a := #groups met, 0≤a≤3. ✓
- 5·K_4 = 30 internal W-edges; e(W)≤65−22=43 ⇒ non-internal ≤13; a are x-edges;
  delete x's ≤1 nb per met group ⇒ a parts size 3, 5−a size 4, cross ≤13−a. ✓
- Plan: independent transversal T of reduced parts ⇒ T∪{x} independent 6-set ⊥. ✓

FIVE-PART LEMMA (probabilistic + structural), verified case by case:
Transversal picks 1/part (parts are cliques ⇒ only cross-edges can appear).
Random uniform transversal; edge between size-s,size-t parts selected w.p. 1/(st).
E[selected] = Σ_e 1/(s_e t_e). E<1 ⇒ independent transversal.
- a=0: all 16-prob, ≤13 edges ⇒ E≤13/16<1. ✓
- a=1: max-prob 1/12 (small-large), ≤12 edges ⇒ E≤12/12=1. Equality forces exactly
  12 small-large, 0 large-large (11/12+k/16=1 has no integer k). Then no large-large
  edges; pick any small vertex s_0 (≤1 nb per large part via matching ⇒ ≥3 nonnbs each),
  choose nonnb per large part; large parts mutually nonadjacent ⇒ indep. ✓
- a=2: two small (A,B), z=|A-B edges|≤3. E ≤ z/9+(11−z)/12 = 11/12+z/36 ≤1 (z≤3).
  [VERIFIED numerically: matches, ≤1.] Equality⇒z=3 (perfect A-B matching), 8 small-large,
  0 large-large. Pick a∈A,b∈B nonadjacent (a has 1 B-nb ⇒ 2 nonnbs); each large part
  loses ≤2 (1 from a, 1 from b) ⇒ ≥2 left; no LL edges ⇒ indep. ✓
- a=3: three small A,B,C, k=small-small edges, ≤10 total cross.
  * k≤5: E ≤ (k+30)/36 <1 [4k/36 for small-small + 3(10−k)/36 for the rest]. ✓ VERIFIED.
  * 6≤k≤9: EXACT incl-excl over the 27 small transversals (see derivation below):
    U = 27 − 3k + w − t, w=#deg-2 vtcs, t=#triangles. w≥2k−9 (deg sum n_1+2n_2=2k over
    9 vtcs, max deg 2 ⇒ 2k≤9+w). Triangles vertex-DISJOINT (shared vtx ⇒ 2 nbs in one
    part, violates matching) ⇒ 3t≤w. So U ≥ 27−3k+(2/3)w ≥ 21−5k/3 ⇒ U≥11,10,8,6
    for k=6,7,8,9. Each indep small transversal has 16 large-extensions; each remaining
    edge (≤10−k) kills ≤36 full transversals; 16U > 36(10−k): 176>144,160>108,128>72,
    96>36. [ALL VERIFIED numerically.] ⇒ full independent transversal exists. ✓

EXPANDED STEP #1 — the U=27−3k+w−t inclusion-exclusion (a=3, candidate line 156):
On A∪B∪C (3 parts ×3 = 9 vtcs), edges only cross-part, each pair a matching ⇒ max deg 2.
A "small transversal" = 1 vtx/part, 27 total. Independent ones counted by incl-excl over
the k bad events "edge e is selected":
 • |S|=0: 27.
 • |S|=1 (single edge e=uv, u∈P,v∈P'): transversals with both = 1·1·3 = 3 (free third
   part). Σ = 3k.
 • |S|=2: two edges co-selectable ⇒ share a vertex (3 vtcs can't hold 2 disjoint edges);
   a deg-2 vtx a with nbs b,c gives edge-pair {ab,ac}, co-selected by exactly {a,b,c}
   (forced). #such pairs = #cherries = Σ C(deg,2) = w (deg≤2). Σ = w.
 • |S|=3: all of ab,ac,bc ⇒ triangle, co-selected by {a,b,c} only. Σ = t.
 • |S|≥4: impossible (≤3 edges among 3 vtcs).
 U = 27 − 3k + w − t.  EXACT. Sign pattern +,−,+,− correct. ✓

Then T∪{x} independent 6-set contradicts α=5. P=22 excluded. AIRTIGHT.

---

## §5 — Elimination of P=23 (lines 176–204)

VERDICT: CORRECT.

Excess 2 ⇒ two patterns: [3] (one deg-3) or [2,2] (two deg-2). Only integer
partitions of 2. ✓
- 5.1 [deg 3]: 20 ordinary ⇒ five K_4. x meets 3 indices I, x⊥R_i (i∈I). 3 groups
  R_i (i∈I) pairwise matchings ⇒ E[selected] ≤ 3·4/16 = 3/4 <1 ⇒ indep transversal
  {v_i}. {v_i}_{i∈I} ∪ {x} ∪ (Q−N_Q(x), 2 vtcs) = indep 6-set: x⊥v_i (x⊥R_i),
  v_i⊥q_j (j∉I, v_i's only Q-nb is q_i), x⊥q_j (j∉N_Q(x)). ✓
- 5.2 [two deg-2]: 19 ordinary ⇒ sizes 3,4,4,4,4, R_0 the 3-set.
  * every exceptional z meets q_0: else both nbs large, z⊥ both, pick nonedge (a,b)
    in R_i-R_j matching (≥12 nonedges), {z,a,b}∪(Q−{q_i,q_j}) indep 6-set. ✓
  * z (meets q_0,q_i) complete to R_0: if z misses s∈R_0, then s has ≤1 nb in R_i
    (fixed K_5 {q_i}∪R_i, cap), pick v∈R_i with sv nonedge, {z,s,v}∪(Q−{q_0,q_i})
    indep 6-set. ✓
  * both exceptionals complete to R_0 ⇒ six-set {z_1,z_2}∪{q_0}∪R_0:
    {q_0}∪R_0 = K_4 (6 edges), z_1→{q_0}∪R_0 = 4 edges, z_2 = 4 edges, all distinct
    ⇒ ≥14 > 11 cap ⊥. ✓ [6+4+4=14 recomputed, edges disjoint.]
P=23 excluded. AIRTIGHT.

---

## §6 — Elimination of P=24 (lines 206–303)

VERDICT: CORRECT (most intricate human section; all subcases verified).

Two lemmas (both proven by greedy transversal + independent-6-set contradiction):
- Large-neighbour lemma: exc x (Q-deg d≤4), all nb-groups size 4 ⇒ x⊥ all of them;
  greedy transversal, jth choice forbids ≤ j−1 ≤3 in a size-4 group ⇒ ≥1 free;
  {v_i}∪{x}∪(Q−N_Q(x)) indep 6-set. ⇒ every deg-≤4 exc meets a DEFICIENT group. ✓
- Completion lemma: exactly one deficient nb-group R_i, rest large ⇒ x complete to R_i.
  Else miss u∈R_i, greedy on large groups avoiding u too, last step ≤3 forbidden. ✓

Patterns of excess 3: [4],[3,2],[2,2,2].
- [4]: five K_4 ⇒ deg-4 exc all-large ⇒ large-nbr lemma ⊥. ✓
- [3,2]: sizes 3,4,4,4,4; both exc meet q_0 (only deficient) & complete to R_0
  (completion) ⇒ {2 exc}∪{q_0}∪R_0 has 6+4+4=14>11. ✓ [VERIFIED 14.]
- [2,2,2]: sizes 2,4,4,4,4 OR 3,3,4,4,4.
  * {2,4444}: all 3 exc complete to size-2 R_i; {q_i}∪R_i=K_3 (3), +3·3 = 12>11. ✓
  * {3,3,4,4,4}: THE HARD CASE. A=R_0,B=R_1. Types 0L/1L/01. ≤1 each exclusive type
    (two same-exclusive ⇒ 6+4+4=14 around {q_0}∪A). Multisets {0L,1L,01},{0L,01,01},
    {01,01,01}.
    Four rules verified: (1) missing rectangle [z⊥a,z⊥b ⇒ ab∈E via {z,a,b,q2,q3,q4}];
    (2) pair cap [u,v meet q_0: 6(K4)+2+d_A(u)+d_A(v)+[uv]≤11 ⇒ ≤3, VERIFIED];
    (3) cross cap [b,b'∈B ⊥q_0: 6(K4)+[bb']=1+d_A(b)+d_A(b')≤11 ⇒ ≤4, VERIFIED ⇒ no
    K_{3,2}/K_{2,3}]; (4) nonadj-pair partition [N_A(u),N_A(v) cover A, pair cap ⇒
    disjoint sum 3 ⇒ partition].

    - {0L,1L,01}: pair caps force shared z⊥A (d_A(0L)=3) and z⊥B ⇒ missing rectangle
      ⇒ H=K_{3,3} ⇒ A∪B=K_6=15>11. ✓
    - {0L,01,01}: both shared ⊥A; columns outside N_B(z_1)∩N_B(z_2) complete to A;
      cross cap ⇒ ≤1 complete column ⇒ |∩|≥2 ⇒ d_B(z_1)+d_B(z_2)≥4 > 3 pair cap. ✓
    - {01,01,01}: X={x,y,z}, G[X] nonempty (else X∪{q2,q3,q4} indep). Three subcases:
       · one edge xy: partition on xz,yz ⇒ N_A(x)=N_A(y)=A∖N_A(z), deg a; edge pair cap
         ⇒ a≤1; a=0 ⇒ 2 complete columns = forbidden K_{3,2} ⇒ a=b=1; missing rect for
         z ⇒ a_0b_0∈E; {q_0,q_1,x,y,a_0,b_0}: 6+4+2=12>11. ✓ [VERIFIED 12, 12 distinct.]
       · path x−y−z: nonedge xz ⇒ d_A(x)+d_A(z)=3; two edge pair caps sum ⇒ 3+2d_A(y)≤4
         ⇒ d_A(y)=0, sym d_B(y)=0; missing rect ⇒ H=K_{3,3} ⇒ K_6=15>11. ✓
       · triangle: EXPANDED STEP #2 below.
    Every case impossible ⇒ (6.1) P(Q)≥25 for every independent 5-set. ✓

## §7 — Stability: some 5-set has P≤25 (lines 305–502)

VERDICT (through 7.2 + enumerations): CORRECT. (7.3 subcases below.)

Setup: H=complement, K_6-free, e(H)≥260.
- REGULAR branch: 260≤e(H)≤270, e(H)≡0 mod 13 ⇒ e(H)=260 (273=13·21>270). H 20-reg,
  G 5-reg ⇒ every indep 5-set has P=5·5=25 ⇒ (7.6) holds. ✓ [VERIFIED 13·20=260,13·21=273.]
- NONREGULAR: e(H)≥260>253=t_4(26). BN(r=4,strict) ⇒ 4-clique A in H, deg-sum >8·260/26=80
  ⇒ ≥81. A indep in G, σ=100−Σd_H(a)≤19. ✓ [VERIFIED.]
- (7.1) c≥22−σ: KEY RECONCILIATION (prompt-flagged). e_H(A,outside)=Σd_H(a)−12 (A is
  H-K_4, 6 internal edges doubled) = 88−σ; ≤ 3·22+c ⇒ c≥88−σ−66=22−σ. Candidate's
  "Σd_H(a)−3·26" = (100−σ)−78 = 22−σ, and 78=12+66=3·26 COINCIDES. Candidate CORRECT;
  the naive "Σd_H−3·22=15" is wrong (ignores internal edges). ✓ [VERIFIED 88−σ.]
- C is G-clique (H-edge in C ⇒ H-K_6); c≤5 (G-clique ≤5 else K_6, 15>11); 17≤σ≤19. ✓
- D=V−A−C, |D|=22−c; every D-vtx meets A; all σ A-edges go to D; e(D)≥L_5(22−c). (7.2). ✓
- TABLE (all 6 rows REPRODUCED EXACTLY by script): P(A+x)=σ+(c−1)+⌊e(C,D)/c⌋,
  e(C,D)≤65−σ−C(c,2)−L_5(22−c). Only rows σ=19 (c=3,4,5) have maxP≥26. Under the
  "all P≥26" assumption ⇒ σ=19, every x∈C has d_G(x)≥7 (7.3). ✓ [L_5(17,18,19)=21,24,27
  VERIFIED.]
- Obs 1 (hitting sets of 5-clique-partition, one cross-edge exceptional case): DERIVED,
  correct — S hits every indep transversal iff S⊇ a whole part, OR (one cross-edge uv)
  S⊇B_i−{u} and B_j−{v} with B_i∖S={u},B_j∖S={v}. ✓
- Obs 2 (mask/colour): unique-colour D; nonadj same-colour u,v with M(u)∪M(v)≠C ⇒
  {u,v,x}∪(A−colour) indep 6-set; so an indep transversal with pairwise mask-unions ⊊C
  needs 5 distinct colours from 4 A-vtcs ⇒ impossible. DERIVED, correct. ✓

### 7.1 (c=5): equality ⇒ e(C,D)=15, e(D)=21, D=K4+K4+K3+K3+K3 (unique Turán min),
each x∈C has d_D(x)=3 (each≥3, Σ=15). N_D(x) hits every indep transversal (else 6-set)
⇒ =one K_3 part (obs1, size-3 hitting set ⊇ whole part). Two C-vtcs same K_3 + third:
{x1,x2,x3}triangle(3)+K_3(3)+x1→K_3(3)+x2→K_3(3)=12>11. 5 vtcs, 3 K_3 parts ⇒ pigeonhole
collision ⊥. ✓ [VERIFIED 12.]

### 7.2 (c=4): equality ⇒ e(C,D)=16, e(D)=24, D=K4·3+K3·2; each x∈C d_D(x)=4 ⊇ whole part.
Chosen parts distinct (repeat K4 ⇒ K6=15; repeat K3+third ⇒ 12). 19 A-edges/18 D-vtcs ⇒
one doubled vtx, 17 unique. Each part ≥2 low-mask (≤1) ordinary vtcs: chosen K4 all mask
{chooser} (fixed K5 {x}∪K4 + x' ⇒ d(x')=0); chosen K3 ≥2 chooser-singletons (≤1 spare
from other K3-chooser); unchosen part ≤2 spares ⇒ ≥2 low-mask. Pick low-mask ordinary
transversal (avoid doubled vtx) ⇒ pairwise mask-union ≤2<4 ⇒ obs2 needs 5 colours from 4
⊥. ✓ [Incidence budget: p+q=4 choosers, only K3-choosers have 1 spare each; consistent.]

### (7.4)/(7.5) enumerations — EXHAUSTIVE, VERIFIED BY SCRIPT:
(7.4): e(C,D)+e(D)≤43, e(D)∈[27,28], e(C,D)∈[15,16] ⇒ exactly (27,15),(27,16),(28,15). ✓
(7.5): D=5 cliques (Brouwer, e(D)≤28), parts of 19 size≤5, within=ΣC(s,2)∈{27,28}:
ONLY (4,4,4,4,3)+0cross [e=27], (4,4,4,4,3)+1cross [e=28], (5,4,4,3,3)+0cross [e=28].
(5,4,4,4,2)/(5,5,3,3,3)=29 excluded; (5,5,4,3,2)=30 excluded; size≥6 ⇒ K_6 excluded. ✓

### 7.3 (c=3): every D-vtx unique colour (19 edges/19 vtcs). e(C,D)=15, each d_D(x)=5.
VERDICT: CORRECT (minor exposition note E1 below).
Goal: indep transversal, all masks ≤1 ⇒ pairwise union ≤2 <3=c ⇒ obs2 ⊥.
- NO cross-edge (4,4,4,4,3): each N_D(x)⊇whole part (obs1). Chosen K4=chooser-singletons
  (fixed K5); chosen K3 has singleton (other 2 C-vtcs give ≤2 edges: 3+3+3=9,cap⇒≤2).
  Base 12 (3 K4) or 11 (2K4+K3); unchosen K4/K3 all-mask≥2 needs 8/6 > remainder ≤4/5 ⇒
  low-mask exists everywhere. Transversal ⇒ ⊥. ✓ [VERIFIED.]
- NO cross-edge (5,4,4,3,3): K5 unchooseable (chooser+K5=K6). chosen from {4,4,3,3};
  base 11 or 10; e(C,D)=15 (forced) ⇒ remainder ≤4 or 5 < 6 ⇒ low-mask everywhere. ✓
- ONE cross-edge (4,4,4,4,3), uv:
  * two K4's: excep hitting set size 6 > N_D size 5 ⇒ all whole parts; unchosen endpoint
    K4 has low-mask nonendpoint (3 nonendpts, all-≥2 needs 6 > rem); pick nonendpoints in
    endpoint parts ⇒ avoid cross-edge. ✓
  * K4–K3: excep set size 5 = N_D size; ≤1 C-vtx uses it (two users ⇒ 3+3+3+3=12>11);
    if none ⇒ whole-part arg; if one: K4-endpoint part has singleton (9,cap⇒≤2 further),
    K3-endpoint part has low-mask (8,cap⇒≤3 further < needed 4), other K4's low-mask
    (all-high=8 ⇒ both x2,x3 complete ⇒ K6 contra). pick K4-nonendpoint ⇒ avoid uv. ✓
  [ALL budgets VERIFIED numerically.]

⇒ (7.6) some indep 5-set has P≤25. With (6.1): (7.7) some Q has P=25, all have ≥25. ✓

NOTE E1 (exposition, NOT a gap): candidate's blanket "at most 16 incidences" (line 470)
is loose for the (5,4,4,3,3) base-10 sub-case, where naively remainder ≤16−10=6 does NOT
strictly exceed the 6 an unchosen K3 needs. The conclusion is rescued by the FORCED exact
value e(C,D)=15 (from (7.4), since (5,4,4,3,3) has e(D)=28⇒e(C,D)=15), giving remainder ≤5<6.
Rigorous, but the candidate should cite 15 not 16 there. No effect on validity.

---

## §8 — Exact P=25 structural split (lines 511–565)

VERDICT: CORRECT. Eight signatures EXHAUSTIVE (script-verified), all sum to P=25.

- Excess = 25−21 = 4. Exceptional degree patterns = partitions of 4 into parts≥1, +1:
  [5],[4,2],[3,3],[3,2,2],[2,2,2,2]. ✓
- Ordinary = 21−k; deficiency k−1 distributed over 5 groups (each 1..4). All 5 groups
  nonempty (4 groups·4=16<17 for k=4). Gives exactly 8 signatures [SCRIPT-VERIFIED]:
  5|44444, 42|34444, 33|34444, 322|24444, 322|33444, 2222|14444, 2222|23444, 2222|33344. ✓
- Every deg-≤4 exceptional meets a deficient group (large-nbr lemma). (deg-5 in sig 5 handled
  by SAT.) ✓
- EXCHANGE INEQUALITY (8.1): w∈R_i ⇒ Q'=(Q−q_i)∪{w} indep (w's only Q-nb is q_i). (6.1):
  P(Q')≥25=P(Q). P(Q')=25−d(q_i)+d(w) ⇒ d(w)≥d(q_i). d(q_i)=|R_i|+s_i (nbs: R_i + s_i
  exceptionals; other-group ordinaries ⊥q_i). d(w)=1+(|R_i|−1)+d_{W−R_i}(w). Cancel ⇒
  d_{W−R_i}(w) ≥ s_i. ✓ [Derivation airtight.]

---

## §9 — seven replay-certified signatures (lines 567–709)

VERDICT: lemma TAKEN AS GIVEN (per assignment; cert semantics/relaxation-safety handled
by parallel reviewer). Internal-chain role checked:
- Lemma excludes signatures 1–7 (5,42,33,322_24444,322_33444,2222_14444,2222_23444).
- Manifest list = exactly those 7 (line 652); 2222_33344 explicitly absent → §10. ✓
- §8 table order matches; 7 + 1(§10) = all 8. No signature double-covered or dropped. ✓
- 2222_23444 formula ranges over ALL masks satisfying degree+deficient-hit (line 656) — no
  reliance on a human type classification, so no hidden completeness gap there. ✓
[I did not re-derive the CNF encodings — out of assigned scope, given as safe relaxations.]

## §10 — the eighth signature 2222_33344 (lines 711–814)

VERDICT: CORRECT (defect lemma taken as given; counting + premise-consistency verified).

- Defect lemma premise check (prompt-flagged): the finite lemma fixes anchored K_4s
  ({q_i}∪S_i), exact masks, and mixed-mask completion edges. In the ACTUAL gap graph these
  all hold: S_i cliques + anchors ✓; masks from signature ✓; mixed-mask (one deficient +
  one large index) completion edges FORCED by the completion lemma ✓. Both-deficient-mask
  exceptions get NO completion edge — consistent (completion lemma needs exactly one
  deficient nb-group, so it correctly does not apply). Core 1–11 window holds (core six-sets
  are G six-sets). Premises consistent, application valid. ✓
- (10.1): Σs_i=8; Σ|R_i|s_i = 3(s0+s1+s2)+4(s3+s4) = 3(8−l)+4l = 24+l ⇒ D≥24+l. ✓
- D=2a+b+t (ordinary external incidence: 2a cross ord-ord + (b+t) exc-ord). ✓
- R=a+b+t+c (non-internal W-edges); 2R=2a+2b+2t+2c = D+b+t+2c. ✓
- 2R = D+b+t+2c ≥ D+b+2c ≥ (24+l)+b+2c = 24+(l+b+2c) ≥ 24+15 = 39 ⇒ R≥20.
- internal = 3·3+2·6 = 21; R ≤ e(W)−21 ≤ (65−25)−21 = 19. CONTRADICTION R≥20 vs ≤19. ✓
  [ALL VERIFIED numerically.]

---

## §11 — the exact value N(5)=25 (lines 822–846)

VERDICT: MATH CORRECT. One artifact-naming discrepancy (A1), not a math gap.

- AG(2,5) has 25 points, 6 parallel classes (5 finite slopes + vertical). Colours 1–4 =
  slopes 1–4; colour 0 = slope-0 (horizontal) ∪ vertical. 5 colours from 6 classes. ✓
- Each class = 5 parallel lines partition 25 pts; 6 pts, 5 lines ⇒ pigeonhole a monochromatic
  pair. Colours 1–4 each appear (single class); colour 0 appears (both H and V pairs). ⇒
  every six-set sees all 5 ⇒ balanced K_25 ⇒ N(5)≥25. ✓
- Restriction-monotonicity: balanced K_n (n≥26) restricts to balanced K_26 (matches
  PROBLEM.md monotonicity). Main theorem (no balanced K_26) ⇒ N(5)≤25. So N(5)=25. ✓
- C(25,6)=177100 VERIFIED.
- verify.py interface matches §11's cited command; JSON format {r,n,colours} matches.

FINDING A1 (artifact availability, NOT math): the cited certificate
`data/candidates/affine_k25_r5.json` is ABSENT from this repo. BUT the equivalent
`data/candidates/ag25_merge_0_inf.json` (affine grid, slopes 0 and ∞ merged — EXACTLY the
§11 horizontal+vertical merge) EXISTS and I RAN IT:
  `python3 tools/verify.py data/candidates/ag25_merge_0_inf.json`
  → "BALANCED: r=5, n=25; all 177100 subsets of size 6 see all 5 colours." exit 0.
verify.py --selftest also PASSED. So the construction's MATH is confirmed by the ground-truth
referee; only the filename in the writeup is stale. Publication should either commit the
named file or fix the citation.

---

## LOGIC SWEEP (whole-chain dependency + quantifiers)

VERDICT: SOUND. No circularity, quantifiers consistent.

- (6.1)+(7.6)→(7.7): (6.1) ∀Q P(Q)≥25; (7.6) ∃Q P(Q)≤25 ⇒ that Q has P=25, and ∀Q ≥25.
  Consistent. ✓
- §7 does NOT depend on §§4–6: §7 assumes ¬(7.6) = "∀Q P≥26" and derives a contradiction
  (indep 6-set / cap violation), using only α=5, the 1–11 cap, BN/Brouwer, and the table —
  NOT (6.1). So no circularity between the "∀≥25" track (§§3–6) and the "∃≤25" track (§7). ✓
- §7 uses only the "≥26-contradiction," never (6.1)/P≥25. ✓
- (6.1) is used ONLY in §8's exchange inequality (8.1), and §§3–6 establish it beforehand. ✓
- Dependency order §3 → §§4–6 (⇒6.1) ; §3(+lit) → §7 (⇒7.6) ; (6.1)+(7.6) → §8 → §9,§10.
  Acyclic. ✓
- Exchange inequality legitimately needs (6.1) for EVERY 5-set (incl. Q'); §§4–6 prove (6.1)
  universally (candidate's own emphasis, lines 100–102). This is the crucial correctly-handled
  point. ✓
- Signature coverage: §8's 8 signatures exhaustive (verified); §9 lemma kills 1–7, §10 kills 8.
  §9 lemma's premises = (GAP)+(7.7)+signature, all established; encodes (8.1) via (6.1). ✓
- Final contradiction: (7.7) guarantees a P=25 Q; §§9–10 make every signature of it impossible
  ⇒ no gap graph ⇒ no balanced K_26. Contrapositive chain intact from §2. ✓

---

## FINAL VERDICT

**SURVIVES.** After line-by-line recomputation of every number in the internal chain
(§§2–8, §10 counting, §11) I found NO fatal error and NO genuine mathematical gap. Two
non-fatal findings only: E1 (exposition looseness in §7.3, rescued by a forced exact value)
and A1 (stale certificate filename in §11; an equivalent committed cert passes the referee,
which I ran). The proof's correctness reduces, as designed, to the TWO machine-checked lemmas
(§9 seven-signature, §10 three-K_3 defect) — explicitly out of my assigned scope and taken as
given — plus the three literature theorems (given, faithfully applied). Within the human chain,
the weakest but still-valid link is §7.3's incidence budgeting.

Three least-obvious steps I fully expanded above:
1. §4 a=3 inclusion–exclusion U=27−3k+w−t (EXPANDED STEP #1).
2. §6 triangle subcase forcing all six H-degrees =1 then H=K_6 (EXPANDED STEP #2).
3. §7 (7.1) intersection bound c≥22−σ (the 3·26=78 = 12 internal + 66 slack reconciliation).

Publication requirements: (a) commit `data/candidates/affine_k25_r5.json` or fix the §11
citation to the existing `ag25_merge_0_inf.json`; (b) fix §7.3 to cite e(C,D)=15 (not "≤16")
in the (5,4,4,3,3) sub-case; (c) the whole result remains contingent on independent
replay/audit of the §9 and §10 certificates (outside this review's scope).

## One-line-per-finding index

- L52–69 §2 reduction (65 minority, 1–11 cap, direction): CORRECT.
- L71–102 §3 (α=5, P≥22 via R_i cliques ≤4, P≤31): CORRECT.
- L104–174 §4 P=22 five-part lemma (a=0,1,2,3; U=27−3k+w−t; 16U>36(10−k)): CORRECT.
- L176–204 §5 P=23 (deg-3 transversal; two-deg-2 → 6+4+4=14>11): CORRECT.
- L206–303 §6 P=24 (large-nbr/completion lemmas; {3,3,4,4,4} 3 type-cases; 3 X-graph subcases): CORRECT.
- L305–368 §7 regular branch (260, mult-13) + BN (σ≤19) + (7.1) c≥22−σ + 6-row table (σ=19): CORRECT.
- L387–401 §7.1 c=5 (D=K4²K3³; N_D=K3; 5 vs 3 pigeonhole; 12>11): CORRECT.
- L403–430 §7.2 c=4 (low-mask transversal; obs2 5-from-4): CORRECT.
- L432–497 §7.3 c=3 ((7.4),(7.5) exhaustive; 3 subcases incl. K4–K3 cross-edge): CORRECT [note E1].
- L511–565 §8 eight signatures EXHAUSTIVE + exchange ineq (8.1): CORRECT.
- L567–709 §9 seven-signature lemma: GIVEN (scope); connection/coverage checked CORRECT.
- L711–814 §10 defect lemma GIVEN; 2R=D+b+t+2c≥39 ⇒ R≥20 vs ≤19: CORRECT; premises consistent.
- L822–846 §11 N(5)=25 construction: MATH CORRECT; FINDING A1 (filename), ran equivalent cert PASS.
- E1 (L470): "≤16 incidences" loose; rescued by forced e(C,D)=15. Non-fatal exposition.
- A1 (L835): cited `affine_k25_r5.json` absent; `ag25_merge_0_inf.json` present & verify.py→BALANCED.


EXPANDED STEP #2 — triangle subcase (candidate lines 287–296):
G[X]=triangle ⇒ all 3 pairs edges ⇒ each pair d_A-sum ≤2 and d_B-sum ≤2 (pair cap −1).
No degree is 0: suppose d_A(z)=0 ⇒ z⊥A; a B-column z misses is complete to A (missing
rect); cross cap ⇒ ≤1 complete column ⇒ z misses ≤1 column ⇒ d_B(z)≥2; pair caps ⇒
d_B(x)=d_B(y)=0 ⇒ x,y⊥B ⇒ each missed A-row complete to B, cross cap ⇒ d_A(x),d_A(y)≥2
⇒ d_A(x)+d_A(y)≥4 > 2 pair cap ⊥. So all six degrees ≥1; with pair sums ≤2 ⇒ all =1.
Cap on {q_0,q_1,x,y,z,a}: 4(q_0→x,y,z,a)+3(q_1→x,y,z)+3(triangle)+m ≤11 ⇒ m≤1 ⇒ each
a∈A meets ≤1 of X; Σ d_A=3 over 3 A-vtcs each ≤1 ⇒ bijection A↔X, likewise B↔X.
For any a,b: a third exc misses both (∃ w∈X∖{v_a,v_b}) ⇒ missing rect ⇒ ab∈E ⇒ H=K_{3,3}
⇒ A∪B=K_6=15>11 ⊥. AIRTIGHT.

---
