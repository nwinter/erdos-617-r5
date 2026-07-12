# WIP (partial results only — NOT a complete proof): hand-proof framework for [MH″]

Author session: 2026-07-10. Status: **work in progress**; the framework and the partial
bounds below are computationally verified (tools/handproof_check.py) but the argument is
NOT complete. A parallel machine attempt (gpt-5.6-sol via codex) is running on the same
target; merge whatever survives.

## Target

[MH″]: no balanced 5-colouring of $K_{25}$ has a colour (wlog 0) and a 4-set $T$ with
$\alpha(G_0 - T) \le 4$. (Machine-verified TRUE analogues fail at $n \le 24$ — witnesses
exist — so every step must be checked to bite only at $n = 25$; see RESULTS.md R6.)

## Setup and the exact counting identity

Let $V_{out}$ = the 21 non-$T$ vertices, $G := G_0[V_{out}]$, $N = 21$, $e = e(G)$,
$d_v$ = degrees in $G$, $t$ = triangles of $G$. The hitter condition gives
$\alpha(G) \le 4$, and per vertex $v$, with $W_v = V_{out} \setminus N_G[v]$
($|W_v| = 20 - d_v$):

  (P)  $\alpha(G[W_v]) \le 3$  for every $v \in V_{out}$
       [an independent 4-set in $W_v$ plus $v$ would be an independent 5-set avoiding $T$].

**Identity** (verified exactly on the n=24 witness):
$$\sum_{v} e(G[W_v]) \;=\; N e \;-\; \sum_v d_v^2 \;+\; 3t.$$
Proof: an edge $xy \in E(G)$ lies in $W_v$ iff $v \notin N(x) \cup N(y)$ (note
$\{x,y\} \subseteq N(x)\cup N(y)$ since $xy$ is an edge), and
$|N(x) \cup N(y)| = d_x + d_y - \lambda_{xy}$; summing $\lambda$ over edges gives $3t$.

**Lower bound per vertex**: $e(G[W_v]) \ge f(20 - d_v)$ where
$f(m) = \binom{m}{2} - ex(m, K_4)$ (complement Turán; $\alpha \le 3$).
$f$: 12→18, 13→22, 14→26, 15→30, 16→35, 17→40, 18→45, 19→51, 20→57. (Convex.)

**Cherry bound**: $3t \le \sum_v \binom{d_v}{2}$.

**Budget**: the other four classes restricted to $V_{out}$ each have $\alpha \le 5$
(21 vertices ⇒ $\ge 34$ edges each), so $e \le \binom{21}{2} - 4\cdot 34 = 74$.

## Proved partial results (machine-checked arithmetic, tools/handproof_check.py)

- Combining identity + per-vertex bound + cherry bound into the necessary condition
  $N e - \sum d_v^2 + \sum \binom{d_v}{2} \ge \sum_v f(20 - d_v)$ and maximizing the
  left side over ALL integer degree sequences with $\sum d_v = 2e$ (exact DP, no
  Jensen): **every $e \le 44$ is infeasible at $n=25$**. Hence in any h4-witness at 25,
  $e(G_0[V_{out}]) \ge 45$ — while the same computation at $n = 24$ (N=20) leaves
  $e \ge 40$ feasible, and the actual verified witness has $e = 41$, 4-regular-ish,
  $t = 40$, sitting 10 above the identity's lower bound (602 vs 592) with cherries
  nearly tight (120 vs 128). The framework is essentially sharp at 24.

## Structural constraints available for the finish (all balance-derived, verified logic)

1. **cap-11 ⇒ $K_{2,2,2}$-free**: any 6 vertices span ≤ 11 $G$-edges, and $K_{2,2,2}$
   has 12. So $G$ (and every class) contains no octahedron subgraph.
2. **cap-11 ⇒ common-neighbourhood sparsity**: for an edge $xy$, any 4 vertices of
   $\Lambda_{xy} = N(x) \cap N(y)$ span ≤ 2 edges (the 6-set $\{x,y\} \cup$ those 4
   already carries $1 + 2\cdot4 = 9$ edges). Hence $G[\Lambda_{xy}]$ has all components
   with ≤ 2 edges; $e(G[\Lambda_{xy}]) \le \tfrac{2}{3}|\Lambda_{xy}|$.
3. **$K_6$-freeness**: $\omega(G[\Lambda_{xy}]) \le 3$; cliques of $G$ ≤ 5.
4. $R(4,4) = 18$: every $v$ with $d_v \le 2$ has a colour-0 $K_4$ inside $W_v$.
5. The floor states (R6) suggest the extremal tension concentrates at a single vertex —
   a "last vertex cannot integrate" argument may be cleaner than global counting.

## The remaining gap

The DP window $e \in [45, 74]$ at $n = 25$ survives the current inequalities. The
cherry bound is the weak link ($3t \le \sum\binom{d_v}{2}$ ignores 1–3 entirely).
Candidate finishing moves:
(a) triangle upper bound for $K_{2,2,2}$-free + cap-11 graphs sharper than cherries
    (books $B_k$ ARE allowed with independent pages, so bound via edges-in-$\Lambda$
    counting: $3t = \sum_{xy} \lambda_{xy}$ and constraint-2 restricts how $\Lambda$'s
    overlap — count $K_4$'s: each $K_4$ has 6 edges each contributing ≥2 to some
    $\Lambda$, and cap-11 bounds $K_4$-density in 6-sets…);
(b) import the OTHER classes: the 4 remaining classes on $V_{out}$ hold $210 - e \le 165$
    edges, each needs $\alpha \le 5$ AND cap-11 AND $K_{2,2,2}$-freeness; at $e \ge 45$
    their average 41.25 is within 7 of their Turán floor 34 ⇒ they are near-5K_4ish
    partitions of 21 vertices (stability), which constrains the pairs available to $G$;
(c) the per-vertex conditions (P) for vertices INSIDE $W_v$'s (second-order: apply (P)
    within the graphs $G[W_v]$, which have $\alpha \le 3$ — a recursive descent one
    level deeper, i.e. $\alpha(G[W_v \setminus N[u]]) \le 2$ for $u \in W_v$, and
    $\alpha \le 2$ graphs on $m$ vertices need $\ge \binom{m}{2} - ex(m,K_3)$ edges —
    much stronger floors).

Next session: try (c) first (it worked at level one), validated against the n=24
witness at each step; then (b) with the stability argument.

## Update (2026-07-10, later): the PINCER — both jaws now have teeth

**Bottom jaw**: level-2 recursion saturates UNCAPPED (f** = f exactly for m=12..16;
disjoint-triple-clique extremals satisfy the per-vertex conditions). But cap-11 kills
those extremals for m ≥ 16 (a K_6 part exceeds the cap; 3 parts of size ≤5 cover only
15 < m ⇒ α ≥ 4). Exact capped floors f**_cap(m), m = 16..19, computing via SAT
(tools/fstar_exact.py --cap → data/sat/fstar_capped.log); then rerun lp_scan2 with them
→ new e_lo (currently 45).

**Top jaw (first tooth PROVED)**: at e = 74 (budget max) the four other classes each sit
at their α≤5 Turán floor on the 21 points, which forces each to be EXACTLY a disjoint
(5,4,4,4,4)-clique partition (Turán equality), pairwise orthogonal (edge-disjointness);
G is then forced to be the complement of their union. SAT verdict
(tools/orth_partitions.py 4 --alpha4): **UNSAT — no such system has α(G) ≤ 4. Hence
e(G_0[V_out]) ≤ 73 in any h4-witness at n = 25.** (The bare design without the α-condition
IS satisfiable — the α(G) ≤ 4 requirement is what kills it.)

**Walking the top jaw down (rigorous route)**: for e = 74 − k, the other classes carry
combined excess k; by Füredi's exact stability (complement side: K_6-free with ex − t
edges ⇒ 5-partite after ≤ t deletions), each class is a clique partition with ≤ t_c
edits, Σ t_c ≤ k. Encode partitions + ≤ k global pair-edits + α(complement-G) ≤ 4
(+ optionally the per-vertex (P) conditions and cap-11 on G) — one small SAT instance
per k. Each UNSAT lowers the ceiling by one. If ceiling meets the capped floor: MH″
is PROVED via a chain of small certified SAT lemmas + the counting identity — all
hand-checkable modulo a table of tiny SAT verdicts.

**Falsification guard — PASSED, and it discriminates.** The identical top-jaw probe at
n = 24 (20 points, four orthogonal (4,4,4,4,4)-partitions, α(complement) ≤ 4) is **SAT**,
while at n = 25 (21 points, (5,4,4,4,4)) it is **UNSAT**. First tool in the project that
provably separates 24 from 25 at the structural level. The root cause is visible:
21 = 4·5 + 1 forces one oversized part, while 20 = 4·5 splits perfectly — the
conjecture's "+1" propagates down the whole reduction (26 → 25 → 21) and is precisely
what kills the extremal design. This is strong evidence the pincer is the right proof
shape, and suggests the eventual hand proof will hinge on the odd part of size 5.
