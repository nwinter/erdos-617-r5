# Candidate proof package for the `r=5` case of Erdős Problem 617

STATUS: **reviewed candidate, awaiting independent external scrutiny.**  The
complete informal composition passed the fresh adversarial review in
`review_queue/full_r5_proof_review.md`; the later unconditional Lean chain
passed the separate review in `review_queue/formal_r5_end_to_end_review.md`.
Per the project ground rules, neither review is described as “proof complete.”

Date: 2026-07-11.

This document is intended to be a complete informal proof package.  Its
finite machine-assisted lemma is stated mathematically, its reduction from
graphs to CNF is given explicitly, and the replay commands and trust boundary
are part of the proof.  No bare SAT/UNSAT verdict is used.  Nothing in this
file should be moved to `RESULTS.md` on its author's judgement.

## 1. Statement, terminology, and source ingredients

An edge-colouring of `K_n` by five colours is **balanced** when every six
vertices see all five colours.  The claim is:

> **Candidate theorem.**  No balanced five-colouring of `K_26` exists.
> Moreover, the largest order admitting a balanced five-colouring is
> `N(5)=25`.

The proof uses ordinary Turán's theorem, including its equality
characterization (`papers/turan-erdos-1977.md`), and the following two
published theorems.  The cited local notes record retrieval dates, source
links, exact statements, source hashes, and the pages read.

1. Bollobás--Nikiforov's strict clique degree-sum theorem
   (`papers/bollobas-nikiforov-2005.md`): if a nonregular `n`-vertex,
   `m`-edge graph has `m>=t_r(n)`, it has an `r`-clique whose ambient degree
   sum is strictly greater than `2rm/n`.
2. Brouwer's exact Turán stability theorem
   (`papers/brouwer-1981-turan-extension.md`): if `alpha(F)<=t`, `n>2t`, and
   `e(F)<=T(n,t)+floor(n/t)-2`, where `T(n,t)` is the minimum number of edges
   in an `n`-vertex graph of independence number at most `t`, then `F` is a
   union of `t` cliques.

The original colouring conjecture and the affine-plane construction are
recorded from Erdős--Gyárfás in `papers/erdos-gyarfas-1999.md`.

For a graph `G` and a vertex set `S`, write `e(S)` for the number of induced
edges, and for disjoint sets `S,T`, write `e(S,T)` for the number of edges
between them.  For an independent set `Q`, its boundary is

```text
P(Q)=e(Q,V(G)-Q)=sum_(q in Q) d_G(q).
```

## 2. The minority-colour graph reduction

Suppose, for contradiction, that a balanced five-colouring of `K_26`
exists.  Its 325 edges are partitioned among five colours, so one colour has
at most 65 edges.  Let `G` be the spanning graph formed by that colour.

Every six-set has at least one `G`-edge, because otherwise it misses the
chosen colour.  Every six-set has at most 11 `G`-edges: if it had at least
12, at most three of its 15 edges would remain for the other four colours,
so one of those colours would be absent.  Thus the assumed colouring
produces a graph satisfying

```text
|V(G)|=26,       e(G)<=65,       1<=e(S)<=11 for every |S|=6.       (GAP)
```

Call such a graph a **gap graph**.  It is enough to prove that no gap graph
exists.

## 3. Independent five-sets and the first boundary bound

The lower end of (GAP) says `alpha(G)<=5`.  In fact `alpha(G)=5`.  If
`alpha(G)<=4`, the complement is `K_5`-free, so Turán's theorem gives

```text
e(G)>=C(26,2)-t_4(26)=325-253=72>65.
```

Fix an independent five-set
`Q={q_0,q_1,q_2,q_3,q_4}` and put `W=V(G)-Q`, so `|W|=21`.  Every vertex of
`W` has a neighbour in `Q`, because otherwise it extends `Q` to an
independent six-set.  Consequently `P(Q)>=21`.

If equality held, every vertex of `W` would have a unique neighbour in `Q`.
Put vertices having neighbour `q_i` into `R_i`.  Each `R_i` is a clique:
two nonadjacent members together with `Q-{q_i}` would be independent.
Moreover `|R_i|<=4`, since five members together with `q_i` form a `K_6`
and have 15 edges.  Five sets of size at most four cannot cover 21 vertices.
Hence

```text
P(Q)>=22                                                    (3.1)
```

for every independent five-set `Q`.  Also `alpha(G[W])<=5`, so complementary
Turán gives `e(W)>=10+4*6=34`; hence `P(Q)<=31`.  Only the lower frontier
will be needed.

We now eliminate `P=22,23,24`.  The details are included because the later
exchange argument requires the conclusion for **every** independent
five-set, not only an optimized one.

## 4. Elimination of `P=22`

Assume `P(Q)=22`.  The 21 positive `Q`-degrees have excess one above their
minimum, so there is one exceptional vertex `x` of `Q`-degree two and twenty
ordinary vertices of degree one.  The ordinary groups `R_i` are cliques of
order at most four, and they cover twenty vertices; hence all five are
`K_4`s.

For two distinct groups, `G[R_i,R_j]` is a matching.  Indeed, for
`y in R_j`, the six-set `{q_i} union R_i union {y}` contains the ten edges
of the fixed `K_5={q_i} union R_i`; the cap 11 allows `y` at most one
neighbour in `R_i`.  Reverse `i,j` for the other endpoint degrees.
Similarly, if `xq_i` is present then `x` is anticomplete to `R_i`, while if
it is absent then `x` has at most one neighbour there.  Let `a` be the
number of groups met by `x`; then `0<=a<=3`, with at most one neighbour in
each such group.

The five internal `K_4`s use 30 `W`-edges.  Since
`22+e(W)=e(G)<=65`, all other `W`-edges number at most 13.  After deleting
the possible neighbour of `x` from each group it meets, we obtain five parts,
`a` of size three and `5-a` of size four, whose pair graphs are matchings and
whose cross-edge count is at most `13-a`.

We use the following transversal lemma.

> **Five-part lemma.**  If five parts have sizes three in `a` cases and four
> in the other cases, where `0<=a<=3`, every pair graph is a matching, and
> there are at most `13-a` cross-edges, then there is an independent
> transversal.

Choose a transversal uniformly.  An edge between parts of sizes `s,t` is
chosen with probability `1/(st)`.  For `a=0`, the union bound is at most
`13/16<1`.  For `a=1`, it is at most `12/12=1`; equality requires all 12
edges to run from the small part to the four large parts.  Then choose any
small-part vertex and a nonneighbour in every large part, between which there
are no edges.  For `a=2`, let `z<=3` be the number of edges between the two
small parts.  The union bound is at most

```text
z/9+(11-z)/12 = 11/12+z/36 <=1.
```

Equality forces `z=3`, the full 11-edge budget, and no edge between large
parts.  Choose a nonedge between the small parts, then avoid the at most two
forbidden values in each large part.

For `a=3`, call the small parts `A,B,C` and let `k` be their cross-edge
count.  If `k<=5`, the union bound is `(k+30)/36<1`.  If `6<=k<=9`, let `w`
be the number of degree-two vertices in the graph on `A union B union C`, and
`t` its number of triangles.  Pairwise matching gives maximum degree two,
and exact inclusion--exclusion over the 27 small transversals gives

```text
U=27-3k+w-t.
```

The degree sum gives `w>=2k-9`; the triangles are vertex-disjoint, so
`3t<=w`.  For `k=6,7,8,9` this yields respectively
`U>=11,10,8,6`.  Each independent small transversal has 16 extensions to
the two large parts.  Any remaining edge destroys at most 36 extensions,
and at most `10-k` edges remain.  In the four cases,

```text
16U >= 176,160,128,96 > 144,108,72,36 = 36(10-k).
```

Thus some extension is independent, proving the lemma.

Apply it after deleting the neighbours of `x`.  Its independent transversal,
together with `x`, is an independent six-set.  This contradiction excludes
`P=22`.

## 5. Elimination of `P=23`

The excess of the 21 positive `Q`-degrees is now two.  There are only two
patterns.

### 5.1. One exceptional of degree three

The twenty ordinary vertices form five `K_4` groups.  Let `x` be exceptional
and let `I=N_Q(x)`, `|I|=3`.  For every `i in I`, the fixed-`K_5` rule makes
`x` anticomplete to `R_i`.  Between any two of these three groups there is a
matching.  A uniform transversal of the three groups has expected selected
edge count at most `3*4/16=3/4`; choose one selecting none.  It, `x`, and
the two vertices of `Q-N_Q(x)` form an independent six-set.

### 5.2. Two exceptionals of degree two

The nineteen ordinary vertices have group sizes `3,4,4,4,4`; call the
three-set `R_0`.  Every exceptional `z` must meet `q_0`.  Otherwise its two
neighbour groups are large, `z` is anticomplete to both, and a nonedge
between those groups extends `z` together with the three retained vertices
of `Q` to an independent six-set.

Write the other neighbour of `z` as `q_i`.  Then `z` is complete to `R_0`.
If `z` missed `s in R_0`, the fixed `K_5={q_i} union R_i` makes `z`
anticomplete to `R_i` and gives `s` at most one neighbour in that four-set.
Choose `v in R_i` missed by `s`; then
`{z,s,v} union (Q-{q_0,q_i})` is independent.  Thus both exceptionals are
complete to `R_0`, and the six-set consisting of them and
`{q_0} union R_0` has at least `6+4+4=14` edges.  This excludes `P=23`.

## 6. Elimination of `P=24`

We first isolate two consequences of the fixed-`K_5` rule.  They are stated
only for exceptional vertices.

- **Large-neighbour lemma.**  If an exceptional `x`, of `Q`-degree at most
  four, has only size-four neighbour groups, choose one vertex from those
  groups greedily.  At the `j`th choice, the previous `j-1<=3` choices each
  forbid at most one of the four values.  The resulting transversal, `x`,
  and `Q-N_Q(x)` are six independent vertices.
- **Completion lemma.**  If exactly one neighbour group `R_i` of `x` is
  deficient and all its other neighbour groups are large, then `x` is
  complete to `R_i`.  Otherwise begin with a missed `u in R_i` and make the
  same greedy choices, now avoiding `u` too.  At the last step at most three
  values are forbidden, again producing an independent six-set.

At `P=24`, the excess is three, so the exceptional-degree pattern is
`[4]`, `[3,2]`, or `[2,2,2]`.

- In `[4]`, the twenty ordinary vertices form five large groups, contradicting
  the large-neighbour lemma.
- In `[3,2]`, the group sizes are `3,4,4,4,4`.  Both exceptionals must meet
  the deficient group and are complete to it, giving the same
  `6+4+4=14` count around its fixed `K_4`.
- In `[2,2,2]`, the sizes are either `2,4,4,4,4` or `3,3,4,4,4`.  In the
  first case all three exceptionals meet and complete to the deficient
  two-set.  With its anchor `q_i` this gives `3+3*3=12` edges on six
  vertices.

It remains to handle sizes `3,3,4,4,4`.  Write `A=R_0`, `B=R_1`.  Each
degree-two exceptional has type `0L`, `1L`, or `01`, according as its
`Q`-mask uses deficient index 0 only, deficient index 1 only, or both.
Completion makes type `0L` complete to `A` and type `1L` complete to `B`.
There is at most one of either exclusive type, because two around the same
fixed `K_4` give 14 edges.  Thus the type multiset is one of

```text
{0L,1L,01},       {0L,01,01} up to symmetry,       {01,01,01}.
```

For a type-`01` vertex `z` and the bipartite graph `H=G[A,B]`, use four
elementary rules:

1. **Missing rectangle.**  If `z` misses `a in A` and `b in B`, then `ab`
   is an edge, or `{z,a,b,q_2,q_3,q_4}` is independent.
2. **Pair cap.**  If exceptionals `u,v` both meet `q_0`, then the six-set
   `{q_0} union A union {u,v}` gives
   `d_A(u)+d_A(v)+1_(uv in E)<=3`; symmetrically in `B`.
3. **Cross cap.**  For distinct `b,b' in B`, the six-set
   `{q_0} union A union {b,b'}` gives
   `d_A(b)+d_A(b')<=4`; symmetrically for row degrees.  Thus `H` has no
   `K_(3,2)` and no `K_(2,3)`.
4. **Nonadjacent pair partition.**  If type-`01` vertices `u,v` are
   nonadjacent, the only possible edges in
   `{u,v,a,q_2,q_3,q_4}` are `ua,va`, so their `A`-neighbourhoods cover `A`.
   The pair cap makes their total size at most three, hence the
   neighbourhoods partition `A`.  Likewise they partition `B`.

For `{0L,1L,01}`, the pair caps with the exclusive vertices make the shared
vertex anticomplete to both `A` and `B`; the missing-rectangle rule makes
`H` complete, a `K_6`.  For `{0L,01,01}`, both shared vertices are
anticomplete to `A`.  Their missing rectangles make every column outside
the intersection of their `B`-neighbourhoods complete.  The cross cap allows
at most one such column, so the intersection has size at least two and their
total `B`-degree is at least four, contradicting the pair cap.

Finally let all three vertices be shared, `X={x,y,z}`.  The graph on `X` is
nonempty, or `X union {q_2,q_3,q_4}` is independent.

- If it has one edge, say `xy`, the partition rule on `xz,yz` makes `x,y`
  have the same `A`-neighbourhood, complementary to that of `z`, and likewise
  in `B`.  The edge pair cap makes the common degrees `a,b<=1`.  If `a=0`,
  the missing rectangle gives a forbidden `K_(3,2)`; so `a=b=1`.  If
  `a_0,b_0` are the common neighbours of `x,y`, the missing rectangle for
  `z` gives `a_0b_0`.  The set
  `{q_0,q_1,x,y,a_0,b_0}` has six anchor-to-exceptional/ordinary edges,
  four edges from `x,y` to `a_0,b_0`, and `xy,a_0b_0`: twelve in total.
- If it is the path `x-y-z`, the nonedge `xz` gives
  `d_A(x)+d_A(z)=3`; the two edge pair caps give
  `d_A(x)+d_A(y)<=2` and `d_A(z)+d_A(y)<=2`.  Thus `d_A(y)=0`, and similarly
  `d_B(y)=0`; its missing rectangle makes `H` complete.
- If it is a triangle, every pair of degrees into either side sums to at
  most two.  No such degree is zero: if `d_A(z)=0`, the missing rectangle
  and absence of `K_(3,2)` force `d_B(z)>=2`; pair caps make the other two
  `B`-degrees zero, after which their missing rectangles and absence of
  `K_(2,3)` force both corresponding `A`-degrees at least two, contradicting
  their pair cap.  Hence all six degrees equal one.  The cap on
  `{q_0,q_1} union X union {a}` says each `a in A` meets at most one vertex
  of `X`; the three incidences therefore give a bijection, and likewise in
  `B`.  For any `a,b`, a third exceptional misses both, so its missing
  rectangle forces `ab`.  Again `H` is complete.

Every case is impossible.  Combining Sections 3--6 gives the reviewed
frontier

```text
P(Q)>=25 for every independent five-set Q.                 (6.1)
```

## 7. Stability: some independent five-set has `P<=25`

This section reproduces the optimized-boundary argument.  Let `H` be the
complement of `G`.  It is `K_6`-free and has at least 260 edges.

If `H` is regular, Turán gives `260<=e(H)<=t_5(26)=270`, while regularity
makes `e(H)` a multiple of 13.  Hence `e(H)=260`, `H` is 20-regular, and
`G` is 5-regular.  Any independent five-set then has boundary 25.

Suppose `H` is nonregular.  Since `e(H)>=260>t_4(26)=253`, the strict
Bollobás--Nikiforov theorem supplies an `H`-clique `A` of order four with
ambient `H`-degree sum strictly greater than `8e(H)/26>=80`, hence at least
81.  Thus `A` is independent in `G` and

```text
sigma=sum_(a in A)d_G(a)=100-sum_(a in A)d_H(a)<=19.
```

Let `C` be the common open `H`-neighbourhood of `A`: equivalently, the
vertices outside `A` with no `G`-neighbour in `A`.  The four-set intersection
bound gives

```text
c=|C| >= sum_(a in A)d_H(a)-3*26 = 22-sigma.               (7.1)
```

An `H`-edge inside `C` would complete `A` to an `H`-`K_6`, so `C` is a
`G`-clique.  The upper window gives `c<=5`, hence `17<=sigma<=19`.

Put `D=V(G)-(A union C)`, so `|D|=22-c`.  Every vertex of `D` meets `A`,
and all `sigma` edges incident with `A` go to `D`.  Since
`alpha(G[D])<=5`, complementary Turán gives the lower bound `L_5(22-c)`,
the edge count in five as-equal-as-possible cliques.  The exact edge
partition is

```text
e(G)=sigma+C(c,2)+e(C,D)+e(D).                             (7.2)
```

Choose `x in C` of minimum `D`-degree.  Then `A union {x}` is independent,
and (7.2) gives the following complete table:

| `sigma` | `c` | `|D|` | `L_5(|D|)` | maximum `e(C,D)` | maximum `P(A+x)` |
|---:|---:|---:|---:|---:|---:|
| 17 | 5 | 17 | 21 | 17 | 24 |
| 18 | 4 | 18 | 24 | 17 | 25 |
| 18 | 5 | 17 | 21 | 16 | 25 |
| 19 | 3 | 19 | 27 | 16 | 26 |
| 19 | 4 | 18 | 24 | 16 | 26 |
| 19 | 5 | 17 | 21 | 15 | 26 |

For example the last column is

```text
sigma+c-1+floor((65-sigma-C(c,2)-L_5(22-c))/c).
```

Only the last three rows remain if, contrary to the desired conclusion,
every independent five-set has boundary at least 26.  Therefore
`sigma=19`, and every `x in C` satisfies

```text
d_G(x)>=26-sigma=7.                                        (7.3)
```

We use two elementary observations.

1. If `D` is a union of five nonempty clique parts, a subset meets every
   independent transversal exactly when it contains a whole part.  If there
   is one cross-edge `uv` between parts `B_i,B_j`, a hitting set either
   contains a whole part or contains both `B_i-{u}` and `B_j-{v}`.  Indeed,
   in the latter exceptional case the available choices in the two endpoint
   parts are forced to be `{u}` and `{v}`; otherwise one can choose an
   avoiding allowed transversal.
2. When every vertex of `D` has a unique neighbour in `A`, call it the
   vertex's `A`-colour and put `M(v)=N(v) intersect C`.  If nonadjacent
   `u,v` have the same colour and `M(u) union M(v)!=C`, choose
   `x in C-(M(u) union M(v))`; the other three vertices of `A`, with
   `u,v,x`, form an independent six-set.  Therefore an independent
   transversal whose five masks have pairwise union smaller than `C` would
   require five distinct colours from only four vertices of `A`, impossible.

### 7.1. The case `c=5`

Equality in (7.2), (7.3), and Turán forces

```text
e(C,D)=15,       e(D)=21,       D=K4+K4+K3+K3+K3,
```

and every `x in C` has exactly three neighbours in `D`.  Its neighbourhood
must hit every independent transversal, or such a transversal with `x` is
independent.  Thus it is one of the three `K_3` parts.  Two vertices of `C`
cannot choose the same `K_3`: with a third vertex of `C`, the six-set has
at least `3+3+3+3=12` edges (the two internal triangles and the two complete
joins from the first two `C` vertices).  Five vertices cannot choose
distinctly among three parts.

### 7.2. The case `c=4`

Equality forces

```text
e(C,D)=16,       e(D)=24,       D=K4+K4+K4+K3+K3,
```

and every `C` vertex has four `D`-neighbours and hence contains a whole part
in its neighbourhood.  The four chosen parts are distinct: repeated `K_4`
choices make a `K_6`, while repeated `K_3` choices with a third `C` vertex
give 12 edges as above.

The 19 `A`--`D` edges dominate 18 vertices, so exactly one vertex has two
`A`-neighbours and all others have a unique colour.  Every clique part has
at least two ordinary vertices whose `C`-mask has size at most one:

- every vertex in a chosen `K_4` has exactly its chooser in its mask, by the
  cap on that fixed `K_5` with any other vertex of `C`;
- in a chosen `K_3`, at most one spare edge from the other possible `K_3`
  chooser enters the part, leaving at least two chooser-singletons;
- the sole unchosen part receives at most the two spare edges of the
  size-three choosers, again leaving at least two low-mask vertices.

Choose one such ordinary vertex from each part, avoiding the sole exceptional
vertex.  The five vertices form an independent transversal; every pair of
masks has union of size at most two, smaller than `|C|=4`.  The colour
observation is contradictory.

### 7.3. The case `c=3`

Now every one of the 19 vertices of `D` has a unique `A`-colour.  The edge
partition leaves only

```text
(e(D),e(C,D))=(27,15),(27,16), or (28,15).                 (7.4)
```

Brouwer's theorem applies to `G[D]`: here `alpha<=5`, `19>10`, and

```text
e(D)<=28=T(19,5)+floor(19/5)-2=27+3-2.
```

Thus `D` is the union of five cliques.  The only possibilities, by summing
the five within-part edge counts, are

```text
(4,4,4,4,3) with no cross-edge;
(5,4,4,3,3) with no cross-edge;
(4,4,4,4,3) with one cross-edge.                           (7.5)
```

We produce an allowed independent transversal all of whose masks have size
at most one, contradicting the colour observation because `|C|=3`.

With no cross-edge, each of the three `C`-neighbourhoods contains a whole
part.  A `K_5` cannot be chosen, because it and its chooser form a `K_6`,
and chosen parts are distinct by the earlier `K_4`/`K_3` cap counts.  A
chosen `K_4` consists entirely of chooser-singletons.  A chosen `K_3` has a
singleton because the other two `C` vertices contribute at most two edges
to it.  The base incidences used by the chosen parts are:

```text
12 or 11 in (4,4,4,4,3), and 11 or 10 in (5,4,4,3,3).
```

There are at most 16 incidences altogether.  If every vertex of an unchosen
part had mask size at least two, that part alone would require at least six
or eight further incidences, exceeding the remainder.  Hence each part has
a low-mask choice.

If the single cross-edge joins two `K_4` parts, the exceptional hitting set
from observation 1 has size six, while each `C`-neighbourhood has size five
by (7.4); all three neighbourhoods therefore choose whole parts.  The same
incidence count supplies a low-mask nonendpoint in an unchosen endpoint part,
while a chosen endpoint part consists of chooser-singletons.  The selected
transversal can avoid the cross-edge.

Suppose finally the cross-edge joins a `K_4` to the `K_3`.  Its exceptional
hitting set is the three nonendpoints of the `K_4` together with the two
nonendpoints of the `K_3`.  At most one vertex of `C` uses this set: two such
vertices, the three `K_4` nonendpoints, and the third `C` vertex span at
least 12 edges.  If none uses it, the whole-part argument applies.  If one
does, the other two choose distinct whole parts.  On `C` plus the three
`K_4` nonendpoints, the two triples contribute six internal edges and the
exceptional chooser contributes three cross-edges, so at most two further
incidences are possible; one
nonendpoint is a chooser-singleton.  On `C` plus the cross `K_3`, the chooser
contributes two edges and the cap leaves at most three further incidences;
making all three triangle vertices have mask at least two would require four.
Thus that part also has a low-mask vertex.  The remaining incidence budget
supplies low choices in the other parts.  Choose the low `K_4` nonendpoint;
the transversal is allowed and has all masks of size at most one.

All three `c` cases are impossible.  We have proved

```text
some independent five-set Q has P(Q)<=25.                  (7.6)
```

Together, (6.1) and (7.6) say that a hypothetical gap graph has an
independent five-set `Q` with

```text
P(Q)=25, while every independent five-set has boundary at least 25.       (7.7)
```

## 8. Exact `P=25`: the exhaustive structural split

Fix `Q` as in (7.7), put `W=V-Q`, and call `w in W` ordinary when it has one
`Q`-neighbour.  Define

```text
R_i={w in W:N_Q(w)={q_i}}.
```

Each `R_i` is a clique of order at most four, as in Section 3.  A group of
order four together with `q_i` is a fixed `K_5`, so every outside vertex has
at most one neighbour in it.  In particular, an exceptional vertex meeting
`q_i` is anticomplete to that large `R_i`.

The positive `Q`-degrees of the 21 vertices sum to 25, so their total excess
over one is four.  The partitions of four give exactly

```text
[5], [4,2], [3,3], [3,2,2], [2,2,2,2].
```

If there are `k` exceptionals there are `21-k` ordinary vertices.  Since
five ordinary groups have capacity four, distributing the deficit gives
exactly the following eight signatures:

| signature | exceptional `Q`-degrees | ordinary group sizes |
|---|---|---|
| `5` | `5` | `4,4,4,4,4` |
| `42` | `4,2` | `3,4,4,4,4` |
| `33` | `3,3` | `3,4,4,4,4` |
| `322_24444` | `3,2,2` | `2,4,4,4,4` |
| `322_33444` | `3,2,2` | `3,3,4,4,4` |
| `2222_14444` | `2,2,2,2` | `1,4,4,4,4` |
| `2222_23444` | `2,2,2,2` | `2,3,4,4,4` |
| `2222_33344` | `2,2,2,2` | `3,3,3,4,4` |

For every exceptional of degree at most four, at least one neighbour group
is deficient.  Otherwise all of its neighbour groups are large and the
greedy large-neighbour lemma of Section 6 gives an independent six-set.

There is one further inequality used in every machine branch and in the
last human count.  For `w in R_i`, the set
`Q'=(Q-{q_i}) union {w}` is independent.  By (6.1), `P(Q')>=25=P(Q)`, so

```text
d(w)>=d(q_i).
```

If `s_i` is the number of exceptionals meeting `q_i`, then
`d(q_i)=|R_i|+s_i`, while `w` has the edge to `q_i`, its `|R_i|-1` group
edges, and its edges to `W-R_i`.  Cancelling gives the **exchange inequality**

```text
d_(W-R_i)(w)>=s_i.                                         (8.1)
```

## 9. Exact `P=25`: seven replay-certified signatures

This section uses the direct package in
`lanes/p25_certificate/FULL_P25_REPORT.md`, whose exact standalone scope
passed fresh review in `review_queue/minority_p25_exclusion_review.md` at
commit `f017c57`.  The mathematical claim supplied by its direct portion is:

> **Certified seven-signature lemma.**  No graph satisfying (GAP), (7.7),
> and any one of the first seven signatures in the table of Section 8 exists.

Here is the full reduction and certificate semantics, so that the lemma is
not a black-box solver assertion.

For each signature, `lanes/p25_certificate/encode.py` labels the five
vertices of `Q`, the ordinary groups, and the exceptions.  It fixes exactly:

- all `Q`--`Q` nonedges;
- for every ordinary vertex, its unique `Q`-edge and its other four
  `Q`-nonedges;
- every within-`R_i` clique edge;
- each exceptional's displayed exact `Q`-degree;
- for each exceptional of degree at most four, the clause that it meets at
  least one deficient index.

Every other edge is a primary Boolean variable.  It adds only the following
necessary conditions.

1. Because `P=25` and `e(G)<=65`, one has `e(W)<=40`.  After subtracting
   the fixed within-group edges, a cardinality constraint bounds all flexible
   `W`-edges.
2. For every `w in R_i`, the direct comparison clauses encode (8.1): the
   number of exceptional neighbours of `q_i` is at most the number of
   `W-R_i` neighbours of `w`.
3. For every six-set without an already fixed edge, a positive clause says
   that at least one of its variable edges is present.  Six-sets with a fixed
   edge are already nonempty.
4. For every six-set containing a fixed clique
   `{q_i} union R_i`, a cardinality constraint bounds its edge count by 11.

The formula deliberately omits upper caps for unanchored six-sets and omits
other valid consequences, including completion edges.  Thus every actual
gap graph of the given signature produces a primary assignment satisfying
all these clauses.  The formula is a relaxation in the safe direction.

The primary cardinality encoding is a balanced forward totalizer.  If a
primary assignment obeys the intended bound, assign each totalizer output
according to the number of true input occurrences below it; this extends the
primary assignment to a CNF model.  Repeated weighted literals are retained
as separate occurrences.  The direct exact-degree and comparison clauses
are truth-function encodings without auxiliaries.  `encode.py --selftest`
exhaustively truth-tables these encodings on small inputs, including repeated
literals and every direct comparison shape used here.

For each of the seven signatures, CaDiCaL generated an ASCII LRAT derivation
of the empty clause from the full totalizer formula.  Dependency closure then
selected a subset of input clauses and densely renamed its variables.
CaDiCaL generated a **fresh** ASCII LRAT derivation for that compact CNF.
The committed `*.origin.json` reconstructs every compact clause, in order,
from the deterministically regenerated full formula.  Therefore compact
UNSAT implies full-formula UNSAT without trusting the core extractor.

The repository's strict RUP-LRAT checker replays every addition from live
positive hints, checks unit propagation/conflict and deletion discipline,
and requires a derived empty clause.  Consequently the LRAT files, together
with the deterministic CNF semantics above, prove the seven-signature lemma;
neither CaDiCaL's verdict nor its internal reasoning is trusted.

As fault-diversity checks, not additional axioms, each signature is also
regenerated using independently implemented Sinz sequential counters and
solved UNSAT by Kissat 4.0.4, and Kissat also solves every compact primary
CNF UNSAT.  Raising only the global edge cap from 65 to 66 makes the
`2222_23444` relaxation SAT in both encodings.  The stored primary model is
rescored without auxiliaries and has

```text
e(G)=66, P=25, e(W)=41, minimum six-set edge count=1,
maximum anchored six-set edge count=11, minimum exchange margin=0.
```

It has unanchored dense six-sets, exactly as this relaxation permits.  This
one-edge perturbation checks the load-bearing budget direction.

The covered list in the committed manifest is exactly

```text
5, 42, 33, 322_24444, 322_33444, 2222_14444, 2222_23444;
```

`2222_33344` is explicitly absent.  In particular, the
`2222_23444` formula ranges over all exceptional masks satisfying the exact
degree and deficient-hit clauses; it does not rely on an incomplete human
type classification.

Exact resource-capped regeneration and replay commands are:

```text
PYTHONDONTWRITEBYTECODE=1 python3 tools/run_capped.py \
  --max-rss-gib 4 --max-seconds 1800 -- \
  python3 lanes/p25_certificate/encode.py --selftest

PYTHONDONTWRITEBYTECODE=1 python3 tools/run_capped.py \
  --max-rss-gib 4 --max-seconds 1800 -- \
  python3 lanes/p25_certificate/certify_full_p25.py \
    --verify --kissat-on-verify --timeout 240

# Full regeneration of the primary proofs, secondary formulas, and SAT control:
PYTHONDONTWRITEBYTECODE=1 python3 tools/run_capped.py \
  --max-rss-gib 4 --max-seconds 1800 -- \
  python3 lanes/p25_certificate/certify_full_p25.py \
    --generate --timeout 240

# Durable source-level Mathlib replay of the seven committed LRATs, one Lean
# process at a time, followed by their axiom display:
cd lean
python3 ../tools/run_capped.py --max-rss-gib 8 --max-seconds 1800 -- \
  lake env lean Erdos617/P25Certificates/Pattern5.lean
python3 ../tools/run_capped.py --max-rss-gib 8 --max-seconds 1800 -- \
  lake env lean Erdos617/P25Certificates/Pattern42.lean
python3 ../tools/run_capped.py --max-rss-gib 8 --max-seconds 1800 -- \
  lake env lean Erdos617/P25Certificates/Pattern33.lean
python3 ../tools/run_capped.py --max-rss-gib 8 --max-seconds 1800 -- \
  lake env lean Erdos617/P25Certificates/Pattern322_24444.lean
python3 ../tools/run_capped.py --max-rss-gib 8 --max-seconds 1800 -- \
  lake env lean Erdos617/P25Certificates/Pattern322_33444.lean
python3 ../tools/run_capped.py --max-rss-gib 8 --max-seconds 1800 -- \
  lake env lean Erdos617/P25Certificates/Pattern2222_14444.lean
python3 ../tools/run_capped.py --max-rss-gib 8 --max-seconds 1800 -- \
  lake env lean Erdos617/P25Certificates/Pattern2222_23444.lean
python3 ../tools/run_capped.py --max-rss-gib 8 --max-seconds 1800 -- \
  lake env lean P25CertificatesAxiomAudit.lean
cd ..
```

The committed manifest is `lanes/p25_certificate/full_p25_manifest.json`; the
review records its SHA-256 as
`028eefead2cb883ffd3f47e64ae5a3a005f3442417c9178f4b010c4e63626a75`.
The compact proof artifacts are under
`lanes/p25_certificate/certificates/full_p25/`.

The fresh review regenerated all seven compact CNFs and LRATs byte-for-byte.
Timing-bearing JSON fields make a newly generated manifest file's hash
nondeterministic; no soundness claim depends on those timing fields.  Formula
hashes, origins, proofs, and substantive metadata reproduced.

## 10. Exact `P=25`: the eighth signature

It remains to exclude `2222_33344`.  Let the deficient ordinary groups be
`S_0,S_1,S_2`, each of order three, and the large groups have indices 3,4.
Let `X` be the four degree-two exceptions.  Put

```text
s_i = number of exceptions adjacent to q_i,
l   = s_3+s_4,
b   = e(X,S_0 union S_1 union S_2),
c   = e(X).
```

Every exception meets a deficient index by the large-neighbour lemma.  If
its other neighbour is one of `q_3,q_4`, the completion lemma makes it
complete to the corresponding deficient `S_i`.  Restricting (GAP) to the
18-vertex core `Q union S_0 union S_1 union S_2 union X` gives all the
premises of the following reviewed finite lemma.

> **Three-`K_3` defect lemma.**  Under those premises,
> `l+b+2c>=15`.

For completeness, this lemma is itself not a bare solver verdict.  There are
nine possible degree-two `Q`-masks: all pairs except `{q_3,q_4}`.  The action
of permutations of the three deficient indices, the two large indices, and
the four exceptions has exactly 58 orbits on all `9^4=6561` labelled mask
assignments.  `mask_orbits.json` lists them, and the independent review also
verified the count by Burnside's lemma.

For each orbit, `defect_lemma.py` fixes precisely the three anchored `K_4`s,
the exact masks, and the required mixed-mask completion edges.  Every other
core edge is a primary variable.  It encodes the exact 1--11 window for all
`C(18,6)=18564` core six-sets and the negation
`l+b+2c<=14`, counting each `X`--`X` literal twice.  A forward-totalizer CNF
for every orbit has a compact ASCII LRAT proof accepted by the strict replay
checker.  Origin maps reconstruct the compact clauses from regenerated full
formulas.  Separate sequential-counter formulas are freshly UNSAT under
Kissat.  Mathlib's `lrat_proof` command also elaborates all 58 committed
CNF/proof pairs with only its standard axiom profile.  Raising just the
six-set cap to 12 gives a stored model whose direct rescore is

```text
minimum=1, maximum=12, l=0, b=10, c=2, l+b+2c=14.
```

The exact resource-capped replay and regeneration commands are:

```text
PYTHONDONTWRITEBYTECODE=1 python3 tools/run_capped.py \
  --max-rss-gib 4 --max-seconds 1800 -- \
  python3 lanes/p25_certificate/encode.py --selftest
PYTHONDONTWRITEBYTECODE=1 python3 tools/run_capped.py \
  --max-rss-gib 4 --max-seconds 1800 -- \
  python3 lanes/p25_certificate/certify_defect.py \
    --verify --kissat-on-verify --timeout 240

# Full regeneration of all 58 compact proofs and both full encodings:
PYTHONDONTWRITEBYTECODE=1 python3 tools/run_capped.py \
  --max-rss-gib 4 --max-seconds 1800 -- \
  python3 lanes/p25_certificate/certify_defect.py \
    --generate --timeout 240

# Durable Mathlib replay of all 58 committed LRATs:
cd lean
python3 ../tools/run_capped.py --max-rss-gib 8 --max-seconds 1800 -- \
  lake env lean ../lanes/p25_certificate/MathlibReplay.lean
cd ..
```

Now sum (8.1) over all ordinary vertices.  Since
`sum_i s_i=8`, the total ordinary incidence to vertices outside its own
group is at least

```text
3(s_0+s_1+s_2)+4(s_3+s_4)=3(8-l)+4l=24+l.                 (10.1)
```

Let `R` be the number of `W`-edges other than the 21 internal edges of the
three `K_3`s and two `K_4`s.  Let `a` count cross-group ordinary--ordinary
edges and let `t` count exception--ordinary edges into the two large groups.
Then

```text
ordinary external incidence D=2a+b+t,
R=a+b+t+c,
2R=D+b+t+2c.
```

Therefore, using (10.1) and the defect lemma,

```text
2R=D+b+t+2c
  >= D+b+2c
  >= (24+l)+b+2c
  >=39.
```

Thus `R>=20`.  But the global edge budget and `P=25` give

```text
R<=65-25-21=19,
```

a contradiction.  The eighth and final signature is impossible.

Sections 8--10 exclude every possible exact-`P=25` gap graph.  Together with
Sections 2--7, this gives the candidate conclusion that no gap graph exists
and therefore no balanced five-colouring of `K_26` exists.  The fresh review
in `review_queue/full_r5_proof_review.md` independently checked and passed
this complete composition.

## 11. The exact value `N(5)=25`

The lower bound is explicit.  Take the 25 vertices of the affine plane
`F_5^2`.  The six direction classes are the five finite slopes and the
vertical direction.  Give the four nonzero finite slopes colours 1,2,3,4,
and merge the horizontal and vertical classes into colour 0.

Each direction class partitions the 25 points into five parallel lines.
For each direction class, among any six points some pair (depending on the
class) lies on the same line.
Thus every six-set contains an edge of each of colours 1--4 and contains an
edge of colour 0 (indeed one horizontal and one vertical pair).  This is a
balanced colouring of `K_25`.  The committed certificate is
`data/candidates/affine_k25_r5.json`; the independent referee command is

```text
python3 tools/verify.py data/candidates/affine_k25_r5.json
```

and reports that all 177,100 six-sets see all five colours.

Balancedness is inherited by restrictions to vertex subsets.  Hence a
balanced colouring on any order at least 26 would restrict to a balanced
`K_26`, which the preceding argument excludes.  Therefore the candidate
theorem gives `N(5)=25`.

## 12. Verification ledger and review record

The human components have already passed separate fresh reviews:

- minority reduction and initial structure:
  `review_queue/minority_structural_reductions_review.md`;
- exact `P=22,23,24` exclusions:
  `review_queue/minority_p22_exclusion_review.md`,
  `review_queue/minority_p23_exclusion_review.md`, and
  `review_queue/minority_p24_exclusion_review.md`;
- optimized stability `P<=25` and both literature specializations:
  `review_queue/stability_boundary25_review.md`;
- the isolated three-`K_3` defect certificate:
  `review_queue/p25_defect_certificate_review.md`.
- the standalone exact-`P=25` exclusion, with universal boundary at least 25
  as an explicit premise:
  `review_queue/minority_p25_exclusion_review.md` (commit `f017c57`).

During assembly on 2026-07-11, the author also reran the following checks.
Their current resource-capped forms are:

```text
python3 tools/verify.py --selftest
python3 tools/verify.py data/candidates/affine_k25_r5.json
PYTHONDONTWRITEBYTECODE=1 python3 tools/run_capped.py \
  --max-rss-gib 4 --max-seconds 1800 -- \
  python3 lanes/p25_certificate/encode.py --selftest
PYTHONDONTWRITEBYTECODE=1 python3 tools/run_capped.py \
  --max-rss-gib 4 --max-seconds 1800 -- \
  python3 lanes/p25_certificate/certify_full_p25.py \
    --verify --kissat-on-verify --timeout 240
```

All four commands exited zero; the last replayed all seven direct branches
and independently rescored the 66-edge control.  These reruns do not replace
the cited fresh reviews.

The fresh adversarial review in `review_queue/full_r5_proof_review.md` checked
in particular:

1. that the minority-colour thresholds are exactly 0 and 12;
2. that (6.1) applies to every independent five-set, making the exchange
   inequality legitimate;
3. the regular branch and every equality case in Section 7;
4. exhaustiveness of the eight signatures;
5. that every actual graph extends to each CNF encoding and that compact
   clause origin/replay is in the sound direction;
6. the `2R` accounting in Section 10; and
7. that the affine construction plus restriction monotonicity really gives
   the exact value, not merely a lower bound.

The review verdict is PASS for the complete informal argument.  This file
remains a reviewed candidate awaiting independent external scrutiny, never a
self-certified result or a claim of “proof complete.”
