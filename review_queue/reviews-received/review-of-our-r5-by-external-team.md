# Team B adversarial review of external candidate A

Date: 2026-07-13

## Scope and method

This review covers PROBLEM.md and all three documents in
review_queue/external-candidate-A: candidate-chain.md, candidate-lemma-1.md, and
candidate-lemma-2.md. It audits the pinned definition of balance, all
\(K_{25}\)/\(K_{26}\) transitions, quantifiers, empty colours, arithmetic,
literature use, and circularity. The Kang--Pikhurko paper cited by candidate
Lemma 1 was read at the supplied URL. No Lean command or solver was run.

This is a verdict on a candidate proof package, not a claim that publication or
external scrutiny is complete.

## Executive verdicts

### Chain

**SURVIVES (as a conditional deduction).** The theorem in
candidate-chain.md:30-67 follows from [MH″] and [MM] exactly as stated. There is
no \(K_{25}\)/\(K_{26}\) mismatch, hidden surjectivity assumption, or quantifier
reversal.

The document retains historical labels saying the hypotheses are pending at
candidate-chain.md:18-28, although its header at candidate-chain.md:3-9 says
they were later discharged. This is a presentation inconsistency only.

### Lemma 1 / [MH″]

**SURVIVES, with explicit expansions required for publication.** The argument
rules out a balanced \(K_{25}\) colouring with a colour \(c\) and four-set
\(T\) satisfying \(\alpha(G_c-T)\le4\). The strongest compressed step,
candidate-lemma-1.md:369-385, has a valid elementary expansion below. The
minimum-degree step at candidate-lemma-1.md:431-461 also extends to degrees
below four.

The stronger 21-vertex statement at candidate-lemma-1.md:3-10 does not need a
separate cap-11 hypothesis. The bounds \(\alpha(G_i)\le5\) for all five colours
already imply that every six-set contains every colour, hence cap-11. The later
header weakening at candidate-lemma-1.md:853-857 is harmless but unnecessary.

### Lemma 2 / [MM]

**SURVIVES under this review's granted-machine-fact protocol, provided the
document's adopted \(r=7\) repair is integrated.** The weighted
one-\(K_5\) argument and the two-\(K_5\) unhit-edge argument survive independent
audit. The main body stops after identifying the \(r=7\) weight vector at
candidate-lemma-2.md:539-548. The missing contradiction is supplied at
candidate-lemma-2.md:783-807 and adopted at candidate-lemma-2.md:837-844.
With that paragraph treated as part of the proof, the case closes. It must be
inserted into the main proof for publication. If only the main body through
line 656 were submitted, the verdict would instead be **GAP, patchable** at
the \(r=7\) branch. Per the requested protocol, the stated finite/SAT facts
are treated as given rather than replayed in this review.

## Weakest point

After integrating the \(r=7\) paragraph, the weakest load-bearing dependency is:

> No graph on 11 vertices has \(\alpha\le2\) while every six-set spans at most
> 11 edges.

Lemma 2 uses this at candidate-lemma-2.md:296-305,
candidate-lemma-2.md:396-402, and candidate-lemma-2.md:800-806. The candidate
reports multiple SAT checks and DRAT certificates at
candidate-lemma-2.md:698-704 and candidate-lemma-2.md:846-847, but the prose
does not identify exact CNF/proof files, hashes, checker version, and commands.
That is a publication-auditability weakness, not a mathematical gap under the
requested granted-fact protocol and not a discovered counterexample.

The weakest handwritten inference is the compressed two-\(K_5\) step at
candidate-lemma-1.md:375. It is sound after the expansion below.

## Expansion 1: chain fibres and exact size

Fix \(x\) in a hypothetical balanced colouring of \(K_{26}\), put
\(V'=V\setminus\{x\}\), and define

\[
T_c=\{v\in V':\chi(xv)=c\}.
\]

The five sets \(T_c\) are fibres of one function, so they partition 25 vertices
(candidate-chain.md:32-36). If \(F\subseteq V'\setminus T_c\) were an
independent five-set in \(G_c\), then \(F\cup\{x\}\) would have no \(c\)-edge:
there is none inside \(F\), and none on a spoke from \(x\) to \(F\). Thus

\[
\alpha(G_c-T_c)\le4
\]

for every colour, as claimed at candidate-chain.md:38-41.

If \(|T_c|\le4\), enlarge it to a four-set \(T_c^+\). Deleting more vertices
cannot increase independence number, so
\(\alpha(G_c-T_c^+)\le4\), contradicting [MH″]. Hence every fibre has size at
least five. Five such fibres sum to 25, so all have size exactly five
(candidate-chain.md:50-54).

For \(c\ne c'\), the five-set \(T_{c'}\) is disjoint from \(T_c\). If it had no
edge of colour \(c\), it would be an independent five-set in \(G_c-T_c\).
Consequently \(T_{c'}\) contains an edge of each of the four colours different
from \(c'\). Those four edges are distinct, so at most \(10-4=6\) of its edges
have colour \(c'\) (candidate-chain.md:56-61). Taking \(c'=m\), a minority
colour on \(K_{25}\), matches every premise of [MM].

This is why exact fibre size five is indispensable.

## Expansion 2: Kang--Pikhurko equality translation and \(21>20\)

For an ordinary colour \(F_i\) on the 21-vertex set \(S\), an
\(F_i\)-\(K_5\) would be an independent five-set in the special graph \(H\).
Thus \(\omega(F_i)\le4\). Put \(J_i=\overline{F_i}\). Then \(J_i\) is
\(K_6\)-free, \(\alpha(J_i)=\omega(F_i)\le4\), and it is not 5-partite:
five independent parts in \(J_i\) would each have size at most four and cover
at most \(5\cdot4=20<21\) vertices.

The cited theorem therefore gives

\[
e(J_i)\le t_5(21)-\left\lfloor\frac{21}{5}\right\rfloor+1
=176-4+1=173,
\]

so \(e(F_i)\ge37\), as at candidate-lemma-1.md:61-81. The source's Theorem 4
and Lemma 5 give precisely these equality vectors on the 20 old vertices:

\[
(4,4,4,4,4),\qquad(3,4,4,4,5),\qquad(3,3,4,5,5).
\]

The latter two contain an \(F_i\)-\(K_5\), so only the all-four vector survives.

For the equality construction, call the old parts \(N_1,\ldots,N_5\), the
added vertex \(x\), the distinguished vertex in \(N_2\) \(y\), and the
nonempty proper source subset of \(N_1\) \(C\). In the complement \(F_i\), set

\[
A=N_2\cup\{x\},\qquad B=N_1.
\]

Then \(F_i[A]=K_5-xy\), \(F_i[B]=K_4\), and the \(F_i\)-edges across \(A,B\)
are \(x(N_1\setminus C)\) and \(yC\), exactly
\((4-|C|)+|C|=4\) edges. This validates candidate-lemma-1.md:85-104 for every
permitted \(|C|\).

The missing edge \(xy\) must have special colour \(H\), or \(A\) would be
\(H\)-independent. For each of the other three ordinary colours \(j\ne i\),
every \(B\cup\{a,a'\}\) must contain a \(j\)-edge. Since \(B\) is an
\(i\)-clique and \(xy\) is an \(H\)-edge, this forces at least four
\(j\)-edges across \(A,B\). Since \(B\) is \(H\)-independent, every
\(a\in A\) must have an \(H\)-neighbour in \(B\), forcing at least five
\(H\)-edges across. The 20 cross-edges would contain at least

\[
4+3\cdot4+5=21
\]

colour-disjoint edges. This contradiction, at
candidate-lemma-1.md:105-134, upgrades the lower bound to \(e(F_i)\ge38\).

The cited Kang--Pikhurko source supports the bound and equality construction.
If the text continues to call the bound Brouwer's theorem, it needs a separate
Brouwer citation.

## Expansion 3: Lemma 1's two-\(K_5\) step

Suppose \(Q,R\) are disjoint \(H\)-\(K_5\)'s and \(L\) is the remaining
11-set, as at candidate-lemma-1.md:353-385. Cap-11 implies that every vertex
outside a fixed \(H\)-\(K_5\) has at most one neighbour in it.

If \(S\subseteq L\) were an independent triple, at least two vertices of each
of \(Q,R\) would avoid all of \(S\). The \(Q\)-\(R\) graph is a matching, so
the two avoider sets cannot be completely joined. Choose a nonadjacent pair
\(q\in Q,r\in R\). Then \(S\cup\{q,r\}\) is an independent five-set,
contrary to \(\alpha(H)\le4\). Thus \(\alpha(H[L])\le2\).

If \(L\) contained a third \(K_5=P\), let \(D\) be the six vertices outside
\(Q\cup R\cup P\). If \(u,v\in D\) were nonadjacent, choose vertices
successively from \(Q,R,P\), each avoiding \(u,v\) and all earlier choices.
At the three stages at most \(2,3,4\) vertices of the current five-clique are
forbidden, so each choice is possible. The resulting five vertices are
independent, again contradicting \(\alpha(H)\le4\). Hence \(D\) would have to
be a \(K_6\), violating cap-11. Therefore \(\omega(H[L])\le4\).

This supplies the claims compressed into candidate-lemma-1.md:375 and permits
the original \(M(11)\ge35\) argument. Lemma 1 does not require the stronger
clique-number-free 11-vertex SAT primitive used by Lemma 2.

The minimum-degree conclusion also covers \(d_H(v)<4\). Then \(W_v\) has more
than 16 vertices; select any 16. On that \(K_{16}\), the special graph has at
least 46 edges and every ordinary graph at least 20, totalling
\(46+4\cdot20=126>\binom{16}{2}=120\).

## Expansion 4: closing Lemma 2's \(r=7\) case

After eliminating unhit edges, every \(ij\in E(F)\) satisfies

\[
d_i+d_j\ge6,
\]

and \(D=\sum_i d_i\le r+5\) (candidate-lemma-2.md:523-535).

For \(r=7\), the seven-edge graph \(F\) contains two disjoint edges, so these
inequalities force \(D\ge12\); the budget forces \(D=12\). The finite
classification used here is that, up to order, the only nonnegative
five-tuple of total 12 with at least seven pair-sums at least six is

\[
(0,0,0,6,6).
\]

The seven eligible pairs are the high--high pair and the six high--zero
pairs, so all seven lie in \(F\). Choose a weight-six vertex \(t_i\) and a
weight-zero vertex \(t_j\). Their \(F\)-edge is hit, so

\[
B-(Z_i\cup Z_j)=B-Z_i
\]

is a clique. It has \(10-6=4\) vertices and is a \(K_4\).

Now \(X=B\cup\{t_i\}\) has 11 vertices and \(\alpha(X)\le2\). An independent
triple cannot lie in \(B\), because \(\alpha(B)\le2\). A triple containing
\(t_i\) would have its other two vertices in \(B-Z_i=K_4\), so they would be
adjacent. Cap-11 is inherited. Thus \(X\) is the forbidden 11-vertex
\(\alpha\le2\) cap-11 graph. This is the closure at
candidate-lemma-2.md:783-807, adopted at candidate-lemma-2.md:837-844.

It must be inserted after candidate-lemma-2.md:541-548.

## Remaining audit checks

### Definitions and empty colours

PROBLEM.md:16-18 permits a non-surjective colouring. Neither proof assumes
surjectivity independently. Balance forces every colour on every six-set, and
the 21-vertex independence formulation has the same effect. The colour graphs
partition all edges even before this consequence is used.

### Ambient vertex set

All \(G_c\), \(T_c\), [MH″], and [MM] data live on the same 25-vertex
restriction. Only candidate-chain.md:38-41 uses the deleted vertex \(x\) and
the full \(K_{26}\), to prove \(\alpha(G_c-T_c)\le4\).

### Arithmetic

The following were independently recomputed arithmetically:

- \(t_5(21)=176\), \(t_5(16)=102\), and \(t_5(15)=90\);
- the corresponding non-5-partite bounds \(173,100,88\);
- all eight \(L(s)\) affine conclusions in candidate-lemma-1.md:291-313;
- the complete \(\Psi\)-slack sequence in candidate-lemma-1.md:333-345;
- the equality triples at candidate-lemma-1.md:508-512;
- all edge totals in the chain and expansions above.

No discrepancy was found.

### Circularity

The dependency direction is

\[
\text{Kang--Pikhurko and finite graph bounds}
\longrightarrow
\begin{cases}
\text{Lemma 1 / [MH″]},\\
\text{Lemma 2 / [MM]},
\end{cases}
\longrightarrow
\text{extension-obstruction chain}.
\]

Lemma 1 does not use [MM]. Lemma 2 imports the \(M/L\) toolkit and the stronger
11-vertex primitive, but not Lemma 1's conclusion.

## Exact requirements before publication

1. **Integrate the \(r=7\) repair.** Insert candidate-lemma-2.md:783-807
   immediately after candidate-lemma-2.md:541-548. A load-bearing case closure
   cannot remain solely in an appended review.

2. **Define T2--T5 before Lemma 2 first uses them.** State:

   - **T2:** \(\sum_v e(G[W_v])=n e(G)-\sum_vd_v^2+3\tau(G)\);
   - **T3:** the cap-11 bound
     \(e(G[N(v)])\le\lfloor3d(v)(d(v)-1)/10\rfloor\) for \(d(v)\ge5\),
     with its small-degree convention;
   - **T4:** every \(M(s)\), \(L(s)\), clique-number condition, and the
     separate 11-vertex nonexistence primitive;
   - **T5:** a vertex outside a cap-11 \(K_5\) has at most one neighbour in
     it, so cross-graphs between disjoint \(K_5\)'s are matchings.

3. **Give certificate-grade identifiers for every finite/SAT primitive.**
   For the clique-number-free 11-vertex statement, record:

   - its exact mathematical statement and encoding direction;
   - generator path and exact command;
   - static CNF path, size, counts, and SHA-256;
   - DRAT/LRAT path, size, and SHA-256;
   - checker name/version, exact command, exit status, and output;
   - an explicit confirmation that the encoding has \(\alpha\le2\), cap-11,
     and no clique-number hypothesis.

   Apply the same standard to any \(M(9)\), \(M(10)\), arithmetic, or
   weight-vector fact described as machine-verified. Preserve the distinction
   that the 9- and 10-vertex minima require \(\omega\le4\), while the
   11-vertex nonexistence primitive is clique-number-free.

4. **Make the \(r=7\) weight classification checkable.** Give a short
   exhaustive hand lemma for \((0,0,0,6,6)\), or identify the enumeration
   script, command, output, and hash.

5. **Clarify Lemma 1's standing hypotheses.** Sections 4.1 and 4.2,
   candidate-lemma-1.md:195-313, should state that all graphs and induced
   graphs in the recursion are cap-11. If retaining the stronger 21-vertex
   theorem, add one sentence explaining why its independence bounds imply
   balance and cap-11.

6. **Expand Lemma 1's terse steps.** Insert the two-\(K_5\) argument above at
   candidate-lemma-1.md:375, and state explicitly that \(d_H(v)\le4\) is
   handled by a 16-subset of \(W_v\).

7. **Cite Brouwer separately or change attribution.** Kang--Pikhurko supports
   the bound and equality classification used. If calling the bound Brouwer's
   theorem, provide Brouwer's full original citation separately and cite
   Kang--Pikhurko for equality. Otherwise call it the Kang--Pikhurko theorem
   and explain the historical antecedent. State the exact hypotheses
   \(K_{r+1}\)-free, \(\chi>r\), and \(n\ge2r+1\).

8. **Normalize status language.** Replace the historical pending labels in
   candidate-chain.md:18-28 with exact references to the reviewed lemmas and
   certificate records. Retain the repository's status language: reviewed
   candidate awaiting external scrutiny, not a unilateral claim of proof
   completion.

## Findings ledger

- **FATAL:** none found in the chain or either lemma. None remains in the full
  Lemma 2 document when its adopted \(r=7\) repair is integrated and the
  finite/SAT statements are granted as required by this review protocol.
- **PUBLICATION-BLOCKING:** the \(r=7\) closure is absent from Lemma 2's main
  body; machine primitives lack exact certificate identifiers; T2--T5 are not
  self-containedly defined; Brouwer lacks a separate citation despite the
  attribution.
- **FIXABLE EXPOSITION:** Lemma 1's two-\(K_5\) and degree-\(\le4\) steps are
  too compressed; its cap-11 recursion hypothesis should be explicit.
- **COSMETIC:** historical status wording and the unnecessary weakening of
  Lemma 1's opening statement.

## Final disposition

**THE THREE-DOCUMENT CANDIDATE SURVIVES TEAM B'S ADVERSARIAL REVIEW, SUBJECT TO
THE PUBLICATION-BLOCKING INTEGRATIONS ABOVE.** The chain is a sound implication;
Lemma 1 is sound after expanding two compressed arguments; and Lemma 2 is sound
with the adopted \(r=7\) paragraph treated as part of the proof. The principal
remaining publication task is identifier-level documentation of the finite
certificates on which Lemma 2 relies; their statements were granted for this
review as instructed.
