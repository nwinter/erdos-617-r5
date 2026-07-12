# Proof of [MM]

The claim is true.

A small toolkit caveat first: the phrase “any clique number” in the \(\alpha\le2\) part of (T4) cannot literally apply to the stated 9- and 10-vertex minima, since \(K_5\sqcup K_4\) and \(K_5\sqcup K_5\) are counterexamples. Below, every use of those \(\alpha\le2\) results occurs after \(\omega\le4\) has been established. When an added vertex could create a \(K_5\), that possibility is handled separately.

Assume for contradiction that \(G,T\) satisfy (a)–(d). Put

\[
H=G-T,\qquad m=e(H),\qquad x=e_G(T,H),\qquad s=e(G[T]).
\]

Then

\[
|H|=20,\qquad \alpha(H)\le4,\qquad s\le6,\qquad m+x+s\le60. \tag{1}
\]

Let

\[
r=10-s\ge4
\]

be the number of nonedges of \(G[T]\).

## 1. Peeling disjoint \(K_5\)’s from \(H\)

Suppose \(Q_1,\dots,Q_k\) are disjoint \(K_5\)’s in \(H\), and put

\[
R=H-\bigcup_{i=1}^k Q_i.
\]

Then

\[
\alpha(R)\le4-k. \tag{2}
\]

Indeed, if \(S\subseteq R\) were independent with \(|S|=5-k\), choose \(q_i\in Q_i\) successively so that all chosen vertices remain independent. At step \(i\), the vertices of \(S\) forbid at most \(5-k\) vertices of \(Q_i\), and \(q_1,\dots,q_{i-1}\) forbid at most \(i-1\), by (T5). Thus at most

\[
(5-k)+(i-1)\le4
\]

vertices of \(Q_i\) are forbidden, so \(q_i\) can be chosen. This gives an independent 5-set in \(H\), contradicting \(\alpha(H)\le4\).

Consequently, the maximum number of disjoint \(K_5\)’s in \(H\) is one of

\[
0,\ 1,\ 2,\ 4. \tag{3}
\]

Indeed, three disjoint \(K_5\)’s leave five vertices whose independence number is at most one by (2), so those five vertices form a fourth \(K_5\).

We eliminate these four cases.

## 2. \(H\) is \(K_5\)-free

For \(v\in H\), write \(d_v=d_H(v)\) and

\[
W_v=H\setminus N_H[v].
\]

Then \(|W_v|=19-d_v\), and \(\alpha(H[W_v])\le3\): otherwise \(v\) together with an independent 4-set in \(W_v\) would be an independent 5-set in \(H\).

Define \(\ell(q)\) by the \(L\)-table for \(13\le q\le19\), and by the ordinary complement-Turán bound

\[
\ell(q)=\binom q2-t_3(q)
\]

for \(q\le12\). Thus, indexed by \(d=0,\dots,19\),

\[
\ell(19-d)=
(73,62,53,46,38,31,24,18,15,12,9,7,5,3,2,1,0,0,0,0). \tag{4}
\]

Because \(H\) is \(K_5\)-free, every \(H[W_v]\) has \(\omega\le4\), so

\[
e(H[W_v])\ge \ell(19-d_v). \tag{5}
\]

Let

\[
f(d)=
\begin{cases}
\binom d2,&d\le4,\\[2mm]
\left\lfloor\frac{3d(d-1)}{10}\right\rfloor,&d\ge5.
\end{cases}
\]

By (T2) and (T3),

\[
\begin{aligned}
\sum_v \ell(19-d_v)
&\le \sum_v e(H[W_v])\\
&=20m-\sum_vd_v^2+\sum_v e(H[N(v)])\\
&\le20m-\sum_vd_v^2+\sum_v f(d_v).
\end{aligned}
\]

Since \(20m=10\sum_vd_v\), this says

\[
\sum_v g(d_v)\le0, \tag{6}
\]

where

\[
g(d)=\ell(19-d)+d^2-f(d)-10d.
\]

Direct substitution gives, for \(d=0,\dots,19\),

\[
2g(d)+17d-84=
(62,39,22,11,0,1,0,5,18,33,50,73,100,129,162,197,236,281,328,377).
\]

Every entry is nonnegative, hence

\[
g(d)\ge42-\frac{17}{2}d.
\]

Using (6),

\[
0\ge\sum_vg(d_v)
\ge20\cdot42-\frac{17}{2}\sum_vd_v
=840-17m.
\]

Therefore

\[
m\ge50. \tag{7}
\]

Now fix a nonedge \(tt'\) of \(G[T]\), and put

\[
U_{tt'}=N_H(t)\cup N_H(t').
\]

Then

\[
\alpha(H-U_{tt'})\le3, \tag{8}
\]

since an independent 4-set there, together with \(t,t'\), would be an independent 6-set in \(G\).

Double-counting the sets \(U_{tt'}\) over the \(r\) nonedges of \(T\) gives

\[
\sum_{tt'}|U_{tt'}|
\le\sum_{tt'}\bigl(d_H(t)+d_H(t')\bigr)
\le4x. \tag{9}
\]

We split according to \(m\).

- If \(m\ge53\), then \(|U_{tt'}|\ge3\) for every nonedge \(tt'\). Otherwise \(H-U_{tt'}\) contains an 18-vertex induced subgraph with \(\alpha\le3,\omega\le4\), forcing at least \(L(18)=62\) edges. Hence, using (1),

  \[
  3r\le4x\le4(50+r-m)\le4(r-3),
  \]

  so \(r\ge12\), impossible.

- If \(m=51\) or \(52\), then \(|U_{tt'}|\ge4\), since a residual 17-set would require \(L(17)=53\) edges. Thus

  \[
  4r\le4x,
  \]

  but

  \[
  x\le50+r-m<r,
  \]

  a contradiction.

- Suppose \(m=50\). First, \(\delta(H)\ge3\). Indeed, if \(d(v)\le2\), then

  \[
  m\ge d(v)+L(19-d(v))\ge\min\{73,63,55\}>50.
  \]

  If some \(|U_{tt'}|\le4\), enlarge it to a 4-set \(U\). Then \(H-U\) has at least \(L(16)=46\) edges. The number of edges incident with \(U\) is at least

  \[
  \sum_{u\in U}d(u)-e(H[U])
  \ge12-\binom42=6.
  \]

  Hence \(m\ge46+6=52\), contradiction. Therefore every \(|U_{tt'}|\ge5\). From (9),

  \[
  5r\le4x.
  \]

  But (1) gives \(x\le r\), so \(5r\le4r\), impossible.

Thus \(H\) cannot be \(K_5\)-free.

## 3. Four disjoint \(K_5\)’s

Write

\[
H=Q_1\cup Q_2\cup Q_3\cup Q_4,
\qquad Q_i\cong K_5.
\]

By (T5), every \(H[Q_i,Q_j]\) is a matching, and every \(t\in T\) has at most one neighbor in each \(Q_i\).

Choose a nonedge \(tt'\) of \(G[T]\), which exists because \(s\le6\). Put

\[
A_i=Q_i\setminus\bigl(N(t)\cup N(t')\bigr).
\]

Then \(|A_i|\ge3\). There is no independent transversal of \(A_1,\dots,A_4\), since such a transversal together with \(t,t'\) would be independent of size six.

We use the following elementary fact.

> If four parts have size at least three, every bipartite graph between two parts is a matching, and there is no independent transversal, then every vertex of every part has a neighbor in each other part.

To prove it, suppose \(v\in A_i\) has no neighbor in \(A_j\). In each of the other two parts delete the at-most-one neighbor of \(v\); at least two vertices remain in each. The matching between these two residual sets cannot cover all pairs, so choose nonadjacent vertices \(y,z\), both also nonadjacent to \(v\). The vertices \(y,z\) forbid at most two vertices of \(A_j\), while \(v\) forbids none. Since \(|A_j|\ge3\), a fourth vertex can be chosen, yielding an independent transversal.

Therefore each of the six bipartite graphs \(H[A_i,A_j]\) contains at least three edges. Hence

\[
e(H)\ge4\binom52+6\cdot3=58. \tag{10}
\]

By (1),

\[
s+x\le2. \tag{11}
\]

A graph on five vertices with at most two edges contains an independent triple \(P\). Delete from \(Q_1,Q_2,Q_3\) all neighbors of \(P\). By (11), at most two vertices are deleted in total, so at least three remain in each clique. Since the cross-graphs are matchings, an independent transversal of these three residual parts can be chosen greedily. Together with \(P\), it gives an independent 6-set in \(G\), contradiction.

Thus four disjoint \(K_5\)’s are impossible.

## 4. Exactly one \(K_5\)

Let \(Q\cong K_5\) be the unique \(K_5\), and put \(R=H-Q\). By (2),

\[
|R|=15,\qquad \alpha(R)\le3,\qquad \omega(R)\le4.
\]

Hence, by (T4),

\[
e(R)=38+b,\qquad b\ge0. \tag{12}
\]

Put

\[
p=e(Q,R).
\]

By (T5), each \(r\in R\) has at most one neighbor in \(Q\).

For \(t_i\in T\), let \(q_i\) denote its possible neighbor in \(Q\), put

\[
Z_i=N_R(t_i),\qquad d_i=|Z_i|,
\]

let \(a\) be the number of defined \(q_i\)’s, and put \(D=\sum_i d_i\). The edge budget is

\[
b+p+a+D+s\le12. \tag{13}
\]

Let \(F\) be the graph of nonedges of \(G[T]\), so \(e(F)=r=10-s\ge4\).

For \(ij\in E(F)\):

- If \(q_i,q_j\) are not two distinct vertices of \(Q\), then

  \[
  \alpha\bigl(R-(Z_i\cup Z_j)\bigr)\le2.
  \]

  Otherwise an independent triple there, together with \(t_i,t_j\), has at most four neighbors in \(Q\), so a missed vertex of \(Q\) completes an independent 6-set. Since the residual graph has \(\omega\le4\), (T4) implies it has at most ten vertices. Therefore

  \[
  d_i+d_j\ge5. \tag{14}
  \]

- If \(q_i,q_j\) are distinct, let \(P\subseteq R\) be the vertices having a neighbor in \(Q\). Then \(|P|=p\). Applying the same argument inside \(R-(Z_i\cup Z_j\cup P)\) gives

  \[
  d_i+d_j+p\ge5. \tag{15}
  \]

We now perform a small weighted count. Call a vertex of \(T\) marked if it has a \(Q\)-neighbor. Let \(h\) be the number of \(F\)-edges joining marked vertices with distinct \(Q\)-neighbors. Summing (14)–(15),

\[
\sum_{ij\in E(F)}(d_i+d_j)
\ge5r-\min(p,5)h.
\]

On the other hand,

\[
\sum_{ij\in E(F)}(d_i+d_j)
=\sum_i d_i d_F(i)\le4D,
\]

and

\[
h\le\min\left\{r,\binom a2\right\}.
\]

From (13),

\[
D\le r+2-p-a.
\]

Consequently a necessary condition is

\[
5r-\min(p,5)\min\left\{r,\binom a2\right\}
\le4(r+2-p-a). \tag{16}
\]

Elementary substitution in (16) gives:

- if \(a\le1\), then \(p+a\le1\);
- \(a=2,3,4\) is impossible;
- if \(a=5\), the only possibilities are

  \[
  (p,r)=(4,10),\quad
  p=5,\ r\ge8,\quad
  p=6,\ r\ge9,\quad
  p=7,\ r=10. \tag{17}
  \]

For completeness, when \(a=2\), (16) gives \(r\le\min(p,5)-4p\); when \(a=3\), it gives \(r\le3\min(p,5)-4p-4\). For \(a=4\), separating \(r\le6\) and \(r\ge7\) gives no \(r\ge4\). For \(a=5\), (16) becomes

\[
(5-\min(p,5))r\le4(r-p-3),
\]

which gives exactly (17).

The case \((p,a,r)=(4,5,10)\) is impossible: every pair of \(T\) has weight-sum at least one, so at most one \(d_i\) is zero and \(D\ge4\); but (13) gives \(D\le3\).

Two possibilities remain.

### 4.1 \(p+a\le1\)

Every \(F\)-edge satisfies \(d_i+d_j\ge5\).

If \(F\) is not a star, then, since \(e(F)\ge4\), it contains two disjoint edges. Hence \(D\ge10\), so (13) forces \(r\ge8\). But \(K_5\) with at most two edges deleted contains a 5-cycle. Summing the five inequalities \(d_i+d_j\ge5\) around that cycle gives

\[
2D\ge25,
\]

so \(D\ge13\), whereas (13) gives \(D\le r+2\le12\), contradiction.

Thus \(F=K_{1,4}\). If \(t\) is its center, summing the four edge inequalities gives

\[
3d_R(t)+D\ge20.
\]

Since (13) gives \(D\le6\), we have \(d_R(t)\ge5\), and at least one leaf of the star has \(R\)-degree zero. For that leaf, (14) shows

\[
\alpha(R-N_R(t))\le2. \tag{18}
\]

Consider \(X=R+t\). Then \(\alpha(X)\le3\), cap-11 holds, and

\[
e(X)=e(R)+d_R(t)\le44. \tag{19}
\]

If \(X\) is \(K_5\)-free, (T4) gives \(e(X)\ge L(16)=46\), contradicting (19). If \(X\) contains a \(K_5\), it contains \(t\), since \(R\) is \(K_5\)-free. Deleting that \(K_5\) leaves 11 vertices with \(\omega\le4\). Their independence number is at most two: an independent triple would, by (T5), miss some vertex of the deleted \(K_5\), producing an independent 4-set in \(X\). This contradicts (T4).

### 4.2 \(p\in\{5,6,7\}\) and \(a=5\)

From (13),

\[
D+s\le7-p,
\]

so \(D\le2\) and \(r=10-s\ge8\).

Delete \(\bigcup_i Z_i\) from \(R\). At least 13 vertices remain, so by (T4) they contain an independent triple \(S\). For every \(ij\in E(F)\), the five vertices

\[
S\cup\{t_i,t_j\}
\]

are independent. Avoiding an independent sixth vertex in \(Q\) forces their five \(Q\)-neighbors to be all five distinct vertices of \(Q\). Hence

\[
\{q_i,q_j\}=Q\setminus N_Q(S),
\]

the same fixed two-element set for every \(ij\in E(F)\). Thus every edge of \(F\) lies between two fixed \(q\)-color classes. Such a bipartite graph on five vertices has at most

\[
\left\lfloor\frac{25}{4}\right\rfloor=6
\]

edges, contradicting \(e(F)\ge8\).

Therefore the one-\(K_5\) case is impossible.

## 5. Exactly two \(K_5\)’s

Let the two cliques be \(Q_1,Q_2\), and let \(B\) be the remaining ten vertices. Then

\[
\alpha(B)\le2,\qquad \omega(B)\le4,
\]

so

\[
e(B)=25+b,\qquad b\ge0. \tag{20}
\]

Let

\[
c=e(Q_1,Q_2)+e(B,Q_1\cup Q_2),
\]
\[
y=e(T,Q_1\cup Q_2),\qquad D=e(T,B).
\]

The budget becomes

\[
b+c+y+D+s\le15,
\]

or equivalently

\[
b+c+y+D\le r+5. \tag{21}
\]

For \(t_i\in T\), put

\[
Z_i=N_B(t_i),\qquad d_i=|Z_i|.
\]

Call an edge \(ij\in E(F)\) *unhit* if \(B-(Z_i\cup Z_j)\) contains a nonedge \(uv\).

For an unhit edge, the four independent vertices

\[
t_i,t_j,u,v
\]

must have four distinct neighbors in each \(Q_\ell\), and the unique missed vertex of \(Q_1\) must be adjacent to the unique missed vertex of \(Q_2\). Indeed, otherwise the two cliques contain a mutually nonadjacent pair missed by all four vertices, producing an independent 6-set. Thus:

- \(t_i,t_j\) each have two neighbors in \(Q_1\cup Q_2\);
- \(u,v\) contribute four edges from \(B\) to \(Q_1\cup Q_2\);
- one edge joins \(Q_1\) to \(Q_2\).

Suppose there are \(h\) unhit edges, incident with \(\rho\) vertices of \(T\). Then

\[
y\ge2\rho,\qquad c\ge5. \tag{22}
\]

Every other \(F\)-edge is hit, meaning \(B-(Z_i\cup Z_j)\) is a clique. Since \(\omega(B)\le4\),

\[
|Z_i\cup Z_j|\ge6.
\]

Therefore

\[
6(r-h)\le4D. \tag{23}
\]

From (21)–(22),

\[
D\le r-2\rho.
\]

Combining with (23),

\[
r+4\rho\le3h. \tag{24}
\]

But \(h\le\binom{\rho}{2}\). For \(\rho=2,3,4\), (24) is impossible because \(r\ge4\). If \(\rho=5\), then (21) forces \(r=10,D=0,c=5,y=10\). Thus \(T\) is independent and has only ten incident edges into the 20 vertices of \(H\). Some \(h\in H\) has no \(T\)-neighbor, so \(T\cup\{h\}\) is independent of size six. Contradiction.

Hence there are no unhit edges. Thus for every \(ij\in E(F)\),

\[
|Z_i\cup Z_j|\ge6,
\qquad\text{and therefore}\qquad
d_i+d_j\ge6. \tag{25}
\]

Also, by (21),

\[
D\le r+5. \tag{26}
\]

We classify the possibilities.

- If \(r=5\) or \(6\), then \(F\) contains two disjoint edges, so (25) gives \(D\ge12\), contradicting \(D\le10\) or \(11\).

- If \(r=7\), then \(D=12\). The only nonnegative five-tuple of total weight 12 having at least seven pairs of sum at least six is

  \[
  (0,0,0,6,6).
  \]

  The seven eligible pairs are precisely the edge joining the two weight-six vertices and their six edges to the zero-weight vertices. Hence a weight-six vertex paired with a zero-weight vertex has \(Z_i\) itself hitting every nonedge of \(B\).

- If \(r=8\) or \(9\), then \(F\) contains a 5-cycle. Summing (25) around it gives \(D\ge15\), contradicting \(D\le13\) or \(14\).

- If \(r=10\), summing (25) over all ten pairs gives \(4D\ge60\). Hence \(D=15\), and equality forces

  \[
  d_1=\cdots=d_5=3.
  \]

  Since every union has size at least six, the five 3-element sets \(Z_i\) are pairwise disjoint, impossible inside a 10-element set.

It remains \(r=4\). Then \(D\le9\). If the four edges of \(F\) were not a star, \(F\) would contain two disjoint edges and \(D\ge12\). Thus

\[
F=K_{1,4}. \tag{27}
\]

Let \(t_0\) be its center.

If some leaf has weight zero, then (25) says that \(B-N_B(t_0)\) is a clique. The graph \(B+t_0\) would have \(\alpha\le2\) on 11 vertices. If it were \(K_5\)-free, this contradicts (T4). If it contained a \(K_5\), that clique would contain \(t_0\); the remaining six vertices would have to form a \(K_6\), since any nonedge among them could be extended by a missed vertex of the \(K_5\) to an independent triple. But a \(K_6\) violates cap-11. Thus this case is impossible.

Consequently all four leaves have positive weight. From (25) and \(D\le9\), equality is forced:

\[
d_B(t_0)=5,\qquad d_B(t_i)=1\quad(1\le i\le4),\qquad D=9. \tag{28}
\]

Equation (21) now gives

\[
b=c=y=0. \tag{29}
\]

In particular \(e(B)=25\).

Put

\[
Z=N_B(t_0),\qquad C=B-Z,
\]

so \(|Z|=|C|=5\). Let the unique \(B\)-neighbor of leaf \(t_i\) be \(z_i\). Since \(Z\cup\{z_i\}\) hits all nonedges of \(B\),

\[
B-(Z\cup\{z_i\})
\]

is a clique. Because \(\omega(B)\le4\), necessarily \(z_i\in C\) and

\[
B[C-\{z_i\}]=K_4. \tag{30}
\]

For every \(v\in B\), its nonneighbors form a clique, since \(\alpha(B)\le2\). That clique has size at most four, so \(d_B(v)\ge5\). As \(e(B)=25\), the average degree is five. Hence \(B\) is 5-regular.

Let \(X=e_B(Z,C)\). Degree sums over \(Z\) and \(C\) give

\[
25=2e(B[Z])+X=2e(B[C])+X,
\]

so

\[
e(B[Z])=e(B[C]). \tag{31}
\]

The 6-set \(\{t_0\}\cup Z\) gives

\[
5+e(B[Z])\le11,
\]

hence \(e(B[Z])\le6\). On the other hand, (30) gives \(e(B[C])\ge6\). By (31),

\[
e(B[Z])=e(B[C])=6. \tag{32}
\]

Thus \(z_i\) is isolated inside \(B[C]\), because the six edges of \(C-\{z_i\}\cong K_4\) exhaust \(e(B[C])\). Since \(B\) is 5-regular, \(z_i\) is adjacent to all five vertices of \(Z\).

For any \(z\in Z\), consider

\[
\{t_0,z_i\}\cup (Z-\{z\}).
\]

It spans

\[
4+4+\bigl(6-d_{B[Z]}(z)\bigr)
=14-d_{B[Z]}(z)
\]

edges. Cap-11 therefore gives \(d_{B[Z]}(z)\ge3\) for every \(z\in Z\). Hence

\[
12=2e(B[Z])
=\sum_{z\in Z}d_{B[Z]}(z)
\ge15,
\]

a contradiction.

Thus the two-\(K_5\) case is impossible.

## Conclusion

The maximum number of disjoint \(K_5\)’s in \(H=G-T\) can only be \(0,1,2,\) or \(4\), and every case has been eliminated. Therefore no such graph \(G\) exists.

The two boundary hypotheses enter essentially:

- \(e(G[T])\le6\) gives \(r=10-e(G[T])\ge4\), supplying the necessary nonedges of \(T\) and driving all weighted hitting arguments.
- \(e(G)\le60\) supplies the sharp budgets (1), (13), and (21); in the final two-\(K_5\) boundary it forces \(e(B)=25\) and exact equality throughout.

---

# Verification ledger (author session, 2026-07-10)

| item | method | verdict |
|---|---|---|
| §2 g-table (20 entries) + m≥50 | exact recomputation | ALL MATCH, all nonneg |
| §4 (16) elimination + case list (17) | exhaustive (a,p,r) scan | MATCHES EXACTLY (a≤1 ⇒ p+a≤1; a∈{2,3,4} empty; a=5 ⇒ p∈{4..7}) |
| toolkit caveat | the candidate CAUGHT an error in the author's brief: "α≤2 + cap-11, any ω" is false for 9/10 vertices (K_5⊔K_4, K_5⊔K_5); only the 11-vertex nonexistence is ω-free (confirmed: our ω≤5 SAT run) | candidate's handling looks correct; reviewer must audit every α≤2 use |
| §5 r=7 bullet | hand check | **GAP: states forced structure, missing the closing contradiction** — the same B+t argument as the r=4 zero-leaf case appears to close it (|Z_i| = d_i = 6, B−Z_i clique ⇒ B+t_i has α≤2 on 11 vertices ⇒ nonexistence lemma; K_5-through-t_i branch ⇒ K_6 ⇒ cap). Reviewer: confirm and write out. |
| §1 peeling, §3 transversal fact, §4.1/4.2, §5 remaining bullets | line-by-line hand check (author) | sound at first pass |
| fresh-session adversarial review | to be spawned | pending |

---

## Adversarial review (2026-07-10, fresh session)

Reviewer scope: decide whether this candidate correctly proves **[MM]** as stated in
`review_queue/extension-chain.md` — no graph $G$ on 25 vertices with $\alpha(G)\le5$,
cap-11, $e(G)\le60$, and a 5-set $T$ with $\alpha(G-T)\le4$, $e(G[T])\le6$. If correct,
then (with the accepted chain deduction and the accepted [MH″]) the $r=5$ case of Erdős 617
is settled, so I treated every step with maximal suspicion. I read PROBLEM.md,
extension-chain.md, this file, mh2-gpt56-candidate.md, and the [MM] brief (the source of the
toolkit (T1)–(T6)) in full, re-derived every load-bearing inequality by hand, and re-ran
every finite claim on my own independent SAT/arithmetic scripts (scratchpad, pysat/CaDiCaL,
not the repo's `verify_gpt_*`).

**Independent machine re-verifications I ran (all green):**
- **§2 g-table**: `ell(19−d)` (4) reproduced exactly from L(13..19)+complement-Turán; the
  vector `2g(d)+17d−84` reproduced exactly (all 20 entries, all ≥0); $840/17\Rightarrow m\ge50$.
- **§4 inequality (16)**: full scan over $a\in\{0..5\}, p\in\{0..15\}, r\in\{4..10\}$.
  Survivors are EXACTLY: $a\le1\Rightarrow p+a\le1$; $a\in\{2,3,4\}$ empty; $a=5\Rightarrow
  (p,r)\in\{(4,10),(5,8),(5,9),(5,10),(6,9),(6,10),(7,10)\}$ — i.e. (17) verbatim. The
  candidate's per-$a$ intermediate formulas ($a{=}2$: $r\le\min(p,5)-4p$; $a{=}3$:
  $r\le3\min(p,5)-4p-4$; $a{=}5$: $(5-\min(p,5))r\le4(r-p-3)$) all match `cond16` pointwise.
- **M(9)=19, M(10)=25** for $\alpha\le2,\omega\le4$,cap-11: $e\le18$ / $e\le24$ UNSAT,
  $e\le19$ / $e\le25$ SAT. Confirmed the caveat is REAL: on 10 vertices the $\omega$-free
  version is SAT (K₅⊔K₅, 20 edges), so M(10)=25 genuinely needs $\omega\le4$.
- **$\omega$-free 11-vertex nonexistence** ($\alpha\le2$+cap-11, any $\omega$): **UNSAT by
  TWO independent encodings** — direct (edge vars, atmost-11 per 6-set) and complement
  (triangle-free $J$ with $\ge4$ $J$-edges per 6-set). Also n=12 UNSAT. This is the pivotal
  fact; monotonicity (induced subgraphs inherit $\alpha\le2$+cap-11) extends it to all $\ge11$.
- **§4.1 / §5 finite claims**: K₅ minus $\le2$ edges always has a Hamilton 5-cycle (brute
  force); max bipartite edges on parts summing $\le5$ is 6 $=\lfloor25/4\rfloor$; the only
  4-edge graph on 5 vertices with matching number $\le1$ is $K_{1,4}$; e(F)$\ge5$ forces two
  disjoint edges.
- **§5 r=7 weight vector** (THE FLAGGED GAP): the ONLY nonnegative 5-tuple summing to 12 with
  $\ge7$ pairs of sum $\ge6$ is $(0,0,0,6,6)$ — confirmed by exhaustive enumeration.

### Per-section findings

**§1 peeling lemma (2),(3) — CORRECT.** The greedy choice of $q_i\in Q_i$ avoiding
$\le(5-k)+(i-1)\le4$ forbidden vertices (each of $S$ and each earlier $q$ has $\le1$
neighbour in $Q_i$ by T5) yields an independent 5-set $S\cup\{q_1,\dots,q_k\}$, contradicting
$\alpha(H)\le4$. Hence $\alpha(R)\le4-k$; $k=3$ forces $\alpha(R)\le1$ on 5 vertices $\Rightarrow$
a 4th K₅; $k\ge5$ needs $>20$ vertices. Cases $\{0,1,2,4\}$ exhaustive and mutually exclusive
by $k_{\max}$.

**§2 $H$ is K₅-free — CORRECT.** (5) is a sound floor ($H[W_v]$ has $\alpha\le3$, $\omega\le4$
since $H$ K₅-free, cap-11 inherited); (T2)+(T3)+trivial $f(d\le4)=\binom d2$ give (6); the
g-table nonnegativity gives $m\ge50$ (7). The $U_{tt'}$ argument is airtight in all three
$m$-branches: since $m\le60<62=L(18)$, $|U_{tt'}|\le2$ is impossible so $|U|\ge3$ always;
$m\ge53\Rightarrow3r\le4x\le4(r-3)\Rightarrow r\ge12$; $m\in\{51,52\}\Rightarrow|U|\ge4$
(else $L(17)=53$) $\Rightarrow r\le x\le r-1$; $m=50\Rightarrow\delta(H)\ge3$ (else
$d(v)+L(19-d(v))\ge55$) and every $|U|\ge5$ (a 4-set $U\supseteq U_{tt'}$ gives
$L(16)=46$ plus $\ge12-6=6$ incident edges $=52>50$), so $5r\le4x\le4r$. Budget
$x\le50+r-m$ derived correctly from $m+x+s\le60$, $s=10-r$.

**§3 four K₅'s — CORRECT.** The "elementary fact" proof is valid: if $v\in A_i$ has no
neighbour in $A_j$, deleting $v$'s $\le1$ neighbour from each of the two other parts leaves
$\ge2$ each; a matching between two $\ge2$-sets misses a non-adjacent pair $y,z$; then $y,z$
forbid $\le2$ of $A_j$ and $v$ forbids $0$, so ($|A_j|\ge3$) a 4th vertex completes an
independent transversal. Hence each cross-graph saturates both sides ($\ge3$ edges), giving
$e(H)\ge40+18=58$; then $s+x\le2$, an independent triple $P\subseteq T$, and $\le2$ deleted
vertices leave $\ge3$ per clique for a greedy transversal $\Rightarrow$ independent 6-set.

**§4 one K₅ — CORRECT.** $R=H-Q$ is K₅-free (a K₅ in $R$ is vertex-disjoint from $Q$
$\Rightarrow$ two disjoint K₅'s), so $e(R)\ge L(15)=38$ legitimately. Budget (13) correct
($m=48+p+b$, $x=a+D$). (14): the residual $R-(Z_i\cup Z_j)$ has $\alpha\le2$ (else an
independent triple $+t_i,t_j$ has $\le4$ Q-neighbours $\Rightarrow$ a missed $Q$-vertex $\Rightarrow$
independent 6-set) and cap-11, so by the $\omega$-free 11-vertex nonexistence it has $\le10$
vertices $\Rightarrow d_i+d_j\ge5$. (15) is the same with $P$ removed (kills $S$'s Q-neighbours
when $q_i\ne q_j$). Weighted count: $\sum(d_i+d_j)\ge5r-\min(p,5)h$ (case-(b) edges give
$\ge5-p\ge5-\min(p,5)$), $\le4D$, $h\le\min\{r,\binom a2\}$, $D\le r+2-p-a$ $\Rightarrow$ (16).
Scan confirms (17) and the $(4,5,10)$ exclusion ($d_i+d_j\ge1$ per pair $\Rightarrow$ at most one
zero $\Rightarrow D\ge4>3$).
- **§4.1 ($p+a\le1$) — CORRECT.** All edges case-(a) ($d_i+d_j\ge5$). Non-star $F$ $\Rightarrow$
  two disjoint edges $\Rightarrow D\ge10\Rightarrow r\ge8\Rightarrow$ 5-cycle $\Rightarrow2D\ge25$,
  $D\ge13>r+2$. So $F=K_{1,4}$, $r=4$; the center has $d_R(t)\ge5$, a zero-weight leaf gives
  $\alpha(R-N_R(t))\le2$ (18), and $X=R+t$ (16 vtx, $\alpha\le3$, cap-11, $e\le44$) is either
  K₅-free ($e\ge L(16)=46>44$) or has a K₅-through-$t$ whose deletion leaves an 11-vertex
  $\alpha\le2$ cap-11 graph (nonexistent). Both branches close.
- **§4.2 ($p\in\{5,6,7\},a=5$) — CORRECT** (this was flagged as the "weakest link"; it holds).
  $D\le2$, $r\ge8$; deleting $\bigcup Z_i$ ($\le2$ vtx) leaves $\ge13$ vertices which (by the
  11-vertex nonexistence, cap-11) have $\alpha\ge3$, giving a fixed independent triple $S$
  avoiding **all** $Z_i$. For every F-edge $ij$, $S\cup\{t_i,t_j\}$ is an independent 5-set;
  to avoid an independent 6-set all five of $Q$ must be hit, forcing $|N_Q(S)|=3$ and
  $\{q_i,q_j\}=Q\setminus N_Q(S)$ — the same 2-set for every F-edge. The flagged worry
  ($|N_Q(S)|<3$) is *fine*: then five distinct Q-neighbours are impossible for ANY F-edge, so
  a Q-vertex is missed $\Rightarrow$ immediate independent 6-set (a quicker contradiction). With
  $|N_Q(S)|=3$, F embeds in a bipartite graph on $\le5$ vertices, $e(F)\le\lfloor25/4\rfloor=6
  <8\le r$. (The candidate omits the trivial $|N_Q(S)|<3$ sub-case — cosmetic.)

**§5 two K₅'s — CORRECT with the r=7 repair written out below.** $\alpha(B)\le2$ (peeling,
$k=2$), $\omega(B)\le4$ (a K₅ in $B$ gives 3 disjoint K₅'s), so $e(B)\ge M(10)=25$ — a
legitimate $\alpha\le2,\omega\le4$ use ($\omega\le4$ established, as required). Budget (21)
correct ($m=45+b+c$). Unhit-edge analysis: exactly one missed vertex per $Q_\ell$ (a 2nd
missed vertex, with the $Q_1$–$Q_2$ matching, would leave a non-adjacent missed pair
$\Rightarrow$ 6-set), the two missed vertices adjacent, giving $y\ge2\rho$, $c\ge5$; hit edges
give $|Z_i\cup Z_j|\ge6$; (23)+(21)$\Rightarrow$(24) $r+4\rho\le3h$, killing $\rho\in\{2,3,4\}$
($r\ge4$) and $\rho=5$ (forces $r{=}10,D{=}0,y{=}10$: some $h\in H$ has no T-neighbour
$\Rightarrow T\cup\{h\}$ independent 6-set). So $h=0$ and every F-edge has $d_i+d_j\ge6$ (25).
Then $r{=}5,6$ (two disjoint edges $\Rightarrow D\ge12>r+5$), $r{=}8,9$ (5-cycle $\Rightarrow
D\ge15$), $r{=}10$ (all $d_i{=}3$, five disjoint 3-sets in a 10-set — impossible) all close.
The **r=4 endgame (27)–(32)** I checked edge-by-edge: $F=K_{1,4}$, $d_B(t_0)=5$, leaves
weight 1, $b=c=y=0$, $e(B)=25$, $B$ 5-regular (every non-neighbourhood is a clique of size
$\le4$ so $\delta\ge5$, avg 5), $e(B[Z])=e(B[C])=6$, $z_i$ isolated in $B[C]$ and adjacent to
all of $Z$; the 6-set $\{t_0,z_i\}\cup(Z\setminus\{z\})$ spans $14-d_{B[Z]}(z)\le11$ so
$d_{B[Z]}(z)\ge3$ $\forall z$, whence $12=2e(B[Z])\ge15$. Contradiction. Every count verified.

### The r=7 repair (confirmed sound; written out)

The submitted §5 r=7 bullet establishes the forced structure and stops. Here is the closing
contradiction. It is verbatim the candidate's own r=4 zero-leaf argument, and rests only on
already-verified facts.

At $r=7$: (26) gives $D\le r+5=12$, and F (7 edges $>4$) contains two disjoint edges, so (25)
gives $D\ge12$; hence $D=12$. Every F-edge $ij$ satisfies $d_i+d_j\ge6$ (25, since $h=0$), so
the weight vector $(d_1,\dots,d_5)$ — nonnegative, summing to 12, with $\ge7$ pairs of sum
$\ge6$ (the 7 F-edges) — must be $(0,0,0,6,6)$ (exhaustively the unique such vector; verified).
Thus $F$ is exactly those 7 pairs: the two weight-6 vertices are F-adjacent to each other and
to all three weight-0 vertices.

Pick a weight-6 vertex $t_i$ ($d_i=|Z_i|=6$) and a weight-0 vertex $t_j$ ($Z_j=\varnothing$).
The pair $ij$ is an F-edge, and $h=0$ makes it hit, so $B-(Z_i\cup Z_j)=B-Z_i$ is a clique.
Since $|B-Z_i|=10-6=4$ and $\omega(B)\le4$, $B-Z_i$ is a $K_4$.

Now consider $X=B+t_i$ (11 vertices). $\alpha(X)\le2$: any independent triple lies either in
$B$ (impossible, $\alpha(B)\le2$) or is $\{t_i,u,v\}$ with $u,v$ non-adjacent to $t_i$, i.e.
$u,v\in B-Z_i=K_4$, forcing $u,v$ adjacent — impossible. $X\subseteq G$ is cap-11. So $X$ is an
$\alpha\le2$, cap-11 graph on 11 vertices, which does not exist (T4, $\omega$-free — SAT-
confirmed here two ways). Contradiction. (One may instead mirror the r=4 branch: if $X$ has a
K₅ it runs through $t_i$, deletion leaves a $K_6$ by T5, violating cap-11; if K₅-free, the
$\omega\le4$ 11-vertex nonexistence applies. Either route closes it; the $\omega$-free fact
makes the split unnecessary.) $\square$

### Findings ledger
- **FATAL: none.**
- **FIXABLE (submitted text incomplete; now repaired):** §5 r=7 bullet stops before the
  contradiction. Closed above (weight vector $(0,0,0,6,6)$ unique $\Rightarrow$ a weight-6/weight-0
  F-edge makes $B+t_i$ an 11-vertex $\alpha\le2$ cap-11 graph $\Rightarrow$ nonexistent). This is
  the candidate's own r=4 argument; it introduces no new machinery.
- **COSMETIC:** (i) §4.2 omits the trivial $|N_Q(S)|<3$ sub-case (an even quicker 6-set).
  (ii) §4.1's "contradicts (T4)" for the independent 4-set is really "contradicts $\alpha(X)\le3$",
  after which the 11-vertex $X$-residual contradicts (T4); both hold. (iii) The opening caveat
  is correct and load-bearing: M(9)/M(10) need $\omega\le4$; the only such use (§5 $e(B)\ge25$)
  has $\omega(B)\le4$ established, and every other $\alpha\le2$ use invokes the $\omega$-free
  11-vertex nonexistence. No improper use found.

### Verdict

**VERDICT: ACCEPTED MODULO** the r=7 repair written out above (which the candidate itself
flagged and which reuses no new machinery). With that one paragraph inserted, the proof of
[MM] is **correct and complete**: the case split on the number of disjoint K₅'s (0,1,2,4) is
exhaustive, every case closes, every arithmetic value (§2 g-table, §4 (16)-scan, §5 r=7 weight
vector, §5 r=4 endgame counts) and every finite graph fact (M(9), M(10) with $\omega\le4$, the
$\omega$-free 11-vertex nonexistence via two independent encodings, the Hamiltonicity/bipartite/
star lemmas) was independently re-derived or machine-checked, the caveat on the M-values is
respected everywhere, and all four hypotheses of [MM] ($\alpha(G)\le5$, cap-11, $e(G)\le60$,
the 5-set $T$ with $\alpha(G-T)\le4$ and $e(G[T])\le6$) are used essentially. No circularity;
the theorem proved is exactly [MM] as stated in extension-chain.md.

---

# Post-review disposition (author session, 2026-07-10)

The single ACCEPTED-MODULO item — the missing r=7 conclusion in §5 — is discharged by the
reviewer's fully-written repair above (verbatim the candidate's own r=4 zero-leaf argument;
rests on the triple-confirmed ω-free 11-vertex nonexistence). The repair text is adopted
into the proof as the official closing of the r=7 bullet. The reviewer's cosmetic note on
§4.2 (spelling out that q_i = q_j F-edges are impossible outright, and that |N_Q(S)| < 3
gives an immediate contradiction) is likewise adopted.

**STATUS: [MM] is PROVED** (adversarially reviewed; arithmetic machine-verified; all α≤2
uses audited against the ω-caveat; primitive SAT facts DRAT-certified in data/sat/prim_*).
