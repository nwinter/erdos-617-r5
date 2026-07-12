# The claim is true

In fact, we prove the stronger statement:

> There is no 5-colouring of \(K_{21}\) whose colour graphs have independence numbers at most
> \[
> (4,5,5,5,5).
> \]

Applying this to the \(21\) vertices outside \(T\) proves MH\(^{\prime\prime}\).

We use (F1), (F2), and one classical refinement of Turán’s theorem. Facts (F3) and (F5) are not needed; (F4) is checked explicitly at the end.

## 1. Reduction to \(21\) vertices

Suppose, for contradiction, that the claimed colouring of \(K_{25}\) exists. Let

\[
S=V(K_{25})\setminus T,\qquad |S|=21,
\]

and write

\[
H=G_0[S],\qquad F_i=G_i[S]\quad(1\le i\le4).
\]

Then

\[
\alpha(H)\le4,\qquad \alpha(F_i)\le5.
\]

Every six vertices in \(S\) contain every colour, so every induced six-vertex subgraph of any one colour has at most \(11\) edges, by (F1). Every colour graph is also \(K_6\)-free.

For \(v\in S\), put

\[
W_v=S\setminus(\{v\}\cup N_H(v)).
\]

Then

\[
\alpha(H[W_v])\le3.
\]

Conversely, this condition for every \(v\) is equivalent to \(\alpha(H)\le4\): an independent \(5\)-set, after choosing one of its vertices as \(v\), leaves an independent \(4\)-set in \(W_v\). Thus property (P) is not extra information; the gain must come from cap-11 and the other colours.

## 2. A classical non-partite Turán theorem

We use the following theorem of Brouwer, together with its equality classification by Kang and Pikhurko.

> If \(Y\) is an \(n\)-vertex \(K_{r+1}\)-free graph with \(\chi(Y)>r\), where \(n\ge2r+1\), then
> \[
> e(Y)\le t_r(n)-\left\lfloor\frac nr\right\rfloor+1.
> \]

The extremal graphs are also explicitly classified. We only use the cases \(r=5\), \(n=15,16,21\). A proof and the equality classification appear in [Kang–Pikhurko, *Maximum \(K_{r+1}\)-free graphs which are not \(r\)-partite*](https://matstud.org.ua/texts/2005/24_1/24_1_012_020.pdf).

## 3. Every ordinary colour has at least \(38\) edges on \(S\)

First, every \(F_i\) is \(K_5\)-free. Indeed, an \(F_i\)-\(K_5\) would have no \(H\)-edges and hence would be an \(H\)-independent \(5\)-set.

Let \(J_i=\overline{F_i}\). Then \(J_i\) is \(K_6\)-free. Moreover,

\[
\alpha(J_i)=\omega(F_i)\le4.
\]

Thus \(J_i\) is not \(5\)-partite: five independent parts would contain at most \(5\cdot4=20\) vertices. Brouwer’s theorem gives

\[
e(J_i)\le t_5(21)-4+1=176-3=173,
\]

and hence

\[
e(F_i)\ge210-173=37. \tag{3.1}
\]

We now exclude equality.

For \(n=21,r=5\), the equality classification has possible part-size sequences

\[
(4,4,4,4,4),\quad(3,4,4,4,5),\quad(3,3,4,5,5)
\]

on the \(20\) old vertices in the extremal construction. The latter two yield a \(K_5\) in \(F_i\), so only \((4,4,4,4,4)\) is possible.

In that case there are disjoint sets \(A,B\) with

\[
|A|=5,\qquad |B|=4,
\]

such that:

- \(F_i[A]=K_5-xy\) for some \(x,y\in A\);
- \(F_i[B]=K_4\);
- exactly four \(i\)-edges join \(A\) to \(B\).

The sole non-\(i\) edge \(xy\) in \(A\) must be an \(H\)-edge; otherwise \(A\) would contain no \(H\)-edge.

Fix another ordinary colour \(j\ne i\). For every pair \(a,a'\in A\), the six-set

\[
B\cup\{a,a'\}
\]

must contain a \(j\)-edge. Neither \(B\) nor \(aa'\) contains a \(j\)-edge, so such an edge must run from \(\{a,a'\}\) to \(B\). Consequently at most one vertex of \(A\) has no \(j\)-neighbour in \(B\), and therefore

\[
e_j(A,B)\ge4.
\]

Also \(B\) is \(H\)-independent. Hence every \(a\in A\) has an \(H\)-neighbour in \(B\), or else \(B\cup\{a\}\) would be an \(H\)-independent \(5\)-set. Thus

\[
e_H(A,B)\ge5.
\]

The \(20\) edges between \(A\) and \(B\) would therefore include at least

\[
4+3\cdot4+5=21
\]

edges, a contradiction. Hence

\[
\boxed{e(F_i)\ge38\quad(1\le i\le4).} \tag{3.2}
\]

## 4. Exact cap-11 recursion

We next derive a sharp lower bound for \(H\).

Let \(G\) be a graph on \(q\) vertices, with \(m=e(G)\), degrees \(d_v\), triangle count \(\tau(G)\), and

\[
W_v=V(G)\setminus(\{v\}\cup N_G(v)).
\]

An edge \(xy\) belongs to \(G[W_v]\) for exactly

\[
q-d_x-d_y+|N(x)\cap N(y)|
\]

vertices \(v\). Therefore

\[
\sum_v e(G[W_v])
=qm-\sum_vd_v^2+3\tau(G). \tag{4.1}
\]

Also

\[
3\tau(G)=\sum_v e(G[N(v)]). \tag{4.2}
\]

Cap-11 bounds the last expression. If \(d=d(v)\ge5\), then every five-set \(A\subseteq N(v)\) satisfies

\[
5+e(G[A])\le11,
\]

so \(e(G[A])\le6\). Double-counting over the five-subsets of \(N(v)\) gives

\[
e(G[N(v)])\binom{d-2}{3}
\le6\binom d5,
\]

and hence

\[
e(G[N(v)])\le
b(d):=
\left\lfloor\frac{3d(d-1)}{10}\right\rfloor. \tag{4.3}
\]

For \(d\le4\), put \(b(d)=\binom d2\).

If in addition \(\omega(G)\le4\), then \(G[N(v)]\) is \(K_4\)-free, so we may use

\[
u(d):=\min\{b(d),\operatorname{ex}(d,K_4)\}. \tag{4.4}
\]

### 4.1 Graphs with \(\alpha\le2,\omega\le4\)

Let \(Z\) have \(\alpha(Z)\le2\) and \(\omega(Z)\le4\). Its complement \(J\) is triangle-free with \(\alpha(J)\le4\). Therefore \(\Delta(J)\le4\), giving

\[
e(Z)\ge
\max\left\{
\binom{\lfloor s/2\rfloor}{2}
+\binom{\lceil s/2\rceil}{2},
\binom s2-2s
\right\}. \tag{4.5}
\]

Three small sharpenings are needed:

\[
M(9)=19,\qquad M(10)=25,\qquad M(11)=35, \tag{4.6}
\]

and no such cap-11 graph exists on \(12\) vertices.

For \(s=9\), equality \(e(Z)=18\) would make \(J\) triangle-free and \(4\)-regular. Choose \(v\in J\), let \(A=N_J(v)\), and let \(B\) be the remaining four vertices. Then \(A\) is independent, \(e_J(A,B)=12\), and \(e_J(B)=2\). If \(xy\in E(J[B])\), the \(A\)-neighbourhoods of \(x,y\) are disjoint. Writing \(q_x=d_B(x)\), their \(A\)-degrees are \(4-q_x\), so disjointness requires \(q_x+q_y\ge4\). This is impossible when the two edges of \(J[B]\) form either a matching or a \(P_3\). Thus \(e(Z)\ge19\).

For \(s=11\), (4.5) gives \(e(Z)\ge33\).

If \(e(Z)=33\), then \(J\) is \(4\)-regular. If \(A,B\) are complementary sets of sizes \(5,6\), regularity gives

\[
e_J(B)=e_J(A)+2.
\]

Cap-11 on \(Z[B]\) implies \(e_J(B)\ge4\), so every five-set of \(J\) spans at least two edges. Choose \(v\) and let \(I=N_J(v)\). The six remaining vertices all have exactly two neighbours in \(I\) and induce a \(C_6\). Along this cycle the two-element \(I\)-neighbourhoods alternate between complementary pairs \(P,I\setminus P\). The two vertices of \(P\), together with the three cycle vertices labelled \(I\setminus P\), form a \(J\)-independent \(5\)-set, contradicting \(\alpha(J)\le4\).

If \(e(Z)=34\), then \(e(J)=21\) and \(\Delta(J)\le4\). The total degree deficit from four is two. Choose a degree-four vertex \(v\) nonadjacent to all deficient vertices, put \(A=N_J(v)\), and let \(B\) be the remaining six vertices. Then

\[
e_J(A,B)=12,\qquad e_J(B)=5.
\]

For \(x\in B\), put \(p_x=d_A(x)\). Cap on \(A\cup\{x,y\}\) gives

\[
p_x+p_y+\mathbf1_{xy\in E(J)}\ge4. \tag{4.7}
\]

This forces all \(p_x=2\). Consequently \(J[B]\) has degree sequence either that of \(C_5\cup K_1\), \(P_6\), or \(C_4\cup K_2\). Adjacent vertices have complementary two-subsets of \(A\) as their \(A\)-neighbourhoods. This cannot alternate around \(C_5\); in the \(P_6\) and \(C_4\cup K_2\) cases one obtains a six-set with at most three \(J\)-edges, contradicting cap-11 for \(Z\). Hence \(e(Z)\ge35\).

Finally, on \(12\) vertices, every non-neighbourhood is a clique of size at most five, so every degree is at least six. Applying (4.1)–(4.3) gives

\[
\sum_v\left[
\binom{11-d_v}{2}+d_v^2-6d_v-b(d_v)
\right]\le0.
\]

For \(d=6,7,8,9,10,11\), the bracket equals respectively

\[
1,1,3,7,13,22,
\]

which is impossible.

### 4.2 Graphs with \(\alpha\le3,\omega\le4\)

Let \(L(s)\) be the following lower bounds:

\[
\begin{array}{c|rrrrrrrr}
s&13&14&15&16&17&18&19&20\\ \hline
L(s)&24&31&38&46&53&62&73&84.
\end{array} \tag{4.8}
\]

For \(s\le12\), use the ordinary complement-Turán bound for independence number three.

Here is the verification of (4.8). For a graph \(X\) of order \(s\), \(\alpha(X)\le3\), \(\omega(X)\le4\), define

\[
\Phi_s(d)
=M(s-1-d)+d^2-\frac{s}{2}d-u(d),
\]

where \(M\) is the preceding \(\alpha\le2,\omega\le4\) bound. From

\[
\sum_v(e(W_v)-e(N(v)))
=se(X)-\sum_vd_v^2
\]

we get

\[
\sum_v\Phi_s(d_v)\le0. \tag{4.9}
\]

Direct substitution gives affine lower bounds

\[
\Phi_s(d)\ge A_s-B_sd
\]

with

\[
\begin{array}{c|rrrrrrrr}
s&13&14&15&16&17&18&19&20\\ \hline
A_s&25&26&30&34&28&34&57&125/2\\
B_s&7&6&6&6&9/2&5&15/2&15/2 .
\end{array}
\]

Thus

\[
e(X)\ge\left\lceil\frac{sA_s}{2B_s}\right\rceil,
\]

which is exactly (4.8).

### 4.3 Applying the recursion to \(H\)

Assume for the moment that \(H\) is \(K_5\)-free. Then \(\omega(H)\le4\), while every \(H[W_v]\) has independence number at most three.

Define

\[
\Psi(d)
=L(20-d)+d^2-\frac{21}{2}d-u(d).
\]

Using (4.8) for \(20-d\ge13\) and the ordinary complement-Turán bounds below that, direct substitution gives

\[
\Psi(d)\ge52-\frac{19}{2}d
\qquad(0\le d\le20).
\]

The successive nonnegative slacks are

\[
32,21,11,4,1,0,0,2,6,14,23,34,48,63,79,97,117,139,163,188,214.
\]

Therefore, by (4.1)–(4.4),

\[
0\ge\sum_v\Psi(d_v)
\ge21\cdot52-\frac{19}{2}\sum_vd_v
=1092-19e(H).
\]

Hence

\[
\boxed{H\text{ \(K_5\)-free}\implies e(H)\ge58.} \tag{4.10}
\]

## 5. \(H\) cannot contain a \(K_5\)

Suppose \(Q\) is an \(H\)-\(K_5\), and put \(X=S\setminus Q\), so \(|X|=16\).

For every \(x\in X\), cap-11 on \(Q\cup\{x\}\) gives

\[
d_H(x,Q)\le1. \tag{5.1}
\]

If \(X\) contained an \(H\)-independent \(4\)-set, its four vertices would collectively have at most four neighbours in \(Q\); some \(q\in Q\) would avoid all four, giving an independent \(5\)-set. Thus

\[
\alpha(H[X])\le3. \tag{5.2}
\]

If \(H[X]\) is \(K_5\)-free, (4.8) gives

\[
e(H[X])\ge46.
\]

Otherwise let \(R\subset X\) be another \(H\)-\(K_5\), and put \(L=X\setminus R\), so \(|L|=11\). Then \(\alpha(H[L])\le2\): an independent triple in \(L\), together with suitably chosen nonadjacent vertices of \(Q\) and \(R\), would form an independent \(5\)-set. Moreover \(\omega(H[L])\le4\); otherwise a third \(K_5\) in \(L\), together with (5.1), would force an \(H\)-\(K_6\). Thus

\[
e(H[L])\ge35,
\]

and consequently

\[
e(H[X])\ge10+35=45. \tag{5.3}
\]

For every ordinary colour \(i\), \(F_i[X]\) is \(K_4\)-free: an \(i\)-coloured \(K_4\) would be an \(H[X]\)-independent \(4\)-set, contradicting (5.2).

Let \(J=\overline{F_i[X]}\). It is \(K_6\)-free and not \(5\)-partite, since each independent part has size at most three. Brouwer’s theorem gives

\[
e(J)\le t_5(16)-3+1=102-2=100,
\]

so

\[
e(F_i[X])\ge120-100=20.
\]

Summing all five colours inside \(X\) now gives

\[
\binom{16}{2}
\ge45+4\cdot20=125,
\]

whereas \(\binom{16}{2}=120\), a contradiction. Therefore

\[
\boxed{H\text{ is }K_5\text{-free}.} \tag{5.4}
\]

## 6. All five edge bounds must be equalities

From (3.2), (4.10), and (5.4),

\[
e(H)+\sum_{i=1}^4e(F_i)
\ge58+4\cdot38=210.
\]

But these five graphs partition \(E(K_{21})\), which has exactly \(210\) edges. Hence

\[
\boxed{e(H)=58,\qquad e(F_i)=38\quad(1\le i\le4).} \tag{6.1}
\]

## 7. Excluding the equality case

### 7.1 \(H\) has minimum degree at least five

Suppose \(d_H(v)=4\). Then \(|W_v|=16\), and

\[
\alpha(H[W_v])\le3,\qquad \omega(H[W_v])\le4.
\]

Thus, by (4.8),

\[
e(H[W_v])\ge46.
\]

For each ordinary colour \(i\), \(F_i[W_v]\) is \(K_4\)-free, since an \(i\)-\(K_4\) in \(W_v\), together with \(v\), would be an \(H\)-independent \(5\)-set. As above, Brouwer’s theorem gives

\[
e(F_i[W_v])\ge20.
\]

Therefore the \(120\) edges of \(K_{16}\) would satisfy

\[
120\ge46+4\cdot20=126,
\]

impossible. Hence

\[
\delta(H)\ge5. \tag{7.1}
\]

Since \(2e(H)=116<6\cdot21\), some vertex has degree exactly five. Fix such a vertex \(v\), and put

\[
A=N_H(v),\qquad Q=A\cup\{v\},\qquad W=S\setminus Q.
\]

Thus \(|A|=5\), \(|Q|=6\), and \(|W|=15\). Write

\[
r=e_H(A),\qquad w=e_H(W),\qquad c=e_H(A,W).
\]

Since \(\alpha(H[W])\le3\) and \(\omega(H[W])\le4\), (4.8) gives \(w\ge38\). Cap on \(Q\) gives \(r\le6\).

Put

\[
a=\sum_{x\in A}(d_H(x)-5)\ge0,\qquad \eta=w-38\ge0.
\]

Summing the degrees of vertices in \(A\),

\[
25+a=5+2r+c,
\]

so

\[
c=20+a-2r.
\]

Using \(e(H)=58\),

\[
58=5+r+w+c
=63-r+a+\eta.
\]

Thus

\[
a+(6-r)+\eta=1.
\]

The only possibilities are

\[
(r,w,c)=(5,38,10),\ (6,38,9),\ (6,39,8). \tag{7.2}
\]

### 7.2 A low ordinary colour on \(W\)

The four ordinary colours partition the non-\(H\) edges of \(K_{15}[W]\). Hence

\[
\sum_{i=1}^4e(F_i[W])
=105-w\in\{66,67\}.
\]

Some ordinary colour, say \(i\), therefore has

\[
e(F_i[W])\le16. \tag{7.3}
\]

Also \(F_i[W]\) is \(K_4\)-free, because \(H[W]\) has independence number at most three.

By (F2),

\[
e(F_i[W])\ge15.
\]

If equality holds, then

\[
F_i[W]=5K_3.
\]

If \(e(F_i[W])=16\), its complement has \(89\) edges. A non-\(5\)-partite \(K_6\)-free graph on \(15\) vertices has at most

\[
t_5(15)-3+1=90-2=88
\]

edges. Hence the complement is \(5\)-partite. Since \(\omega(F_i[W])\le3\), all five parts have size three.

Thus in either case there is a partition

\[
W=C_1\dot\cup\cdots\dot\cup C_5, \tag{7.4}
\]

where every \(C_j\) is an \(i\)-coloured triangle and hence is \(H\)-independent.

For each \(j\), define

\[
X_j=\{q\in Q:e_H(q,C_j)=0\}.
\]

If two vertices of \(X_j\) were \(H\)-nonadjacent, those two vertices together with \(C_j\) would form an \(H\)-independent \(5\)-set. Hence \(X_j\) is an \(H\)-clique. Since \(H\) is \(K_5\)-free,

\[
|X_j|\le4.
\]

Therefore at least two distinct vertices of \(Q\) send an \(H\)-edge into each \(C_j\), and

\[
c=e_H(Q,W)\ge2\cdot5=10. \tag{7.5}
\]

This excludes the last two cases in (7.2). Consequently

\[
(r,w,c)=(5,38,10). \tag{7.6}
\]

Equality in (7.5) means that for each \(j\):

- exactly two vertices of \(Q\) send an \(H\)-edge into \(C_j\);
- each sends exactly one such edge;
- the other four vertices form the \(H\)-\(K_4\) \(X_j\).

Now \(v\) has no \(H\)-neighbour in \(W\), so \(v\in X_j\). Put

\[
F=H[A].
\]

Since \(r=5\), \(e(F)=5\). We can write

\[
X_j=\{v\}\cup T_j,
\]

where \(T_j\) is a triangle of \(F\). The two vertices of \(A\setminus T_j\) each send exactly one \(H\)-edge into \(C_j\), while vertices of \(T_j\) send none.

For \(x\in A\), let

\[
\rho_x=\bigl|\{j:x\in T_j\}\bigr|.
\]

Its \(H\)-degree is exactly

\[
d_H(x)=1+d_F(x)+(5-\rho_x).
\]

By (7.1), \(d_H(x)\ge5\), so

\[
\rho_x\le d_F(x)+1. \tag{7.7}
\]

But

\[
\sum_{x\in A}\rho_x=5\cdot3=15
\]

and

\[
\sum_{x\in A}(d_F(x)+1)=2e(F)+5=15.
\]

Thus equality holds in (7.7) for every \(x\), and in particular

\[
\rho_x=d_F(x)+1\ge1.
\]

Therefore the triangles \(T_1,\dots,T_5\) cover all five vertices of \(A\).

That is impossible in a five-edge graph. One triangle already uses three edges. A second triangle introducing one new vertex and sharing an edge with the first uses the remaining two edges but covers only four vertices; a triangle introducing both remaining vertices requires at least three additional edges. Hence triangles covering five vertices require at least six edges.

This contradiction completes the proof.

\[
\boxed{\text{No such balanced colouring exists.}}
\]

## 8. Why the argument does not contradict \(n=24\)

For \(n=24\), deleting the four-vertex hitter leaves \(20\) vertices.

There the special colour can be

\[
4K_5,
\]

with exactly \(40\) edges, while an ordinary \(K_5\)-free colour can attain

\[
5K_4,
\]

with \(30\) edges. Thus the basic lower sum is only

\[
40+4\cdot30=160<\binom{20}{2}=190.
\]

More pointedly, if the special graph contains a \(K_5\), deleting it leaves \(15\) vertices. The corresponding lower bounds are only

\[
30+4\cdot15=90\le\binom{15}{2}=105,
\]

whereas at \(21\) vertices the same deletion leaves \(16\) vertices and gives the decisive contradiction

\[
45+4\cdot20=125>\binom{16}{2}=120.
\]

So the proof uses the \(25\)-vertex hypothesis quantitatively and does not apply at \(n=24\), in agreement with (F4).

Facts used:

- (F1): cap-11 and \(K_6\)-freeness throughout the recursion;
- (F2): all complement-Turán bounds, equality structures, and the total edge count;
- (F3): not used;
- (F4): verified by the preceding threshold calculation;
- (F5): not used.

---

# Verification ledger (Claude session, 2026-07-10)

| item | method | verdict |
|---|---|---|
| §2 external theorem (Brouwer bound) | literature agent read Kang–Pikhurko 2005 (primary) + arXiv:2404.07486 (secondary); papers/brouwer-kang-pikhurko.md | REAL; hypotheses & bound exact |
| §3/§5/§7 uses of the bound (n=21,16,15) | same + arithmetic recomputation (t_5 values 176/102/90 → 173/100/88) | ALL FAITHFUL |
| §3 equality classification + A/B structure | agent re-enumerated KP Lemma 5 optimality conditions; translated construction | FAITHFUL (part sizes (4,4,4,4,4) only; exactly 4 cross edges confirmed) |
| §4.2–4.3 recursion arithmetic (L-table, Ψ slacks, e≥58) | exact recomputation, tools/verify_gpt_arith.py | ALL EIGHT L(s) VALUES + slack sequence + conclusion EXACT |
| M(9)=19, M(10)=25 | SAT (tools/verify_gpt_tables.py) | CONFIRMED |
| M(11)=35 | SAT: **no such graph exists at all on 11 vertices** — CONFIRMED by two independent encodings (Z-side and complement J-side, 2026-07-10) | candidate's value is a VALID (conservative) lower bound; truth stronger — §5's two-K_5 case vacuous (count improves to 126>120); ω(H[L])≤4 concern moot |
| M(12) nonexistence | SAT (tools/verify_gpt_tables.py) | CONFIRMED |
| L(13..16) direct SAT | running (data/sat/gpt_tables_check.log) | pending (values LOWER than claimed would be fatal; higher is fine) |
| §5–§7 logic | line-by-line hand check (author session) | sound; the one flagged step (ω(H[L])≤4) is mooted by confirmed M(11) nonexistence |
| full adversarial review (fresh session) | reviewer-mh2 spawned 2026-07-10 | COMPLETE — see below |

---

## Adversarial review (2026-07-10, fresh session)

Reviewer scope: decide whether this candidate correctly proves **[MH″]** (no
balanced 5-colouring of $K_{25}$ with a colour $c$ and 4-set $T$, $\alpha(G_c-T)\le4$).
I re-derived every load-bearing step by hand and re-checked every finite claim with
my own encodings (scratchpad scripts, independent of the repo's `verify_gpt_*`).
Read in full: PROBLEM.md, extension-chain.md, this file, brouwer-kang-pikhurko.md,
NOTES.md, mh2-handproof-wip.md, and the encoders. I re-ran `verify_gpt_arith.py` and
wrote fresh SAT/arithmetic checks.

**Independent machine re-verifications I ran (all green):**
- Identities (4.1) and (4.2): re-derived by hand; confirmed exactly on 400 random
  graphs (sizes 4–14).
- (4.3) $b(d)=\lfloor 3d(d-1)/10\rfloor$: derived the ratio $6\binom d5/\binom{d-2}3=3d(d-1)/10$.
- M(9)=19, M(10)=25, M(11)=**None (no graph exists)** re-derived by SAT (my own encoding,
  cap-11 as atmost-11). Confirms the ledger; M(11)≥35 holds vacuously.
- §4.2 affine bounds $A_s-B_s d$: **valid pointwise on every feasible $d$** (min slack 0),
  and $\lceil sA_s/2B_s\rceil = L(s)$ for all $s=13..20$ (exact rational arithmetic).
- L(13..20)=24,31,38,46,53,62,73,84 reproduced by DP (bypassing affine bounds);
  Ψ slacks 32,21,11,4,1,0,0,…,214 all $\ge0$; $e(H)\ge1092/19\Rightarrow\ge58$.
- §7 finite lemmas: (a) **no 5-vertex 5-edge graph has all vertices triangle-covered**
  (brute force; min for a full triangle-cover is 6) — the final contradiction; (b)
  $\delta(H)\ge5$ holds strictly for **all** $d\le4$, not just $d=4$; (c) the $(r,w,c)$
  system yields exactly $\{(5,38,10),(6,38,9),(6,39,8)\}$, and $c\ge10$ leaves only $(5,38,10)$.
- **§5 Case B (decisive):** independent SAT shows **no cap-11 graph on 11 vertices with
  $\alpha\le2$ exists at all** (any $\omega$, not just $\omega\le4$).

Note: my direct-SAT cross-check of L(13),L(15) and a probe of the §1 "header" question both
timed out on this machine (expensive cap-11 UNSAT); neither is load-bearing — the L-values are
rigorously established by the recursion (identity + SAT'd M-values + pointwise affine bounds + DP),
and the header point is cosmetic.

### Per-section findings

**A. §1 reduction + (P) — CORRECT.** Restricting a balanced $K_{25}$ (+$c$,+$T$) to
$S=V\setminus T$ gives $H=G_c[S]$ with $\alpha(H)=\alpha(G_c-T)\le4$, $F_i=G_i[S]$ with
$\alpha(F_i)\le5$, and cap-11 + $K_6$-freeness on all five classes (6-subsets of $S$ are
6-subsets of $V$). (P) $\alpha(H[W_v])\le3\Leftrightarrow\alpha(H)\le4$ verified both directions.
*COSMETIC:* the boxed "stronger statement" mentions only the independence numbers $(4,5,5,5,5)$,
but the body genuinely uses cap-11 and $K_6$-freeness (invoked in §1). The literal header is thus
not what is proved; it should say "…arising from a balanced $K_{25}$" or list cap-11/$K_6$-free.
Irrelevant to [MH″], which supplies exactly those properties.

**B. §3 $e(F_i)\ge38$ — CORRECT.** $F_i$ $K_5$-free (else $H$-indep 5-set); $J_i=\overline{F_i}$
$K_6$-free, $\alpha(J_i)=\omega(F_i)\le4$, not 5-partite ($5\cdot4=20<21$); Brouwer $\Rightarrow
e(F_i)\ge37$. Equality excluded: only $(4,4,4,4,4)$ survives ($K_5$-freeness kills the others), the
$A/B$ structure is literature-FAITHFUL, $xy$ must be an $H$-edge, and the 20 $A$–$B$ edges carry
$4$ ($i$, exactly) $+\,5$ ($H$, $\ge$) $+\,3\times4$ ($j$, $\ge$, three ordinary $j\ne i$),
colour-disjoint, so $\ge21>20$. Every sub-claim checked by hand.

**C. §4 machinery — CORRECT.** (4.1),(4.2),(4.3), and $u(d)=\min(b(d),\mathrm{ex}(d,K_4))$
(uses $K_4$-free neighbourhoods when $\omega\le4$) all verified.

**D. §4.1 M-values — CORRECT (values); cosmetic write-up defects.** M(9)=19 hand proof verified
in full. M(11): the $e(Z)=33$ ($C_6$) and $e(Z)=34$ arguments are actually sound — "forces all
$p_x=2$" holds because $p_{x_0}=1$ would give $\sum_y p_y\ge15-d_B(x_0)$, forcing $d_B(x_0)\ge4>3$
(its max under $\Delta(J)\le4$); the final sub-case exclusions are terse but superseded. SAT gives
the stronger M(11)=None, so M(11)≥35 is valid vacuously. *COSMETIC:* the 12-vertex step says
"clique of size at most **five**, so every degree is at least **six**"; correct is size $\le4$ /
degree $\ge7$ ($\omega\le4$). Harmless — brackets $1,1,3,7,13,22$ for $d=6..11$ are all positive,
so the spurious $d=6$ term only strengthens the contradiction; SAT confirms M(12)=None.

**E. §4.2 L-table — CORRECT.** (4.9) re-derived with correct signs ($+M(W_v)$ lower, $-u(d)$ upper).
Degrees with $s-1-d\ge12$ genuinely infeasible. The affine bounds ARE valid pointwise (I feared
they were the loose link — they are not). DP and affine ceilings agree with the claimed $L$.

**F. §4.3 $e(H)\ge58$ — CORRECT.** $\Psi(d)\ge52-\tfrac{19}2d$ verified pointwise. No circular use
of (4.10): its hypothesis ($H$ $K_5$-free) is discharged independently in §5.

**G. §5 $H$ is $K_5$-free — CONCLUSION CORRECT; one sub-argument FIXABLE (unjustified as written).**
(5.1),(5.2) correct. Case A ($H[X]$ $K_5$-free): $e(H[X])\ge L(16)=46$ — solid. Case B
($H[X]\supseteq K_5=R$; $L=X\setminus R$, $|L|=11$):
- $\alpha(H[L])\le2$ is **correct**. The candidate's elided "suitably chosen nonadjacent vertices
  of $Q$ and $R$" is justified: cap-11 makes the $Q$–$R$ bipartite $H$-graph a matching, so the
  avoider sets $Q_0,R_0$ (each $\ge2$) have $\le\min$ cross-edges, leaving a non-adjacent pair
  that completes the independent 5-set.
- $\omega(H[L])\le4$ ("otherwise a third $K_5$ + (5.1) forces an $H$-$K_6$"): **I could not
  reconstruct this and judge it unjustified as written** (three disjoint $K_5$'s give only
  matchings across, not a $K_6$). *But the step is unnecessary:* my independent SAT shows **no
  cap-11 $\alpha\le2$ graph exists on 11 vertices for any $\omega$**. Since $H[L]$ is cap-11
  (induced) with $\alpha\le2$, Case B is **vacuous** — hence always Case A, $e(H[X])\ge46$, and
  $46+4\cdot20=126>120$ (or the candidate's $45+80=125$) gives the contradiction. VALID.
  *Repair:* the ledger's vacuousness is currently pinned to M(11) **with $\omega\le4$**, which
  needs the unproven $\omega(H[L])\le4$; use instead the $\omega$-free 11-vertex nonexistence
  (verified here) and drop the $\omega(H[L])\le4$ claim.

**H. §6 equalities — CORRECT.** $58+4\cdot38=210=\binom{21}2\Rightarrow e(H)=58,\ e(F_i)=38$.

**I. §7 endgame — CORRECT.** $\delta(H)\ge5$: text does only $d=4$; I verified all $d\le4$ give
strict contradictions ($216>190,189>171,166>153,145>136,126>120$) — conclusion holds; add the
$d\le3$ line. Degree-5 vertex exists ($116<126$). The $(r,w,c)$ arithmetic, the $5K_3$ forcing
(Turán uniqueness at 15; Brouwer $88<89$ at 16), the $X_j$-clique/$c\ge10$ step forcing $(5,38,10)$,
the $\rho_x$ counting ($\sum\rho_x=15=\sum(d_F(x)+1)\Rightarrow$ equality $\Rightarrow$ triangles
cover $A$), and the closing "5 triangles need $\ge6$ edges vs $e(F)=5$" all verified (the last by
brute force).

**J. §8 $n=24$ non-contradiction — CORRECT (illustrative).** $40+4\cdot30=160<190$,
$30+4\cdot15=90\le105$, $45+4\cdot20=125>120$ all check. Not load-bearing; "30" is the
$4K_5\to3K_5$ example value, not a claimed floor. Confirms the proof bites only at $n=25$
(odd part $21=4\cdot5+1$), matching the WIP's SAT falsification guard.

**K. Global — no circularity.** Order $M\text{-values}\to L\text{-table}\to\{(4.10),\S5\}$; §5 uses
(4.8)+M-values, never (4.10). The final contradiction contradicts exactly the assumption that the
[MH″] configuration exists. Cap-11 encodings (mine and repo's) faithfully model "every 6-set
$\le11$ edges."

### Findings ledger
- **FATAL: none.**
- **FIXABLE (validity holds; submitted text incomplete):** (i) §5 Case B — the $\omega(H[L])\le4$
  justification is unsound/unverifiable; replace with the verified fact that no cap-11 $\alpha\le2$
  graph exists on 11 vertices for any $\omega$ (Case B vacuous). This is the one real gap in the
  submitted text, closed by a machine lemma slightly stronger than the ledger's. (ii) §7.1 — add
  the $d\le3$ cases of $\delta(H)\ge5$ (a fortiori).
- **COSMETIC:** (iii) the boxed "stronger statement" omits the cap-11/$K_6$-free hypotheses the
  body uses; (iv) §4.1 12-vertex "clique $\le5$/degree $\ge6$" should be "$\le4$/$\ge7$"; M(11)/M(12)
  hand-proofs terse but SAT-covered.

### Verdict

**VERDICT: ACCEPTED MODULO** the two FIXABLE write-up repairs — chiefly (i), replacing §5's
unjustified $\omega(H[L])\le4$ step with the verified 11-vertex nonexistence lemma (no $\omega$
bound), which makes Case B vacuous. With that repair the proof of [MH″] is **correct and complete**:
every load-bearing arithmetic value, finite exclusion, and combinatorial step has been
independently re-derived or machine-checked, no circular dependency exists, and the argument bites
only at $n=25$. The submitted text contains exactly one real (but repairable, now-verified) gap;
the remaining items are cosmetic.

---

# Post-review repairs applied (author session, 2026-07-10)

Per the adversarial review's ACCEPTED MODULO verdict:
1. **§5 Case B repair (the one real gap)**: the claim ω(H[L]) ≤ 4 is unjustified as
   written, but unnecessary. Replacement lemma (machine-verified THREE ways: author's
   Z-side SAT with ω≤5 [= ω-free, as cap-11 already forbids K_6], author's complement
   J-side SAT, reviewer's independent SAT): **no graph on 11 vertices has α ≤ 2 and
   every 6-set spanning ≤ 11 edges — regardless of clique number.** Hence if H contained
   two disjoint K_5s, L = X∖R (11 vertices) would be such a graph (α(H[L]) ≤ 2 as
   correctly established in the candidate; cap-11 inherited): contradiction. So H
   contains at most one K_5, Case B never occurs, and §5's final count is
   46 + 4·20 = 126 > 120.
2. **Header fix**: the boxed "stronger statement" must include the standing hypotheses
   actually used: the 21-vertex 5-colouring inherits cap-11 and K_6-freeness from
   balancedness of the ambient K_25 (they hold for every class on every subset).
   The proved statement is: no 5-colouring of K_21 with all classes cap-11 and
   K_6-free has colour-graph independence numbers (4,5,5,5,5). [MH″] follows.
3. **§7.1**: δ(H) ≥ 5 as stated handles d = 4; d ≤ 3 a fortiori (W_v grows, floors
   L(16..19) ≥ 46 only strengthen the same count) — reviewer verified all d ≤ 4.
4. **§4.1 12-vertex wording**: non-neighbourhood is a clique of size ≤ 4 (ω ≤ 4),
   so δ ≥ 7; the candidate's "≥ 6" is a weaker premise covering more cases — harmless,
   and the value is SAT-confirmed anyway.

STATUS: with these repairs, [MH″] is PROVED (adversarially reviewed; every
load-bearing number machine-verified; external theorem literature-verified).
