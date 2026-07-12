# [ErGy99] Erdős–Gyárfás, "Split and balanced colorings of complete graphs"

## 1. Citation, source, grade

- **Full citation:** P. Erdős and A. Gyárfás, *Split and balanced colorings of complete graphs*, Discrete Mathematics **200** (1999) 79–86. Received 16 Feb 1996; revised 10 Jan 1997; accepted 7 Apr 1998. Publisher DOI `10.1016/S0012-365X(98)00323-9`, PII `S0012-365X(98)00323-9`.
- **Source actually read:** full-text PDF from Gyárfás's own page at the Rényi Institute, `https://www.renyi.hu/~gyarfas/Cikkek/92_splitandbalanced.pdf` (8 pp., matches the published version pagination 79–86). Retrieved and read in full **2026-07-05**.
- **Grade: VERIFIED** for everything in sections 2–6 below (read directly from the paper's text). The follow-up-literature notes in section 7 are marked individually.
- **Cross-check:** the paper's Conjecture 1 is *verbatim* the erdosproblems.com/617 statement and the `google-deepmind/formal-conjectures` Lean statement `Erdos617.erdos_617` (see section 8). All three agree.

---

## 2. Exact definitions (quoted verbatim)

**Split coloring** (Introduction, p. 80):

> An edge coloring of a complete graph $K$ with $r$ colors is called an **$(r,n)$-split coloring** if the vertices of $K$ can be partitioned into $r$ sets $S_1,\dots,S_r$ so that $S_i$ has no monochromatic $K_n$ in color $i$ for each $i$ ($1\le i\le r$). Usual split graphs correspond to $(2,2)$-split colorings.

> [...] let $f_r(n)$ be the smallest integer $m$ such that there exists an $r$-coloring of $K_m$ which is not $(r,n)$-split. Equivalently, $f_r(n)-1$ is the largest $m$ for which every $r$-coloring of the edges of $K_m$ is $(r,n)$-split.

**Balanced coloring** (Introduction, p. 80):

> An edge $r$-coloring of $K_N$ is called **balanced $(r,n)$-coloring** if every $A\subseteq V(K_N)$ such that $|A|=\lceil N/r\rceil$ contains a monochromatic $K_n$ in all colors. We define $g_r(n)$ as the minimum $N$ such that $K_N$ has a balanced $(r,n)$-coloring. Observe that a balanced $(r,n)$ coloring is not an $(r,n)$-split coloring, therefore $f_r(n)\le g_r(n)$.

Abstract phrasing (p. 79): "$f_r(n)$ [is] the smallest $N$ for which the complete graph $K_N$ has a coloring which is not $(r,n)$-split"; "Balanced $(r,n)$-colorings are defined as edge $r$-colorings of $K_N$ such that every subset of $\lceil N/r\rceil$ vertices contains a monochromatic $K_n$ in all colors."

**Problem 617 is the $n=2$ case.** A monochromatic $K_2$ in color $i$ is just an edge of color $i$, so *balanced $(r,2)$-coloring of $K_N$* = "every $\lceil N/r\rceil$-subset sees all $r$ colors". Equivalently: **each color class (as a graph) has independence number $\le \lceil N/r\rceil-1$** (a color-$i$-free vertex subset is exactly an independent set in the color-$i$ graph).

---

## 3. THE conjecture = Problem 617 (quoted verbatim), and how it pins down $g_r(2)$

The paper proves (Theorems 5,6, section 5) that
$$ r^2+1 \;\le\; g_r(2)\;\le\; r^2+r+1 \qquad(\text{upper bound needs a projective plane of order } r+1).$$
Then (p. 80):

> The special cases $r=3,4$ suggest that the upper bound is the truth ($g_2(2)=5$ seems to be exceptional). This would follow from the following conjecture:
>
> **Conjecture 1.** If the edges of $K_{r^2+1}$ are colored with $r$ colors then there exist $r+1$ vertices with at least one missing color among them ($r\ge 3$).

> The proof of this conjecture for $r=3,4$ is in the last section. From affine planes of order $r$ one can easily construct $r$-colorings of $K_{r^2}$ in which every set of $r+1$ vertices spans all colors. In fact, $r-1$ color classes can be defined by parallel classes of lines, and one by the union of two parallel classes. **This flexibility might suggest that the conjecture is not true.**

(Emphasis mine on the last sentence — the authors themselves flag doubt. See section 6, "attack notes".)

**Why Conjecture 1 $\Rightarrow g_r(2)=r^2+r+1$ (the reasoning the paper compresses):** For $r^2+1\le N\le r^2+r$ the balanced threshold is constant, $\lceil N/r\rceil=r+1$, so "balanced $(r,2)$" means "every $(r+1)$-subset sees all colors" = "every color class has $\alpha\le r$" for *all* these $N$. Deleting a vertex cannot raise $\alpha$, so **balanced($K_{N+1}$) $\Rightarrow$ balanced($K_N$)** within this range; contrapositively, if $K_{r^2+1}$ has no balanced coloring (Conjecture 1) then neither do $K_{r^2+2},\dots,K_{r^2+r}$. At $N=r^2+r+1$ the threshold jumps to $r+2$ and Theorem 5's construction succeeds. Hence Conjecture 1 forces $g_r(2)=r^2+r+1$.

**Relation to this repo's $N(r)$ (from PROBLEM.md).** PROBLEM.md defines $N(r)=$ largest $n$ admitting a balanced $r$-colouring (= every $(r+1)$-subset sees all $r$ colours = every colour class has $\alpha\le r$). This is exactly the fixed-threshold-$(r+1)$ quantity, cleaner than $g_r(2)$. The affine-plane construction gives $N(r)\ge r^2$ when an affine plane of order $r$ exists; **Conjecture 1 is precisely $N(r)\le r^2$, i.e. $N(r)=r^2$.** Do **not** conflate $N(r)$ with $g_r(2)$: they diverge because $g_r(2)$ uses the growing threshold $\lceil N/r\rceil$ and jumps at $N=r^2+r+1$.

---

## 4. What the paper proves for the balanced $(r,2)$ question (the core of Problem 617)

### Theorem 6 — lower bound $r^2+1\le g_r(2)$ (i.e. $K_{r^2}$ has no balanced $(r,2)$-coloring). VERIFIED.
Proof (Turán on the minority color, p. 83–84): take any $r$-coloring of $K_{r^2}$ and let red be a color class with no more edges than any other (the "minority" color), so
$$\#\text{red}\le \binom{r^2}{2}\big/ r.$$
A graph on $r^2$ vertices with **no** independent set of size $r$ (i.e. $\alpha\le r-1$) has a $K_r$-free complement, so by Turán it needs at least as many edges as the disjoint union of $r-1$ nearly-equal cliques on $r^2$ vertices — namely $r-2$ cliques $K_{r+1}$ and one $K_{r+2}$, giving $(r-2)\binom{r+1}{2}+\binom{r+2}{2}$ edges. But
$$ \frac{\binom{r^2}{2}}{r} \;<\; (r-2)\binom{r+1}{2}+\binom{r+2}{2},$$
which holds for all $r$. So red has $<$ that many edges $\Rightarrow$ red has an independent set of $r$ vertices $\Rightarrow$ those $r$ vertices span no red edge $\Rightarrow$ the coloring is not balanced. ("One needs a bit more careful calculation to see that there are no balanced $(r,2)$-colorings of $K_m$ for $m<r^2$ but this is omitted.")

### Theorem 5 — upper bound $g_r(2)\le r^2+r+1$ **if a projective plane of order $r+1$ exists**. VERIFIED.
Construction (p. 83): let $G_r$ = disjoint union of $r$ copies of $K_r$ and one $K_{r+1}$. Take a projective plane $P$ of order $r+1$ with two distinguished lines $L_1,L_2$, and $x\in L_2\setminus L_1$. Pick $r$ points $y_1,\dots,y_r\in L_1\setminus L_2$. Let $S=$ (points of $P$ off both distinguished lines) $\cup\{x\}$; then $|S|=r^2+r+1$. For each $i$, the $r+1$ lines through $y_i$ other than $L_1$ partition $S$ into $r$ blocks of size $r$ and one block of size $r+1$ (the block on the line through $y_i$ and $x$); let $H_i$ be the union of cliques on this partition, so $H_i\cong G_r$, and the $H_i$ are pairwise edge-disjoint. Color $H_i$ with color $i$ (color leftover pairs arbitrarily). Every $\lceil(r^2+r+1)/r\rceil=r+2$-subset of $S$ meets some block of the $(r+1)$-block partition of $H_i$ in two points (pigeonhole into $r+1$ blocks), hence contains a color-$i$ edge — balanced.

**>>> CRITICAL FOR r=5:** this construction needs a **projective plane of order $r+1=6$**, which **does not exist** (Bruck–Ryser; equivalently Tarry's resolution of Euler's 36-officers problem — no two orthogonal Latin squares of order 6). So **Theorem 5 gives *nothing* for $r=5$**: the paper does not establish $g_5(2)\le 31$, and does not even establish $g_5(2)$ is finite. Conjecture 1 for $r=5$ (= Problem 617) is only the *lower/impossibility* side, $K_{26}$ has no balanced coloring; even if proved, it yields only $g_5(2)\ge 31$, not equality. The whole $r=5$ picture is genuinely more open than $r=3,4$.

### Proposition 2 — $g_3(2)=13$, via Lemma 1. VERIFIED. (This is Conjecture 1 for $r=3$: $K_{r^2+1}=K_{10}$.)
> **Lemma 1.** If $K_{10}$ is colored with three colors then there exist four vertices spanning a $K_4$ with at least one missing color.

Proof (p. 84–85), reconstructed with the paper's steps made explicit:
- Let $G_1$ be the **minority** color class. On 10 vertices with $\le\lfloor 45/3\rfloor=15$ edges, so either $G_1$ is 3-regular (exactly 15 edges) or has a vertex $x_1$ with $\deg_{G_1}(x_1)\le 2$.
- **3-regular case:** by **Brooks' theorem**, $G_1$ is either 3-colorable or contains $K_4$. If 3-colorable, some color class of $G_1$ has $\ge\lceil 10/3\rceil=4$ vertices, independent in $G_1$ ⇒ 4 vertices missing color 1. If $K_4\subseteq G_1$, those 4 vertices are all-color-1 ⇒ miss colors 2,3. Either way done.
- **$\deg_{G_1}(x_1)\le 2$ case:** delete $x_1$ and its $\le 2$ neighbors; the remaining set $X$ (vertices non-adjacent to $x_1$ in color 1) has $|X|\ge 7$. If $G_1[X]$ has 3 independent vertices, they plus $x_1$ give 4 vertices pairwise non-adjacent in color 1 ⇒ missing color 1, done. So assume $\alpha(G_1[X])\le 2$; since $|X|\ge 7> R(3,3)=6$, $G_1[X]$ contains a triangle $Y$ (all color 1). Put $Z=X\setminus Y$. If two vertices of $Z$ are non-adjacent in $G_1$ then $G_1[X]$ contains $K_4-e$; otherwise $G_1[Z]$ is complete (a $K_{\ge4}$). In both cases 4 vertices span a $K_4$ or $K_4-e$ in color 1 ⇒ they miss at least one of colors 2,3.

Combined with Theorems 5,6 ($10\le g_3(2)\le 13$; note projective plane of order 4 exists) and the monotonicity of section 3, Lemma 1 gives $g_3(2)=13=3^2+3+1$.
**Tools used: minority-color edge count, Brooks' theorem, $R(3,3)=6$.**

### Proposition 3 — $g_4(2)=21$, via Lemma 2. VERIFIED (argument transcribed; long). (Conjecture 1 for $r=4$: $K_{r^2+1}=K_{17}$.)
> **Lemma 2.** If $K_{17}$ is colored by four colors then there exist five vertices spanning a $K_5$ with at least one missing color.

Proof structure (p. 85–86) — this is an intricate ad hoc argument, reproduced in outline:
- $G_1$ = minority color. $|E(G_1)|\le\lfloor\binom{17}{2}/4\rfloor=\lfloor136/4\rfloor=34$, so either $\delta(G_1)\le 3$ or $G_1$ is 4-regular.
- **4-regular case:** Brooks ⇒ $G_1$ is 4-colorable (⇒ a class of $\ge\lceil17/4\rceil=5$ vertices missing color 1) or contains $K_5$ (⇒ 5 vertices missing colors 2,3,4). Done.
- **$\delta(G_1)\le 3$ case:** take $x_1$ of degree $\le 3$, $M=N_{G_1}(x_1)$. A counting step gives a vertex $x_2$ of degree $\le 2$ in $G_1[A]$, $A=V\setminus(\{x_1\}\cup M)$; let $N=N_{G_1[A]}(x_2)$ and $X=V\setminus(\{x_1,x_2\}\cup M\cup N)$, so $|X|\ge 8$. May assume $G_1[X]$ has no 3 independent vertices (else with $x_1,x_2$ get 5 independent in $G_1$ ⇒ done), and assume property **(∗): $G_1$ has no 5-vertex subgraph with 8 edges.**
  - **Case 1: $G_1[X]$ contains $K_4=Y$.** With $Z=X\setminus Y$ and (∗), each $z\in Z$ sends $\le1$ edge to $Y$ in color 1, forcing $G_1[Z]$ complete; a short sub-argument (using $|M|=3,|N|=4$, (∗), and picking non-adjacent pairs $y_i,z_j$) produces 5 vertices independent in $G_1$ ⇒ 5 vertices missing color 1.
  - **Case 2: $G_1[X]$ has no $K_4$.** Since $R(3,4)=9$ and $\alpha(G_1[X])\le 2$ on $|X|\ge 8$, the extremal graph is unique: $G_1[X]$ is the 8-cycle with its short chords ($C_8^2$). An edge-counting argument across $[X,X],[N,X],[M,N],[M,X]$ (needing $\ge 35$ edges, contradicting the $\le34$ bound / definition of $G_1$; if instead a $K_{3,3}$ appears between $M$ and $N\setminus\{u,v\}$, then $u,v$ send 6 edges to $X$, contradiction) finishes the case.

Combined with Theorems 5,6 ($17\le g_4(2)\le 21$; projective plane of order 5 exists) and monotonicity, $g_4(2)=21=4^2+4+1$.
**Tools used: minority-color edge count, Brooks' theorem, $R(3,4)=9$ (with unique extremal graph $C_8^2$), a forbidden-5-vertex-8-edge condition, $K_{3,3}$ counting. The argument is heavily tailored to $r=4$ and does not visibly generalize.**

### Other balanced/split values in the paper (VERIFIED, context):
- **Theorem 2:** $f_2(n)=n^2$. **Theorem 3:** $2n(n-1)<g_2(n)\le(2n-1)^2$.
- **Theorem 4:** $\binom{r}{2}<f_r(2)$ (lower bound for the split function; parity of $r$ matters in the proof).
- **Theorem 1:** any $(r,n+1)$-Ramsey coloring is an $(r,n)$-split critical coloring.
- **Proposition 1:** $f_3(2)=8$. **Proposition 4:** $12\le f_4(2)\le 16$, $13\le g_2(3)\le 17$.
- Exceptional small value: $g_2(2)=5$ (pentagon 2-coloring of $K_5$; each color a $C_5$, $\alpha=2$). This is why Conjecture 1 requires $r\ge3$: for $r=2$, $K_{r^2+1}=K_5$ *does* have a balanced coloring, so Conjecture 1 is false at $r=2$.

---

## 5. The affine-plane construction of $K_{r^2}$ (the near-miss to build for r=5). VERIFIED (paper) + reconstructed.

The paper states (p. 80) that affine planes of order $r$ give an $r$-coloring of $K_{r^2}$ in which every $(r+1)$-set spans all colors ($r-1$ colors = single parallel classes, one color = union of two parallel classes). Reconstructed explicitly:

Affine plane $AG(2,r)$: $r^2$ points; lines of size $r$; $r+1$ parallel classes, each a partition of the points into $r$ lines. Every pair of points lies on exactly one line, so the $r+1$ parallel classes partition $E(K_{r^2})$. Build an $r$-coloring:
- **Colors $1,\dots,r-1$:** color $i$ = all edges lying within a line of parallel class $i$ (so color $i$ is a disjoint union of $r$ cliques $K_r$). Its independent sets pick $\le1$ point per line ⇒ $\alpha=r$.
- **Color $r$:** edges within lines of parallel class $r$ **and** class $r+1$ (merge two classes). Independent sets pick $\le1$ per line in both classes ⇒ a partial transversal of the $r\times r$ grid ⇒ $\alpha=r$.

All $r$ color classes have $\alpha=r$, so **every $(r+1)$-subset sees all $r$ colors** — a balanced $r$-coloring of $K_{r^2}$, witnessing $N(r)\ge r^2$.

**For $r=5$ (directly actionable):** $AG(2,5)$ exists (5 is prime), $r^2=25$, $r+1=6$ parallel classes. Colors 1–4 = parallel classes 1–4 (each = 5 disjoint $K_5$'s); color 5 = classes 5∪6. This is a concrete balanced 5-coloring of $K_{25}$ (every 6 vertices see all 5 colors), one vertex short of the $K_{26}$ target. **The natural counterexample attack is to extend/perturb this $K_{25}$ coloring to 26 vertices; the natural proof attack is to show no such extension (and no other coloring) can exist.** The authors' own "flexibility" remark points here: the choice of *which* two parallel classes to merge (and more generally the freedom in the construction) is exactly the slack a $K_{26}$ counterexample would have to exploit.

---

## 6. Remarks bearing directly on r=5 / K_26, and on general upper bounds

1. **First open case.** The paper proves Conjecture 1 only for $r=3,4$ (Lemmas 1,2). $r=5$ is untouched here and remains open (confirmed by the 2026 Lean formalization tagging only $r=3,4$ as solved; see §8).
2. **No projective plane of order 6** ⇒ Theorem 5's upper-bound construction fails at $r=5$. So $g_5(2)\le 31$ is *not* established by this paper, and $g_5(2)=31$ would not follow from Conjecture 1 alone for $r=5$ the way $g_3(2)=13,g_4(2)=21$ follow for $r=3,4$. (For $r=3,4$ the needed planes — orders 4 and 5 — exist.)
3. **General upper bound the paper gives:** only $g_r(2)\le r^2+r+1$ conditional on a projective plane of order $r+1$; no unconditional $g_r(2)\le c r^2$ is proved. So for $r$ where no plane of order $r+1$ exists (6, 10, 14, …), the paper leaves even finiteness of $g_r(2)$ unaddressed.
4. **General lower bound:** $g_r(2)\ge r^2+1$ (Theorem 6), holding for all $r$; this is the only fully general balanced result. Problem 617 asks to push the impossibility from $r^2$ up to $r^2+1$.
5. **Proof-method scaling.** The $r=3$ proof needs Brooks + $R(3,3)=6$; the $r=4$ proof already needs $R(3,4)=9$, the unique extremal graph $C_8^2$, and a delicate multi-region edge count. A same-style $r=5$ proof would engage the minority graph $G_1$ on 26 vertices with $\le\lfloor\binom{26}{2}/5\rfloor=\lfloor325/5\rfloor=65$ edges, i.e. either **exactly 5-regular** (Brooks ⇒ 5-colorable ⇒ a class of $\ge\lceil26/5\rceil=6$ vertices missing color 1, **or** $K_6$ ⇒ 6 vertices missing colors 2–5 — this max-edge case is clean) or $\delta(G_1)\le4$ (the hard low-degree regime, needing $R(3,5)=14$, $R(4,4)=18$, $R(3,6)=18$, $R(4,5)=25$-type inputs and much heavier case analysis). This suggests a computational / SAT approach may be more tractable than hand-generalizing Lemma 2.

---

## 7. Split colorings interacting with balanced, and follow-up literature

**Split ↔ balanced link inside the paper:** the only formal bridge is $f_r(n)\le g_r(n)$ (a balanced coloring is never split). For $n=2$ this chains with Theorem 4 to $\binom{r}{2}<f_r(2)\le g_r(2)$, and with Theorem 6 to $r^2+1\le g_r(2)$. The split function $f_r(2)$ is far smaller than $g_r(2)$ (e.g. $f_3(2)=8$ vs $g_3(2)=13$), so split results do not directly constrain the $K_{26}$ balanced question.

**Follow-up literature (mark grades; none found that resolves the balanced $r=5$ case):**
- Z. Füredi, R. Ramamurthi, *On splittable colorings of graphs and hypergraphs*, J. Graph Theory **40**(4) (2002) 226–237, DOI `10.1002/jgt.10044`. **[Author/venue VERIFIED via Crossref 2026-07-11 — this corrects an earlier note that named the co-author as A. Gyárfás; it is Ramamurthi.]** Scope **LEAD** (Wiley abstract HTTP 403, not read): title and context indicate it develops the **split** side ($f_r$, splittability), not the balanced $r^2+1$ conjecture. Confirmed off the critical path by the 2026-07-11 citation sweep (`papers/citation-sweep.md`): split $f_r$ is a strictly different, smaller quantity ($f_3(2)=8$ vs $g_3(2)=13$).
- No paper found announcing progress on Conjecture 1 / $g_r(2)$ for $r=5$ or general $r$. Multiple targeted searches (balanced coloring $K_{26}$, $r^2+1$, projective plane order 6, "split and balanced colorings" citations) returned only the split/generalized-Ramsey line of work, not this specific conjecture. **Consistent with the problem being open.** Note: "Erdős–Gyárfás conjecture" (Wikipedia) and "Erdős–Gyárfás function/problem $f(n,p,q)$" are a *different* body of work (generalized Ramsey, cycle lengths) — **do not conflate** with Problem 617.
- The paper's own references: [1] Földes–Hammer (split graphs, 1977); [2] Gleason–Greenwood (Ramsey, 1955, source of $R(3,4)$ etc.); [3] Golumbic (perfect graphs text); [4] Graham–Rothschild–Spencer (*Ramsey Theory*, 1980); [5] Gyárfás–Lehel (Helly-type problem in trees, 1969). **VERIFIED** (read from the reference list).

---

## 8. The formal statement (from `google-deepmind/formal-conjectures`, `FormalConjectures/ErdosProblems/617.lean`). VERIFIED (fetched via GitHub API 2026-07-05).

The Lean file's docstring restates Conjecture 1 verbatim and cites [ErGy99]. Machine statement of the open problem:
```lean
theorem erdos_617 (r : ℕ) (hr : r ≥ 3) {V : Type} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V = r^2 + 1) (coloring : Sym2 V → Fin r) :
    ∃ (S : Finset V) (k : Fin r),
      S.card = r + 1 ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k
```
i.e. *some* $(r+1)$-set $S$ and *some* color $k$ with no edge of $S$ colored $k$. Tagged `research open`. Companion lemmas `erdos_617.variants.r_eq_3` and `.r_eq_4` are tagged `research solved` (matching Lemmas 1,2). Variant `.r2` formalizes "fails for infinitely many $r$ if $r^2+1$ is replaced by $r^2$" as: the set of $r$ for which $K_{r^2}$ *has* a balanced coloring (every $(r+1)$-set sees all $r$ colors) is infinite — this is exactly the affine-plane construction of §5, valid at least for all prime-power $r$.

---

## 9. One-paragraph summary for the successor session

Problem 617 is Erdős–Gyárfás **Conjecture 1** of [ErGy99]: for $r\ge3$, $K_{r^2+1}$ has no *balanced* $r$-coloring (a coloring in which every $(r+1)$ vertices see all $r$ colors; equivalently every color class has independence number $\le r$). It is proved for $r=3$ ($K_{10}$, Lemma 1: Brooks + $R(3,3)=6$) and $r=4$ ($K_{17}$, Lemma 2: Brooks + $R(3,4)=9$ + heavy case analysis), false for $r=2$ (pentagon $K_5$). The extremal near-miss is the affine-plane coloring of $K_{r^2}$ (for $r=5$: $AG(2,5)$ gives an explicit balanced 5-coloring of $K_{25}$), and the authors explicitly note the "flexibility" of that construction as grounds for doubting the conjecture. For **$r=5$** specifically the situation is worse than $r=3,4$ on *both* sides: the impossibility ($K_{26}$) is the open Problem 617, **and** the matching upper bound $g_5(2)\le31$ is unavailable because there is **no projective plane of order 6**, so Theorem 5 does not apply.
