# Brouwer's non-r-partite Turán theorem and the Kang–Pikhurko extremal classification

Verification of the external theorem used in `review_queue/mh2-gpt56-candidate.md`
(Section 2, applied in Sections 3, 5, 7.1, 7.2).

## 1. Citation, source, grade

- **Bound (Brouwer).** A. E. Brouwer, *Some lotto numbers from an extension of Turán's theorem*,
  Math. Centrum report ZW152, Amsterdam (1981), 6 pp. — the origin of the edge bound.
  I did **not** read this report directly (it is a 1981 Mathematisch Centrum technical report,
  not online in a fetchable form). Its statement is quoted below from a secondary source.
- **Bound + extremal classification (Kang–Pikhurko).** M. Kang and O. Pikhurko,
  *Maximum $K_{r+1}$-free graphs which are not $r$-partite*, Matematychni Studii **24** (2005), no. 1, 12–20.
  DOI `10.30970/ms.24.1.12-20`. Received 08.07.2004.
  - **Source actually read:** the exact PDF the candidate cites,
    `https://matstud.org.ua/texts/2005/24_1/24_1_012_020.pdf`, retrieved **2026-07-10**,
    text extracted with `pdftotext -layout` and read in full (all 8 pp., Theorems 1–4, Lemma 5, proofs).
  - **Grade: VERIFIED** for everything attributed to KP in §§2–3 below.
- **Secondary confirmation of Brouwer's statement + attribution:** Ren, Wang, Wang, Yang,
  *Extremal triangle-free graphs with chromatic number at least four*, arXiv:2404.07486, Theorem 1.3,
  which cites Brouwer [4] = the ZW152 report above. Retrieved and read (relevant pages) **2026-07-10**.
  - **Grade: VERIFIED** that this paper states Brouwer's bound in exactly the form below and
    attributes it to Brouwer (1981). This is a secondhand statement of Brouwer's result, but a
    published, refereed one, and it agrees with the KP primary source.

**Bottom line:** the load-bearing external theorem is real, correctly attributed
("Brouwer's bound + Kang–Pikhurko equality classification"), and correctly cited (right paper, right URL).
All five uses in the candidate are **FAITHFUL**. Details and per-use verdicts below.

## 2. The theorem, exactly as stated in the sources

Notation (KP §1): $t_r(n) = e(T_r(n)) = \mathrm{ex}(n, K_{r+1})$ is the Turán number,
$T_r(n)$ the complete $r$-partite Turán graph. Define
$$\mathcal G_{n,r} = \{G : v(G)=n,\ K_{r+1}\not\subseteq G,\ \chi(G) > r\}\quad(\text{i.e. }K_{r+1}\text{-free and not }r\text{-partite}),$$
$$p_r(n) = \max\{e(G) : G \in \mathcal G_{n,r}\}.$$

**Brouwer (1981), as restated in arXiv:2404.07486, Thm 1.3 (quoted verbatim):**
> Let $G$ be a non-$r$-partite $K_{r+1}$-free graph on $n$ vertices. Then $e(G)\le t_r(n)-\lfloor n/r\rfloor+1.$

**Kang–Pikhurko, Theorem 1 (quoted verbatim from the PDF):**
> Let $n\ge r+3$ and $r\ge 2$. If $r>\frac{n-1}{2}$, then $p_r(n)=t_r(n)-2$. If $r\le\frac{n-1}{2}$, then
> $$p_r(n)=t_r(n)-\left\lfloor\frac{n}{r}\right\rfloor+1.\tag{1}$$
> Moreover, the extremal graphs are characterized by Theorem 4 and Lemma 5.

**On the hypotheses.** The candidate states the bound with hypothesis "$n\ge 2r+1$". This is *exactly*
KP's regime for formula (1): $r\le\frac{n-1}{2}\iff n\ge 2r+1$. Below that threshold the answer changes
to $t_r(n)-2$. (The arXiv restatement of Brouwer omits the threshold because $t_r(n)-\lfloor n/r\rfloor+1$
remains a valid *upper* bound for all $n\ge r+3$ — for $n\le 2r$ one has $\lfloor n/r\rfloor\le 2$, so
$t_r(n)-2\le t_r(n)-\lfloor n/r\rfloor+1$ — it is merely not tight there.) The candidate's every use has
$n\in\{15,16,21\}\ge 11 = 2r+1$ with $r=5$, so all uses lie in the regime where (1) holds **with equality
attained** and the KP extremal classification applies. Correct.

## 3. The extremal classification (KP Theorem 4 + Lemma 5), exactly as in the source

**The construction $G(\mathbf n)$ (KP §2, verbatim-faithful paraphrase).**
Fix $n\ge r+3$. Choose integers $1\le n_1\le\dots\le n_r$ with $\sum_i n_i=n-1$ and $n_{r-1}\ge 2$,
and pairwise disjoint sets $N_i$, $|N_i|=n_i$. Let $s,t$ be the two smallest indices with $n_i>1$
(so $|s-t|=1$), and $S=[r]\setminus\{s,t\}$. Choose a *proper* subset $A^\ast\subset N_s$
($\emptyset\ne A^\ast\ne N_s$) and a vertex $y\in N_t$. Start from the complete $r$-partite graph
$K_r(N_1,\dots,N_r)$; **add one vertex $x$** adjacent to everything in $(\bigcup_{i\in S}N_i)\cup(\{y\}\cup A^\ast)$;
and **remove all edges between $y$ and $A^\ast$**. This $G(\mathbf n)$ is $K_{r+1}$-free with $\chi>r$
(KP prove both), and $e(G(\mathbf n))=\sigma_2(\mathbf n)+\sigma_1(\mathbf n)-n_s-n_t+1$.

**KP Theorem 4 (verbatim):** "Let $r\ge2$ and $n\ge r+3$. Then $p_r(n)$ equals the maximum of $e(G(\mathbf n))$
over all integers satisfying (3). **Moreover, all extremal graphs are described by our construction.**"
— So every equality graph is some $G(\mathbf n)$; there are no sporadic extremal graphs.

**KP Lemma 5 (verbatim), the optimal sequences.** For $r\le\frac{n-1}{2}$, the optimal $\mathbf n$ are
*precisely* those satisfying $\sum n_i=n-1$, $n_1\le\dots\le n_r$, $n_{r-1}\ge2$, and
$$n_1\ge2,\qquad n_2\le n_1+1,\qquad n_r\le n_1+2,\qquad n_r\le n_3+1.$$
(There are between 1 and 3 such sequences.)

## 4. Verification of the arithmetic

Turán edge counts and Brouwer bounds, recomputed in Python
(`comb(n,2)` minus within-part pairs for the balanced parts):

| $r=5$ | Turán parts | $t_5(n)$ | $\lfloor n/5\rfloor$ | Brouwer bound $t_5(n)-\lfloor n/5\rfloor+1$ |
|---|---|---|---|---|
| $n=21$ | $(5,4,4,4,4)$ | **176** | 4 | $176-4+1=\mathbf{173}$ |
| $n=16$ | $(4,3,3,3,3)$ | **102** | 3 | $102-3+1=\mathbf{100}$ |
| $n=15$ | $(3,3,3,3,3)$ | **90** | 3 | $90-3+1=\mathbf{88}$ |

All three match the candidate ($176-3=173$, $102-2=100$, $90-2=88$; note the candidate writes the
$-\lfloor n/r\rfloor+1$ correction as $-3$, $-2$, $-2$ respectively, which is right). **Arithmetic confirmed.**

## 5. Per-use verdicts

### USE 1 — Section 3, $n=21$ edge bound. **FAITHFUL.**
$J_i=\overline{F_i}$ on the 21 vertices of $S$ is $K_6$-free ($\alpha(F_i)\le5$) and not 5-partite
($\alpha(J_i)=\omega(F_i)\le4$, so 5 parts cover $\le20<21$). Brouwer with $r=5,n=21\ge11$ gives
$e(J_i)\le173$, hence $e(F_i)\ge210-173=37$. Correct application and arithmetic.

### USE 2 — Section 3, $n=21$ equality classification + $A,B$ structure. **FAITHFUL.**
When $e(F_i)=37$, $J_i$ is a maximum graph in $\mathcal G_{21,5}$, so by KP Theorem 4 it is some $G(\mathbf n)$
with $\mathbf n$ optimal (Lemma 5). I enumerated Lemma 5's conditions for $r=5$, $\sum n_i=20$ in Python:
the optimal sequences are **exactly $(4,4,4,4,4)$, $(3,4,4,4,5)$, $(3,3,4,5,5)$** — matching the candidate's
list on "the 20 old vertices." In $F_i=\overline{J_i}$ each part $N_j$ becomes a clique $K_{n_j}$; a part of
size 5 is a $K_5$ in $F_i$, but $F_i$ is $K_5$-free, so the two sequences containing a 5 are excluded and only
$(4,4,4,4,4)$ survives. Exactly as the candidate states.

The $A,B$ structure is also faithful. Translating $G(\mathbf n)$ with $\mathbf n=(4,4,4,4,4)$ (here
$s=1,t=2$, $A^\ast\subset N_1$, $y\in N_2$) into $F_i=\overline{G(\mathbf n)}$:
- Take $A=N_2\cup\{x\}$ (size 5). $N_2$ is a $K_4$ in $F_i$; $x$ is $F_i$-adjacent to $N_2\setminus\{y\}$
  (3 vertices) but not to $y$. So $F_i[A]=K_5-xy$. ✔ (matches "$F_i[A]=K_5-xy$")
- Take $B=N_1$ (size 4). $N_1$ is a $K_4$ in $F_i$. ✔ (matches "$F_i[B]=K_4$")
- Cross $F_i$-edges $A\!-\!B$: from $x$ to $N_1\setminus A^\ast$ ($4-|A^\ast|$ edges) plus from $y$ to $A^\ast$
  ($|A^\ast|$ edges); the other three vertices of $N_2$ send none. Total $(4-|A^\ast|)+|A^\ast|=4$,
  **independent of $|A^\ast|\in\{1,2,3\}$.** ✔ (matches "exactly four $i$-edges join $A$ to $B$")

So the three structural bullets hold for every $(4,4,4,4,4)$ extremal graph. (The candidate's downstream
deductions — that $xy$ must be an $H$-edge, $e_j(A,B)\ge4$, $e_H(A,B)\ge5$, contradiction $\ge21>20$ — are
internal cap-11/$\alpha(H)\le4$ arguments, outside this literature check; the *external structural input*
they consume is correct.)

### USE 3 — Section 5, $n=16$ edge bound. **FAITHFUL.**
$J=\overline{F_i[X]}$, $|X|=16$, is $K_6$-free ($\alpha(F_i[X])\le5$) and not 5-partite
($\alpha(J)=\omega(F_i[X])\le3$ since $F_i[X]$ is $K_4$-free, so 5 parts cover $\le15<16$).
Brouwer with $r=5,n=16\ge11$: $e(J)\le100$, hence $e(F_i[X])\ge120-100=20$. Correct.

### USE 4 — Section 7.1, $n=16$ edge bound. **FAITHFUL.**
Identical structure to USE 3 with $X=W_v$, $|W_v|=16$; $F_i[W_v]$ is $K_4$-free, giving $e(F_i[W_v])\ge20$.
Correct.

### USE 5 — Section 7.2, $n=15$ edge bound (contrapositive). **FAITHFUL.**
$\overline{F_i[W]}$, $|W|=15$, is $K_6$-free ($\alpha(F_i[W])\le5$) and has $\binom{15}{2}-16=89$ edges.
Brouwer with $r=5,n=15\ge11$ says a $K_6$-free *non*-5-partite graph on 15 vertices has $\le t_5(15)-3+1=88<89$
edges; hence $\overline{F_i[W]}$ must be 5-partite. With $\omega(F_i[W])\le3$ this forces five parts of size 3,
i.e. $W$ splits into five $i$-triangles. Correct use of the bound in contrapositive form.

## 6. Discrepancies found

**None.** The theorem is stated with the correct bound, the correct attribution (Brouwer for the bound,
Kang–Pikhurko for the extremal classification), the correct hypothesis regime ($n\ge2r+1$), and the correct
citation/URL. The arithmetic ($t_5(21)=176$, $t_5(16)=102$, $t_5(15)=90$) is right. The equality-case
part-size enumeration for $n=21$ reproduces KP Lemma 5 exactly, and the $A/B$ structural description is a
faithful reading of KP's explicit construction $G(\mathbf n)$. Every one of the five uses is FAITHFUL.

*One caveat for the record, not a defect:* KP's own paper does **not** cite Brouwer (their reference list has
no Brouwer entry) — they appear to have rediscovered the bound and additionally supplied the extremal
classification. The attribution "Brouwer's theorem + Kang–Pikhurko classification" is nonetheless the standard
and correct one (confirmed by arXiv:2404.07486, which cites both). The candidate relies only on facts that are
explicitly in the KP paper I read, so this does not affect any verdict.
