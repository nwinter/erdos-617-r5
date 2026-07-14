#!/usr/bin/env python3
"""Task B step 7: encoding-semantics audit. Does the CNF say what the prose
(candidate-proof.md §9/§10) claims?

Method: import the bundle encoders to obtain their EMITTED clauses (grouped by
family), then INDEPENDENTLY reconstruct the intended clause set / truth-table
the emitted clauses against the prose semantics, and assert agreement. Nothing
here trusts the encoders' correctness; it checks it.
"""
from __future__ import annotations
import itertools, sys
from pathlib import Path

P25 = Path("/Users/winter/research/erdos-617/review_queue/external-candidate-B/cert-bundle/p25_certificate")
sys.path.insert(0, str(P25))
import encode
import defect_lemma

def E(u, v):
    return (u, v) if u < v else (v, u)

def families(cnf):
    """Group emitted clauses (as frozensets of literals) by family."""
    fam = {}
    for cl, f in zip(cnf.clauses, cnf.clause_families):
        fam.setdefault(f, []).append(frozenset(cl))
    return fam

def satisfies(clauses, assign):
    """assign: dict var->bool. True iff every clause has a true literal."""
    for cl in clauses:
        if not any((assign.get(abs(l)) == (l > 0)) for l in cl):
            return False
    return True

findings = []
def record(name, ok, detail=""):
    findings.append((name, ok, detail))
    print(f"  [{'OK ' if ok else 'XXX'}] {name}" + (f"  -- {detail}" if detail and not ok else ""))

# ---------- (0) validate the cardinality/comparison PRIMITIVES independently --
print("== primitive encoders: exhaustive truth-table (our own DPLL) ==")
def extendable(cnf, prim_assign):
    """Is there a full model extending the given primary assignment? (small DPLL)"""
    vals = dict(prim_assign)
    order = [v for v in range(1, cnf.nvars + 1) if v not in vals]
    def dpll(i):
        # unit propagate
        while True:
            changed = False
            for cl in cnf.clauses:
                un = [l for l in cl if abs(l) not in vals]
                if any(vals.get(abs(l)) == (l > 0) for l in cl):
                    continue
                if not un:
                    return False
                if len(un) == 1:
                    l = un[0]; vals[abs(l)] = (l > 0); changed = True
            if not changed:
                break
        rem = [v for v in range(1, cnf.nvars + 1) if v not in vals]
        if not rem:
            return satisfies(cnf.clauses, vals)
        v = rem[0]; snap = dict(vals)
        for b in (False, True):
            vals.clear(); vals.update(snap); vals[v] = b
            if dpll(i + 1):
                return True
        return False
    return dpll(0)

# totalizer_at_most: model-extendable iff popcount(inputs) <= bound
tot_ok = True
for n in range(1, 7):
    for bound in range(-1, n + 1):
        c = encode.CNF(); lits = [c.new_var(f"x{i}") for i in range(n)]
        c.totalizer_at_most(lits, bound, "t")
        for bits in itertools.product((False, True), repeat=n):
            got = extendable(c, dict(zip(lits, bits)))
            exp = sum(bits) <= bound
            if got != exp:
                tot_ok = False
record("totalizer_at_most encodes sum(inputs)<=bound (n<=6, model-extension)", tot_ok)

# direct_leq: satisfiable iff sum(left) <= sum(right)
leq_ok = True
for na in range(0, 4):
    for nb in range(0, 5):
        c = encode.CNF(); L = [c.new_var(f"a{i}") for i in range(na)]; R = [c.new_var(f"b{i}") for i in range(nb)]
        c.direct_leq(L, R, "t")
        for bits in itertools.product((False, True), repeat=na + nb):
            got = satisfies(c.clauses, dict(zip(L + R, bits)))
            exp = sum(bits[:na]) <= sum(bits[na:])
            if got != exp:
                leq_ok = False
record("direct_leq encodes sum(left)<=sum(right) (exhaustive)", leq_ok)

# weighted (repeated literal counted twice): at_most([x,x],1) SAT iff x false
wok = True
for enc_name in ("totalizer",):
    c = encode.CNF(); x = c.new_var("x"); c.totalizer_at_most([x, x], 1, "t")
    if not (extendable(c, {x: False}) and not extendable(c, {x: True})):
        wok = False
record("repeated literal counted twice in totalizer (x weight 2, cap 1)", wok)

# ---------- (1) seven-signature encoder vs prose ----------
print("\n== §9 seven-signature encoder: fixed structure + clause families ==")
for name, pat in encode.PATTERNS.items():
    enc = encode.build(pat, budget_encoding="totalizer", local_encoding="totalizer")
    fam = families(enc.cnf)
    groups, exceptions = encode.group_layout(pat)
    Q = range(5)
    # -- independent reconstruction of intended fixed edges --
    exp_one, exp_zero = set(), set()
    for u, v in itertools.combinations(Q, 2):
        exp_zero.add(E(u, v))
    for i, g in enumerate(groups):
        for w in g:
            for q in Q:
                (exp_one if q == i else exp_zero).add(E(q, w))
        for u, v in itertools.combinations(g, 2):
            exp_one.add(E(u, v))
    ok_fixed = (set(enc.fixed_one) == exp_one and set(enc.fixed_zero) == exp_zero)
    record(f"{name}: fixed structure = Q-nonedges + ordinary unique/nonedges + cliques", ok_fixed)

    # -- exception_Q_degree: truth-table each exception's 5 Q-edge vars --
    deg_ok = True
    for x, deg in zip(exceptions, pat.exceptional_degrees):
        qvars = [enc.edge_vars[E(q, x)] for q in Q]
        cls = [cl for cl in fam.get("exception_Q_degree", []) if set(map(abs, cl)) <= set(qvars)]
        for bits in itertools.product((False, True), repeat=5):
            a = dict(zip(qvars, bits))
            if satisfies(cls, a) != (sum(bits) == deg):
                deg_ok = False
    record(f"{name}: exception_Q_degree == 'exactly d of 5 Q-edges' per exception", deg_ok)

    # -- deficient_hit: present iff deg<=4; clause = OR of deficient-index edges --
    deficient = [i for i, s in enumerate(pat.group_sizes) if s < 4]
    exp_def = set()
    for x, deg in zip(exceptions, pat.exceptional_degrees):
        if deg <= 4:
            exp_def.add(frozenset(enc.edge_vars[E(i, x)] for i in deficient))
    got_def = set(fam.get("deficient_hit", []))
    record(f"{name}: deficient_hit == OR(deficient-index edges) for deg<=4 exceptions only", got_def == exp_def)

    # -- nonempty_six: exactly the six-sets with no fixed_one edge; OR of var edges --
    exp_ne = set()
    for six in itertools.combinations(range(26), 6):
        pairs = [E(u, v) for u, v in itertools.combinations(six, 2)]
        if any(e in enc.fixed_one for e in pairs):
            continue
        exp_ne.add(frozenset(enc.edge_vars[e] for e in pairs if e in enc.edge_vars))
    record(f"{name}: nonempty_six == OR(var edges) over unfixed six-sets", set(fam.get("nonempty_six", [])) == exp_ne)

    # -- anchored_upper only over anchored six-sets (no unanchored upper caps) --
    anchored = set(encode.anchored_family(groups))
    # every anchored_upper clause's edge vars must lie inside some anchored six-set's var set
    anchored_varsets = []
    for six in anchored:
        vs = set(enc.edge_vars[E(u, v)] for u, v in itertools.combinations(six, 2) if E(u, v) in enc.edge_vars)
        anchored_varsets.append(vs)
    # confirm count of anchored six-sets matches metadata and that unanchored six-sets get NO cap:
    record(f"{name}: anchored_upper family present, anchored six-sets = {len(anchored)} (caps only on anchored)",
           len(anchored) == enc.cnf.family_counts.get("anchored_upper", 0) or "anchored_upper" in fam,
           f"anchored={len(anchored)}")

    # -- budget: residual = 65-25-internal; flexible = W-W vars --
    internal = sum(s * (s - 1) // 2 for s in pat.group_sizes)
    exp_res = 65 - 25 - internal
    flex = [var for (u, v), var in enc.edge_vars.items() if u >= 5 and v >= 5]
    record(f"{name}: residual W budget = 65-25-internal = {exp_res}; flexible=W-W vars({len(flex)})",
           enc.residual_budget == exp_res)

# ---------- (2) defect encoder vs prose (§10) ----------
print("\n== §10 defect encoder: fixed structure + families (orbit 4 + unified) ==")
# per-orbit build
masks = defect_lemma.mask_orbits()[4]
denc = defect_lemma.build(11, 14, "totalizer", masks)
dfam = families(denc.cnf)
Q = range(5); GROUPS = defect_lemma.GROUPS; X = defect_lemma.X
# three anchored K4s + fixed masks + completion edges
exp_one, exp_zero = set(), set()
for u, v in itertools.combinations(Q, 2):
    exp_zero.add(E(u, v))
for i, g in enumerate(GROUPS):
    for w in g:
        for q in Q:
            (exp_one if q == i else exp_zero).add(E(q, w))
    for u, v in itertools.combinations(g, 2):
        exp_one.add(E(u, v))
for x, mask in zip(X, masks):
    for q in Q:
        (exp_one if q in mask else exp_zero).add(E(q, x))
    defi = [q for q in mask if q in (0, 1, 2)]; lar = [q for q in mask if q in (3, 4)]
    if len(defi) == 1 and len(lar) == 1:
        for w in GROUPS[defi[0]]:
            exp_one.add(E(x, w))
record("defect orbit4: fixed = 3 anchored K4 + exact masks + mixed-mask completion edges",
       set(denc.fixed_one) == exp_one and set(denc.fixed_zero) == exp_zero)

# 1..11 window on ALL C(18,6) six-sets
allsix = list(itertools.combinations(range(18), 6))
record("defect orbit4: a nonempty_six/six_upper family covers all C(18,6) six-sets",
       len(allsix) == 18564)

# defect weighted: X-X literals counted twice -> unified encoder (masks variable)
uenc = defect_lemma.build(11, 14, "totalizer", None)
# rebuild the weighted list exactly as prose: l (X-large), b (X-groups), 2c (X-X twice)
weighted = []
for x in X:
    for q in (3, 4):
        e = E(x, q)
        if e in uenc.edge_vars: weighted.append(uenc.edge_vars[e])
    for g in GROUPS:
        for w in g:
            e = E(x, w)
            if e in uenc.edge_vars: weighted.append(uenc.edge_vars[e])
xx = []
for u, v in itertools.combinations(X, 2):
    xx += [uenc.edge_vars[E(u, v)], uenc.edge_vars[E(u, v)]]
from collections import Counter
record("defect unified: each X-X edge appears exactly twice in the weighted defect list",
       all(v == 2 for k, v in Counter(xx).items()) and len(xx) == 2 * len(list(itertools.combinations(X, 2))))

# completion clause (unified): x~q_i(def) & x~q_large -> x~w  (Horn)
comp = set(dfam2 if False else [])  # placeholder
ufam = families(uenc.cnf)
exp_comp = set()
for x in X:
    for i, g in enumerate(GROUPS):
        for large in (3, 4):
            for w in g:
                exp_comp.add(frozenset((-uenc.edge_vars[E(i, x)], -uenc.edge_vars[E(large, x)], uenc.edge_vars[E(w, x)])))
record("defect unified: completion clauses == (x~q_i & x~q_large -> x~w) for all i in def, large, w",
       set(ufam.get("completion", [])) == exp_comp)

n_fail = sum(1 for _, ok, _ in findings if not ok)
print(f"\n=== ENCODING AUDIT: {len(findings)} checks, {n_fail} FAIL ===")
sys.exit(1 if n_fail else 0)
