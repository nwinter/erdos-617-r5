"""Generate the base_classification_deg3 isomorphism proof body (mirrors base_classification_deg2).
Map: position -> vertex.  0:sp1 1:sp2 2:y1 3:y2 4:s 5:z1 6:z2 7:z3 8:t."""

# position -> (varname, class, membership hyp or None)
POS = {
    0: ("sp1", "sp", "hsp1"), 1: ("sp2", "sp", "hsp2"),
    2: ("y1", "y", "hym1"),   3: ("y2", "y", "hym2"),
    4: ("s", "s", None),
    5: ("z1", "z", "hzm1"),   6: ("z2", "z", "hzm2"),   7: ("z3", "z", "hzm3"),
    8: ("t", "t", None),
}

def base9A2_adj(a, b):
    if a == b: return False
    if a == 8: return b in (0, 1, 4)
    if b == 8: return a in (0, 1, 4)
    return (a // 4 != b // 4) and not ((a == 4 and b in (0, 1)) or (b == 4 and a in (0, 1)))

# ---- distinctness ∀-lemmas (emitted as haves). Pairwise ≠ term for ordered pair (i,j) i≠j ----
def ne_term(i, j):
    """A term proving  var(i) ≠ var(j)."""
    vi, ci, mi = POS[i]; vj, cj, mj = POS[j]
    # same class multi-element
    if ci == cj == "sp": return "hsp12" if (i, j) == (0, 1) else "hsp12.symm"
    if ci == cj == "y":  return "hy12" if (i, j) == (2, 3) else "hy12.symm"
    if ci == cj == "z":
        pair = tuple(sorted((i, j)))
        name = {(5, 6): "hz12", (5, 7): "hz13", (6, 7): "hz23"}[pair]
        return name if (i, j) == pair else name + ".symm"
    # s / t
    if {ci, cj} == {"s", "t"}: return "hst" if ci == "s" else "hst.symm"
    # s vs class
    if ci == "s": return f"hs_{cj} {vj} {mj}"
    if cj == "s": return f"(hs_{ci} {vi} {mi}).symm"
    if ci == "t": return f"ht_{cj} {vj} {mj}"
    if cj == "t": return f"(ht_{ci} {vi} {mi}).symm"
    # sp/y/z cross (a<b in {sp,y,z})
    order = {"sp": 0, "y": 1, "z": 2}
    if order[ci] < order[cj]:
        return f"h{ci}_{cj} {vi} {mi} {vj} {mj}"
    else:
        return f"(h{cj}_{ci} {vj} {mj} {vi} {mi}).symm"

# collect unique ne terms for the injectivity first|
inj_terms = []
seen = set()
for i in range(9):
    for j in range(9):
        if i == j: continue
        t = ne_term(i, j)
        if t not in seen:
            seen.add(t); inj_terms.append(t)

# ---- adjacency terms (edges) both orientations ----
def adj_term(i, j):
    """term proving J.Adj var(i) var(j), given base9A2_adj(i,j) is True."""
    vi, ci, mi = POS[i]; vj, cj, mj = POS[j]
    # t-s
    if {ci, cj} == {"s", "t"}:
        return "hst_adj" if (ci, cj) == ("s", "t") else "hst_adj.symm"
    # t-sp  (J.Adj t sp = htsp sp hsp)
    if ci == "t" and cj == "sp": return f"htsp {vj} {mj}"
    if ci == "sp" and cj == "t": return f"(htsp {vi} {mi}).symm"
    # s-y (J.Adj s y = hsy y hy)
    if ci == "s" and cj == "y": return f"hsy {vj} {mj}"
    if ci == "y" and cj == "s": return f"(hsy {vi} {mi}).symm"
    # sp-z (J.Adj sp z = hspz sp hsp z hz)
    if ci == "sp" and cj == "z": return f"hspz {vi} {mi} {vj} {mj}"
    if ci == "z" and cj == "sp": return f"(hspz {vj} {mj} {vi} {mi}).symm"
    # y-z
    if ci == "y" and cj == "z": return f"hyz {vi} {mi} {vj} {mj}"
    if ci == "z" and cj == "y": return f"(hyz {vj} {mj} {vi} {mi}).symm"
    raise ValueError(f"unexpected edge {i},{j} classes {ci},{cj}")

# ---- non-adjacency terms (non-edges) both orientations ----
def nonadj_term(i, j):
    """term proving ¬ J.Adj var(i) var(j), given base9A2_adj(i,j) is False, i≠j."""
    vi, ci, mi = POS[i]; vj, cj, mj = POS[j]
    if ci == cj == "sp": return "hspindep sp1 hsp1 sp2 hsp2 hsp12" if (i, j) == (0, 1) else "hspindep sp2 hsp2 sp1 hsp1 hsp12.symm"
    if ci == cj == "y":  return "hyindep y1 hym1 y2 hym2 hy12" if (i, j) == (2, 3) else "hyindep y2 hym2 y1 hym1 hy12.symm"
    if ci == cj == "z":
        lo, hi = min(i, j), max(i, j)
        nm = {(5, 6): ("z1 hzm1 z2 hzm2 hz12"), (5, 7): ("z1 hzm1 z3 hzm3 hz13"), (6, 7): ("z2 hzm2 z3 hzm3 hz23")}[(lo, hi)]
        if (i, j) == (lo, hi): return f"hzindep {nm}"
        # symm
        nm2 = {(5, 6): "z2 hzm2 z1 hzm1 hz12.symm", (5, 7): "z3 hzm3 z1 hzm1 hz13.symm", (6, 7): "z3 hzm3 z2 hzm2 hz23.symm"}[(lo, hi)]
        return f"hzindep {nm2}"
    # sp-y : ¬Adj sp y = hnspy sp hsp y hy ; y-sp = fun h => hnspy ... h.symm
    if ci == "sp" and cj == "y": return f"hnspy {vi} {mi} {vj} {mj}"
    if ci == "y" and cj == "sp": return f"fun h => hnspy {vj} {mj} {vi} {mi} h.symm"
    # sp-s : J.Adj sp s -> ¬ = fun h => hnssp sp hsp h.symm ; s-sp: hnssp sp hsp
    if ci == "sp" and cj == "s": return f"fun h => hnssp {vi} {mi} h.symm"
    if ci == "s" and cj == "sp": return f"hnssp {vj} {mj}"
    # s-z : hnsz z hz ; z-s: fun h => hnsz z hz h.symm
    if ci == "s" and cj == "z": return f"hnsz {vj} {mj}"
    if ci == "z" and cj == "s": return f"fun h => hnsz {vi} {mi} h.symm"
    # t-y : hnty y hy ; y-t
    if ci == "t" and cj == "y": return f"hnty {vj} {mj}"
    if ci == "y" and cj == "t": return f"fun h => hnty {vi} {mi} h.symm"
    # t-z : hntz z hz ; z-t
    if ci == "t" and cj == "z": return f"hntz {vj} {mj}"
    if ci == "z" and cj == "t": return f"fun h => hntz {vi} {mi} h.symm"
    raise ValueError(f"unexpected non-edge {i},{j} classes {ci},{cj}")

edge_terms, nonedge_terms = [], ["fun h => (J.ne_of_adj h) rfl"]
es, ns = set(), set(nonedge_terms)
for i in range(9):
    for j in range(9):
        if i == j: continue
        if base9A2_adj(i, j):
            t = adj_term(i, j)
            if t not in es: es.add(t); edge_terms.append(t)
        else:
            t = nonadj_term(i, j)
            if t not in ns: ns.add(t); nonedge_terms.append(t)

# ---- emit ----
def emit_first(terms, indent, wrap="exact"):
    lines = []
    for t in terms:
        lines.append(" " * indent + f"| {wrap} " + (f"({t})" if wrap == "exact" and t.startswith("fun") else t))
    return "\n".join(lines)

out = []
out.append("  obtain ⟨spokes, ys, zs, hspcard, hycard, hzcard, hcover, hsnsp, hsny, hsnz,")
out.append("    htnsp, htny, htnz, hspydisj, hspzdisj, hyzdisj, htsp, hsy, hspz, hyz,")
out.append("    hnssp, hnsz, hnty, hntz, hnspy, hspindep, hyindep, hzindep⟩ :=")
out.append("    base_deg3_structure J hK3 s t hst hst_adj hs3 ht3 hother")
out.append("  obtain ⟨sp1, sp2, hsp12, hspeq⟩ := Finset.card_eq_two.mp hspcard")
out.append("  obtain ⟨y1, y2, hy12, hyeq⟩ := Finset.card_eq_two.mp hycard")
out.append("  obtain ⟨z1, z2, z3, hz12, hz13, hz23, hzeq⟩ := Finset.card_eq_three.mp hzcard")
out.append("  have hsp1 : sp1 ∈ spokes := by rw [hspeq]; exact Finset.mem_insert_self _ _")
out.append("  have hsp2 : sp2 ∈ spokes := by rw [hspeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)")
out.append("  have hym1 : y1 ∈ ys := by rw [hyeq]; exact Finset.mem_insert_self _ _")
out.append("  have hym2 : y2 ∈ ys := by rw [hyeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)")
out.append("  have hzm1 : z1 ∈ zs := by rw [hzeq]; exact Finset.mem_insert_self _ _")
out.append("  have hzm2 : z2 ∈ zs := by rw [hzeq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)")
out.append("  have hzm3 : z3 ∈ zs := by rw [hzeq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))")
# distinctness ∀-lemmas
out.append("  have hs_sp : ∀ w ∈ spokes, s ≠ w := fun w h he => hsnsp (he ▸ h)")
out.append("  have hs_y : ∀ w ∈ ys, s ≠ w := fun w h he => hsny (he ▸ h)")
out.append("  have hs_z : ∀ w ∈ zs, s ≠ w := fun w h he => hsnz (he ▸ h)")
out.append("  have ht_sp : ∀ w ∈ spokes, t ≠ w := fun w h he => htnsp (he ▸ h)")
out.append("  have ht_y : ∀ w ∈ ys, t ≠ w := fun w h he => htny (he ▸ h)")
out.append("  have ht_z : ∀ w ∈ zs, t ≠ w := fun w h he => htnz (he ▸ h)")
out.append("  have hsp_y : ∀ u ∈ spokes, ∀ w ∈ ys, u ≠ w := fun u hu w hw he => (Finset.disjoint_left.mp hspydisj hu) (he ▸ hw)")
out.append("  have hsp_z : ∀ u ∈ spokes, ∀ w ∈ zs, u ≠ w := fun u hu w hw he => (Finset.disjoint_left.mp hspzdisj hu) (he ▸ hw)")
out.append("  have hy_z : ∀ u ∈ ys, ∀ w ∈ zs, u ≠ w := fun u hu w hw he => (Finset.disjoint_left.mp hyzdisj hu) (he ▸ hw)")
# map
out.append("  set f : Fin 9 → Fin 9 := fun i =>")
out.append("    if i = 0 then sp1 else if i = 1 then sp2 else if i = 2 then y1 else if i = 3 then y2")
out.append("    else if i = 4 then s else if i = 5 then z1 else if i = 6 then z2 else if i = 7 then z3 else t")
out.append("    with hf")
out.append("  have hinj : Function.Injective f := by")
out.append("    intro i j hij")
out.append("    fin_cases i <;> fin_cases j <;>")
out.append("      simp only [hf, Fin.isValue, Fin.reduceEq, reduceIte, reduceCtorEq] at hij ⊢ <;>")
out.append("      first")
out.append("        | rfl")
for t in inj_terms:
    out.append(f"        | exact absurd hij ({t})")
    out.append(f"        | exact absurd hij ({t}).symm")
out.append("  let e := Equiv.ofBijective f ((Finite.injective_iff_bijective).mp hinj)")
out.append("  have hψ : ∀ i j : Fin 9, J.Adj (f i) (f j) ↔ base9A2.Adj i j := by")
out.append("    intro i j")
out.append("    fin_cases i <;> fin_cases j <;>")
out.append("      simp only [hf, Fin.isValue, if_true, if_false, reduceIte, reduceCtorEq] <;>")
out.append("      first")
out.append("        | (refine iff_of_true ?_ (by decide); first")
for t in edge_terms:
    out.append(f"            | exact " + (f"({t})" if t.startswith("fun") else t))
out[-1] = out[-1] + ")"
out.append("        | (refine iff_of_false ?_ (by decide); first")
for t in nonedge_terms:
    out.append(f"            | exact " + (f"({t})" if t.startswith("fun") else t))
out[-1] = out[-1] + ")"
out.append("  refine ⟨e.symm, fun u v => ?_⟩")
out.append("  have hu : f (e.symm u) = u := e.apply_symm_apply u")
out.append("  have hv : f (e.symm v) = v := e.apply_symm_apply v")
out.append("  have h := hψ (e.symm u) (e.symm v)")
out.append("  rw [hu, hv] at h")
out.append("  exact h")

body = "\n".join(out)
with open("scratchpad/deg3_iso_body.txt", "w") as fh:
    fh.write(body)
print(body)
print("\n\n# edge terms:", len(edge_terms), " nonedge terms:", len(nonedge_terms), " inj terms:", len(inj_terms))
