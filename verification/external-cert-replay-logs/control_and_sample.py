#!/usr/bin/env python3
"""Task B step 6 (perturbation controls) + step 5 (cadical full-formula sample).

Independent: our own graph scorer (not the bundle's score()/validate()), and
cadical/kissat for SAT/UNSAT verdicts.
"""
from __future__ import annotations
import itertools, json, subprocess, sys, tempfile, os
from pathlib import Path

REPO = Path("/Users/winter/research/erdos-617")
P25 = REPO / "review_queue/external-candidate-B/cert-bundle/p25_certificate"
ENV = {"PYTHONDONTWRITEBYTECODE": "1", "PATH": os.environ["PATH"]}


def E(u, v):
    return (u, v) if u < v else (v, u)


def solve(cnf, want):
    r = subprocess.run(["cadical", "--plain", "-q", str(cnf)],
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    return r.returncode, (r.returncode == want)


# ---- independent scorer for the 26-vertex signature control -----------------
def score_signature(edges, group_sizes):
    edges = set(edges)
    Q = range(5)
    groups = []
    cur = 5
    for s in group_sizes:
        groups.append(list(range(cur, cur + s)))
        cur += s
    exceptions = list(range(cur, 26))
    P = sum(E(q, w) in edges for q in Q for w in range(5, 26))
    eW = sum(E(u, v) in edges for u, v in itertools.combinations(range(5, 26), 2))
    six_counts = [sum(E(u, v) in edges for u, v in itertools.combinations(six, 2))
                  for six in itertools.combinations(range(26), 6)]
    # anchored six-sets: contain {i} U group_i
    anchored_max = 0
    for i, g in enumerate(groups):
        clique = [i] + g
        need = 6 - len(clique)
        outside = [v for v in range(26) if v not in clique]
        for extra in itertools.combinations(outside, need):
            six = clique + list(extra)
            cnt = sum(E(u, v) in edges for u, v in itertools.combinations(six, 2))
            anchored_max = max(anchored_max, cnt)
    margins = []
    for i, g in enumerate(groups):
        s_i = sum(E(i, x) in edges for x in exceptions)
        for w in g:
            ext = sum(E(w, v) in edges for v in range(5, 26) if v != w and v not in g)
            margins.append(ext - s_i)
    masks = [[q for q in Q if E(q, x) in edges] for x in exceptions]
    return {"edge_count": len(edges), "P": P, "e_W": eW,
            "min_six": min(six_counts), "max_six": max(six_counts),
            "max_anchored_six": anchored_max, "min_exchange_margin": min(margins),
            "exception_masks": masks}


# ---- independent scorer for the 18-vertex defect control --------------------
def score_defect(edges):
    edges = set(edges)
    X = range(14, 18)
    six_counts = [sum(E(u, v) in edges for u, v in itertools.combinations(six, 2))
                  for six in itertools.combinations(range(18), 6)]
    l = sum(E(x, q) in edges for x in X for q in (3, 4))
    b = sum(E(x, w) in edges for x in X for w in range(5, 14))
    c = sum(E(u, v) in edges for u, v in itertools.combinations(X, 2))
    return {"min_six": min(six_counts), "max_six": max(six_counts),
            "l": l, "b": b, "c": c, "defect": l + b + 2 * c}


def main():
    out = {}
    with tempfile.TemporaryDirectory() as d:
        tmp = Path(d)
        # ---- control 1: cap 65 -> 66 on 2222_23444 (expect SAT) ----
        cnf = tmp / "cap66.cnf"
        subprocess.run([sys.executable, "encode.py", "--pattern", "2222_23444",
                        "--budget-slack", "1", "--output", str(cnf)],
                       cwd=P25, env=ENV, check=True, stdout=subprocess.DEVNULL)
        rc, sat = solve(cnf, 10)
        ctrl = json.loads((P25 / "full_p25_budget66_control.json").read_text())
        edges = [tuple(e) for e in ctrl["selected_primary_edges"]]
        sc = score_signature(edges, [2, 3, 4, 4, 4])
        out["cap66"] = {"cadical_rc": rc, "sat": sat, "our_score": sc,
                        "expected": {"edge_count": 66, "P": 25, "e_W": 41,
                                     "min_six": 1, "max_anchored_six": 11,
                                     "min_exchange_margin": 0}}
        print("CAP66  cadical:", "SAT" if sat else f"rc={rc}", "| our rescore:", sc)

        # ---- control 2: six-set cap 11 -> 12 on defect mask 4 (expect SAT) ----
        cnf2 = tmp / "cap12.cnf"
        subprocess.run([sys.executable, "defect_lemma.py", "--cap", "12",
                        "--mask-index", "4", "--output", str(cnf2)],
                       cwd=P25, env=ENV, check=True, stdout=subprocess.DEVNULL)
        rc2, sat2 = solve(cnf2, 10)
        ctrl2 = json.loads((P25 / "cap12_control.json").read_text())
        edges2 = [tuple(e) for e in ctrl2["selected_primary_edges"]]
        sc2 = score_defect(edges2)
        out["cap12"] = {"cadical_rc": rc2, "sat": sat2, "our_score": sc2,
                        "expected": {"min_six": 1, "max_six": 12, "l": 0, "b": 10,
                                     "c": 2, "defect": 14}}
        print("CAP12  cadical:", "SAT" if sat2 else f"rc={rc2}", "| our rescore:", sc2)

        # ---- step 5: cadical FRESH on FULL formulas (>=2 sigs + >=5 orbits) ----
        full_results = []
        for name in ["5", "2222_23444"]:
            fc = tmp / f"full_{name}.cnf"
            subprocess.run([sys.executable, "encode.py", "--pattern", name,
                            "--output", str(fc)], cwd=P25, env=ENV, check=True,
                           stdout=subprocess.DEVNULL)
            rc, uns = solve(fc, 20)
            full_results.append({"kind": "signature", "key": name, "cadical_rc": rc, "unsat": uns})
            print(f"FULL sig {name}: cadical", "UNSAT" if uns else f"rc={rc}")
        for idx in [0, 4, 10, 20, 30, 50]:
            fc = tmp / f"full_orbit_{idx}.cnf"
            subprocess.run([sys.executable, "defect_lemma.py", "--mask-index", str(idx),
                            "--output", str(fc)], cwd=P25, env=ENV, check=True,
                           stdout=subprocess.DEVNULL)
            rc, uns = solve(fc, 20)
            full_results.append({"kind": "orbit", "key": idx, "cadical_rc": rc, "unsat": uns})
            print(f"FULL orbit {idx:02d}: cadical", "UNSAT" if uns else f"rc={rc}")
        out["cadical_full_sample"] = full_results

    Path("/private/tmp/claude-501/-Users-winter-research-erdos-617/6e908324-b2c0-4c6c-9413-c6d8812a5533/scratchpad/taskB/controls_sample.json").write_text(json.dumps(out, indent=1))
    print("\nwrote controls_sample.json")


if __name__ == "__main__":
    main()
