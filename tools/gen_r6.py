#!/usr/bin/env python3
"""Generate + score candidate balanced 6-colourings of K_36 (r=6) from algebraic starts.

There is NO affine plane of order 6 (Euler's 36 officers / no 2 MOLS of order 6), so unlike
r=5 (AG(2,5)) there is no construction giving a provably balanced K_36. The concrete shadow of
this: over Z_6 only the units {1,5} give Latin "slopes", so the difference colouring has at
most ~3 genuinely safe partition-classes (vertical, horizontal, one diagonal) -- each a
partition of Z_6^2 into 6 hexads, hence pigeonhole-safe (any 7 vertices repeat a block, so
that colour is always present). The remaining difference-classes must be packed into the
other colours, and THOSE are where 7-subsets can miss a colour.

We build several such difference (Cayley) colourings, score each with tools/score6 (the fast
scorer; verify.py is the referee), and write the best to data/r6/constructions/best_n36.json
as a warm start for locsearch6. Also a couple of product / random comparisons.

Vertices: (x,y) in Z_6^2, id = 6*x + y.  An edge {p,q} has difference (dx,dy)=(xq-xp,yq-yp)
mod 6; colour is a function of the +/- class of (dx,dy) (edges are unordered).

Usage: python3 tools/gen_r6.py            # build, score, report; writes constructions/*.json
"""
import json, os, subprocess, itertools, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
OUT = os.path.join(ROOT, "data", "r6", "constructions")
SCORE6 = os.path.join(HERE, "score6")
N = 36
R = 6


def canon(dx, dy):
    """Canonical representative of the +/- class of a nonzero difference (dx,dy) in Z_6^2."""
    a = (dx % 6, dy % 6)
    b = ((-dx) % 6, (-dy) % 6)
    return min(a, b)


# All 19 +/- classes and a structural label.
CLASSES = []
seen = set()
for dx in range(6):
    for dy in range(6):
        if (dx, dy) == (0, 0):
            continue
        c = canon(dx, dy)
        if c not in seen:
            seen.add(c)
            CLASSES.append(c)


def label(c):
    dx, dy = c
    if dx == 0:
        return "vert"          # same-column pairs
    if dy == 0:
        return "horiz"         # same-row pairs
    if dy == dx:
        return "diag+"         # y - x constant
    if (dy + dx) % 6 == 0:
        return "diag-"         # x + y constant
    return "leftover"


def build_matrix(colour_of_class):
    """colour_of_class: dict canon-class -> colour in 0..R-1 (must cover all 19 classes)."""
    M = [[-1] * N for _ in range(N)]
    for p in range(N):
        xp, yp = divmod(p, 6)
        for q in range(p + 1, N):
            xq, yq = divmod(q, 6)
            c = colour_of_class[canon(xq - xp, yq - yp)]
            M[p][q] = M[q][p] = c
    return M


def write(name, M):
    path = os.path.join(OUT, name)
    with open(path, "w") as f:
        json.dump({"r": R, "n": N, "colours": M}, f)
    return path


def score(path):
    """Return #violated 7-subsets via tools/score6 (fast C scorer)."""
    out = subprocess.run([SCORE6, path], capture_output=True, text=True)
    # line: "score6: n=36 V violations of TOTAL"
    for tok in out.stdout.split():
        if tok.isdigit():
            return int(tok)
    raise RuntimeError(f"score6 failed on {path}: {out.stdout} {out.stderr}")


def score_classmap(cmap, tmpname="_tmp_score.json"):
    return score(write(tmpname, build_matrix(cmap)))


def main():
    os.makedirs(OUT, exist_ok=True)
    if not os.path.exists(SCORE6):
        sys.exit("build tools/score6 first: cc -O3 -o tools/score6 tools/score6.c")

    vert = [c for c in CLASSES if label(c) == "vert"]
    horiz = [c for c in CLASSES if label(c) == "horiz"]
    dplus = [c for c in CLASSES if label(c) == "diag+"]     # incl (3,3)
    dminus = [c for c in CLASSES if label(c) == "diag-"]    # excl (3,3): (3,3) is labelled diag+
    left = [c for c in CLASSES if label(c) == "leftover"]
    print(f"classes: vert={vert} horiz={horiz} diag+={dplus} diag-={dminus}")
    print(f"leftover ({len(left)}): {left}")

    results = []  # (violations, name)

    # ---- Construction A: linear4 + best 2-split of the 8 leftover classes into colours 4,5.
    # colour 0=vert, 1=horiz, 2=diag+ (safe partition), 3=diag- (semi-safe: K6-minus-matching).
    base = {}
    for c in vert:  base[c] = 0
    for c in horiz: base[c] = 1
    for c in dplus: base[c] = 2
    for c in dminus: base[c] = 3
    bestA, bestAsplit = None, None
    for bits in range(1 << len(left)):
        cmap = dict(base)
        for i, c in enumerate(left):
            cmap[c] = 4 + ((bits >> i) & 1)
        v = score_classmap(cmap)
        if bestA is None or v < bestA:
            bestA, bestAsplit = v, bits
    cmapA = dict(base)
    for i, c in enumerate(left):
        cmapA[c] = 4 + ((bestAsplit >> i) & 1)
    write("A_linear4_n36.json", build_matrix(cmapA))
    results.append((bestA, "A_linear4_n36.json"))
    print(f"A linear4 (best 2-split of leftovers): {bestA} violations")

    # ---- Construction B: (3,3) split OUT to a leftover, both diagonals semi-safe.
    # 0=vert,1=horiz,2=diag+ w/o (3,3), 3=diag- , leftover+(3,3) -> {4,5} best split.
    base2 = {}
    for c in vert:  base2[c] = 0
    for c in horiz: base2[c] = 1
    for c in dplus:
        base2[c] = 2
    for c in dminus: base2[c] = 3
    movable = list(left) + [(3, 3)]     # (3,3) becomes assignable
    bestB, bestBsplit = None, None
    for bits in range(1 << len(movable)):
        cmap = dict(base2)
        for i, c in enumerate(movable):
            cmap[c] = 4 + ((bits >> i) & 1)
        v = score_classmap(cmap)
        if bestB is None or v < bestB:
            bestB, bestBsplit = v, bits
    cmapB = dict(base2)
    for i, c in enumerate(movable):
        cmapB[c] = 4 + ((bestBsplit >> i) & 1)
    write("B_linear3diag_n36.json", build_matrix(cmapB))
    results.append((bestB, "B_linear3diag_n36.json"))
    print(f"B linear3+diag ((3,3) freed): {bestB} violations")

    # ---- Construction C: 3 safe classes (vert,horiz,diag+); pack diag-+leftover greedily into 3,4,5.
    baseC = {}
    for c in vert:  baseC[c] = 0
    for c in horiz: baseC[c] = 1
    for c in dplus: baseC[c] = 2
    rest = dminus + left
    cmapC = dict(baseC)
    for i, c in enumerate(rest):        # seed a full valid assignment (round-robin over 3,4,5)
        cmapC[c] = 3 + (i % 3)
    for _ in range(3):                  # a few greedy sweeps to a local optimum
        for c in rest:
            best_c, best_v = cmapC[c], score_classmap(cmapC)
            for col in (3, 4, 5):
                cmapC[c] = col
                v = score_classmap(cmapC)
                if v < best_v:
                    best_v, best_c = v, col
            cmapC[c] = best_c
    vC = score_classmap(cmapC)
    write("C_greedy3hard_n36.json", build_matrix(cmapC))
    results.append((vC, "C_greedy3hard_n36.json"))
    print(f"C greedy-pack into 3 hard colours: {vC} violations")

    # ---- Construction P: K_6 x K_6 product / rook-ish. Colour by a mix of row/col relations.
    # (a,b): same row a -> colour by (b-b') class; same col b -> by (a-a'); else by (a-a')/(b-b')-ish.
    def prod_colour(p, q):
        a1, b1 = divmod(p, 6); a2, b2 = divmod(q, 6)
        da, db = (a2 - a1) % 6, (b2 - b1) % 6
        if da == 0:              # same row
            return 0
        if db == 0:              # same column
            return 1
        # both differ: 4 "product slopes" folded into 4 colours by (da,db) pattern
        return 2 + (((da * db) % 6) % 4)
    Mp = [[-1] * N for _ in range(N)]
    for p in range(N):
        for q in range(p + 1, N):
            Mp[p][q] = Mp[q][p] = prod_colour(p, q)
    vP = score(write("P_product_n36.json", Mp))
    results.append((vP, "P_product_n36.json"))
    print(f"P product/rook: {vP} violations")

    # ---- Random Cayley + random plain, for comparison (structure should beat these hugely).
    import random
    for s in (1, 2, 3):
        rng = random.Random(1000 + s)
        cmap = {c: rng.randrange(R) for c in CLASSES}
        vR = score_classmap(cmap, f"_tmp_randcayley{s}.json")
        results.append((vR, f"randcayley_s{s}"))
    rng = random.Random(42)
    Mr = [[-1] * N for _ in range(N)]
    for p in range(N):
        for q in range(p + 1, N):
            Mr[p][q] = Mr[q][p] = rng.randrange(R)
    vRand = score(write("_tmp_randplain.json", Mr))
    results.append((vRand, "randplain"))

    # clean up tmp scoring files
    for f in os.listdir(OUT):
        if f.startswith("_tmp"):
            os.remove(os.path.join(OUT, f))

    print("\n=== n=36 baseline scores (violations of 8,347,680 seven-subsets), best first ===")
    results.sort()
    for v, name in results:
        print(f"  {v:>10,}  {name}")

    # write the best real construction (exclude random comparisons) as the warm start
    real = [(v, n) for v, n in results if not n.startswith(("randcayley", "randplain"))]
    real.sort()
    bestv, bestname = real[0]
    src = os.path.join(OUT, bestname)
    dst = os.path.join(OUT, "best_n36.json")
    with open(src) as f:
        data = f.read()
    with open(dst, "w") as f:
        f.write(data)
    print(f"\nbest construction: {bestname} ({bestv:,} violations) -> {dst}")
    print(f"random-plain baseline for reference: {vRand:,} violations")


if __name__ == "__main__":
    main()
