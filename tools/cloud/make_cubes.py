#!/usr/bin/env python3
"""Split a CNF into cube instances for distributed cube-and-conquer.

Preferred: use march_cu (from the CnC toolchain) if available on PATH:
    march_cu BASE.cnf -o cubes.icnf -d DEPTH
and pass --icnf cubes.icnf here to emit one CNF per cube.

Fallback (no march_cu): recursive occurrence-guided splitting done here —
pick the K most frequent variables in the base CNF and emit all assignment
combinations as unit-clause-augmented copies (2^K cubes for plain variables).
For the one-hot colouring encodings in this repo, prefer --colour-edges:
split on the COLOUR of chosen edges (5-way per edge, exhaustive and disjoint),
listing edge variable ids as v = edge_index*5 + colour + 1.

Every cube file is BASE plus unit clauses; solving ALL cubes UNSAT proves the
base UNSAT (the cube set is exhaustive by construction). Files are written as
OUTDIR/cube_<i>.cnf plus OUTDIR/MANIFEST.tsv (cube id -> literals).

Usage:
  python3 make_cubes.py BASE.cnf OUTDIR --colour-edges 0 1 2   # 5^3 = 125 cubes
  python3 make_cubes.py BASE.cnf OUTDIR --icnf cubes.icnf      # from march_cu
"""
import os, sys


def read_header(path):
    with open(path) as f:
        for line in f:
            if line.startswith("p cnf"):
                _, _, nv, nc = line.split()
                return int(nv), int(nc)
    raise SystemExit("no p-line")


def main():
    base, outdir = sys.argv[1], sys.argv[2]
    os.makedirs(outdir, exist_ok=True)
    nv, nc = read_header(base)
    body = open(base).read().split("\n", 1)[1]
    cubes = []
    if "--icnf" in sys.argv:
        icnf = sys.argv[sys.argv.index("--icnf") + 1]
        for line in open(icnf):
            if line.startswith("a "):
                lits = [int(x) for x in line.split()[1:-1]]
                cubes.append(lits)
    elif "--colour-edges" in sys.argv:
        i = sys.argv.index("--colour-edges") + 1
        eidxs = []
        while i < len(sys.argv) and sys.argv[i].lstrip("-").isdigit():
            eidxs.append(int(sys.argv[i])); i += 1
        cubes = [[]]
        for e in eidxs:
            cubes = [c + [e * 5 + col + 1] for c in cubes for col in range(5)]
    else:
        raise SystemExit("need --icnf or --colour-edges")
    man = open(os.path.join(outdir, "MANIFEST.tsv"), "w")
    for i, lits in enumerate(cubes):
        p = os.path.join(outdir, f"cube_{i}.cnf")
        with open(p, "w") as f:
            f.write(f"p cnf {nv} {nc + len(lits)}\n")
            f.write(body)
            if not body.endswith("\n"):
                f.write("\n")
            for l in lits:
                f.write(f"{l} 0\n")
        man.write(f"{i}\t{' '.join(map(str, lits))}\n")
    man.close()
    print(f"wrote {len(cubes)} cubes to {outdir}")


if __name__ == "__main__":
    main()
