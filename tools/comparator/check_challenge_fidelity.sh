#!/usr/bin/env bash
#
# check_challenge_fidelity.sh — fast, Linux-free fidelity guard for the comparator
# Challenge (tools/comparator/Challenge.lean).
#
# WHY THIS EXISTS.  comparator (the Linux-only leanprover tool) proves that our
# Solution proves the Challenge's *stated* theorems within the axiom budget.  But
# our Challenge is self-contained: it VENDORS the six statement-reachable
# definitions (`edgeCountIn`, `IsIndep`, `Main`, `alphaAtMost`, `AB21`,
# `KPEqualityClassification`) rather than importing them, so that an auditor can
# read Challenge.lean alone.  The whole harness is only meaningful if those
# vendored copies are the SAME objects as the canonical ones the Solution proves.
# comparator itself enforces this (it body-compares every statement-reachable
# constant against the built Solution), but that check runs only on Linux.  This
# script is the independent, everywhere-runnable guard: it verifies each vendored
# block is TEXTUALLY identical to its canonical source, and that the four theorem
# SIGNATURES match `lean617/Lean617/Final.lean`.  Textual identity of the source,
# under identical imports/opens, gives elaboration identity — which is what
# comparator will confirm at the kernel level.
#
# It does NOT need Lean, Mathlib, a build, or a network.  Run it anywhere:
#   tools/comparator/check_challenge_fidelity.sh
# Exit 0 = every vendored block and signature matches canonical.  Non-zero =
# drift (prints a unified diff of the first offender).  Wire it into CI and run
# it after any edit to Statements/LTable/Equality21/Final.lean or Challenge.lean.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
CHALLENGE="$REPO_ROOT/tools/comparator/Challenge.lean"

[ -f "$CHALLENGE" ] || { echo "FAIL: Challenge not found: $CHALLENGE" >&2; exit 1; }

python3 - "$REPO_ROOT" "$CHALLENGE" <<'PY'
import re, sys, difflib

repo, challenge = sys.argv[1], sys.argv[2]

# (decl_kind, name, canonical_file_relative_to_repo)
# defs: whole block (signature + body) is compared.
# theorems: only the signature (text up to the proof delimiter " :=") is compared,
#           because the Challenge's proof is `sorry` while the Solution's is real.
DEFS = [
    ("def", "edgeCountIn",               "lean617/Lean617/Statements.lean"),
    ("def", "IsIndep",                   "lean617/Lean617/Statements.lean"),
    ("def", "Main",                      "lean617/Lean617/Statements.lean"),
    ("def", "alphaAtMost",               "lean617/Lean617/LTable.lean"),
    ("def", "AB21",                      "lean617/Lean617/Equality21.lean"),
    ("def", "KPEqualityClassification",  "lean617/Lean617/Equality21.lean"),
]
THMS = [
    ("theorem", "erdos_617_r5_unconditional",          "lean617/Lean617/Final.lean"),
    ("theorem", "erdos_617_r5_upstream_unconditional", "lean617/Lean617/Final.lean"),
    ("theorem", "erdos_617_r5",                        "lean617/Lean617/Final.lean"),
    ("theorem", "erdos_617_r5_upstream",               "lean617/Lean617/Final.lean"),
]

def read(path):
    with open(path, encoding="utf-8") as f:
        return f.read().splitlines()

def extract_block(lines, kind, name):
    # Start line: optional `noncomputable `, then `def`/`theorem`, then the exact
    # name, then a delimiter (space/paren/brace/colon) so that e.g. `erdos_617_r5`
    # does NOT match `erdos_617_r5_unconditional`.
    start = re.compile(r'^(noncomputable )?' + kind + r' ' + re.escape(name) + r'([ ({:]|$)')
    idx = next((i for i, ln in enumerate(lines) if start.match(ln)), None)
    if idx is None:
        return None
    block = [lines[idx]]
    # Continuation lines are indented (start with a space); the block ends at the
    # first blank line or the first line beginning at column 0.
    j = idx + 1
    while j < len(lines) and lines[j].strip() != "" and lines[j][:1] == " ":
        block.append(lines[j])
        j += 1
    return "\n".join(block)

def signature_only(block):
    # Keep everything up to (not including) the proof delimiter " :=". Lean TYPES
    # never contain " :=" (that token only introduces a value/proof), so the first
    # occurrence is the delimiter.
    i = block.find(" :=")
    return block if i < 0 else block[:i]

chal = read(challenge)
failures = 0

def check(kind, name, canon_rel, sig_only):
    global failures
    canon_lines = read(f"{repo}/{canon_rel}")
    canon = extract_block(canon_lines, kind, name)
    mine  = extract_block(chal, kind, name)
    what = "signature" if sig_only else "definition"
    if canon is None:
        print(f"FAIL: {kind} {name}: not found in canonical {canon_rel}"); failures += 1; return
    if mine is None:
        print(f"FAIL: {kind} {name}: not found in Challenge.lean"); failures += 1; return
    if sig_only:
        canon, mine = signature_only(canon), signature_only(mine)
    if canon != mine:
        print(f"FAIL: {kind} {name}: vendored {what} differs from canonical ({canon_rel})")
        for d in difflib.unified_diff(
                canon.splitlines(), mine.splitlines(),
                fromfile=f"canonical:{canon_rel}", tofile="Challenge.lean", lineterm=""):
            print("  " + d)
        failures += 1
    else:
        print(f"ok:   {kind} {name}  ({what} identical to {canon_rel})")

for kind, name, f in DEFS:
    check(kind, name, f, sig_only=False)
for kind, name, f in THMS:
    check(kind, name, f, sig_only=True)

if failures:
    print(f"\nCHALLENGE FIDELITY FAILED: {failures} mismatch(es).")
    sys.exit(1)
print("\nCHALLENGE FIDELITY PASSED: all 6 vendored definitions and 4 theorem "
      "signatures are byte-identical to their canonical sources.")
PY
