#!/usr/bin/env bash
#
# Regenerate the four SAT-primitive LRAT certificates that the Lean proof
# kernel-checks (lean617/Lean617/Primitives.lean, via `include_str` +
# `native_decide`). See FORMAL.md F3 for the full write-up.
#
# Pipeline for each primitive, exactly as validated:
#   1. emit the DIMACS CNF from the Lean definitions `nonexCNF` / `MCNF`
#      (the SAME `Erdos617F3` encoding the proof checks — no drifting copy);
#   2. solve with CaDiCaL producing an LRAT proof, with `--inprocessing=false`
#      (CRITICAL: otherwise CaDiCaL introduces fresh variables the Lean checker
#      silently drops, and the proof diverges);
#   3. trim + renumber the LRAT so its clause ids are consecutive (what Lean's
#      `compactLratChecker` requires); this mirrors bv_decide's `LratCert.load`.
# The emitted CNF is checksum-verified against tools/certgen/checksums.txt
# (canonical); the resulting LRAT is written to lean617/Lean617/certs/.
#
# Prerequisites: elan/lake toolchain, a built Mathlib cache in lean617/
# (`cd lean617 && lake exe cache get && lake build`), and CaDiCaL on PATH.
#
# Runtime: M9/M10 are seconds; nonex11/nonex12 can take minutes to hours of
# CaDiCaL time and produce ~340MB / ~455MB certificates. Pass primitive names as
# arguments to regenerate a subset, e.g. `tools/regen_certificates.sh M9 M10`.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN_DIR="$REPO_ROOT/lean617"
CERT_DIR="$LEAN_DIR/Lean617/certs"
EMIT="$REPO_ROOT/tools/certgen/emit_cnf.lean"
TRIM="$REPO_ROOT/tools/certgen/trim_lrat.lean"
MANIFEST="$REPO_ROOT/tools/certgen/checksums.txt"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

# emit args and certificate filename per primitive (bash-3.2 portable: no namerefs).
emit_args_for() {  # echoes the emit_cnf.lean arguments for a primitive
  case "$1" in
    nonex11) echo "nonex 11" ;;
    nonex12) echo "nonex 12" ;;
    M9)      echo "M 9 18" ;;
    M10)     echo "M 10 24" ;;
  esac
}

command -v cadical >/dev/null 2>&1 || { echo "ERROR: cadical not found on PATH." >&2; exit 1; }
command -v lake    >/dev/null 2>&1 || { echo "ERROR: lake not found on PATH (install elan)." >&2; exit 1; }
[ -d "$CERT_DIR" ] || mkdir -p "$CERT_DIR"

sha256() { shasum -a 256 "$1" | awk '{print $1}'; }

expected_cnf_sha() {  # $1 = primitive name
  awk -v p="$1" '$1==p && NF==4 && length($4)==64 {print $4}' "$MANIFEST" | head -1
}

regen_one() {
  local name="$1"
  local args; args="$(emit_args_for "$name")"
  local cnf="$WORK/${name}.cnf" raw="$WORK/${name}_raw.lrat" out="$CERT_DIR/${name}.lrat"

  echo "=== $name ==="
  echo "[1/3] emit CNF ..."
  # shellcheck disable=SC2086 -- $args is a deliberately word-split argument list
  ( cd "$LEAN_DIR" && lake env lean --run "$EMIT" $args "$cnf" )
  local got exp; got="$(sha256 "$cnf")"; exp="$(expected_cnf_sha "$name")"
  if [ -n "$exp" ] && [ "$got" != "$exp" ]; then
    echo "  FATAL: CNF sha256 mismatch for $name" >&2
    echo "    expected $exp" >&2
    echo "    got      $got" >&2
    echo "  The encoding drifted from tools/certgen/checksums.txt — stop and investigate." >&2
    exit 1
  fi
  echo "  CNF sha256 OK ($got)"

  echo "[2/3] CaDiCaL (--inprocessing=false, LRAT) ..."
  # CaDiCaL exits 20 on UNSAT; that is success here.
  set +e
  cadical "$cnf" "$raw" --lrat --binary=false --quiet --shrink=0 --unsat --inprocessing=false
  local rc=$?
  set -e
  if [ "$rc" -ne 20 ]; then
    echo "  FATAL: CaDiCaL did not report UNSAT (exit $rc)." >&2; exit 1
  fi

  echo "[3/3] trim + renumber -> $out"
  ( cd "$LEAN_DIR" && lake env lean --run "$TRIM" "$raw" "$out" )
  echo "  wrote $out ($(sha256 "$out"))"
  echo
}

targets=("$@")
if [ "${#targets[@]}" -eq 0 ]; then
  targets=(nonex11 nonex12 M9 M10)
fi
for t in "${targets[@]}"; do
  case "$t" in
    nonex11|nonex12|M9|M10) regen_one "$t" ;;
    *) echo "unknown primitive: $t (expected nonex11|nonex12|M9|M10)" >&2; exit 1 ;;
  esac
done

echo "Done. Certificates in $CERT_DIR"
echo "Re-check the proof with:  cd lean617 && lake build && lake env lean AxiomAudit.lean"
