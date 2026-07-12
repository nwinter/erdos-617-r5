#!/usr/bin/env bash
#
# Source-level `sorry` gate: fails if any Lean source under the proof library
# contains a real `sorry`. This is a cheap cross-check; the AUTHORITATIVE gate is
# the axiom audit (a real `sorry` leaves `sorryAx`, which tools/axiom_audit.sh
# rejects). Prose mentions of "sorry-free" in comments are excluded.
#
# Run from anywhere: tools/sorry_grep.sh   (expects zero real hits)

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# `\bsorry\b` matches a standalone `sorry` and also `sorry-free` (the hyphen is a
# word boundary); it does NOT match `sorryAx`. We drop the documented prose form.
hits="$(grep -rnE '\bsorry\b' \
          "$REPO_ROOT/lean617/Lean617/" \
          "$REPO_ROOT/lean617"/*.lean 2>/dev/null \
        | grep -vE 'sorry-free' || true)"

if [ -n "$hits" ]; then
  echo "FAIL: candidate real 'sorry' in Lean sources:" >&2
  printf '%s\n' "$hits" >&2
  exit 1
fi

echo "SORRY GATE PASSED: no real 'sorry' in lean617/Lean617/ or lean617/*.lean."
