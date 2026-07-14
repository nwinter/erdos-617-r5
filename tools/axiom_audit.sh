#!/usr/bin/env bash
#
# Axiom audit gate for the four final theorems (lean617/AxiomAudit.lean).
#
# Passes iff every axiom every final theorem depends on is one of:
#   - an entry in the expected-axioms fixture tools/axiom_allowlist.txt
#     (currently: exact propext/Classical.choice/Quot.sound + FOUR TIGHT
#      per-primitive globs for the SAT-reflection axioms unsat_{nonex11,nonex12,
#      M9,M10}). After the ROUND-2026-07-14 kernel-pure migration the globs are
#      deliberately per-primitive (NOT a blanket *native_decide*), so the 10
#      KP-construction witnesses — now kernel `decide`, contributing no reflection
#      axioms — are regression-checked: if any regresses to native_decide its
#      axiom name will not match and the audit FAILS.
# FAILS on any `sorry`/`sorryAx`, or any other (unexpected) axiom.
#
# The expected list lives entirely in the fixture, so if R1 discharges
# `BrouwerFacts` and the discharge introduces new axioms, updating the audit is a
# one-line edit to tools/axiom_allowlist.txt (see the team-lead directive).
#
# The three standard axioms and at least one native_decide axiom must actually be
# present, so a parse failure or empty output cannot pass silently.
#
# Run from the repository root (or anywhere): tools/axiom_audit.sh
# Requires a built project (cd lean617 && lake exe cache get && lake build).

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN_DIR="$REPO_ROOT/lean617"
ALLOWLIST="$REPO_ROOT/tools/axiom_allowlist.txt"

[ -f "$ALLOWLIST" ] || { echo "FAIL: allowlist fixture not found: $ALLOWLIST" >&2; exit 1; }

# Parse the fixture into two lists of patterns.
exact_patterns=""
glob_patterns=""
while IFS= read -r line; do
  line="${line%%#*}"                      # strip comments
  line="$(printf '%s' "$line" | sed 's/^[[:space:]]*//; s/[[:space:]]*$//')"
  [ -z "$line" ] && continue
  case "$line" in
    exact:*) exact_patterns="$exact_patterns
${line#exact:}" ;;
    glob:*)  glob_patterns="$glob_patterns
${line#glob:}" ;;
    *) echo "FAIL: malformed allowlist line (need exact:/glob:): $line" >&2; exit 1 ;;
  esac
done < "$ALLOWLIST"

# Is $1 permitted by the fixture? echoes "exact", "glob", or nothing.
allow_kind() {
  local a="$1" p
  while IFS= read -r p; do [ -n "$p" ] && [ "$a" = "$p" ] && { echo exact; return; }; done <<EOF
$exact_patterns
EOF
  while IFS= read -r p; do
    [ -z "$p" ] && continue
    # shellcheck disable=SC2254 -- glob pattern is intentional
    case "$a" in $p) echo glob; return ;; esac
  done <<EOF
$glob_patterns
EOF
}

echo "Running #print axioms on the four final theorems ..."
out="$(cd "$LEAN_DIR" && lake env lean AxiomAudit.lean 2>&1)"
echo "----- raw output -----"
printf '%s\n' "$out"
echo "----------------------"

# Split every bracketed axiom list into one token per line.
axioms="$(printf '%s\n' "$out" \
  | tr '\n' ' ' \
  | grep -oE '\[[^]]*\]' \
  | tr ',[]' '\n\n\n' \
  | sed 's/^ *//; s/ *$//' \
  | grep -vE '^$' || true)"

if [ -z "$axioms" ]; then
  echo "FAIL: could not parse any axioms from the audit output." >&2
  exit 1
fi

fail=0
have_std=0
have_native=0
while IFS= read -r a; do
  [ -z "$a" ] && continue
  case "$a" in *[Ss]orry*) echo "FAIL: sorry axiom present: $a" >&2; fail=1; continue ;; esac
  case "$(allow_kind "$a")" in
    exact) have_std=$((have_std + 1)) ;;         # a standard axiom (propext/Classical/Quot)
    glob)  have_native=1 ;;                       # a native_decide SAT-reflection axiom
    *)     echo "FAIL: unexpected axiom (not in tools/axiom_allowlist.txt): $a" >&2; fail=1 ;;
  esac
done <<EOF
$(printf '%s\n' "$axioms" | sort -u)
EOF

# The three standard axioms should each appear (once, after sort -u).
if [ "$have_std" -lt 3 ]; then
  echo "FAIL: expected all three standard axioms (propext/Classical.choice/Quot.sound); saw $have_std." >&2
  fail=1
fi
if [ "$have_native" -ne 1 ]; then
  echo "FAIL: expected the native_decide SAT-reflection axiom(s); none found." >&2
  fail=1
fi

if [ "$fail" -ne 0 ]; then
  echo "AXIOM AUDIT FAILED." >&2
  exit 1
fi

echo "AXIOM AUDIT PASSED: every axiom is in tools/axiom_allowlist.txt (standard three + native_decide SAT reflection); no sorry."
