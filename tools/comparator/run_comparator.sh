#!/usr/bin/env bash
#
# run_comparator.sh — assemble the comparator workspace and run the check for the
# four final theorems.  This is the single source of truth for the Linux
# invocation; CI (.github/workflows/verify.yml, job `comparator`) calls it, and so
# should any human running it in a Linux container.
#
# WHAT IT DOES
#   1. Discovers the three comparator binaries (landrun, lean4export, comparator)
#      from env vars or PATH.  It does NOT build them — see BUILDING below.
#   2. Builds a throwaway lake workspace ($WORKDIR, default tools/comparator/.work,
#      git-ignored) whose toolchain is OUR Lean (v4.30.0) so that Challenge and
#      Solution are built with the same toolchain + Mathlib the Solution needs:
#         - depends on mathlib @ v4.30.0 and on this repo's lean617 (path dep),
#         - `lean_lib Challenge`  = a copy of tools/comparator/Challenge.lean,
#         - the Solution module is `Lean617.Final`, reached through the lean617 dep
#           (no shim: comparator builds and exports `Lean617.Final` directly).
#   3. Invokes `lake env <comparator> <config>` from $WORKDIR.  Exit 0 = the
#      Solution proves all four Challenge theorems within the axiom budget and is
#      kernel-accepted; non-zero = rejected (comparator prints why).
#
# TOOLCHAIN BOUNDARY (the load-bearing caveat — see README.md "Toolchain").
#   Our Solution is Lean v4.30.0; upstream comparator/lean4export track v4.33.
#   `lean4export` reads OUR v4.30 oleans, so it MUST be built against a
#   v4.30.0-compatible revision (olean format is version-specific).  The
#   `comparator` binary only parses lean4export's TEXT export, so a v4.33
#   comparator MAY work if the export format is compatible across those versions;
#   if it is not, either pin comparator+lean4export to a v4.30-compatible commit
#   or bump lean617 to v4.33.  This is why CI runs the job continue-on-error until
#   the pairing is proven.  This script leaves the pinning to the environment
#   (the CI job / your container) and just runs whatever binaries you point it at.
#
# BUILDING THE BINARIES (done by CI or by you, once):
#   landrun    : github.com/Zouuup/landrun  — `go build -o landrun cmd/landrun/main.go`
#   lean4export: github.com/leanprover/lean4export at a v4.30.0-compatible rev,
#                built with elan on the v4.30.0 toolchain (`lake build`)
#   comparator : github.com/leanprover/comparator (pin a commit) — `lake build comparator`
#   then export the paths:
#     COMPARATOR_LANDRUN=/abs/landrun
#     COMPARATOR_LEAN4EXPORT=/abs/lean4export
#     COMPARATOR_COMPARATOR=/abs/comparator            (the comparator exe)
#   On macOS there is no real landrun; point COMPARATOR_LANDRUN at the upstream
#   scripts/fake-landrun.sh to run UNSANDBOXED (dev only — the sandbox guarantee
#   is void; do not treat a macOS pass as authoritative).
#
# ENV OVERRIDES
#   COMPARATOR_LANDRUN, COMPARATOR_LEAN4EXPORT, COMPARATOR_NANODA  (comparator's own)
#   COMPARATOR_COMPARATOR   path to the comparator exe (else `comparator` on PATH)
#   WORKDIR                 workspace dir (default: tools/comparator/.work)
#   MATHLIB_REV/LEAN617_PATH override the workspace deps (defaults derived here)

set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$HERE/../.." && pwd)"
LEAN617_PATH="${LEAN617_PATH:-$REPO_ROOT/lean617}"
CONFIG="$HERE/erdos617_r5.json"
CHALLENGE_SRC="$HERE/Challenge.lean"
WORKDIR="${WORKDIR:-$HERE/.work}"

TOOLCHAIN="$(cat "$LEAN617_PATH/lean-toolchain")"          # leanprover/lean4:v4.30.0
MATHLIB_REV="${MATHLIB_REV:-$(sed -n 's/^[[:space:]]*rev *= *"\(.*\)".*/\1/p' "$LEAN617_PATH/lakefile.toml" | head -1)}"

echo "== comparator run =="
echo "repo             : $REPO_ROOT"
echo "solution (lean617): $LEAN617_PATH   toolchain $TOOLCHAIN   mathlib $MATHLIB_REV"
echo "workspace        : $WORKDIR"

# --- 1. discover binaries -----------------------------------------------------
resolve() {  # resolve VARNAME fallback-command
  local var="$1" fallback="$2" val="${!1:-}"
  if [ -n "$val" ]; then echo "$val"; return; fi
  command -v "$fallback" 2>/dev/null || true
}
LANDRUN="$(resolve COMPARATOR_LANDRUN landrun)"
LEAN4EXPORT="$(resolve COMPARATOR_LEAN4EXPORT lean4export)"
COMPARATOR="$(resolve COMPARATOR_COMPARATOR comparator)"

missing=0
for pair in "landrun:$LANDRUN" "lean4export:$LEAN4EXPORT" "comparator:$COMPARATOR"; do
  name="${pair%%:*}"; path="${pair#*:}"
  if [ -z "$path" ] || [ ! -x "$path" ]; then
    echo "MISSING binary: $name (set COMPARATOR_${name^^} or put it on PATH; see BUILDING in this script)" >&2
    missing=1
  else
    echo "$name -> $path"
  fi
done
[ "$missing" -eq 0 ] || { echo "Aborting: build/point the comparator binaries first." >&2; exit 3; }

case "$(uname -s)" in
  Linux) : ;;
  *) echo "WARNING: not Linux — real landrun sandboxing is unavailable. A pass here is NOT authoritative." >&2 ;;
esac

# --- 2. assemble the workspace ------------------------------------------------
rm -rf "$WORKDIR"
mkdir -p "$WORKDIR/src"
cp "$CHALLENGE_SRC" "$WORKDIR/src/Challenge.lean"
printf '%s\n' "$TOOLCHAIN" > "$WORKDIR/lean-toolchain"

cat > "$WORKDIR/lakefile.toml" <<EOF
name = "comparator_workspace"
defaultTargets = ["Challenge"]

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "$MATHLIB_REV"

[[require]]
name = "lean617"
path = "$LEAN617_PATH"

[[lean_lib]]
name = "Challenge"
srcDir = "src"
EOF

echo "-- workspace lakefile.toml --"; cat "$WORKDIR/lakefile.toml"

# Mathlib olean cache so the sandboxed build does not compile Mathlib from source.
( cd "$WORKDIR" && lake exe cache get ) || echo "WARN: 'lake exe cache get' failed; the sandboxed build may be very slow." >&2

# The Solution (Lean617.Final) needs the four SAT LRAT certificates present.
# They are git-ignored; regenerate them if absent (the machine-check job does the
# same). This is a no-op if a prior step already produced them.
if [ -x "$REPO_ROOT/tools/regen_certificates.sh" ] && [ -z "${SKIP_CERT_REGEN:-}" ]; then
  echo "-- ensuring SAT certificates (tools/regen_certificates.sh) --"
  "$REPO_ROOT/tools/regen_certificates.sh" || echo "WARN: certificate regeneration failed; Solution build may fail." >&2
fi

# --- 3. run comparator --------------------------------------------------------
echo "-- invoking comparator --"
export COMPARATOR_LANDRUN="$LANDRUN"
export COMPARATOR_LEAN4EXPORT="$LEAN4EXPORT"
[ -n "${COMPARATOR_NANODA:-}" ] && export COMPARATOR_NANODA

cd "$WORKDIR"
set -x
lake env "$COMPARATOR" "$CONFIG"
