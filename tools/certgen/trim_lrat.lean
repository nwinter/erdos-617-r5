/-
Trim + renumber an LRAT proof so its clause ids are consecutive, which is what
Lean's `compactLratChecker` (used by `Std.Tactic.BVDecide`'s `verifyCert`)
requires. This mirrors bv_decide's own `LratCert.load` preprocessing.

Two non-obvious requirements the certificate pipeline depends on (see FORMAL.md
F3): CaDiCaL must run with `--inprocessing=false` (else it introduces fresh
variables the Lean checker silently drops), and the resulting LRAT must be
trimmed here (the checker ignores stated ids and appends sequentially, so gapped
ids break the id/index lockstep).

Run (from the `lean617/` directory):
  lake env lean --run ../tools/certgen/trim_lrat.lean raw.lrat certs/nonex11.lrat
-/
import Std.Tactic.BVDecide
import Lean.Elab.Tactic.BVDecide.LRAT.Trim

open Std.Tactic.BVDecide.LRAT
open Lean.Elab.Tactic.BVDecide

def main (args : List String) : IO Unit := do
  match args with
  | [inp, outp] =>
    let bytes ← IO.FS.readBinFile inp
    match parseLRATProof bytes with
    | .error e => IO.eprintln s!"parse error: {e}"; IO.Process.exit 1
    | .ok proof =>
      match LRAT.trim proof with
      | .error e => IO.eprintln s!"trim error: {e}"; IO.Process.exit 1
      | .ok trimmed =>
        IO.FS.writeFile outp (lratProofToString trimmed)
        IO.eprintln s!"trimmed {proof.size} -> {trimmed.size} actions; wrote {outp}"
  | _ => IO.eprintln "usage: trim_lrat <in.lrat> <out.lrat>"; IO.Process.exit 1
