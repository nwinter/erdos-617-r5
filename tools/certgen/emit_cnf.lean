/-
Emit the DIMACS CNF for one SAT primitive, using the SAME definitions
(`nonexCNF` / `MCNF` in namespace `Erdos617F3`) that the shipped Lean proof
kernel-checks in `lean617/Lean617/PrimEncoding.lean`. This guarantees the CNF a
verifier feeds to CaDiCaL is byte-for-byte the one the certificate is checked
against — there is no second, drifting copy of the encoding.

Run (from the `lean617/` directory, after `lake build`):
  lake env lean --run ../tools/certgen/emit_cnf.lean nonex 11 nonex11.cnf
  lake env lean --run ../tools/certgen/emit_cnf.lean M 9 18 M9.cnf

`tools/regen_certificates.sh` drives this.
-/
import Lean617.PrimEncoding

open Erdos617F3

def main (args : List String) : IO Unit := do
  match args with
  | ["nonex", ns, path] =>
    let n := ns.toNat!
    let cnf := nonexCNF n
    IO.eprintln s!"nonex n={n}: {cnf.clauses.size} clauses, maxVar={maxVar cnf}"
    emitDimacs path cnf
  | ["M", ns, ks, path] =>
    let n := ns.toNat!
    let k := ks.toNat!
    let cnf := MCNF n k
    IO.eprintln s!"M n={n} k={k}: {cnf.clauses.size} clauses, maxVar={maxVar cnf}"
    emitDimacs path cnf
  | _ =>
    IO.eprintln "usage: emit_cnf nonex <n> <path> | emit_cnf M <n> <k> <path>"
    IO.Process.exit 1
