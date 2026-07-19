#!/usr/bin/env python3
"""Validate erdos617_r5.json against leanprover/comparator's `Config` structure.

Comparator has no standalone JSON schema file; its config is deserialized by
Lean's derived `FromJson` on this structure (comparator `Main.lean`):

    structure Config where
      challenge_module : String
      solution_module  : String
      theorem_names    : Array String
      definition_names : Option (Array String) := none   -- optional
      permitted_axioms : Array String
      enable_nanoda    : Bool                             -- required (no default)

So we check: well-formed JSON; all required keys present with the right JSON
types; `definition_names` (if present) is a string array; and — because Lean's
`FromJson` silently IGNORES unknown keys — we flag any unexpected key so a typo
(e.g. "permitted_axiom") cannot ship as a silently-empty list.

Usage:  validate_config.py path/to/config.json      (exit 0 = valid)
"""
import json
import sys


def main(path: str) -> int:
    try:
        with open(path) as f:
            cfg = json.load(f)
    except (OSError, json.JSONDecodeError) as e:
        print(f"JSON CONFIG INVALID: cannot parse {path}: {e}")
        return 1

    required = {
        "challenge_module": str,
        "solution_module": str,
        "theorem_names": list,
        "permitted_axioms": list,
        "enable_nanoda": bool,
    }
    optional = {"definition_names": list}
    errs = []

    for k, t in required.items():
        if k not in cfg:
            errs.append(f"missing required key: {k}")
        elif not isinstance(cfg[k], t) or (t is bool and not isinstance(cfg[k], bool)):
            errs.append(f"key {k}: expected {t.__name__}, got {type(cfg[k]).__name__}")
    for k, t in optional.items():
        if k in cfg and not isinstance(cfg[k], t):
            errs.append(f"key {k}: expected {t.__name__}, got {type(cfg[k]).__name__}")
    for k in ("theorem_names", "permitted_axioms", *([("definition_names")] if "definition_names" in cfg else [])):
        v = cfg.get(k)
        if isinstance(v, list):
            bad = [x for x in v if not isinstance(x, str)]
            if bad:
                errs.append(f"key {k}: all elements must be strings; offenders: {bad}")
    unknown = set(cfg) - set(required) - set(optional)
    if unknown:
        errs.append(f"unknown keys (comparator IGNORES these — likely a typo): {sorted(unknown)}")

    if errs:
        print("JSON CONFIG INVALID:")
        for e in errs:
            print("  -", e)
        return 1

    print(f"JSON CONFIG VALID against comparator's Config structure: {path}")
    print(f"  challenge_module : {cfg['challenge_module']!r}")
    print(f"  solution_module  : {cfg['solution_module']!r}")
    print(f"  theorem_names    : {len(cfg['theorem_names'])}")
    for n in cfg["theorem_names"]:
        print(f"      - {n}")
    print(f"  definition_names : {cfg.get('definition_names', '(absent)')}")
    print(f"  permitted_axioms : {len(cfg['permitted_axioms'])}")
    for a in cfg["permitted_axioms"]:
        print(f"      - {a}")
    print(f"  enable_nanoda    : {cfg['enable_nanoda']}")
    return 0


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("usage: validate_config.py path/to/config.json", file=sys.stderr)
        sys.exit(2)
    sys.exit(main(sys.argv[1]))
