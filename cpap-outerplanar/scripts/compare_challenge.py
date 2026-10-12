#!/usr/bin/env python3
"""Development check: the Challenge's constants print as the library's, with `pp.all`.

For each environment (the Challenge's, from `import Challenge`, and the library's, from
`import Outerplanar`), a Lean script collects every `STACS2027` and `Complexity` constant (the
latter from the NP-completeness foundation) that the compared
statements depend on, transitively through types, definition bodies and inductive types
(definitions, matchers, `Decidable` instances and their auxiliary proofs, constructors and
the statements themselves; proofs of theorems are not followed), and prints its kind,
universe parameters, type and value with `pp.all`. The two outputs must be identical.

This anticipates Comparator, which remains the authority (it also checks the proofs); it
explains a mismatch by name. Run after compiling Challenge and Outerplanar with the pinned
Lean toolchain. The Lean scripts
and their outputs are written to a temporary directory (`--keep DIR` keeps them in `DIR`).
"""
from __future__ import annotations

import argparse
import difflib
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from generate_challenge import TARGETS

ROOT = Path(__file__).resolve().parents[1]
LIBRARY = "Outerplanar"

SCRIPT = """module
public import {module}
public import Lean
@[expose] public section
open Lean Meta Elab Command

set_option pp.all true in
set_option pp.maxSteps 100000000 in
run_cmd do
  let env ← getEnv
  let roots : Array Name := #[{roots}]
  let mut seen : NameSet := {{}}
  let mut stack : Array Name := roots
  let mut found : Array Name := #[]
  while 0 < stack.size do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    unless (`STACS2027).isPrefixOf n || (`Complexity).isPrefixOf n do continue
    let some ci := env.find? n | throwError "unknown constant {{n}}"
    found := found.push n
    stack := stack ++ ci.type.getUsedConstants
    match ci with
    | .defnInfo d => stack := stack ++ d.value.getUsedConstants
    | .opaqueInfo d => stack := stack ++ d.value.getUsedConstants
    | .inductInfo d => stack := stack ++ d.ctors.toArray ++ d.all.toArray
    | .ctorInfo d => stack := stack.push d.induct
    | .recInfo d => stack := stack ++ d.all.toArray
    | _ => pure ()
  let mut out : Array String := #[]
  for n in found.qsort Name.lt do
    let some ci := env.find? n | throwError "unknown constant {{n}}"
    let kind := match ci with
      | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor" | .recInfo _ => "recursor" | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom" | .quotInfo _ => "quot"
    let pp (e : Expr) : CommandElabM String := liftTermElabM do
      return toString (← ppExpr e)
    let mut text := s!"== {{kind}} {{n}} {{ci.levelParams}}\\n  type: {{← pp ci.type}}"
    match ci with
    | .defnInfo d => text := text ++ s!"\\n  value: {{← pp d.value}}"
    | .inductInfo d =>
      text := text ++ s!"\\n  params {{d.numParams}} indices {{d.numIndices}} ctors {{d.ctors}}"
    | _ => pure ()
    out := out.push text
  IO.FS.writeFile "{output}" (String.intercalate "\\n" out.toList ++ "\\n")
"""


def run(module: str, work: Path) -> str:
    output = work / f"constants-{module}.txt"
    script = work / f"Constants{module}.lean"
    roots = ", ".join(f"`STACS2027.{name}" for _, name in TARGETS)
    script.write_text(SCRIPT.format(module=module, roots=roots, output=output))
    paths = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=ROOT, text=True,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True).stdout.strip()
    env = os.environ.copy()
    env["LEAN_PATH"] = str(ROOT / ".lake/build/lib/lean") + ":" + paths
    result = subprocess.run(["lean", str(script)], cwd=ROOT, text=True, env=env,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        raise SystemExit(f"Lean failed on {script}:\n{result.stdout}")
    return output.read_text(encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--keep", type=Path, help="write the Lean scripts and outputs to this directory")
    args = parser.parse_args()
    if args.keep:
        args.keep.mkdir(parents=True, exist_ok=True)
        return compare(args.keep.resolve())
    with tempfile.TemporaryDirectory(prefix="compare-challenge-") as work:
        return compare(Path(work))


def compare(work: Path) -> int:
    challenge = run("Challenge", work)
    library = run(LIBRARY, work)
    count = challenge.count("\n== ") + challenge.startswith("== ")
    if challenge != library:
        sys.stdout.writelines(difflib.unified_diff(
            library.splitlines(True), challenge.splitlines(True), f"{LIBRARY} (library)", "Challenge"))
        print(f"\nThe Challenge's constants differ from the library's.", file=sys.stderr)
        return 1
    print(f"All {count} STACS2027 and Complexity constants of the compared statements print identically, "
          f"with pp.all, in the Challenge and in {LIBRARY}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
