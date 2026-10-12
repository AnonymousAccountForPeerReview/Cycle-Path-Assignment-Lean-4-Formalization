#!/usr/bin/env python3
"""Development check: the Challenge's constants print as the library's, with `pp.all`.

For each environment (the Challenge's, from `import Challenge`, and the library's, from
`import Runtimes`), a Lean script collects every `STACS2027` and `Complexity` constant that
the compared statements depend on, transitively through types, definition bodies and
inductive types (definitions, matchers and their auxiliaries, `Decidable` instances and their
auxiliary proofs, structures, constructors and the statements themselves; proofs of theorems
are not followed), and prints its kind, universe parameters, type and value with `pp.all`.
The two outputs must be identical. Imported theorem signatures in the Lean module
system appear as `axiomInfo`; the collector normalizes that metadata tag to `theorem`,
as does the axiom audit collector. Actual declared axioms remain forbidden by the
source checks and axiom audits; proof checking belongs to Comparator.

This anticipates Comparator, which remains the authority (it also checks the proofs); it
explains a mismatch by name. Run after `lake build Challenge Runtimes`. The Lean scripts
and their outputs are written to `work/`.

The sibling formalizations, required by path, have modules named `Challenge` and `Solution`
too, and Lean resolves `import Challenge` to the first match on its search path: the scripts
run with this package's build directory first on `LEAN_PATH`.
"""
from __future__ import annotations

import difflib
import os
from pathlib import Path
import subprocess
import sys

from generate_challenge import TARGETS

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "work"
LIBRARY = "Runtimes"

SCRIPT = """module
import all {module}
meta import Lean
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
      | .axiomInfo _ => "theorem" | .quotInfo _ => "quot"
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


def run(module: str) -> str:
    WORK.mkdir(exist_ok=True)
    output = WORK / f"constants-{module}.txt"
    script = WORK / f"Constants{module}.lean"
    roots = ", ".join(f"`STACS2027.{name}" for _, name in TARGETS)
    script.write_text(SCRIPT.format(module=module, roots=roots, output=output))
    path = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=ROOT, text=True,
                          stdout=subprocess.PIPE, check=True).stdout.strip()
    own = str(ROOT / ".lake/build/lib/lean")
    env = dict(os.environ, LEAN_PATH=os.pathsep.join([own] + [p for p in path.split(os.pathsep) if p != own]))
    result = subprocess.run(["lean", str(script)], cwd=ROOT, text=True, env=env,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        raise SystemExit(f"Lean failed on {script}:\n{result.stdout}")
    return output.read_text(encoding="utf-8")


def main() -> int:
    challenge = run("Challenge")
    library = run(LIBRARY)
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
