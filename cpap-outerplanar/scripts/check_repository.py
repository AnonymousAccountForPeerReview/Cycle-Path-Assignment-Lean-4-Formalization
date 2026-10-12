#!/usr/bin/env python3
"""Static checks of the repository, to run after `lake build`.

1. The NP-completeness foundation and Mathlib are required at their pinned revisions, in
   lakefile.toml and lake-manifest.json; the Section 5 and Section 8 formalizations either
   at their pinned commits (git dependencies) or by path (the sibling directories of the
   published layout; `scripts/dependencies.py` resolves both). Every other package of the
   manifest is pinned to a full commit, and no copy of a dependency is vendored.
2. Challenge.lean is up to date with its sources (so it contains no other command than
   those the generator writes), imports exactly the pinned Mathlib modules listed by the
   generator, contains no meta-level code (`run_cmd`, `#eval`, `elab`, `macro`, …), and obeys
   the 1,000-line and 100 KiB limits.
3. comparator.json, the generator and formalization.yaml name the same compared
   theorems; Challenge.lean has one `sorry` hole for each; only the standard axioms
   are permitted; NanoDa is enabled; Solution.lean imports the whole library. Lemma 19 is
   compared (`outerplanar_block_structure`), no compared statement mentions the propositions `TwoConnectedK23Structure` or
   `HypermapEuler` (neither is a hypothesis of any of them), and Lemma 19 and Lemma 35 are
   stated for `OuterplanarDrawing`, the manuscript's definition of outerplanarity.
4. The library is the import closure of Outerplanar.lean, and every `.lean` file under
   Outerplanar/ belongs to it (`--allow-unimported` only warns about the others, for
   work in progress, and leaves them out of every check).
5. OuterplanarAudit has exactly one axiom guard for every named declaration of the
   library, imports every guard module, and names only standard axioms.
6. Every Lean source starts with `module` and is at most 10,000 lines, and none but
   Challenge.lean contains `sorry`; none uses `admit`, `native_decide`, an axiom,
   `implemented_by`, `extern`, `unsafe`, `debug.skipKernelTC` or `maxHeartbeats 0`.
   (`decide +kernel`, which has the kernel evaluate a decision procedure and adds no
   axiom, is allowed; the guards record the axioms of the declarations using it.)

Proof checking is done by `lake build` and `lake comparator`, not here.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys

from dependencies import dependency_dir, manifest_packages, read_manifest
from generate_challenge import MATHLIB_IMPORTS, TARGETS, statement, without_comments
from lean_declarations import (audit_declarations, library_modules, module_path, plain,
                               stray_modules, supplemental_declarations, SUPPLEMENTAL_MODULES)

ROOT = Path(__file__).resolve().parents[1]
LIBRARY = "Outerplanar"
AUDIT = "OuterplanarAudit"
# The NP-completeness foundation NPCompleteness-Lean4 is required by git at this commit (from the
# URL of lakefile.toml, which the manifest must match).
FOUNDATION_REV = "3e603e795b44fedcf7d6dd65b7d1e30547ead925"
# The sibling formalizations of the same manuscript: (pinned commit when required by git,
# library directory).
SIBLINGS = {
    "cpap-np-hardness": ("d5e4bcfa1c1584104a87ad2aab48e21353823ebc", "NPHardness"),
    "cpap-minor-free": ("c090168e8f0f8fb2410000d034d3d4f333309d84", "MinorFree"),
}
MATHLIB_URL = "https://github.com/leanprover-community/mathlib4.git"
MATHLIB_TAG = "v4.35.0-rc2"
MATHLIB_REV = "065356127b1dc0016f66b7283ce0ce2c4055aa55"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(
    r"\b(native_decide|admit|implemented_by|extern|unsafe|skipKernelTC)\b|^\s*(?:private\s+)?axiom\s"
    r"|maxHeartbeats\s+0\b|maxRecDepth\s+0\b",
    re.M,
)


def fail(message: str) -> None:
    raise SystemExit(f"check_repository: {message}")


def check_pin() -> None:
    lakefile = (ROOT / "lakefile.toml").read_text()
    foundation = re.search(r'name = "np-completeness"\s*\ngit = "([^"]*)"\s*\nrev = "([^"]*)"', lakefile)
    if not foundation or foundation.group(2) != FOUNDATION_REV:
        fail("lakefile.toml does not require the NP-completeness foundation at its pinned commit")
    manifest = read_manifest(ROOT)
    packages = manifest_packages(manifest)
    for name, (rev, library) in SIBLINGS.items():
        q = packages.get(name)
        git = re.search(rf'name = "{name}"\s*\ngit = "([^"]*)"\s*\nrev = "([0-9a-f]{{40}})"', lakefile)
        path = re.search(rf'name = "{name}"\s*\npath = "([^"]*)"', lakefile)
        if git:
            if git.group(2) != rev:
                fail(f"lakefile.toml does not require {name} at its pinned commit {rev}")
            if not q or q.get("type") != "git" or q.get("rev") != rev or q.get("url") != git.group(1):
                fail(f"lake-manifest.json does not pin {name} to the commit and URL of lakefile.toml")
        elif path:
            if not q or q.get("type") != "path" or Path(q.get("dir", "")) != Path(path.group(1)):
                fail(f"lake-manifest.json does not record {name} at the path of lakefile.toml")
        else:
            fail(f"lakefile.toml does not require {name} (by git at a full commit, or by path)")
        if not (dependency_dir(ROOT, name) / library).is_dir():
            fail(f"the sources of {name} ({library}/) are not at its manifest location; run `lake build`")
    mathlib = re.search(r'name = "mathlib"\s*\ngit = "([^"]*)"\s*\nrev = "([^"]*)"', lakefile)
    if not mathlib or mathlib.group(1) != MATHLIB_URL or mathlib.group(2) != MATHLIB_TAG:
        fail(f"lakefile.toml does not require Mathlib at {MATHLIB_TAG}")
    p = packages.get("np-completeness")
    if not p or p.get("url") != foundation.group(1) or p.get("rev") != FOUNDATION_REV:
        fail("lake-manifest.json does not pin np-completeness to the required commit")
    m = packages.get("mathlib")
    if (not m or m.get("url") != MATHLIB_URL or m.get("rev") != MATHLIB_REV
            or m.get("inputRev") != MATHLIB_TAG or m.get("inherited")):
        fail(f"lake-manifest.json does not pin Mathlib {MATHLIB_TAG} to commit {MATHLIB_REV}")
    for name, package in packages.items():
        if package.get("type") == "path" and name in SIBLINGS:
            continue
        if package.get("type") != "git" or not re.fullmatch(r"[0-9a-f]{40}", package.get("rev", "")):
            fail(f"lake-manifest.json does not pin {name} to a full git commit")
    for name in ("Complexity", "Complexity.lean", "NPHardness", "NPHardness.lean", "MinorFree",
                 "MinorFree.lean", "Mathlib", "Mathlib.lean"):
        if (ROOT / name).exists():
            fail(f"a copy of a dependency ({name}) is vendored; it must come from Lake")


def check_challenge() -> None:
    subprocess.run([sys.executable, str(ROOT / "scripts/generate_challenge.py"), "--check"], check=True)
    raw = (ROOT / "Challenge.lean").read_bytes()
    text = raw.decode("utf-8")
    if len(text.splitlines()) > 1000 or len(raw) > 100 * 1024:
        fail("Challenge.lean exceeds 1,000 lines or 100 KiB")
    code = without_comments(text)
    imports = re.findall(r"^((?:public|meta|private)\s+)*import\s+(\S+)", code, re.M)
    expected = [("public ", m) for m in MATHLIB_IMPORTS]
    if imports != expected or not all(m.startswith("Mathlib.") for m in MATHLIB_IMPORTS):
        fail(f"Challenge.lean must import exactly the pinned Mathlib modules {MATHLIB_IMPORTS}, "
             f"found {imports}")
    meta = re.search(r"\b(run_cmd|run_elab|run_meta|run_tac|#eval|elab|elab_rules|macro|macro_rules|"
                     r"syntax|initialize|builtin_initialize|meta)\b", code)
    if meta:
        fail(f"Challenge.lean contains meta-level code: {meta.group(0)}")


# Propositions that state a cited or auxiliary result, proved in the library; a compared
# statement must not take one as a hypothesis.
HYPOTHESES = ("TwoConnectedK23Structure", "HypermapEuler")


def statement_problems(statements: dict[str, str]) -> list[str]:
    """Problems among the compared statements (name -> statement text): Lemma 19 must be
    compared, no statement may mention a proposition of `HYPOTHESES`, and Lemma 19 and Lemma 35
    must be stated for `OuterplanarDrawing` (the manuscript's definition), not for the minor
    characterization `Outerplanar`."""
    problems = []
    codes = {name: " ".join(without_comments(text).split()) for name, text in statements.items()}
    if "outerplanar_block_structure" not in codes:
        problems.append("the compared theorems must include Lemma 19 (`outerplanar_block_structure`)")
    for name, code in codes.items():
        for hypothesis in HYPOTHESES:
            if re.search(rf"\b{hypothesis}\b", code):
                problems.append(f"the compared theorem {name} mentions {hypothesis} (takes it as a hypothesis?)")
    for name in ("outerplanar_block_structure", "outerplanar_linear_ram"):
        code = codes.get(name)
        if code is not None and (not re.search(r"\bOuterplanarDrawing g\b", code)
                                 or re.search(r"\bOuterplanar g\b", code)):
            problems.append(f"the compared theorem {name} must be stated for OuterplanarDrawing")
    return problems


def check_targets() -> None:
    config = json.loads((ROOT / "comparator.json").read_text())
    names = config["theorem_names"]
    if names != [f"STACS2027.{name}" for _, name in TARGETS]:
        fail("comparator.json theorem_names differ from the generator's TARGETS")
    if set(config["permitted_axioms"]) != STANDARD_AXIOMS or len(config["permitted_axioms"]) != 3:
        fail("comparator.json must permit exactly propext, Quot.sound and Classical.choice")
    if config.get("definition_names"):
        fail("comparator.json must not leave definition holes")
    if config.get("enable_nanoda") is not True:
        fail("comparator.json must enable NanoDa")
    if (config.get("challenge_module"), config.get("solution_module")) != ("Challenge", "Solution"):
        fail("comparator.json must compare Challenge with Solution")
    metadata = (ROOT / "formalization.yaml").read_text()
    declared = re.findall(r"^\s*- declaration:\s*(\S+)\s*$", metadata, re.M)
    if sorted(declared) != sorted(names):
        fail("formalization.yaml main_results differ from comparator.json theorem_names")
    challenge = (ROOT / "Challenge.lean").read_text()
    holes = len(re.findall(r"\bsorry\b", without_comments(challenge)))
    if holes != len(names):
        fail(f"Challenge.lean has {holes} sorry holes for {len(names)} targets")
    for problem in statement_problems({name.split(".")[-1]: statement(path, name) for path, name in TARGETS}):
        fail(problem)
    solution = re.findall(r"^(?:public\s+)?import\s+(\S+)", without_comments((ROOT / "Solution.lean").read_text()), re.M)
    if solution != [LIBRARY]:
        fail(f"Solution.lean must import exactly {LIBRARY}, found {solution}")


def check_library(allow_unimported: bool) -> list[Path]:
    strays = stray_modules(ROOT, LIBRARY)
    for p in strays:
        message = f"{p.relative_to(ROOT)} is not imported by {LIBRARY}.lean"
        if not allow_unimported:
            fail(message + " (add it to the library, or pass --allow-unimported for work in progress)")
        print(f"warning: {message}; left out of every check", file=sys.stderr)
    return strays


def check_audit() -> None:
    declared = {plain(d.name) for d in audit_declarations(ROOT, LIBRARY)}
    paths = [ROOT / f"{AUDIT}.lean"] + sorted((ROOT / AUDIT).glob("*.lean"))
    text = "\n".join(p.read_text() for p in paths)
    guards = [plain(g) for g in re.findall(r"^#print axioms\s+(\S+)", text, re.M)]
    if len(guards) != len(set(guards)):
        fail("duplicate axiom guards")
    if set(guards) != declared:
        missing = sorted(declared - set(guards))[:5]
        extra = sorted(set(guards) - declared)[:5]
        fail(f"axiom guards do not match the {LIBRARY} declarations (missing {missing}, extra {extra}); "
             "run scripts/generate_audit.py")
    root_imports = set(re.findall(r"^import\s+(\S+)", (ROOT / f"{AUDIT}.lean").read_text(), re.M))
    for p in paths[1:]:
        if f"{AUDIT}.{p.stem}" not in root_imports:
            fail(f"{AUDIT}.lean does not import {p.stem}")
    for p in paths[1:]:
        imports = re.findall(r"^(?:public\s+)?import\s+(\S+)", p.read_text(), re.M)
        if imports != [LIBRARY]:
            fail(f"{p.relative_to(ROOT)} must import exactly {LIBRARY}")
    for block in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", text):
        if not {a.strip() for a in block.split(",")} <= STANDARD_AXIOMS:
            fail(f"a guard names a nonstandard axiom: {block}")
    supplemental = len(supplemental_declarations(ROOT))
    print(f"{len(guards)} axiom guards cover every named declaration of the "
          f"{len(library_modules(ROOT, LIBRARY))} {LIBRARY} modules and "
          f"{supplemental} declarations in {len(SUPPLEMENTAL_MODULES)} shared supplemental modules")


def check_sources(strays: list[Path]) -> None:
    library = {module_path(ROOT, m) for m in library_modules(ROOT, LIBRARY)}
    count = 0
    for p in sorted(ROOT.rglob("*.lean")):
        rel = p.relative_to(ROOT)
        if ".lake" in rel.parts or p in strays:
            continue
        if rel.parts[0] not in (LIBRARY, AUDIT) and p.name not in (
                "Challenge.lean", "Solution.lean", f"{LIBRARY}.lean", f"{AUDIT}.lean"):
            fail(f"{rel} is not part of any library of the package")
        if rel.parts[0] == LIBRARY and p not in library:
            fail(f"{rel} is not part of the library")
        lines = p.read_text().splitlines()
        if p.is_symlink() or not lines or lines[0] != "module":
            fail(f"{rel} must be a regular file starting with `module`")
        if len(lines) > 10000:
            fail(f"{rel} exceeds 10,000 lines")
        code = without_comments(p.read_text())
        m = FORBIDDEN.search(code)
        if m:
            fail(f"{rel} uses a forbidden construct: {m.group(0).strip()}")
        if p.name != "Challenge.lean" and re.search(r"\bsorry\b", code):
            fail(f"{rel} contains sorry")
        count += 1
    print(f"{count} Lean sources obey the source rules")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--allow-unimported", action="store_true",
                        help="only warn about .lean files under Outerplanar/ outside the library")
    args = parser.parse_args()
    check_pin()
    check_challenge()
    check_targets()
    strays = check_library(args.allow_unimported)
    check_audit()
    check_sources(strays)
    print("All static checks passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
