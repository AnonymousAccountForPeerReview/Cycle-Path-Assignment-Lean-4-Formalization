#!/usr/bin/env python3
"""Static checks of the repository, to run after `lake build`.

1. The outerplanar package, Section 3, Section 4 and Section 7 formalizations are required by
   lakefile.toml, each by path (`../<name>`, the published layout) or as a git dependency at a
   full commit, and lake-manifest.json agrees; the manifest also lists, through them, the
   NP-completeness foundation (at commit 3e603e79…, if fetched by git) and the Section 5 and
   Section 8 formalizations; Mathlib is pinned to its release tag and commit; every git package
   of the manifest is at a full commit; no copy of any dependency is vendored.
2. Challenge.lean is up to date with its sources (so it contains no other command than
   those the generator writes), imports exactly the pinned Mathlib modules listed by the
   generator, contains no meta-level code (`run_cmd`, `#eval`, `elab`, `macro`, …), and obeys
   the 1,000-line and 100 KiB limits.
3. comparator.json, the generator and formalization.yaml name the same compared
   theorems; Challenge.lean has one `sorry` hole for each; only the standard axioms
   are permitted; NanoDa is enabled; Solution.lean imports the whole library. The cited
   algorithms enter exactly the statements of `HYPOTHESES`, each time once, as an explicit
   hypothesis of the recorded shape (`(hF : MinCostFlowSolver F T)`, `(hT : AlmostLinear T)`,
   `(hA : Almost2SatSolver F T)`, `(hT : FPTBound T)`, primed in the statements for all `k`),
   and no other compared statement mentions them.
4. The library is the import closure of Runtimes.lean, and every `.lean` file under
   Runtimes/ belongs to it (`--allow-unimported` only warns about the others, for
   work in progress, and leaves them out of every check).
5. RuntimesAudit has exactly one axiom guard for every named declaration of the
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

from generate_challenge import MATHLIB_IMPORTS, TARGETS, statement, without_comments
from lean_declarations import kernel_name, library_declarations, library_modules, module_path, plain, stray_modules

ROOT = Path(__file__).resolve().parents[1]
LIBRARY = "Runtimes"
AUDIT = "RuntimesAudit"
TESTS = "tests"
# Direct dependencies (sibling formalizations of the same manuscript).
DIRECT = ["cpap-outerplanar", "cpap-tractability", "cpap-bounded-cost", "cpap-approximation"]
# Dependencies of the direct dependencies that the Challenge copies from or that the
# library uses: the commit pinned if fetched by git, or None.
INHERITED = {
    "np-completeness": "3e603e795b44fedcf7d6dd65b7d1e30547ead925",
    "cpap-np-hardness": None,
    "cpap-minor-free": None,
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
# The cited algorithms, as hypotheses of the compared theorems: the min-cost flow algorithm
# (ANONYMIZED et al., FOCS 2023) with its almost-linear bound. The generic Almost 2-SAT
# interface remains compared; the executed compiler instantiates it in the sole-flow
# endpoints. For each, record the compared takers and the shape of their binders.
# The separate sortedNetworkConstruction target
# has type SortedNetworkConstruction; its flow hypothesis is in that independently copied
# proposition definition and is checked with the definition by Comparator.
FLOW = {
    "Runtimes.Flow.cpap4_flow_ram_semantic", "Runtimes.Flow.cpap4_flow_ram_almostLinear",
    "Runtimes.Flow.cpap4_flow_single", "Runtimes.Flow.cpap4_flow_single_almostLinear",
    "Runtimes.Flow.triangle_ram_semantic", "Runtimes.Flow.triangle_ram_almostLinear",
    "Runtimes.Flow.triangle_single", "Runtimes.Flow.triangle_single_almostLinear",
    "Runtimes.cpap4_enum_ram_explicit_semantic", "Runtimes.cpap4_enum_ram_semantic",
    "Runtimes.BoundedCost.boundedCost_triangle", "Runtimes.BoundedCost.boundedCost_triangle_almostLinear",
    "Runtimes.BoundedCost.boundedCost_ram_all", "Runtimes.BoundedCost.boundedCost_ram_all_almostLinear",
    "Runtimes.Flow.polynomialMinCostFlowSolverExists_of_almostLinear",
    "Runtimes.fourCycleAssignment_single",
    "Runtimes.BoundedCost.almostTwoSatFptSolverExists_of_citedFlow",
    "Runtimes.BoundedCost.boundedCost_ram_all_from_citedFlow",
    "Runtimes.BoundedCost.optimalCost_ram_fpt_from_citedFlow",
}
ALMOST_LINEAR = {name for name in FLOW if name.endswith("almostLinear")} | {
    "Runtimes.cpap4_enum_ram_semantic", "Runtimes.fourCycleAssignment_single",
    "Runtimes.BoundedCost.almostTwoSatFptSolverExists_of_citedFlow",
    "Runtimes.BoundedCost.boundedCost_ram_all_from_citedFlow",
    "Runtimes.BoundedCost.optimalCost_ram_fpt_from_citedFlow"}
A2SAT = {"Runtimes.BoundedCost.boundedCost_ram", "Runtimes.BoundedCost.boundedCost_ram_fpt", "Runtimes.BoundedCost.boundedCost_ram_all",
         "Runtimes.BoundedCost.boundedCost_ram_all_almostLinear"}
FPT = A2SAT - {"Runtimes.BoundedCost.boundedCost_ram"}
HYPOTHESES = {
    "MinCostFlowSolver": (FLOW, r"\(hF : (?:Flow\.)?MinCostFlowSolver F T\)"),
    "AlmostLinear": (ALMOST_LINEAR, r"\(h(?:T|AL) : (?:Flow\.)?AlmostLinear T\)"),
    "Almost2SatSolver": (A2SAT, r"\(hA : Almost2SatSolver F('?) T\1\)"),
    "FPTBound": (FPT, r"\(hT('?) : FPTBound T\1\)"),
}


def fail(message: str) -> None:
    raise SystemExit(f"check_repository: {message}")


def check_pin() -> None:
    lakefile = (ROOT / "lakefile.toml").read_text()
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    packages = {p["name"].strip("«»"): p for p in manifest["packages"]}
    for name in DIRECT:
        q = packages.get(name)
        path = re.search(rf'name = "{name}"\s*\npath = "([^"]*)"', lakefile)
        git = re.search(rf'name = "{name}"\s*\ngit = "([^"]*)"\s*\nrev = "([0-9a-f]{{40}})"', lakefile)
        if path:
            if path.group(1) != f"../{name}":
                fail(f"lakefile.toml must require {name} at ../{name}")
            if not q or q.get("type") != "path" or q.get("dir") != path.group(1) or q.get("inherited"):
                fail(f"lake-manifest.json does not record {name} at the path of lakefile.toml")
        elif git:
            if (not q or q.get("type") != "git" or q.get("rev") != git.group(2) or q.get("url") != git.group(1)
                    or q.get("inherited")):
                fail(f"lake-manifest.json does not pin {name} to the commit and URL of lakefile.toml")
        else:
            fail(f"lakefile.toml does not require {name} by path or at a full git commit")
    mathlib = re.search(r'name = "mathlib"\s*\ngit = "([^"]*)"\s*\nrev = "([^"]*)"', lakefile)
    if not mathlib or mathlib.group(1) != MATHLIB_URL or mathlib.group(2) != MATHLIB_TAG:
        fail(f"lakefile.toml does not require Mathlib at {MATHLIB_TAG}")
    requires = re.findall(r'^\[\[require\]\]\s*\nname = "([^"]*)"', lakefile, re.M)
    if sorted(requires) != sorted(DIRECT + ["mathlib"]):
        fail(f"lakefile.toml requires {requires}, expected {sorted(DIRECT + ['mathlib'])}")
    for name, pin in INHERITED.items():
        q = packages.get(name)
        if not q:
            fail(f"lake-manifest.json does not list {name}")
        if q.get("type") == "git" and pin and q.get("rev") != pin:
            fail(f"lake-manifest.json does not pin {name} to commit {pin}")
    m = packages.get("mathlib")
    if (not m or m.get("url") != MATHLIB_URL or m.get("rev") != MATHLIB_REV
            or m.get("inputRev") != MATHLIB_TAG or m.get("inherited")):
        fail(f"lake-manifest.json does not pin Mathlib {MATHLIB_TAG} to commit {MATHLIB_REV}")
    for name, package in packages.items():
        if package.get("type") == "path":
            continue
        if package.get("type") != "git" or not re.fullmatch(r"[0-9a-f]{40}", package.get("rev", "")):
            fail(f"lake-manifest.json does not pin {name} to a full git commit")
    for name in ("Complexity", "Tractability", "BoundedCost", "NPHardness", "Approximation", "MinorFree", "Outerplanar",
                 "Mathlib"):
        for path in (name, f"{name}.lean"):
            if (ROOT / path).exists():
                fail(f"a copy of a dependency ({path}) is vendored; it must come from Lake")


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


def hypothesis_problems(statements: dict[str, str]) -> list[str]:
    """Problems with the cited algorithms among the compared statements (name -> statement text):
    each hypothesis of `HYPOTHESES` is mentioned exactly by its statements, once, in a binder of
    the recorded shape."""
    problems = []
    for name, text in statements.items():
        code = " ".join(without_comments(text).split())
        for hypothesis, (takers, binder) in HYPOTHESES.items():
            count = len(re.findall(rf"\b{hypothesis}\b", code))
            if name not in takers:
                if count:
                    problems.append(f"the compared theorem {name} mentions {hypothesis}")
            elif count != 1 or not re.search(binder, code):
                problems.append(f"the compared theorem {name} must take {hypothesis} once, as `{binder}`")
    for hypothesis, (takers, _) in HYPOTHESES.items():
        for name in sorted(takers - set(statements)):
            problems.append(f"the theorem {name} (taking {hypothesis}) is not compared")
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
    for problem in hypothesis_problems({name: statement(path, name) for path, name in TARGETS}):
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
    declarations = library_declarations(ROOT, LIBRARY)
    declared = {kernel_name(d) for d in declarations}
    paths = [ROOT / f"{AUDIT}.lean"] + sorted((ROOT / AUDIT).glob("*.lean"))
    text = "\n".join(p.read_text() for p in paths)
    guards = re.findall(r"^/-- info: '(\S+)' (?:depends on axioms|does not depend on any axioms)", text, re.M)
    commands = re.findall(r"^#print axioms\s+(\S+)", text, re.M)
    expected_commands = {kernel_name(d): plain(d.name) for d in declarations}
    if len(guards) != len(commands) or any(expected_commands.get(g) != plain(c)
                                         for g, c in zip(guards, commands)):
        fail("axiom guard messages and commands do not match source declaration names")
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
        imports = re.findall(r"^(?:public\s+)?import\s+(?:all\s+)?(\S+)", p.read_text(), re.M)
        if imports != [LIBRARY, *library_modules(ROOT, LIBRARY)]:
            fail(f"{p.relative_to(ROOT)} must import the complete audited library with private declarations")
    for block in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", text):
        if not {a.strip() for a in block.split(",")} <= STANDARD_AXIOMS:
            fail(f"a guard names a nonstandard axiom: {block}")
    print(f"{len(guards)} axiom guards cover every named declaration of the "
          f"{len(library_modules(ROOT, LIBRARY))} {LIBRARY} modules")


def test_libraries() -> set[str]:
    """The root modules of the libraries of lakefile.toml whose sources are under tests/ and
    that are default targets."""
    lakefile = (ROOT / "lakefile.toml").read_text()
    defaults = re.search(r"^defaultTargets\s*=\s*\[([^\]]*)\]", lakefile, re.M)
    targets = set(re.findall(r'"([^"]+)"', defaults.group(1))) if defaults else set()
    libs = re.findall(r'^\[\[lean_lib\]\]\s*\nname = "([^"]+)"\s*\nsrcDir = "([^"]+)"', lakefile, re.M)
    return {name for name, src in libs if src == TESTS and name in targets}


def check_sources(strays: list[Path]) -> None:
    library = {module_path(ROOT, m) for m in library_modules(ROOT, LIBRARY)}
    tests = test_libraries()
    count = 0
    for p in sorted(ROOT.rglob("*.lean")):
        rel = p.relative_to(ROOT)  # (the parts of the absolute path may contain `work`)
        if ".lake" in rel.parts or ".rsync-tmp" in rel.parts or "work" in rel.parts or p in strays:
            continue
        if rel.parts[0] == TESTS:
            if len(rel.parts) != 2 or p.stem not in tests:
                fail(f"{rel} is not the root module of a default-target library of lakefile.toml")
        elif rel.parts[0] not in (LIBRARY, AUDIT) and p.name not in (
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
    for name in tests:
        if not (ROOT / TESTS / f"{name}.lean").is_file():
            fail(f"the test library {name} has no source {TESTS}/{name}.lean")
    print(f"{count} Lean sources obey the source rules")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--allow-unimported", action="store_true",
                        help="only warn about .lean files under Runtimes/ outside the library")
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
