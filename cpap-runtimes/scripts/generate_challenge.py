#!/usr/bin/env python3
"""Generate the independent Challenge, which imports one module of the pinned Mathlib.

Every definition the compared statements use is copied verbatim, with its documentation
comment and in its original order, from the library that defines it:

* the CNF formulas (`Assignment` through `Satisfiable`) from the NP-completeness foundation
  `NPCompleteness-Lean4` (`Complexity/SAT.lean`);
* the cycle-path assignment problem (`Edge` through `HasAssignment`, and the edge load `load`)
  from the Section 5 formalization (`NPHardness/`);
* the flow networks of Section 3 (`FlowNode` through `flowCost`) from the Section 3
  formalization (`Tractability/`);
* the formula `Γ'` of Theorem 4 (`kCycle` through `almostFormula`) and `AlmostSatisfiable`
  from the Section 4 formalization (`BoundedCost/`);
* Algorithm 1 (`pathLoad`, `chooseMin`, `greedyFrom`, `greedy`) and the relaxation of
  Section 7.2 (`weightedSum` through `OptimalFractional`) from the Section 7 formalization
  (`Approximation/`);
* the unit-cost RAM (`RAM.Config` through `RAM.initial`), its bounded runs (`RAM.ExecB`,
  `RAM.ComputesIn`), its graph input `RAM.graphInput`, the label bound `RAM.labelBound` and the
  vertex count `Algo.numV` from the outerplanar formalization (`Outerplanar/`);
* the input encodings of the machines, the cited algorithms as hypotheses
  (`Flow.MinCostFlowSolver`, `Flow.AlmostLinear`, `BoundedCost.Almost2SatSolver`, `BoundedCost.FPTBound`)
  the answer `BoundedCost.BoundedCostAnswer`, and the exact the paper construction claim
  `Flow.SortedNetworkConstruction` from this library (`Runtimes/`).

The sources of the dependencies are found through `lake-manifest.json`: a `path` package at its
`dir` (relative to this package), a `git` package under `.lake/packages/<name>`.

The compared theorems are copied from `Runtimes/` too: each statement, with its documentation
comment, up to its `:=`, followed by `:= by sorry`, in a `namespace … end` block with the
`open` lines of `PREAMBLES`. Each declaration is taken with the documentation comment that
immediately precedes it; where the source has none, the comment in `DOCS` below is inserted
(the term is unchanged, which Comparator checks). Other comments are dropped.

The Challenge imports the pinned Mathlib module `MATHLIB_IMPORTS`, for the real numbers and
real powers of the almost-linear bounds (`AlmostLinear`, `t^{1+ε}`). Declarations elaborated
without Mathlib in their libraries get the prefixes of `CORE_INSTANCES` where Mathlib's
instances would otherwise be chosen (see `docs/FOUNDATION.md`);
`scripts/compare_challenge.py` checks every resulting term.

This is a layout-aware extractor, not a general Lean parser and not a
replacement for Comparator. `--check` detects drift without changing a file.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]


def package_dir(name: str, root: Path = ROOT) -> Path:
    """The source directory of the dependency `name`, from `lake-manifest.json`: the `dir` of a
    `path` package (relative to the package at `root`), `<packagesDir>/<name>` for a `git`
    package."""
    manifest = json.loads((root / "lake-manifest.json").read_text(encoding="utf-8"))
    for package in manifest["packages"]:
        if package["name"].strip("«»") == name:
            if package["type"] == "path":
                return (root / package["dir"]).resolve()
            return root / manifest.get("packagesDir", ".lake/packages") / name
    raise ValueError(f"lake-manifest.json has no package {name}")


FOUNDATION = package_dir("np-completeness")
SECTION3 = package_dir("cpap-tractability")
SECTION4 = package_dir("cpap-bounded-cost")
SECTION5 = package_dir("cpap-np-hardness")
SECTION7 = package_dir("cpap-approximation")
APPENDIXG = package_dir("cpap-outerplanar")
MATHLIB = package_dir("mathlib")

# The Mathlib module the Challenge imports (Mathlib is pinned by lakefile.toml and
# lake-manifest.json): the real numbers, their order, the casts from `ℕ` and the real
# power `x ^ y` (`Real.rpow`) of the almost-linear bounds.
MATHLIB_IMPORTS = [
    "Mathlib.Analysis.SpecialFunctions.Pow.Real",
]

# The compared theorems, in `comparator.json` order: (library file, name relative to the
# namespace `STACS2027`).
TARGETS = [
    ("Runtimes/TwoSatMain.lean", "Runtimes.TwoSat.exists_linear_twoSat"),
    ("Runtimes/ZeroCost.lean", "Runtimes.ZeroCost.zeroCost_ram"),
    ("Runtimes/C4/Statement.lean", "Runtimes.C4.fourCycles_ram_semantic"),
    ("Runtimes/C4/Statement.lean", "Runtimes.C4.fourCycles_ram_paper_semantic"),
    ("Runtimes/C4/Statement.lean", "Runtimes.C4.fourCycles_ram_simple_semantic"),
    ("Runtimes/Flow/Statement.lean", "Runtimes.Flow.cpap4_flow_ram_semantic"),
    ("Runtimes/Flow/EnumeratedConstruction.lean", "Runtimes.Flow.sortedNetworkConstruction"),
    ("Runtimes/Flow/Main.lean", "Runtimes.Flow.cpap4_flow_ram_almostLinear"),
    ("Runtimes/Flow/Single.lean", "Runtimes.Flow.cpap4_flow_single"),
    ("Runtimes/Flow/Single.lean", "Runtimes.Flow.cpap4_flow_single_almostLinear"),
    ("Runtimes/Flow/Statement.lean", "Runtimes.Flow.triangle_ram_semantic"),
    ("Runtimes/Flow/Main.lean", "Runtimes.Flow.triangle_ram_almostLinear"),
    ("Runtimes/Flow/Single.lean", "Runtimes.Flow.triangle_single"),
    ("Runtimes/Flow/Single.lean", "Runtimes.Flow.triangle_single_almostLinear"),
    ("Runtimes/Cpap4EnumStatement.lean", "Runtimes.cpap4_enum_ram_explicit_semantic"),
    ("Runtimes/Cpap4EnumStatement.lean", "Runtimes.cpap4_enum_ram_semantic"),
    ("Runtimes/BoundedCost/Main.lean", "Runtimes.BoundedCost.boundedCost_ram"),
    ("Runtimes/BoundedCost/Top.lean", "Runtimes.BoundedCost.boundedCost_ram_fpt"),
    ("Runtimes/BoundedCost/TriDecide.lean", "Runtimes.BoundedCost.boundedCost_triangle"),
    ("Runtimes/BoundedCost/TriDecide.lean", "Runtimes.BoundedCost.boundedCost_triangle_almostLinear"),
    ("Runtimes/BoundedCost/TriDecide.lean", "Runtimes.BoundedCost.boundedCost_ram_all"),
    ("Runtimes/BoundedCost/TriDecide.lean", "Runtimes.BoundedCost.boundedCost_ram_all_almostLinear"),
    ("Runtimes/Greedy/Main.lean", "Runtimes.Greedy.greedy_ram"),
    ("Runtimes/Greedy/Main.lean", "Runtimes.Greedy.greedy_guarantee_ram"),
    ("Runtimes/ConvexQP/RAM/RelaxSolver.lean", "Runtimes.QPRam.relaxSolver_ram_optimal"),
    ("Runtimes/GeneralCycles/Main.lean", "Runtimes.generalCycleEnumerationRam"),
    ("Runtimes/Flow/PolynomialBound.lean", "Runtimes.Flow.polynomialMinCostFlowSolverExists_of_almostLinear"),
    ("Runtimes/CpapSingle/Complete.lean", "Runtimes.fourCycleAssignment_single"),
    ("Runtimes/BoundedCost/ActualCompilerRAM.lean", "Runtimes.BoundedCost.almostTwoSatFptSolverExists_of_citedFlow"),
    ("Runtimes/BoundedCost/ActualFPT.lean", "Runtimes.BoundedCost.boundedCost_ram_all_from_citedFlow"),
    ("Runtimes/BoundedCost/OptMain.lean", "Runtimes.BoundedCost.optimalCost_ram_fpt_from_citedFlow"),
]

# The `open` lines of the statements of each namespace (those of their source files, less the
# namespaces that hold no declaration of the Challenge).
PREAMBLES = {
    "Runtimes.TwoSat": "open STACS2027.RAM Complexity.SAT",
    "Runtimes.ZeroCost": "open STACS2027 STACS2027.RAM Complexity.SAT",
    "Runtimes.C4": "open STACS2027 STACS2027.Algo STACS2027.RAM",
    "Runtimes.Flow": "open STACS2027 STACS2027.RAM",
    "Runtimes": "open STACS2027 STACS2027.Algo STACS2027.RAM STACS2027.Runtimes.Flow",
    "Runtimes.BoundedCost": "open STACS2027 STACS2027.RAM STACS2027.Runtimes.ZeroCost STACS2027.Runtimes.Flow "
                     "Complexity.SAT",
    "Runtimes.Greedy": "open STACS2027 STACS2027.RAM STACS2027.Runtimes.ZeroCost",
    "Runtimes.QPRam": "open STACS2027 STACS2027.RAM",
}


def without_comments(source: str) -> str:
    """Blank out nested Lean comments, preserving offsets, newlines and strings."""
    result: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    escaped = False
    while index < len(source):
        char = source[index]
        pair = source[index:index + 2]
        if block_depth:
            if pair == "/-":
                block_depth += 1
                result.extend("  ")
                index += 2
            elif pair == "-/":
                block_depth -= 1
                result.extend("  ")
                index += 2
            else:
                result.append("\n" if char == "\n" else " ")
                index += 1
        elif in_string:
            result.append(char)
            index += 1
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
        elif pair == "/-":
            block_depth = 1
            result.extend("  ")
            index += 2
        elif pair == "--":
            end = source.find("\n", index)
            if end == -1:
                result.extend(" " * (len(source) - index))
                break
            result.extend(" " * (end - index))
            index = end
        else:
            result.append(char)
            index += 1
            if char == '"':
                in_string = True
    if block_depth or in_string:
        raise ValueError("Unterminated comment or string in selected source")
    return "".join(result)


BOUNDARY = re.compile(
    r"^(?:@\[[^\n\]]*\]\s*)?(?:(?:public|private|protected|noncomputable|unsafe)\s+)*"
    r"(?:def|abbrev|structure|inductive|theorem|lemma|instance|namespace|end|"
    r"section|open|set_option|attribute|notation|macro|syntax|example|mutual|variable|omit)\b",
    re.M,
)
NAMED = re.compile(
    r"(?:@\[[^\n]*\]\s*)?(?:(?:public|private|protected|noncomputable|unsafe)\s+)*"
    r"(?:def|abbrev|structure|inductive|theorem|lemma)\s+([\w'.]+)\b"
)
INSTANCE = re.compile(r"instance\b[^\n]*\)\s*:\s*Decidable(?:Pred)?\s*\((\w+)")


def chunks(source: str) -> list[tuple[str, str]]:
    """(key, text) for each declaration, text = preceding docstring + declaration.

    Boundaries are found in the comment-free text; the declaration text is cut
    from the original source and loses trailing comments. Keys are declaration
    names, `instance:P` for a `Decidable (P ...)` instance, or `#n` otherwise.
    """
    blank = without_comments(source)
    starts = [m.start() for m in BOUNDARY.finditer(blank)]
    result = []
    previous_end = 0
    for i, (start, end) in enumerate(zip(starts, starts[1:] + [len(source)])):
        content = blank[start:end].rstrip()
        real_end = start + len(content)
        text = source[start:real_end]
        gap = source[previous_end:start]
        doc = ""
        d = gap.rfind("/--")
        if d != -1:
            close = gap.find("-/", d)
            if close != -1 and gap[close + 2:].strip() == "" and blank[previous_end + d:start].strip() == "":
                doc = gap[d:close + 2].strip() + "\n"
        named = NAMED.match(text)
        inst = INSTANCE.match(text)
        key = named.group(1) if named else (f"instance:{inst.group(1)}" if inst else f"#{i}")
        result.append((key, doc + "\n".join(line.rstrip() for line in text.splitlines())))
        previous_end = real_end
    return result


def index_of(source: str, where: str, wanted: list[str]) -> dict[str, tuple[int, str]]:
    """Position and text of each declaration; a wanted key must occur once in the file.

    (Other names, such as `get` in several namespaces of a library file, may repeat.)
    """
    index: dict[str, tuple[int, str]] = {}
    for position, (key, text) in enumerate(chunks(source)):
        if key in index and key in wanted:
            raise ValueError(f"Ambiguous declaration {key!r} in {where}")
        index[key] = (position, text)
    return index


def select(source: str, keys: list[str], where: str) -> str:
    index = index_of(source, where, keys)
    missing = [k for k in keys if k not in index]
    if missing:
        raise ValueError(f"Missing declarations in {where}: {', '.join(missing)}")
    positions = [index[k][0] for k in keys]
    if positions != sorted(positions):
        raise ValueError(f"Declarations out of source order in {where}: {keys}")
    parts = []
    for k in keys:
        text = index[k][1]
        if not text.startswith("/--"):
            if k not in DOCS:
                raise ValueError(f"Undocumented declaration without a DOCS entry in {where}: {k}")
            text = f"/-- {DOCS[k]} -/\n" + text
        elif k in DOCS:
            raise ValueError(f"DOCS entry for an already documented declaration: {k}")
        if k in FRESH_MATCHER:
            text = FRESH_MATCHER_PREFIX + text
        for prefix in CORE_INSTANCES.get(k, []):
            text = prefix + "\n" + text
        parts.append(text)
    return "\n\n".join(parts)


def library(base: Path, path: str, keys: list[str]) -> str:
    return select((base / path).read_text(encoding="utf-8"), keys, path)


def statement(path: str, name: str) -> str:
    """The documented statement of theorem `name` (its last component) in `path`, with its
    proof replaced by `sorry`."""
    return statement_text((ROOT / path).read_text(encoding="utf-8"), name.split(".")[-1], path)


def statements() -> str:
    """The compared statements, in `TARGETS` order; consecutive ones in a sub-namespace of
    `STACS2027` share a `namespace … end` block with the `open` lines of `PREAMBLES`."""
    blocks: list[tuple[str, list[str]]] = []
    for path, name in TARGETS:
        space = ".".join(name.split(".")[:-1])
        text = statement(path, name)
        if blocks and blocks[-1][0] == space:
            blocks[-1][1].append(text)
        else:
            blocks.append((space, [text]))
    parts = []
    for space, texts in blocks:
        body = "\n\n".join(texts)
        if space:
            body = f"namespace {space}\n{PREAMBLES[space]}\n\n{body}\n\nend {space}"
        parts.append(body)
    return "\n\n".join(parts)


def statement_text(source: str, name: str, path: str) -> str:
    index = index_of(source, path, [name])
    if name not in index:
        raise ValueError(f"Missing theorem {name} in {path}")
    text = index[name][1]
    if not text.startswith("/--"):
        raise ValueError(f"Compared theorem without a documentation comment: {name}")
    doc_end = text.index("-/") + 2
    body = text[doc_end:].lstrip("\n")
    if not re.match(r"theorem\s+" + re.escape(name) + r"\b", body):
        raise ValueError(f"{name} in {path} is not a plain theorem")
    assign = without_comments(body).find(":=")
    if assign == -1:
        raise ValueError(f"No `:=` in {name}")
    return text[:doc_end] + "\n" + body[:assign].rstrip() + " := by sorry"


# Lean shares, within one module, auxiliary `match` functions of the same shape; a copied
# declaration listed here would get the option below, which gives it a fresh matcher with the
# library's name and value. (None is needed: no two copied declarations match the same types
# with the same patterns.) Comparator checks the result.
FRESH_MATCHER: set[str] = set()
FRESH_MATCHER_PREFIX = "set_option bootstrap.genMatcherCode false in\n"

# Declarations elaborated in their libraries with Lean core only, whose instance arguments
# Mathlib's instances would take over in this Challenge: each is preceded by
# `attribute [local instance high] I in` for core's instance `I`, which ranks `I` first for
# that one declaration (`c in d` runs `d` in a section after `c`), so that the copy
# elaborates to the library's term; the declaration's text is unchanged. Comparator and
# `scripts/compare_challenge.py` check the result.
ZERO_NAT = "attribute [local instance high] Zero.ofOfNat0 in"
CORE_INSTANCES: dict[str, list[str]] = {
    # `List.sum` over `ℕ` (and `ℤ`): core's `Zero.ofOfNat0`, not Mathlib's `AddMonoid`-based
    # `Zero`.
    "overlap": [ZERO_NAT],
    "cost": [ZERO_NAT],
    "load": [ZERO_NAT],
    "pathLoad": [ZERO_NAT],
    "flowCost": [ZERO_NAT],
    "fractionalLoad": [ZERO_NAT],
    "FractionalSolution": [ZERO_NAT],
    "relaxationObjective": [ZERO_NAT],
}

# Documentation comments for copied declarations that have none in their source.
DOCS: dict[str, str] = {
    "load": "The load of the edge `e` under the paths `ps`: its number of occurrences in them.",
}


HEADER_DOC = """/-! Independent the paper RAM statements; definitions and docstrings are copied verbatim, and cited solver hypotheses remain explicit in their definitions.
Generated by `scripts/generate_challenge.py`; `Solution.lean` imports the proofs. See `docs/paper-map.md` and `docs/FOUNDATION.md` for scope, inputs, pipelines, and core-instance preservation.
-/"""


def compact_comments(source: str) -> str:
    """Keep all declarations, and compact only comment whitespace for the line cap."""
    out, i, quoted, escaped = [], 0, False, False
    while i < len(source):
        if quoted:
            ch = source[i]; out.append(ch); i += 1
            if escaped: escaped = False
            elif ch == "\\": escaped = True
            elif ch == '"': quoted = False
        elif source.startswith('/-', i):
            start, depth = i, 1; i += 2
            while depth:
                if source.startswith('/-', i): depth += 1; i += 2
                elif source.startswith('-/', i): depth -= 1; i += 2
                elif i >= len(source): raise ValueError('Unterminated comment')
                else: i += 1
            out.append(re.sub(r'\s+', ' ', source[start:i]))
        elif source.startswith('--', i):
            end = source.find('\n', i)
            if end < 0: end = len(source)
            out.append(source[i:end]); i = end
        else:
            ch = source[i];out.append(ch);i += 1
            if ch == '"': quoted = True
    return ''.join(out)


def challenge_text() -> str:
    parts = [
        "module\n\n" + "\n".join(f"public import {m}" for m in MATHLIB_IMPORTS),
        HEADER_DOC,
        "@[expose] public section",
        "namespace Complexity.SAT",
        library(FOUNDATION, "Complexity/SAT.lean", [
            "Assignment", "Literal", "Clause", "CNF", "evalLiteral", "evalClause", "evalCNF", "Satisfiable",
        ]),
        "end Complexity.SAT",
        "namespace STACS2027\nopen Complexity.SAT",
        library(SECTION5, "NPHardness/FiniteCycles.lean", [
            "Edge", "Graph", "Cycle", "edge", "pathEdges", "cycleEdges", "IsCycle",
            "instance:IsCycle", "SameCycle", "instance:SameCycle", "selected", "overlap", "cost",
        ]),
        library(SECTION5, "NPHardness/LoadCost.lean", ["load"]),
        library(SECTION5, "NPHardness/CycleRepresentatives.lean", ["cycleRepresentatives"]),
        library(SECTION5, "NPHardness/Enumerate.lean", ["vertices", "neighbors", "walksFrom", "rawCycles", "cycles"]),
        library(SECTION5, "NPHardness/CostSearch.lean", ["selectedOptions", "ValidChoices"]),
        library(SECTION5, "NPHardness/CPAP.lean", ["HasAssignment"]),
        library(SECTION4, "BoundedCost/Algorithm3Search.lean", ["IsOptimalCost"]),
        library(SECTION3, "Tractability/FlowNetwork.lean", [
            "FlowNode", "FlowNode.beq", "Arc", "inflow", "outflow", "IsFlow", "flowValue", "flowCost",
        ]),
        library(SECTION4, "BoundedCost/Encoding.lean", [
            "kCycle", "pathVariable", "cycleEdgeAt", "edgePosition", "edgeVariable", "disjointEdges",
            "pathConstraints", "candidateOverlaps", "overlapClause", "almostFormula", "AlmostSatisfiable",
        ]),
        library(SECTION7, "Approximation/Weighted.lean", ["weightedSum"]),
        library(SECTION7, "Approximation/Loads.lean", ["pathLoad"]),
        library(SECTION7, "Approximation/Greedy.lean", ["chooseMin", "greedyFrom", "greedy"]),
        library(SECTION7, "Approximation/Rounding.lean", [
            "optionLoad", "fractionalLoad", "FractionalSolution", "relaxationObjective", "OptimalFractional",
        ]),
        "namespace RAM",
        library(APPENDIXG, "Outerplanar/RAM/Model.lean", [
            "Config", "Stmt", "Config.setReg", "Config.setMem", "Config.emit", "initial",
        ]),
        library(APPENDIXG, "Outerplanar/RAM/Bounded.lean", ["ExecB", "ComputesIn"]),
        library(APPENDIXG, "Outerplanar/RAM/Layout.lean", ["graphInput", "labelBound"]),
        "end RAM",
        "namespace Algo",
        library(APPENDIXG, "Outerplanar/Algo/Graph.lean", ["proper", "labels", "numV"]),
        "end Algo",
        "namespace Runtimes.TwoSat",
        library(ROOT, "Runtimes/TwoSatSpec.lean", ["code", "IsTwoCNF", "codes"]),
        "end Runtimes.TwoSat",
        "namespace Runtimes.ZeroCost\nopen STACS2027.RAM",
        "section\nvariable (g : Graph) (k : ℕ)",
        library(ROOT, "Runtimes/ZeroCostSpec.lean", ["verts"]),
        "end",
        library(ROOT, "Runtimes/ZeroCostProg.lean", ["zeroCostInput"]),
        "end Runtimes.ZeroCost",
        "namespace Runtimes.Flow",
        library(ROOT, "Runtimes/Flow/Solver.lean", [
            "select", "encArcs", "netInput", "NodeOf", "GoodNet", "IsMinFlow", "FlowAnswer",
            "MinCostFlowSolver", "AlmostLinear",
        ]),
        library(ROOT, "Runtimes/Flow/EdgeSpec.lean", ["verts"]),
        library(ROOT, "Runtimes/Flow/Four.lean", ["OptCost"]),
        "open STACS2027.RAM",
        library(ROOT, "Runtimes/Flow/Prog.lean", ["flowInput"]),
        library(ROOT, "Runtimes/NamedHoles.lean", ["PolynomialMinCostFlowSolverExists", "SortedNetworkConstruction"]),
        "end Runtimes.Flow",
        "namespace Runtimes.BoundedCost\nopen STACS2027.RAM STACS2027.Runtimes.ZeroCost",
        library(ROOT, "Runtimes/BoundedCost/Spec.lean", ["boundedCostInput"]),
        library(ROOT, "Runtimes/BoundedCost/Answer.lean", ["BoundedCostAnswer"]),
        library(ROOT, "Runtimes/BoundedCost/Top.lean", ["paper5"]),
        "namespace OptEmit",
        library(ROOT, "Runtimes/BoundedCost/OptEmit.lean", ["OptimumAnswer"]),
        "end OptEmit",
        library(ROOT, "Runtimes/BoundedCost/Solver.lean", [
            "Clauses2", "SolverDomain", "OccursIn", "a2In", "A2Answer", "Almost2SatSolver", "FPTBound", "shiftL", "shiftF",
        ]),
        library(ROOT, "Runtimes/NamedHoles.lean", ["AlmostTwoSatFptSolverExists"]),
        "end Runtimes.BoundedCost",
        "namespace Runtimes\nopen STACS2027 STACS2027.RAM",
        library(ROOT, "Runtimes/NamedHoles.lean", ["GeneralCycleEnumerationRam"]),
        "end Runtimes",
        statements(),
        "end STACS2027",
    ]
    return "\n".join(line for line in compact_comments("\n\n".join(part.strip() for part in parts)).splitlines() if line.strip()) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if Challenge.lean needs regeneration")
    args = parser.parse_args()
    text = challenge_text()
    if len(text.splitlines()) > 1000 or len(text.encode("utf-8")) > 100 * 1024:
        raise ValueError("Challenge.lean exceeds the 1000-line or 100 KiB submission limit")
    for module in MATHLIB_IMPORTS:
        if not (MATHLIB / (module.replace(".", "/") + ".lean")).is_file():
            raise ValueError(f"{module} is not a module of the pinned Mathlib")
    destination = ROOT / "Challenge.lean"
    if args.check:
        if not destination.exists() or destination.read_text(encoding="utf-8") != text:
            print("Challenge.lean differs from its source declarations; regenerate it.", file=sys.stderr)
            return 1
        print("Challenge.lean matches its selected source declarations.")
    else:
        destination.write_text(text, encoding="utf-8")
        print(f"Generated Challenge.lean (independent statement; {len(TARGETS)} intentional theorem holes, "
              f"{len(text.splitlines())} lines, {len(text.encode('utf-8'))} bytes).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
