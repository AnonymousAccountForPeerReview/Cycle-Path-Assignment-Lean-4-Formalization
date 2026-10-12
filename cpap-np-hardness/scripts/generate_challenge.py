#!/usr/bin/env python3
"""Generate the independent, Init-only Challenge.

The machine model, NP, reductions, CNF formulas and their code, the (≤1,≤2)
restriction, planarity and the incidence graph are copied verbatim, with their
documentation comments and in their original order, from the Challenge of the
NP-completeness foundation `NPCompleteness-Lean4`, read from
`Challenge.lean` of the Lake dependency `np-completeness` (located through `lake-manifest.json`). The block from `Symbol` through
`NPComplete` is copied whole, as docs/FOUNDATION.md of that foundation requires;
from the SAT, planarity and incidence blocks only the declarations used here are
taken, and their relative order is kept.

The CPAP and planar (≤1,≤2)-SAT declarations are copied from this library with
the documentation comment that immediately precedes each of them, so the
Challenge and the library share docstrings. Other comments are dropped.

This is a layout-aware extractor, not a general Lean parser and not a
replacement for Comparator. `--check` detects drift without changing a file.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from dependencies import dependency_dir  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
FOUNDATION = dependency_dir(ROOT, "np-completeness")
FOUNDATION_ID = "NPCompleteness-Lean4"
FOUNDATION_REV = "3e603e795b44fedcf7d6dd65b7d1e30547ead925"


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
    r"section|open|set_option|attribute|notation|macro|syntax|example|mutual)\b",
    re.M,
)
NAMED = re.compile(
    r"(?:@\[[^\n]*\]\s*)?(?:(?:public|private|protected|noncomputable|unsafe)\s+)*"
    r"(?:def|abbrev|structure|inductive)\s+([\w'.]+)\b"
)
INSTANCE = re.compile(r"instance\b[^\n]*\)\s*:\s*Decidable\s*\((\w+)")


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


def select(source: str, keys: list[str], where: str) -> str:
    found = chunks(source)
    index = {}
    for position, (key, text) in enumerate(found):
        if key in index and not key.startswith("#"):
            raise ValueError(f"Ambiguous declaration {key!r} in {where}")
        index[key] = (position, text)
    missing = [k for k in keys if k not in index]
    if missing:
        raise ValueError(f"Missing declarations in {where}: {', '.join(missing)}")
    positions = [index[k][0] for k in keys]
    if positions != sorted(positions):
        raise ValueError(f"Declarations out of source order in {where}: {keys}")
    undocumented = [k for k in keys if not index[k][1].startswith("/--")]
    if undocumented:
        raise ValueError(f"Undocumented declarations in {where}: {', '.join(undocumented)}")
    return "\n\n".join(index[k][1] for k in keys)


def region(source: str, begin: str, end: str, occurrence: int = 1) -> str:
    """The text strictly between the `occurrence`-th line `begin` and the next line `end`."""
    position = -1
    for _ in range(occurrence):
        position = source.index("\n" + begin + "\n", position + 1)
    start = position + len(begin) + 2
    stop = source.index("\n" + end + "\n", start)
    return source[start:stop + 1]


def registered_blocks() -> tuple[str, str, str, str]:
    source = (FOUNDATION / "Challenge.lean").read_text(encoding="utf-8")
    machine = region(source, "namespace Complexity", "end Complexity", 1).strip()
    if not machine.startswith("/--") or "inductive Symbol where" not in machine.split("\n\n")[0] \
            or not machine.rstrip().endswith("InNP L ∧ NPHard L"):
        raise ValueError("Unexpected layout of the foundation's machine block")
    sat = select(region(source, "namespace Complexity.SAT", "end Complexity.SAT", 1), [
        "Word", "Assignment", "Literal", "Clause", "CNF", "evalLiteral", "evalClause",
        "evalCNF", "Satisfiable", "writeNat", "writeValues", "writeList", "encodeLiteral",
        "encodeClause", "encode", "IsLeOneLeTwoCNF",
    ], "the foundation's SAT block")
    planarity = region(source, "namespace Complexity", "end Complexity", 2).strip()
    if not planarity.startswith("/-- `iterate f k x`") or "def PlanarGraph" not in planarity:
        raise ValueError("Unexpected layout of the foundation's planarity block")
    incidence = select(region(source, "namespace Complexity.SAT", "end Complexity.SAT", 2),
                       ["incidenceGraph"], "the foundation's incidence block")
    return machine, sat, planarity, incidence


def library(path: str, keys: list[str]) -> str:
    return select((ROOT / path).read_text(encoding="utf-8"), keys, path)


HEADER = f"""module

public import Init

/-!
# NP-hardness of the cycle-path assignment problem for fixed k ≥ 5

For one machine model and concrete binary codes, the theorems at the end state
that planar (≤1,≤2)-SAT is NP-complete and that, for every fixed `k ≥ 5`, the
cycle-path assignment problem CPAP is NP-hard on general graphs and on planar
graphs (Theorem 6 of the accompanying paper "Cycle-Path Assignment").

* The machine model, NP, polynomial-time many-one reductions, CNF formulas, their
  code `encode`, the (≤1,≤2) restriction, planarity and the incidence graph are
  copied verbatim, with their order, from the Challenge of the NP-completeness
  foundation `{FOUNDATION_ID}` (commit {FOUNDATION_REV[:12]}): all of
  `Symbol` through `NPComplete`, and the declarations used here from its SAT,
  planarity and incidence blocks.
* Planar (≤1,≤2)-SAT adds planarity of the variable–clause incidence graph to
  the foundation's (≤1,≤2) restriction, as planar 3-SAT does to 3-SAT. As in the
  foundation, clauses need not have distinct variables.
* A CPAP instance `(G, B)` is a list of records coded by `encode`: a clause of
  two positive literals `x u, x v` is the edge `{{u, v}}`, and an empty clause adds
  one to the budget `B`. It is a yes-instance when one path of `k - 2` edges can be
  chosen in each simple `k`-cycle of `G` (each cycle counted once) with total cost
  at most `B`; the cost, the edges shared by pairs of chosen paths, is
  `∑_e binom(l(e), 2)` for the edge loads `l(e)` (Definition 1).
* Words coding no formula or instance belong to none of the languages.

Only Lean core is imported. `scripts/generate_challenge.py` generates this file
from the foundation and the library; `Solution.lean` proves the theorems
without importing it.
-/

@[expose] public section"""

TARGETS = """/-- Planar (≤1,≤2)-SAT is NP-complete. -/
theorem planarLeOneLeTwoSAT_np_complete : Complexity.NPComplete PlanarLeOneLeTwoSAT := by sorry

/-- For every fixed `k ≥ 5`, CPAP is NP-hard. -/
theorem cpap_np_hard {k : Nat} (hk : 5 ≤ k) : Complexity.NPHard (CPAP k) := by sorry

/-- **Theorem 6.** For every fixed `k ≥ 5`, CPAP is NP-hard on planar graphs. -/
theorem planarCPAP_np_hard {k : Nat} (hk : 5 ≤ k) :
    Complexity.NPHard (PlanarCPAP k) := by sorry"""


def challenge_text() -> str:
    machine, sat, planarity, incidence = registered_blocks()
    parts = [
        HEADER,
        "namespace Complexity",
        machine,
        "end Complexity\n\nnamespace Complexity.SAT",
        sat,
        "end Complexity.SAT\n\nnamespace Complexity",
        planarity,
        "end Complexity\n\nnamespace Complexity.SAT",
        incidence,
        "end Complexity.SAT\n\nnamespace STACS2027\nopen Complexity Complexity.SAT",
        library("NPHardness/FiniteCycles.lean", [
            "Edge", "Graph", "Cycle", "edge", "pathEdges", "cycleEdges", "IsCycle",
            "instance:IsCycle", "SameCycle", "instance:SameCycle", "selected", "overlap", "cost",
        ]),
        library("NPHardness/CycleRepresentatives.lean", ["cycleRepresentatives"]),
        library("NPHardness/Enumerate.lean", ["vertices", "neighbors", "walksFrom", "rawCycles", "cycles"]),
        library("NPHardness/CostSearch.lean", ["selectedOptions", "ValidChoices"]),
        library("NPHardness/CPAP.lean", ["HasAssignment"]),
        library("NPHardness/GraphEncoding.lean", [
            "validGraphRecord", "recordEdge", "instructionGraph", "instructionBudget",
            "ValidGraphInstructions", "CPAP",
        ]),
        library("NPHardness/PlanarFoundation.lean", ["PlanarCPAP", "IsPlanarLeOneLeTwoCNF", "PlanarLeOneLeTwoSAT"]),
        TARGETS,
        "end STACS2027",
    ]
    return "\n\n".join(part.strip() for part in parts) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if Challenge.lean needs regeneration")
    args = parser.parse_args()
    text = challenge_text()
    if len(text.splitlines()) > 1000:
        raise ValueError("Challenge.lean exceeds the 1000-line limit")
    destination = ROOT / "Challenge.lean"
    if args.check:
        if not destination.exists() or destination.read_text(encoding="utf-8") != text:
            print("Challenge.lean differs from its source declarations; regenerate it.", file=sys.stderr)
            return 1
        print("Challenge.lean matches its selected source declarations.")
    else:
        destination.write_text(text, encoding="utf-8")
        print("Generated Challenge.lean (independent statement; three intentional theorem holes).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
