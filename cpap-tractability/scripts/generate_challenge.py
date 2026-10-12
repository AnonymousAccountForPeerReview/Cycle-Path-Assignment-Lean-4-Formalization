#!/usr/bin/env python3
"""Generate the independent, Init-only Challenge.

The cycle-path assignment problem (`Edge` through `HasAssignment`) is copied
verbatim, with its documentation comments and in its original order, from the
Section 5 formalization of the same manuscript, read from
`NPHardness/` of the Lake dependency `cpap-np-hardness` (located through `lake-manifest.json`), whose Challenge states that problem
for its NP-hardness results; the Solution imports that library
through the Lake dependency `cpap-np-hardness`. The network of
Theorem 2 and the notion of integral flow are copied from `Tractability/FlowNetwork.lean`.
Each declaration is taken with the documentation comment that immediately
precedes it, so the Challenge and the libraries share docstrings. Other comments
are dropped.

No declaration of the NP-completeness foundation `NPCompleteness-Lean4` is needed:
the statement mentions neither machines nor formulas.

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
SECTION5 = dependency_dir(ROOT, "cpap-np-hardness")


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


def library(base: Path, path: str, keys: list[str]) -> str:
    return select((base / path).read_text(encoding="utf-8"), keys, path)


HEADER = """module

public import Init

/-!
# The min-cost flow reductions for four-cycles (Theorem 2) and triangles

For the cycle-path assignment problem `CPAP(G, k)` of the accompanying paper
"Cycle-Path Assignment", the theorems at the end state that the flow network of
Appendix A is correct and has linear size: `G` has an assignment of cost at most `B`
for `k = 4` iff the network has an integral flow of value `2t` and cost at most `B`,
where `t` is the number of simple four-cycles of `G`; and the network has `10t` arcs,
at most `6t + 2` nodes, unit capacities and costs below `t`. Theorem 2's running time
then follows from the cited minimum-cost flow algorithm, which is not formalized.
Likewise for triangles (the corollary `K3TimeComplexity`): `G` has an assignment of
cost at most `B` for `k = 3` iff the triangle network — one node `x_C` per triangle
`C`, arcs `s → x_C` and `x_C → y_e` for the three edges of `C`, the same sink bundles —
has an integral flow of value `t` (the number of triangles) and cost at most `B`; and
that network has `7t` arcs, at most `4t + 2` nodes, unit capacities and costs below `t`.

* The cycle-path assignment problem (`Edge` through `HasAssignment`) is copied
  verbatim, with its order, from the formalization of Section 5 of the same
  manuscript (Lake dependency `cpap-np-hardness`), whose Challenge states it for
  the NP-hardness results of that section. For fixed `k`, the
  simple `k`-cycles of a graph are enumerated once each, by edge set; an assignment
  chooses one vertex of each to omit, leaving a path of `k - 2` edges; its cost is
  the number of edges shared by pairs of chosen paths, `∑_e binom(l(e), 2)`
  (Definition 1).
* The network has a source `s`, a sink `z`, two opposing-pair nodes `x_{C,{e₁,e₃}}`
  and `x_{C,{e₂,e₄}}` for each four-cycle `C` with cyclically ordered edges
  `e₁, e₂, e₃, e₄`, and an edge node `y_e` for each edge `e` on a four-cycle. Its arcs,
  all of capacity one, are `s → x_{C,p}` (cost 0), `x_{C,p} → y_e` for the two edges
  `e` of the pair `p` (cost 0), and `ϖ(e)` parallel arcs `y_e → z` with costs
  `0, …, ϖ(e) - 1`, `ϖ(e)` being the number of four-cycles containing `e`. The triangle
  network has one node `x_C` per triangle instead of the two pair nodes, with arcs
  `s → x_C` and `x_C → y_e` for the three edges of `C`.
* An integral flow is a sublist of the arc list (the arcs carrying one unit) that
  conserves flow at every node other than `s` and `z`; its value is the number of
  its arcs leaving `s`, its cost the sum of their costs.

Only Lean core is imported. `scripts/generate_challenge.py` generates this file
from the two libraries; `Solution.lean` proves the theorems without importing it.
-/

@[expose] public section"""

TARGETS = """/-- **Theorem 2**, the reduction of Appendix A: `CPAP(G, 4)` has an assignment of cost at most
`budget` iff the network has an integral flow of value `2t` and cost at most `budget`, `t` being
the number of simple four-cycles. The minimum cost of such a flow is therefore `OPT`. -/
theorem cpap4_iff_flow (g : Graph) (budget : Nat) :
    HasAssignment g 4 budget ↔
      ∃ flow, IsFlow (fourCycleNetwork g) flow ∧
        flowValue flow = 2 * (cycles g 4).length ∧ flowCost flow ≤ budget := by sorry

/-- The size of the network of Theorem 2: `10t` arcs and at most `6t + 2` nodes, every arc
joining two nodes with cost less than `t` (and capacity one, by construction). -/
theorem fourCycleNetwork_size (g : Graph) :
    (fourCycleNetwork g).length = 10 * (cycles g 4).length ∧
    (networkNodes g).length ≤ 6 * (cycles g 4).length + 2 ∧
    (∀ a ∈ fourCycleNetwork g, a.tail ∈ networkNodes g ∧ a.head ∈ networkNodes g) ∧
    ∀ a ∈ fourCycleNetwork g, a.cost < (cycles g 4).length := by sorry

/-- **Corollary `K3TimeComplexity`**, the reduction: `CPAP(G, 3)` has an assignment of cost at
most `budget` iff the triangle network has an integral flow of value `t` and cost at most
`budget`, `t` being the number of triangles. The minimum cost of such a flow is therefore
`OPT`. -/
theorem cpap3_iff_flow (g : Graph) (budget : Nat) :
    HasAssignment g 3 budget ↔
      ∃ flow, IsFlow (triangleNetwork g) flow ∧
        flowValue flow = (cycles g 3).length ∧ flowCost flow ≤ budget := by sorry

/-- The size of the triangle network: `7t` arcs and at most `4t + 2` nodes, every arc joining
two nodes with cost less than `t` (and capacity one, by construction). -/
theorem triangleNetwork_size (g : Graph) :
    (triangleNetwork g).length = 7 * (cycles g 3).length ∧
    (triangleNodes g).length ≤ 4 * (cycles g 3).length + 2 ∧
    (∀ a ∈ triangleNetwork g, a.tail ∈ triangleNodes g ∧ a.head ∈ triangleNodes g) ∧
    ∀ a ∈ triangleNetwork g, a.cost < (cycles g 3).length := by sorry"""


def challenge_text() -> str:
    parts = [
        HEADER,
        "namespace STACS2027",
        library(SECTION5, "NPHardness/FiniteCycles.lean", [
            "Edge", "Graph", "Cycle", "edge", "pathEdges", "cycleEdges", "IsCycle",
            "instance:IsCycle", "SameCycle", "instance:SameCycle", "selected", "overlap", "cost",
        ]),
        library(SECTION5, "NPHardness/CycleRepresentatives.lean", ["cycleRepresentatives"]),
        library(SECTION5, "NPHardness/Enumerate.lean", ["vertices", "neighbors", "walksFrom", "rawCycles", "cycles"]),
        library(SECTION5, "NPHardness/CostSearch.lean", ["selectedOptions", "ValidChoices"]),
        library(SECTION5, "NPHardness/CPAP.lean", ["HasAssignment"]),
        library(ROOT, "Tractability/FlowNetwork.lean", [
            "FlowNode", "FlowNode.beq", "Arc", "opposingPair", "cycleEdgeList", "cycleCount",
            "sourceArcs", "fourCycle", "pairArcs", "sinkArcs", "fourCycleNetwork", "networkNodes",
            "inflow", "outflow", "IsFlow", "flowValue", "flowCost",
        ]),
        library(ROOT, "Tractability/TriangleNetwork.lean", [
            "triangleAt", "triangleEdgeList", "triangleCount", "triangleSourceArcs", "triangleEdgeArcs",
            "triangleSinkArcs", "triangleNetwork", "triangleNodes",
        ]),
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
        print("Generated Challenge.lean (independent statement; four intentional theorem holes).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
