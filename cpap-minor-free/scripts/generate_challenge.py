#!/usr/bin/env python3
"""Generate the independent, Init-only Challenge.

The planarity block of the NP-completeness foundation `NPCompleteness-Lean4`
(`iterate` through `PlanarGraph`, namespace `Complexity`) is copied whole and
verbatim from the foundation, read from
`Challenge.lean` of the Lake dependency `np-completeness` (located through `lake-manifest.json`) as the Section 5 Challenge
does; the generator checks that it is identical to the corresponding block of
the foundation's library module `Complexity/Planarity.lean`, which the
Solution imports.

The cycle-path assignment problem (`Edge` through `HasAssignment`), the pair
count `pairCount` and the vertex relabelling `mapEdge`, `mapGraph` are copied
verbatim, with their documentation comments and in their original order, from
the Section 5 formalization of the same manuscript, read from
`NPHardness/` of the Lake dependency `cpap-np-hardness` (located through `lake-manifest.json`); the Solution imports that library
through the Lake dependency `cpap-np-hardness` (which requires the
NP-completeness foundation `NPCompleteness-Lean4`). The elimination orders,
Algorithm 4, `K₄`, the block structure and `K_{2,r}` are copied from
`MinorFree/`. Each declaration is taken with the documentation comment that
immediately precedes it; where the Section 5 library has none, the comment in
`DOCS` below is inserted (the term is unchanged, which Comparator checks). Other
comments are dropped.

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
FOUNDATION = dependency_dir(ROOT, "np-completeness")


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
        parts.append(text)
    return "\n\n".join(parts)


def library(base: Path, path: str, keys: list[str]) -> str:
    return select((base / path).read_text(encoding="utf-8"), keys, path)


def region(source: str, begin: str, end: str, occurrence: int = 1) -> str:
    """The text strictly between the `occurrence`-th line `begin` and the next line `end`."""
    position = -1
    for _ in range(occurrence):
        position = source.index("\n" + begin + "\n", position + 1)
    start = position + len(begin) + 2
    stop = source.index("\n" + end + "\n", start)
    return source[start:stop + 1]


def registered_planarity() -> str:
    """The foundation's planarity block, verbatim (as in the Section 5 Challenge)."""
    challenge = (FOUNDATION / "Challenge.lean").read_text(encoding="utf-8")
    block = region(challenge, "namespace Complexity", "end Complexity", 2).strip()
    if not block.startswith("/-- `iterate f k x`") or not block.rstrip().endswith("G.Planar") \
            or "def PlanarGraph" not in block:
        raise ValueError("Unexpected layout of the foundation's planarity block")
    source = (FOUNDATION / "Complexity/Planarity.lean").read_text(encoding="utf-8")
    if region(source, "namespace Complexity", "end Complexity", 1).strip() != block:
        raise ValueError("The foundation's planarity block differs from Complexity/Planarity.lean")
    return block


# This code-generation-only prefix reserves the copied recursive declaration's
# matcher names without changing its kernel term. earliestIndex uses nested
# empty/cons matches, whose shape differs from Section 5's three-alternative
# pathEdges match. Comparator checks every copied auxiliary's name and value.
FRESH_MATCHER = {"earliestIndex"}
FRESH_MATCHER_PREFIX = "set_option bootstrap.genMatcherCode false in\n"

# Documentation comments for the Section 5 declarations copied without one.
DOCS = {
    "mapEdge": "Relabel the endpoints of an edge.",
    "mapGraph": "Relabel the vertices of a graph.",
}


HEADER = """module

public import Init

/-!
# Cycle-path assignment on minor-free graphs: Lemma 25, Theorem 20 and Lemma 23

For the cycle-path assignment problem `CPAP(G, k)` of the accompanying paper
"Cycle-Path Assignment", the theorems at the end state:

* **Lemma 25** (Appendix E): on a graph with a degree-two elimination order (an injective
  vertex ranking in which every vertex has at most two neighbours of larger rank: the order
  in which Algorithm 4 deletes the vertices of an outerplanar graph) in which two distinct
  vertices have at most two common neighbours (Lemma 24, as in every `K_{2,3}`-minor-free
  graph), Algorithm 4's assignment — every four-cycle receives the two edges at its earliest
  vertex — is a cycle-path assignment for `k = 4` of cost zero;
* `K₄` has a perfect four-cycle assignment and no `k`-cycle for `k ≥ 5`;
* assignments of pairwise edge-disjoint blocks, within which every `k`-cycle lies, combine
  to an assignment of the whole graph with the summed cost; hence **Theorem 20**: a graph
  whose four-cycles lie within pairwise edge-disjoint blocks, each outerplanar (given by an
  elimination order and the common-neighbour bound) or a copy of `K₄` — as the blocks of
  every `K_{2,3}`-minor-free graph are, by Lemma 19 — admits a perfect assignment for
  `k = 4`;
* **Lemma 23** (Appendix E): on any graph with `m` edges, every assignment of its `t`
  `k`-cycles, of total load `Q = (k − 2) t`, has `Q² ≤ m (2 c(τ) + Q)` (Cauchy–Schwarz);
  `K_{2,r}` (`n = r + 2` vertices) is planar, has `2r` edges and `binom(r, 2)` four-cycles,
  and every four-cycle assignment of it has cost between
  `r (r − 1)(r − 3) / 4 = (n − 2)(n − 3)(n − 5) / 4` and `r (r − 1)(r − 2)`: `Θ(n³)`.

Lemma 19 (ANONYMIZED), the existence of the elimination order for outerplanar graphs, Lemma 24
for `K_{2,3}`-minor-free graphs, the block decomposition, and the running times (Theorem 21,
Appendix F) are cited or taken as hypotheses here; they are formalized in a separate package
that builds on this one. Numbers are those of the paper of the manuscript.

* Planarity is that of the NP-completeness foundation `NPCompleteness-Lean4` (Lake dependency
  `np-completeness`), whose planarity block (`iterate` through `PlanarGraph`) is copied whole
  and verbatim: following ANONYMIZED's Four Color proof, a hypermap is planar when its genus,
  from the Euler formula, is zero, and a graph, given by its edge list, is planar when some
  planar hypermap on its half-edges pairs the two ends of each edge (`edge`) and has the
  half-edges at a common vertex as its `node` cycles.
* The cycle-path assignment problem (`Edge` through `HasAssignment`), `pairCount` and the
  vertex relabelling (`mapEdge`, `mapGraph`) are copied verbatim, with their order, from the
  formalization of Section 5 of the same manuscript (Lake dependency `cpap-np-hardness`);
  documentation comments are added where that library has none. For fixed `k`, the simple
  `k`-cycles of a graph are enumerated once each, by edge set; an assignment chooses one
  vertex of each to omit, leaving a path of `k - 2` edges (`selectedOptions`); its cost is
  the number of edges shared by pairs of chosen paths, `∑_e binom(l(e), 2)` (Definition 1).
* `EliminationOrder`, `CommonNeighbourBound`, `earliestIndex` and `algorithm4` describe
  Algorithm 4; `k4` and `IsK4` the complete graph on four vertices and its copies;
  `EdgeDisjoint`, `CyclesInBlocks` and `OuterplanarOrK4` the block structure; `biclique r`
  is `K_{2,r}`.

Only Lean core is imported. `scripts/generate_challenge.py` generates this file
from the foundation and the two libraries; `Solution.lean` proves the theorems without
importing it.
-/

@[expose] public section"""

TARGETS = """/-- **Lemma 25** (on the elimination order): on a graph with a degree-two elimination order
in which two distinct vertices have at most two common neighbours — every outerplanar graph —
Algorithm 4 outputs a cycle-path assignment for `k = 4` of cost zero. -/
theorem algorithm4_perfect {g : Graph} {rank : Nat → Nat} (ho : EliminationOrder g rank)
    (hb : CommonNeighbourBound g) :
    ValidChoices ((cycles g 4).map selectedOptions) (algorithm4 rank g) ∧
      cost (algorithm4 rank g) = 0 := by sorry

/-- `K₄` has a perfect four-cycle assignment and no `k`-cycle for `k ≥ 5`. -/
theorem k4_cycle_assignments : HasAssignment k4 4 0 ∧ ∀ k, 5 ≤ k → cycles k4 k = [] := by sorry

/-- Assignments of the blocks combine to an assignment of the whole graph with the summed
budget. -/
theorem hasAssignment_blocks {blocks : List Graph} {k : Nat} (budget : Graph → Nat)
    (hdisj : EdgeDisjoint blocks) (hsplit : CyclesInBlocks blocks k)
    (hb : ∀ b ∈ blocks, HasAssignment b k (budget b)) :
    HasAssignment blocks.flatten k (blocks.map budget).sum := by sorry

/-- **Theorem 20** (on the block structure): a graph whose four-cycles lie within pairwise
edge-disjoint blocks, each outerplanar (with an elimination order and the common-neighbour
bound) or a copy of `K₄` — as the blocks of every `K_{2,3}`-minor-free graph are, by
Lemma 19 — admits a perfect cycle-path assignment for `k = 4`. -/
theorem perfect_assignment_of_blocks {blocks : List Graph} (hdisj : EdgeDisjoint blocks)
    (hsplit : CyclesInBlocks blocks 4) (hb : ∀ b ∈ blocks, OuterplanarOrK4 b) :
    HasAssignment blocks.flatten 4 0 := by sorry

/-- **Lemma 23, the lower bound, on any graph**: with `m = |E|` edges and total load
`Q = (k − 2) t`, every assignment has `Q² ≤ m (2 c(τ) + Q)`, i.e. `c(τ) ≥ (Q²/m − Q)/2`
(Cauchy–Schwarz). -/
theorem cost_lower_bound {g : Graph} {k : Nat} (hg : g.Nodup) {ps : List (List Edge)}
    (hv : ValidChoices ((cycles g k).map selectedOptions) ps) :
    ((k - 2) * (cycles g k).length) * ((k - 2) * (cycles g k).length) ≤
      g.length * (2 * cost ps + (k - 2) * (cycles g k).length) := by sorry

/-- **Lemma 23.** `K_{2,r}` is planar (`Complexity.PlanarGraph`, the NP-completeness foundation's
hypermap definition), has `n = r + 2` vertices, `m = 2r` edges and `binom(r, 2)` four-cycles,
and every four-cycle assignment of it has cost between `(n − 2)(n − 3)(n − 5)/4` and
`(n − 2)(n − 3)(n − 4)`: a family of planar graphs whose optimal four-cycle assignment cost is
`Θ(n³)`. -/
theorem biclique_planar_family (r : Nat) :
    Complexity.PlanarGraph (biclique r) ∧
      (biclique r).length = 2 * r ∧ (cycles (biclique r) 4).length = pairCount r ∧
      ∀ ps, ValidChoices ((cycles (biclique r) 4).map selectedOptions) ps →
        r * (r - 1) * (r - 3) ≤ 4 * cost ps ∧ cost ps ≤ r * (r - 1) * (r - 2) := by sorry"""


def challenge_text() -> str:
    parts = [
        HEADER,
        "namespace Complexity",
        registered_planarity(),
        "end Complexity",
        "namespace STACS2027",
        library(SECTION5, "NPHardness/FiniteCycles.lean", [
            "Edge", "Graph", "Cycle", "edge", "pathEdges", "cycleEdges", "IsCycle",
            "instance:IsCycle", "SameCycle", "instance:SameCycle", "selected", "overlap", "cost",
        ]),
        library(SECTION5, "NPHardness/CycleRepresentatives.lean", ["cycleRepresentatives"]),
        library(SECTION5, "NPHardness/Enumerate.lean", ["vertices", "neighbors", "walksFrom", "rawCycles", "cycles"]),
        library(SECTION5, "NPHardness/CostSearch.lean", ["selectedOptions", "ValidChoices"]),
        library(SECTION5, "NPHardness/CPAP.lean", ["HasAssignment"]),
        library(SECTION5, "NPHardness/LoadCost.lean", ["pairCount"]),
        library(SECTION5, "NPHardness/GraphRelabel.lean", ["mapEdge", "mapGraph"]),
        library(ROOT, "MinorFree/Elimination.lean", [
            "EliminationOrder", "CommonNeighbourBound", "earliestIndex", "algorithm4",
        ]),
        library(ROOT, "MinorFree/K4.lean", ["k4", "IsK4"]),
        library(ROOT, "MinorFree/Blocks.lean", ["EdgeDisjoint", "CyclesInBlocks", "OuterplanarOrK4"]),
        library(ROOT, "MinorFree/Biclique.lean", ["biclique"]),
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
        print("Generated Challenge.lean (independent statement; six intentional theorem holes).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
