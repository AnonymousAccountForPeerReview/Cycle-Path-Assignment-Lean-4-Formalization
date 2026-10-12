#!/usr/bin/env python3
"""Generate the independent Challenge, which imports only three pinned Mathlib modules.

The hypermaps and their planarity (`Complexity.iterate` through `Complexity.halfEdgeEnd`) are
copied verbatim, with their documentation comments and in their original order, from the
NP-completeness foundation (`Complexity/Planarity.lean`); the cycle-path assignment problem
(`Edge` through `HasAssignment`) from the Section 5 formalization of the same manuscript
(`NPHardness/`); `K₄` (`k4`) from the Section 8 formalization (`MinorFree/`). Each dependency's
directory is read from `lake-manifest.json` (`scripts/dependencies.py`: a path dependency in its
`dir`, a git dependency in `.lake/packages/<name>`). Minors, 2-connectivity, the optimum and the
output format (`Outerplanar/Defs.lean`), Lemma 24's conclusion (`Outerplanar/Minors.lean`),
outerplanar drawings (`Outerplanar/OuterplanarDef.lean`), the unit-cost RAM
(`Outerplanar/RAM/Model.lean`), its input format and label bound (`Outerplanar/RAM/Layout.lean`),
its space-bounded runs (`Outerplanar/RAM/Bounded.lean`), and the polygon model with its weak dual
(`Outerplanar/Polygon.lean` through `Outerplanar/WeakDual.lean`) are copied from this library. The
compared theorems are copied from `Outerplanar/` too: each statement, with its documentation
comment, up to its `:=`, followed by `:= by sorry`. Each declaration is taken with the
documentation comment that immediately precedes it; where the source has none, the comment in
`DOCS` below is inserted (the term is unchanged, which Comparator checks). Other comments are
dropped.

The Challenge imports the pinned Mathlib modules `MATHLIB_IMPORTS`, which provide exactly the
Mathlib declarations that the weak-dual statements use (finite sets, their sums, folds and
symmetric differences, `Relation.ReflTransGen`, `List.sublistsLen`, the monoid power on `ℕ`).
Declarations elaborated without Mathlib in their libraries get the prefixes of `CORE_INSTANCES`
where Mathlib's instances would otherwise be chosen (see `docs/FOUNDATION.md`);
`scripts/compare_challenge.py` checks every resulting term.

This is a layout-aware extractor, not a general Lean parser and not a replacement for
Comparator. `--check` detects drift without changing a file.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys

from dependencies import dependency_dir

ROOT = Path(__file__).resolve().parents[1]
FOUNDATION = dependency_dir(ROOT, "np-completeness")
SECTION5 = dependency_dir(ROOT, "cpap-np-hardness")
SECTION8 = dependency_dir(ROOT, "cpap-minor-free")
MATHLIB = dependency_dir(ROOT, "mathlib")

# The Mathlib modules the Challenge imports (Mathlib is pinned by lakefile.toml and
# lake-manifest.json): `Finset.sum` and, through it, finite sets, `Finset.filter`,
# `Finset.card`, `Finset.fold`, the symmetric difference, the monoid structure of `ℕ`,
# `Relation.ReflTransGen` and `∃!`; `Finset.product` (`×ˢ`); `List.sublistsLen`.
MATHLIB_IMPORTS = [
    "Mathlib.Algebra.BigOperators.Group.Finset.Defs",
    "Mathlib.Data.Finset.Prod",
    "Mathlib.Data.List.Sublists",
]

# The compared theorems, in `comparator.json` order: (library file, name relative to the
# namespace `STACS2027`).
TARGETS = [
    ("Outerplanar/OuterplanarCharacterization.lean", "outerplanar_block_structure"),
    ("Outerplanar/PerfectK23.lean", "k23_perfect"),
    ("Outerplanar/LinearK23.lean", "k23_linear_ram"),
    ("Outerplanar/LinearK23.lean", "outerplanar_linear_ram"),
    ("Outerplanar/GeneralAlgorithm.lean", "outerplanar_algorithm_perfect"),
    ("Outerplanar/PlanarTriangles.lean", "TriangleMatching.planar_triangle_perfect_assignment"),
    ("Outerplanar/Minors.lean", "common_neighbours_le_two"),
    ("Outerplanar/WeakDualFacts.lean", "IsPolygon.euler_face_count"),
    ("Outerplanar/WeakDualBij.lean", "IsPolygon.cycle_subtree_bij"),
    ("Outerplanar/WeakDualBij.lean", "IsPolygon.cycle_subtree_bij_simpleCycles"),
    ("Outerplanar/WeakDualCount.lean", "IsPolygon.face_cycle_bound"),
    ("Outerplanar/WeakDualCount.lean", "IsPolygon.edge_cycle_bound"),
    ("Outerplanar/NamedHoles.lean", "IsPolygon.enclosed_faces_bound"),
    ("Outerplanar/NamedHoles.lean", "IsPolygon.enclosing_cycle_count_bound"),
    ("Outerplanar/NamedHoles.lean", "IsPolygon.cycle_child_dichotomy"),
    ("Outerplanar/LeafFaceDeletion.lean", "IsPolygon.leaf_face_deletion"),
]


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
    `STACS2027` share a `namespace … end` block with the section variables of their files."""
    blocks: list[str] = []
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
            body = f"namespace {space}\n\n{VARIABLES[space]}\n\n{body}\n\nend {space}"
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


# Lean shares, within one module, auxiliary `match` functions of the same shape. In the
# libraries, the declarations below live in modules other than those of the Section 5
# declarations whose matchers have the same shape, and each has its own matcher; in this
# single-module Challenge they would reuse the earlier one and elaborate to a different term.
# The option below (which only disables code generation for the matcher) gives the copied
# declaration a fresh matcher with the library's name and value. Comparator checks the result.
FRESH_MATCHER = {"WalkWithin"}
FRESH_MATCHER_PREFIX = "set_option bootstrap.genMatcherCode false in\n"

# The section variables of the statements in a sub-namespace (as in `WeakDual*.lean`).
VARIABLES = {"IsPolygon": "variable {g : Graph} {n : ℕ}", "TriangleMatching": ""}

# Declarations elaborated in their libraries with Lean core only, whose instance arguments
# Mathlib's instances would take over in this Challenge: each is preceded by
# `attribute [local instance high] I in` for core's instance `I`, which ranks `I` first for
# that one declaration (`c in d` runs `d` in a section after `c`), so that the copy
# elaborates to the library's term; the declaration's text is unchanged. Comparator and
# `scripts/compare_challenge.py` check the result.
CORE_INSTANCES: dict[str, list[str]] = {
    # `List.sum` over `ℕ`: core's `Zero.ofOfNat0`, not Mathlib's `AddMonoid`-based `Zero`.
    "overlap": ["attribute [local instance high] Zero.ofOfNat0 in"],
    "cost": ["attribute [local instance high] Zero.ofOfNat0 in"],
}

# Documentation comments for copied declarations that have none in their source.
DOCS: dict[str, str] = {
    "instance:Adj": "Adjacency in the simple graph of an edge list is decidable.",
    "instance:Within": "Being within a segment is decidable.",
    "instance:IsFaceVert": "Being a vertex of the face of a segment is decidable.",
    "instance:ConvexCycle": "Being a convex cycle is decidable.",
}


HEADER_DOC = """/-!
# Outerplanar and `K_{2,3}`-minor-free graphs: Lemmas 19, 24, 27, 29, 31, 35, Theorems 20, 21, and supporting cycle-count bounds

For the cycle-path assignment problem `CPAP(G, k)` of "Cycle-Path Assignment for Local
Differential Privacy: Complexity and Approximation" (the accompanying paper; Section 8
and Appendices E and F), the theorems at the end state, without hypotheses beyond their own:

* **Lemma 19** (`outerplanar_block_structure`): a graph is outerplanar (`OuterplanarDrawing`: its simple graph has a
  planar drawing with every vertex on the outer face) if and only if it has neither `K₄` nor
  `K_{2,3}` as a minor (`HasMinor`, by branch sets); every 2-connected (`TwoConnected`)
  `K_{2,3}`-minor-free graph is outerplanar or a `K₄` (`IsK4Graph`);
* **Theorem 20** (`k23_perfect`): every `K_{2,3}`-minor-free graph admits a perfect cycle-path
  assignment for `k = 4` (an assignment of cost `0`); **Algorithm 4**
  (`outerplanar_algorithm_perfect`) has a global elimination order and produces a perfect
  assignment on every loop-free outerplanar graph;
* the contextual triangle claim (`TriangleMatching.planar_triangle_perfect_assignment`):
  every planar graph has a perfect assignment for `k = 3`;
* **Theorem 21** (`k23_linear_ram`): for every `k ≥ 3` there are a program of the unit-cost RAM
  and a constant `C` such that, on the input encoding of every `K_{2,3}`-minor-free graph `g`
  with `m = |g|` entries, the program halts after at most `C (m + 1)` steps, accessing only the
  memory addresses below `C (L + m + 1)` (`L = RAM.labelBound g`, one more than the largest
  vertex label), with an output that writes an optimal cycle-path assignment of `CPAP(g, k)`:
  linear time and memory;
* **Lemma 35** (`outerplanar_linear_ram`): the same for outerplanar graphs (`OuterplanarDrawing`);
* **Lemma 24** (`common_neighbours_le_two`): in a `K_{2,3}`-minor-free graph, two distinct vertices have at most
  two common neighbours;
* on a 2-connected outerplanar graph written as a polygon (`IsPolygon g n`: the positions
  `0, …, n - 1` in order form a Hamiltonian cycle with respect to which no two edges cross),
  whose bounded faces are the segments `segs g n` (the face of `s` lies directly below `s`):
  **Lemma 27 (1)** (`IsPolygon.euler_face_count`), Euler's formula `r + n = m + 1`; **Lemma 29**
  (`IsPolygon.cycle_subtree_bij`, `IsPolygon.cycle_subtree_bij_simpleCycles`), the boundary map `ψ(S) = ∂S` (`bdry`)
  is a bijection from the subtrees of the weak dual (`IsSubtree`) onto the simple cycles (as
  edge sets; the convex cycles `ConvexCycle` represent them), with inverse `encl`, and
  `|ψ(S)| = ∑_{f ∈ S} d_f - 2 (|S| - 1)`; **Supporting cycle-count bounds** (`IsPolygon.face_cycle_bound`,
  `IsPolygon.edge_cycle_bound`), for `k ≥ 3`, at most `4^k` simple `k`-cycles enclose a face and at
  most `2 · 4^k` contain an edge.

The definitions are copied verbatim, with their documentation and in their source order:

* `Complexity.iterate` through `Complexity.PlanarGraph`: hypermaps and their planarity (genus `0`
  by the Euler formula), from the NP-completeness foundation (`Complexity/Planarity.lean`);
* `Edge` through `HasAssignment`: the cycle-path assignment problem (Definition 1), from the
  Section 5 formalization of the same manuscript; `k4`, `EliminationOrder`, `earliestIndex`
  and `algorithm4` from the Section 8 formalization;
* `Adj` through `OptimalAssignmentOutput` (`Outerplanar/Defs.lean`) and `CommonNeighbours2`
  (`Outerplanar/Minors.lean`): simple graphs of edge lists, walks, 2-connectivity, minors,
  `K_{2,3}`, `K₄` up to renaming, Hamiltonian cycles without crossing edges, the optimum `C*`
  (`IsMinCost`) and the output format of an optimal assignment;
* `simpleEdges`, `OuterplanarEmbedding`, `OuterplanarDrawing` (`Outerplanar/OuterplanarDef.lean`):
  a planar embedding (rotation system) of the simple graph with, in every connected component,
  a face through all the vertices of the component;
* the unit-cost RAM (`Outerplanar/RAM/Model.lean`, the machine of the Section 6 formalization):
  registers and memory `Nat → Nat`, a write-only output, the instructions
  `const add sub load store write` (indirect load and store, no multiplication), sequencing, a
  zero test and a `while ≠ 0` loop, each one step; its graph input `graphInput` and the label
  bound `labelBound` (`Outerplanar/RAM/Layout.lean`); runs within a memory bound, `ExecB` and
  `ComputesIn` (`Outerplanar/RAM/Bounded.lean`);
* the polygon model and its weak dual, `IsPolygon` through `IsSubtree` (`Outerplanar/Polygon.lean`,
  `Convex.lean`, `Segments.lean`, `Faces.lean`, `DPCorrect.lean`, `WeakDual.lean`).

Two elaboration options make the copies elaborate, in this module that imports Mathlib, to the
libraries' terms; they change no term (`docs/FOUNDATION.md`): `WalkWithin` gets its own `match`
auxiliary (`set_option bootstrap.genMatcherCode false in`), and `overlap` and `cost`, elaborated
without Mathlib in their library, rank Lean core's `Zero ℕ` first
(`attribute [local instance high] Zero.ofOfNat0 in`).

Generated by `scripts/generate_challenge.py`; `Solution.lean` proves the theorems without
importing this file.
-/"""


def challenge_text() -> str:
    planarity = "Complexity/Planarity.lean"
    parts = [
        "module\n\n" + "\n".join(f"public import {m}" for m in MATHLIB_IMPORTS),
        HEADER_DOC,
        "@[expose] public section",
        "namespace Complexity",
        library(FOUNDATION, planarity, ["iterate", "Hypermap", "cycleCount"]),
        "namespace Hypermap",
        library(FOUNDATION, planarity, ["linked", "componentCount", "eulerLhs", "eulerRhs", "genus", "Planar"]),
        "end Hypermap",
        library(FOUNDATION, planarity, ["halfEdgeEnd", "PlanarGraph"]),
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
        library(SECTION8, "MinorFree/K4.lean", ["k4"]),
        library(SECTION8, "MinorFree/Elimination.lean", ["EliminationOrder", "earliestIndex", "algorithm4"]),
        library(ROOT, "Outerplanar/Defs.lean", [
            "Adj", "IsVertex", "WalkWithin", "ConnectedWithin", "TwoConnected", "HasMinor", "k23",
            "K23MinorFree", "IsK4Graph", "OuterplanarHam", "IsMinCost", "OptimalAssignmentOutput",
        ]),
        library(ROOT, "Outerplanar/Minors.lean", ["CommonNeighbours2"]),
        library(ROOT, "Outerplanar/OuterplanarDef.lean", ["simpleEdges", "OuterplanarEmbedding", "OuterplanarDrawing"]),
        "namespace RAM",
        library(ROOT, "Outerplanar/RAM/Model.lean", [
            "Config", "Stmt", "Config.setReg", "Config.setMem", "Config.emit", "initial",
        ]),
        library(ROOT, "Outerplanar/RAM/Layout.lean", ["graphInput", "labelBound"]),
        library(ROOT, "Outerplanar/RAM/Bounded.lean", ["ExecB", "ComputesIn"]),
        "end RAM",
        library(ROOT, "Outerplanar/Polygon.lean", ["IsPolygon", "instance:Adj"]),
        library(ROOT, "Outerplanar/Convex.lean", ["ConvexCycle"]),
        library(ROOT, "Outerplanar/Segments.lean", ["Within", "instance:Within"]),
        "namespace IsPolygon",
        library(ROOT, "Outerplanar/Segments.lean", ["segs", "IsChild"]),
        "end IsPolygon",
        "open IsPolygon",
        library(ROOT, "Outerplanar/Faces.lean", ["IsFaceVert", "instance:IsFaceVert", "faceVerts"]),
        library(ROOT, "Outerplanar/DPCorrect.lean", ["instance:ConvexCycle", "convexList", "polyEdges"]),
        "open scoped symmDiff",
        library(ROOT, "Outerplanar/WeakDual.lean", ["faceEdges", "bdry", "encl", "DualAdj", "IsSubtree"]),
        library(ROOT, "Outerplanar/WeakDualFacts.lean", ["chords"]),
        library(ROOT, "Outerplanar/FaceTransport.lean", ["ChordlessCycle", "BoundedFaceBoundary", "BoundaryDualAdj"]),
        library(ROOT, "Outerplanar/LeafFaceDeletion.lean", ["IsDualLeaf", "leafInterior"]),
        statements(),
        "end STACS2027",
    ]
    return "\n\n".join(part.strip() for part in parts) + "\n"


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
        print(f"Generated Challenge.lean (independent statement; {len(TARGETS)} intentional theorem holes).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
