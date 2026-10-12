#!/usr/bin/env python3
"""Generate the independent, Init-only Challenge.

The machine model (the block `Symbol` through `NPComplete`, whole) is copied
verbatim from the Challenge of the NP-completeness foundation `NPCompleteness-Lean4`,
read from `Challenge.lean` of the Lake dependency `np-completeness` (located through `lake-manifest.json`); the CNF formulas and their
code (`Word` through `encode`, with `clauseBound` and `variableBound`) from its library
file `Complexity/SAT.lean` (where `Literal` derives `DecidableEq`, used by Section 5's
occurrence numbering). The cycle-path assignment
problem (`Edge` through `HasAssignment`), the Theorem 8 construction (`Link`
through `formulaGraph`), the occurrence bounds of Definition 7 and `tautological`
are copied the same way from the Section 5 formalization of the same
manuscript, read from `NPHardness/` of the Lake dependency `cpap-np-hardness` (located through `lake-manifest.json`); the Solution
imports both libraries through the Lake dependencies `np-completeness`
and `cpap-np-hardness`. The record format of CPAP instances (`validGraphRecord` through `GraphOutput`)
is copied from Section 5's `GraphEncoding.lean`. The optimization problems,
L-reductions, the Lemma 10 transformation, the unit-cost RAM, its space-bounded
runs (`ExecB`, `ComputesIn`, the same definitions as in the outerplanar formalization) and its
input format are copied from `ApproximationHardness/`. Each declaration is taken with the
documentation comment that immediately precedes it; where the Section 5 library
has none, the comment in `DOCS` below is inserted (the term is unchanged, which
Comparator checks). Other comments are dropped.

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
PCP = dependency_dir(ROOT, "pcp")


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
    r"(?:def|abbrev|structure|inductive|class|theorem|lemma|instance|namespace|end|"
    r"section|open|set_option|attribute|notation|macro|syntax|example|mutual|variable)\b",
    re.M,
)
NAMED = re.compile(
    r"(?:@\[[^\n]*\]\s*)?(?:(?:public|private|protected|noncomputable|unsafe)\s+)*"
    r"(?:def|abbrev|structure|inductive|class)\s+([\w'.]+)\b"
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
        doc = FILE_DOCS.get((where, k), DOCS.get(k))
        if not text.startswith("/--"):
            if doc is None:
                raise ValueError(f"Undocumented declaration without a DOCS entry in {where}: {k}")
            text = f"/-- {doc} -/\n" + text
        elif (where, k) in FILE_DOCS or (k in DOCS and where not in FILE_DOCS_ONLY):
            raise ValueError(f"DOCS entry for an already documented declaration: {k}")
        if k in FRESH_MATCHER or (where, k) in FILE_FRESH_MATCHER:
            text = FRESH_MATCHER_PREFIX + text
        parts.append(text)
    return "\n".join(parts)


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


def registered_machine() -> str:
    """The machine block (`Symbol` through `NPComplete`) of the foundation's Challenge, whole, as
    the foundation's docs/FOUNDATION.md requires."""
    source = (FOUNDATION / "Challenge.lean").read_text(encoding="utf-8")
    machine = region(source, "namespace Complexity", "end Complexity", 1).strip()
    if not machine.startswith("/--") or "inductive Symbol where" not in machine.split("\n\n")[0] \
            or not machine.rstrip().endswith("InNP L ∧ NPHard L"):
        raise ValueError("Unexpected layout of the foundation's machine block")
    return machine


# Lean shares, within one module, auxiliary `match` functions of the same shape. In
# the libraries, `Complexity.SAT.variableBound` and `STACS2027.placeFormula` live in
# different modules and each has its own matcher, and so do `Complexity.SAT.writeNat`
# and `STACS2027.subdividedEdge`; in this single-module Challenge the second of each
# pair would reuse the first's and elaborate to a different term. The option below
# (which only disables code generation for the matcher) gives the copied declaration a
# fresh matcher with the library's name and value. Comparator checks the result.
FRESH_MATCHER = {"placeFormula", "subdividedEdge"}
FRESH_MATCHER_PREFIX = "set_option bootstrap.genMatcherCode false in\n"
# The same, for one declaration of one file: Section 5's `Oriented.clauseVertex` has the match
# shape of `clauseVertex`.
FILE_FRESH_MATCHER = {("NPHardness/OrientedVertexGluing.lean", "clauseVertex")}

# Documentation comments for declarations, by file, where the name alone is ambiguous.
FILE_DOCS = {
    ("NPHardness/OrientedVertexGluing.lean", "Orientation"):
        "An endpoint orientation: for each literal occurrence, whether its shared port edge is reversed.",
    ("NPHardness/OrientedVertexGluing.lean", "orientSide"):
        "The side of a variable port glued to side `side` of a literal edge, reversed if the occurrence is flipped.",
    ("NPHardness/OrientedVertexGluing.lean", "clauseVertex"):
        "`clauseVertex` with oriented port identification: a literal-edge endpoint is glued to the variable-port endpoint on the oriented side.",
    ("NPHardness/OrientedGlobalGraph.lean", "placedClauseGraph"):
        "The clause gadget of clause `j`, glued to the variable ports with the orientation.",
    ("NPHardness/OrientedGlobalGraph.lean", "formulaGraph"):
        "The Theorem 8 graph with oriented port identification.",
    ("NPHardness/OrientedGluing.lean", "EndpointChoices"):
        "Endpoint choices: one bit per literal occurrence, reversing its shared port edge.",
    ("NPHardness/OrientedGluing.lean", "orientedFormulaGraph"):
        "The Theorem 8 graph for the endpoint choices `flips` (Theorem 8 for planar formulas).",
}
# Files whose declarations take their documentation from FILE_DOCS only.
FILE_DOCS_ONLY = {"NPHardness/OrientedVertexGluing.lean", "NPHardness/OrientedGlobalGraph.lean",
    "NPHardness/OrientedGluing.lean"}

# Documentation comments for the Section 5 declarations copied without one.
DOCS = {
    "Link": "A constructor entry: the edge `source`–`target`, subdivided `subdivisions` times.",
    "realizeLinks": "The edges of a list of links, fresh subdivision vertices numbered from `next`.",
    "variableGraph": "`γ_x`, the variable gadget of Step 1 (Figure 4(a)) on vertices `0, …, 6` and its subdivision vertices.",
    "clauseThreeGraph": "`ζ_(c,3)`, the 3-literal clause gadget of Step 2 (Figure 4(b)).",
    "orangeSubdivisions": "Step 3, dashed orange edges: `⌊(k−5)/2⌋` subdivisions, none at `k = 6`.",
    "blueSubdivisions": "Step 3, dashed blue edges: `⌈(k−5)/2⌉` subdivisions, none at `k = 6`.",
    "redSubdivisions": "Step 3, dashed red edge: one subdivision at `k = 6`, none otherwise.",
    "clauseTwoGraph": "`ζ_(c,2)`, the 2-literal clause gadget of Step 3 (Figure 4(c)).",
    "subdivisionCount": "The number of subdivision vertices a list of links creates.",
    "PlacedLiteral": "A literal occurrence: the literal and the number of its earlier occurrences in the formula.",
    "placeLiterals": "Number the occurrences of a clause's literals, continuing the count from `past`.",
    "placeFormula": "Number every literal occurrence of a formula, clause by clause (Step 4's allocation order).",
    "PlacedLiteral.port": "The variable port of an occurrence: `0` for the positive one, `1` and `2` for the first and second negative ones.",
    "blockVertex": "Vertex `v` of the gadget copy numbered `tag`, blocks of `width` vertices.",
    "variableEndpoint": "The endpoints of the variable ports `e_(x,True,1)`, `e_(x,False,1)`, `e_(x,False,2)`: port `0` is `(2, 6)`, port `1` is `(4, 5)`, port `2` is `(0, 3)`.",
    "clauseEndpoint": "The endpoints of the literal edges `e_(c,1)`, `e_(c,2)`, `e_(c,3)` of a clause gadget: `(0, 1)`, `(4, 5)`, `(10, 11)`.",
    "clausePortAt": "The slot and side of a clause-gadget vertex that is an endpoint of a literal edge.",
    "attachmentAt": "The occurrence glued at a clause-gadget vertex, and its side, if the vertex is a literal-edge endpoint.",
    "clauseVertex": "Step 4: the global vertex of vertex `v` of clause gadget `j`, identified with the variable port of the occurrence glued there, or in the clause's own block `n + j`.",
    "mapEdge": "Relabel the endpoints of an edge.",
    "mapGraph": "Relabel the vertices of a graph.",
    "gadgetWidth": "The size of a vertex block: room for the largest gadget.",
    "clauseGraph": "The gadget of a placed clause: `ζ_(c,2)` for two literals, `ζ_(c,3)` otherwise.",
    "placedVariableGraph": "The variable gadget of variable `v`, placed in block `v`.",
    "placedClauseGraph": "The clause gadget of clause `j`, placed in block `n + j` with its literal edges glued to the variable ports.",
    "formulaGraph": "The graph `G` of Theorem 8: every variable gadget, then every clause gadget, glued at the literal ports.",
    "occurrences": "The number of occurrences of the variable `v` with the polarity `positive` in `f`.",
    "ClauseVariablesDistinct": "No variable occurs twice in one clause.",
    "tautological": "A clause containing a variable and its negation.",
    "GraphOutput": "The records `f` are valid and write the graph `g` and the budget `budget`.",
}


HEADER = """module

public import Init

/-!
# Cycle-path assignment: Theorem 11, Corollary 12 and the L-reductions of Appendix D

the accompanying paper "Cycle-Path Assignment". For every `k ≥ 5`: `CPAP(·, k)`
(`cpapProblem k`) is MaxSNP-hard and APX-hard and 3-OCCURRENCE MAX-3-SAT L-reduces to it
(Theorem 11); a PTAS for it gives `P = NP` (Corollary 12); the Theorem 8 graph and Lemma 10's
`polarize` give L-reductions with `C* = 2m − S*` (Appendix D); Theorem 8's construction runs in
`O(n)` time and space on a unit-cost RAM (`RAM.ComputesIn`); planar endpoint bits are computed from
a planar embedding in linear RAM time and in polynomial time. Copied verbatim, in order, from the
NP-completeness foundation `NPCompleteness-Lean4`, the Section 5 formalization, Max3SAT-MaxSNP-APX-Lean4
(`PEqNP` through `APXHard`) and `ApproximationHardness/`; generated by `scripts/generate_challenge.py`.
-/

@[expose] public section"""

TARGETS = """/-- **Theorem 11** (Appendix D): the Theorem 8 graph gives an L-reduction, `α = 5/3`, `β = 1`. -/
theorem cpap_lreduction {k : Nat} (hk : 5 ≤ k) :
    LReductionToCPAP LeOneLeTwoCNF (formulaGraph k) k 5 3 1 1 := by sorry
/-- `C* = 2m − S*` on Definition 7 instances. -/
theorem cpap_optimum {k : Nat} (hk : 5 ≤ k) {f : CNF} (hf : LeOneLeTwoCNF f) {S C : Nat}
    (hS : IsMaxSat f S) (hC : IsMinCost (formulaGraph k f) k C) : C + S = 2 * f.length := by sorry
/-- **Lemma 10**: `polarize` gives Definition 7 instances and an L-reduction, `α = β = 1`. -/
theorem leOneLeTwo_lreduction : (∀ f, ThreeOccurrence f → LeOneLeTwoCNF (polarize f)) ∧
    LReductionSat ThreeOccurrence polarize 1 1 1 1 := by sorry
/-- **Theorem 11 with Lemma 10**: the composition is an L-reduction, `α = 5/3`, `β = 1`. -/
theorem threeOccurrence_cpap_lreduction {k : Nat} (hk : 5 ≤ k) :
    LReductionToCPAP ThreeOccurrence (fun f => formulaGraph k (polarize f)) k 5 3 1 1 := by sorry
/-- **Theorem 8 in `O(n)` time and space on a unit-cost RAM**, with its correctness. -/
theorem gadget_reduction_linear_ram {k : Nat} (hk : 5 ≤ k) :
    ∃ (prog : RAM.Stmt) (C : Nat), ∀ f, LeOneLeTwoCNF f →
      ∃ (es : List (Nat × Nat)) (t : Nat),
        RAM.ComputesIn prog (RAM.ramInput f) (f.length :: RAM.edgeWord es) t (C * (variableBound f + 1)) ∧
        t ≤ C * (variableBound f + 1) ∧ formulaGraph k f = es.map (fun e => edge e.1 e.2) ∧
        (Satisfiable f ↔ HasAssignment (formulaGraph k f) k f.length) := by sorry
/-- **The planar gadget orientation in `O(N)` time and `O(N + n)` space on a unit-cost RAM**. -/
theorem orientation_linear_ram :
    ∃ (prog : RAM.Stmt) (C : Nat), ∀ f rot, BoundedOccurrence f → IsPlanarRotation f rot →
      ∃ out t, RAM.ComputesIn prog (RAM.ramInput f ++ rot) out t
          (C * ((RAM.ramInput f ++ rot).length + variableBound f + 1)) ∧
        t ≤ C * ((RAM.ramInput f ++ rot).length + 1) ∧
        ∀ k, Complexity.PlanarGraph (orientedFormulaGraph (choicesOfBits f (out.map fun x => x == 1)) k f) := by sorry
/-- **The planar gadget orientation in polynomial time** in the foundation's machine model. -/
theorem orientation_polyTime :
    ∃ g : Complexity.Word → Complexity.Word, Complexity.PolyTime g ∧
      ∀ f rot, BoundedOccurrence f → IsPlanarRotation f rot →
        ∀ k, Complexity.PlanarGraph (orientedFormulaGraph (choicesOfBits f (g (encode f ++ Sim.encodeRot rot))) k f) := by sorry"""


HARDNESS_TARGETS = """/-- **Theorem 11**: 3-OCCURRENCE MAX-3-SAT L-reduces to `CPAP(·, k)` (`LReducible`). -/
theorem max3SAT3_lReducible_cpap {k : Nat} (hk : 5 ≤ k) : LReducible max3SAT3 (cpapProblem k) := by sorry
/-- **Theorem 11**: for every `k ≥ 5`, `CPAP(·, k)` is MaxSNP-hard. -/
theorem cpap_maxSNPHard {k : Nat} (hk : 5 ≤ k) : MaxSNPHard (cpapProblem k) := by sorry
/-- **Theorem 11**: for every `k ≥ 5`, `CPAP(·, k)` is APX-hard. -/
theorem cpap_apxHard {k : Nat} (hk : 5 ≤ k) : APXHard (cpapProblem k) := by sorry
/-- **Corollary 12**: for every `k ≥ 5`, if `CPAP(·, k)` has a PTAS then `P = NP`. -/
theorem cpap_no_ptas {k : Nat} (hk : 5 ≤ k) (h : (cpapProblem k).HasPTAS) : PEqNP := by sorry
/-- **Corollary 12**, non-uniformly: approximations within every `1 + 1/(j+1)` give `P = NP`. -/
theorem cpap_not_approximable {k : Nat} (hk : 5 ≤ k)
    (h : ∀ j, (cpapProblem k).ApproximableWithin (j + 2) (j + 1)) : PEqNP := by sorry"""


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
        HEADER,
        "namespace Complexity",
        registered_machine(),
        library(FOUNDATION, "Complexity/Classes.lean", ["InP"]),
        "end Complexity",
        "namespace Complexity.SAT",
        library(FOUNDATION, "Complexity/SAT.lean", [
            "Word", "Assignment", "Literal", "Clause", "CNF", "evalLiteral", "evalClause", "evalCNF",
            "Satisfiable", "IsThreeCNF", "clauseBound", "variableBound", "writeNat", "writeValues", "writeList",
            "encodeLiteral", "encodeClause", "encode",
        ]),
        library(FOUNDATION, "Complexity/PlanarSAT.lean", ["incidenceGraph"]),
        "end Complexity.SAT",
        "namespace Complexity",
        library(FOUNDATION, "Complexity/Planarity.lean", ["iterate", "Hypermap", "cycleCount"]),
        "namespace Hypermap",
        library(FOUNDATION, "Complexity/Planarity.lean", [
            "linked", "componentCount", "eulerLhs", "eulerRhs", "genus", "Planar",
        ]),
        "end Hypermap",
        library(FOUNDATION, "Complexity/Planarity.lean", ["halfEdgeEnd", "PlanarGraph"]),
        "end Complexity",
        "namespace STACS2027\nopen Complexity.SAT",
        library(SECTION5, "NPHardness/FiniteCycles.lean", [
            "Edge", "Graph", "Cycle", "edge", "pathEdges", "cycleEdges", "IsCycle",
            "instance:IsCycle", "SameCycle", "instance:SameCycle", "selected", "overlap", "cost",
        ]),
        library(SECTION5, "NPHardness/CycleRepresentatives.lean", ["cycleRepresentatives"]),
        library(SECTION5, "NPHardness/Enumerate.lean", ["vertices", "neighbors", "walksFrom", "rawCycles", "cycles"]),
        library(SECTION5, "NPHardness/CostSearch.lean", ["selectedOptions", "ValidChoices"]),
        library(SECTION5, "NPHardness/CPAP.lean", ["HasAssignment"]),
        library(SECTION5, "NPHardness/Gadgets.lean", [
            "Link", "subdividedEdge", "realizeLinks", "variableLinks", "variableGraph", "clauseThreeLinks",
            "clauseThreeGraph", "orangeSubdivisions", "blueSubdivisions", "redSubdivisions", "clauseTwoLinks",
            "clauseTwoGraph",
        ]),
        library(SECTION5, "NPHardness/SubdivisionPrograms.lean", ["subdivisionCount"]),
        library(SECTION5, "NPHardness/OccurrencePorts.lean", [
            "PlacedLiteral", "placeLiterals", "placeFormula", "PlacedLiteral.port",
        ]),
        library(SECTION5, "NPHardness/VertexGluing.lean", [
            "blockVertex", "variableEndpoint", "clauseEndpoint", "clausePortAt", "attachmentAt", "clauseVertex",
        ]),
        library(SECTION5, "NPHardness/GraphRelabel.lean", ["mapEdge", "mapGraph"]),
        library(SECTION5, "NPHardness/GlobalGraph.lean", [
            "gadgetWidth", "clauseGraph", "placedVariableGraph", "placedClauseGraph", "formulaGraph",
        ]),
        "namespace Oriented",
        library(SECTION5, "NPHardness/OrientedVertexGluing.lean", ["Orientation"]),
        "variable [Orientation]",
        library(SECTION5, "NPHardness/OrientedVertexGluing.lean", ["orientSide", "clauseVertex"]),
        library(SECTION5, "NPHardness/OrientedGlobalGraph.lean", ["placedClauseGraph", "formulaGraph"]),
        "end Oriented",
        library(SECTION5, "NPHardness/OrientedGluing.lean", ["EndpointChoices", "orientedFormulaGraph"]),
        library(SECTION5, "NPHardness/BoundedSAT.lean", ["occurrences", "BoundedOccurrence"]),
        library(SECTION5, "NPHardness/ClauseRegions.lean", ["ClauseVariablesDistinct"]),
        library(SECTION5, "NPHardness/Preprocess.lean", ["tautological"]),
        library(SECTION5, "NPHardness/GraphEncoding.lean", [
            "validGraphRecord", "recordEdge", "instructionGraph", "instructionBudget", "ValidGraphInstructions",
        ]),
        library(ROOT, "ApproximationHardness/Optimization.lean", [
            "satisfiedCount", "IsMaxSat", "IsMinCost", "LReductionToCPAP", "LReductionSat",
        ]),
        library(ROOT, "ApproximationHardness/LReduction.lean", ["LeOneLeTwoCNF"]),
        library(ROOT, "ApproximationHardness/Polarize.lean", [
            "ThreeOccurrence", "pureThree", "pureValue", "deleted", "kept", "deletedCount", "complemented",
            "flipLiteral", "flipFormula", "padding", "polarize",
        ]),
        "namespace RAM",
        library(ROOT, "ApproximationHardness/RAM/Model.lean", [
            "Config", "Stmt", "Config.setReg", "Config.setMem", "Config.emit", "Exec", "initial", "Computes",
        ]),
        library(ROOT, "ApproximationHardness/RAM/Bounded.lean", ["ExecB", "ComputesIn"]),
        library(ROOT, "ApproximationHardness/RAM/Program.lean", ["signCode", "litCode", "clauseCode", "ramInput", "edgeWord"]),
        "end RAM",
        "namespace Sim",
        library(ROOT, "ApproximationHardness/Sim/ParsePaths.lean", ["encodeEdge", "encodePath", "encodePaths"]),
        library(ROOT, "ApproximationHardness/Sim/OrientRegistered.lean", ["encodeRot"]),
        "end Sim",
        "namespace PlanarAssembly\nopen Complexity",
        library(ROOT, "ApproximationHardness/Planar/ExplicitOrientation.lean", ["occList", "IsPlanarRotation", "choicesOfBits"]),
        "end PlanarAssembly",
        "open PlanarAssembly",
        TARGETS,
        "namespace Embed\nopen Complexity",
        library(ROOT, "ApproximationHardness/Embed/Computed.lean", ["PlanarEmbeddingLinearRAM"]),
        "/-- The uniform linear RAM embedding compiler from the formula alone. -/\ntheorem planarEmbedding_linear_ram : PlanarEmbeddingLinearRAM := by sorry",
        "end Embed",
        "end STACS2027",
        "namespace Complexity",
        library(PCP, "ComplexityExt/PCP/Defs.lean", ["PEqNP"]),
        "namespace SAT",
        library(PCP, "ComplexityExt/PCP/Defs.lean", ["satCount", "assignmentOf"]),
        "end SAT",
        library(PCP, "ComplexityExt/Approx/Defs.lean", ["OptProblem"]),
        "namespace OptProblem",
        library(PCP, "ComplexityExt/Approx/Defs.lean", [
            "IsOpt", "WithinRatio", "ApproxAlgorithm", "ApproximableWithin",
        ]),
        "end OptProblem",
        library(PCP, "ComplexityExt/Approx/Defs.lean", ["unary", "UniformPolyTime", "ComputableNat"]),
        "namespace OptProblem",
        library(PCP, "ComplexityExt/Approx/Defs.lean", ["HasPTAS"]),
        "end OptProblem",
        library(PCP, "ComplexityExt/Approx/Defs.lean", [
            "natBitsFuel", "natBits", "NPO", "absDiff", "LReducible", "QF", "Relations",
            "Relations.holds", "QF.eval", "tuples", "encodeRelations", "Relations.Fits",
            "QF.WellFormed", "maxSNP0", "InMaxSNP", "MaxSNPHard", "SAT.occurrences",
            "SAT.IsThreeOcc", "max3SAT3", "InAPX", "PTASReducible", "APXHard",
        ]),
        "end Complexity",
        "namespace STACS2027\nopen Complexity Complexity.SAT",
        library(ROOT, "ApproximationHardness/Hardness/Problem.lean", ["cpapProblem"]),
        HARDNESS_TARGETS,
        "end STACS2027",
    ]
    # Consecutive declaration blocks are joined without a blank line; namespace, `open`,
    # `variable` and `end` lines are set off by blank lines.
    def is_command(part: str) -> bool:
        return part.startswith(("namespace ", "end ", "open ", "variable ")) or part == HEADER
    text = ""
    previous = None
    for part in (p.strip() for p in parts):
        if previous is not None:
            text += "\n" if not is_command(part) and not is_command(previous) else "\n\n"
        text += part
        previous = part
    return "\n".join(line for line in compact_comments(text).splitlines() if line.strip()) + "\n"


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
        print("Generated Challenge.lean (independent statement; thirteen intentional theorem holes).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
