#!/usr/bin/env python3
"""Generate the independent, Init-only Challenge.

The CNF formulas (`Assignment` through `Satisfiable`) are copied verbatim, with
their documentation comments and in their original order, from the NP-completeness
foundation `NPCompleteness-Lean4`, read from
`Complexity/SAT.lean` of the Lake dependency `np-completeness` (located through `lake-manifest.json`). The cycle-path assignment
problem (`Edge` through `HasAssignment`) is copied the same way from the pinned
Section 5 formalization of the same manuscript, read from
`NPHardness/` of the Lake dependency `cpap-np-hardness` (located through `lake-manifest.json`), whose Challenge states that problem
for its NP-hardness results; the Solution imports both libraries
through the Lake dependencies `np-completeness` and `cpap-np-hardness`.
The 2-CNF encodings of Theorem 4 and Corollary 5 are copied from
`BoundedCost/Encoding.lean`, and the steps of Algorithm 3 from
`BoundedCost/Algorithm3Recovery.lean`, `BoundedCost/Algorithm3Core.lean` and
`BoundedCost/Algorithm3Search.lean`. Each declaration is taken with the documentation
comment that immediately precedes it, so the Challenge and the libraries share
docstrings. Other comments are dropped.

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
    undocumented = [k for k in keys if not index[k][1].startswith("/--")]
    if undocumented:
        raise ValueError(f"Undocumented declarations in {where}: {', '.join(undocumented)}")
    return "\n\n".join(index[k][1] for k in keys)


def library(base: Path, path: str, keys: list[str]) -> str:
    return select((base / path).read_text(encoding="utf-8"), keys, path)


HEADER = """module

public import Init

/-!
# The bounded-cost FPT algorithm for cycle-path assignment: encodings and Algorithm 3

For the cycle-path assignment problem `CPAP(G, k)` of the accompanying paper
"Cycle-Path Assignment", the theorems at the end state, for every `k ≥ 4`, that the
encodings of Section 4 and Appendix B are correct and have the claimed sizes, and that
the steps of Algorithm 3 are correct:

* Almost 2-SAT accepts `(Γ', Ψ)` — deleting at most `Ψ` clause occurrences from the
  replicated formula `Γ'` leaves a satisfiable formula — iff `G` has an assignment of
  cost at most `Ψ` (Theorem 4); every clause of `Γ'` has two literals on the `kt`
  variables `b_{C,e}`, `Γ₁` has exactly `k(k−3)t/2` path constraints, there are at most
  `kt(t−1)/2` candidate overlaps, and `Γ'` has `(Ψ+1)|Γ₁| + |𝒰|` clause occurrences.
* The zero-cost formula — `Γ₁` with the prefix encoding of "at most one cycle keeps
  `e`" — is satisfiable iff `G` has an assignment of cost `0` (Corollary 5); it is a
  2-CNF on fewer than `2kt` variables with at most `|Γ₁| + 3kt` clauses.
* Algorithm 3: restricting `G` to its `k`-cycle core (the edges on simple `k`-cycles)
  changes neither the enumerated cycles nor the assignments; the overlaps `𝓘` whose
  constraints a solution of Almost 2-SAT deletes number at most `Ψ`, and `Γ_𝓘` stays
  satisfiable; the last loop (marked edges `W_C`, a vertex `ρ(C)` with
  `W_C ⊆ E(C, ρ(C))`, the path `τ(C) = E(C) \\ E(C, ρ(C))`) turns every solution of `Γ_𝓘`
  into an assignment of cost at most `|𝓘|`, and every solution of the zero-cost formula
  into one of cost `0`; for `Ψ = 0`, 2-SAT on `Γ_∅` suffices.
* Computing `OPT` by increasing `Ψ`: the test is monotone in `Ψ` and eventually
  succeeds, the first `Ψ` it accepts is `OPT`, and the search `searchOptimum`, run with
  any correct decision procedure for the test, returns `OPT`.

The running times of the cited Almost 2-SAT and 2-SAT algorithms, and of cycle
enumeration, are not formalized; their outputs are quantified over.

* Formulas are those of the NP-completeness foundation `NPCompleteness-Lean4`
  (`Complexity.SAT`: `Assignment` through `Satisfiable`), copied verbatim.
* The cycle-path assignment problem (`Edge` through `HasAssignment`) is copied
  verbatim, with its order, from the formalization of Section 5 of the same
  manuscript (Lake dependency `cpap-np-hardness`), whose Challenge states it for
  the NP-hardness results of that section. For fixed `k`, the simple `k`-cycles
  of a graph are enumerated once each, by edge set; an assignment chooses one
  vertex of each to omit, leaving a path of `k - 2` edges; its cost is the number
  of edges shared by pairs of chosen paths, `∑_e binom(l(e), 2)` (Definition 1).
* The variable `b_{C_i,e}` of the edge at position `j` of the `i`-th cycle is the
  number `i·k + j`. `Γ₁` forbids marking two vertex-disjoint edges of a cycle; the
  overlap constraint `λ_u` of a candidate overlap `u = (i, i', e)` requires one of
  the two paths to omit `e`; `Γ_𝓘` keeps the `λ_u` outside `𝓘`; `Γ'` repeats `Γ₁`
  `Ψ + 1` times and adds every `λ_u`. The zero-cost formula replaces the `λ_u` of
  each edge `e` on cycles `C_1, …, C_p` by the prefix clauses on the auxiliary
  variables `s_{e,1}, …, s_{e,p−1}`, numbered from `kt` on.

Only Lean core is imported. `scripts/generate_challenge.py` generates this file
from the three libraries; `Solution.lean` proves the theorems without importing it.
-/

@[expose] public section"""

TARGETS = """/-- **Theorem 4**, the encoding: Almost 2-SAT accepts `(Γ', Ψ)` iff `CPAP(G, k)` has an
assignment of cost at most `Ψ`, for every `k ≥ 4`. -/
theorem almostSatisfiable_iff_hasAssignment {k : Nat} (hk : 4 ≤ k) (g : Graph) (Ψ : Nat) :
    AlmostSatisfiable (almostFormula g k Ψ) Ψ ↔ HasAssignment g k Ψ := by sorry

/-- The size of `Γ'`: a 2-CNF on the `kt` variables `b_{C,e}`, with `k(k−3)t/2` path
constraints, at most `kt(t−1)/2` candidate overlaps and `(Ψ+1)|Γ₁| + |𝒰|` clause occurrences,
`t` being the number of simple `k`-cycles. -/
theorem almostFormula_size (g : Graph) (k Ψ : Nat) :
    (∀ cl ∈ almostFormula g k Ψ, cl.length = 2 ∧ ∀ l ∈ cl, l.var < k * (cycles g k).length) ∧
    2 * (pathConstraints g k).length = k * (k - 3) * (cycles g k).length ∧
    2 * (candidateOverlaps g k).length ≤ k * (cycles g k).length * ((cycles g k).length - 1) ∧
    (almostFormula g k Ψ).length =
      (Ψ + 1) * (pathConstraints g k).length + (candidateOverlaps g k).length := by sorry

/-- **Corollary 5**, the encoding: the zero-cost formula is satisfiable iff `CPAP(G, k)` has
an assignment of cost `0`, for every `k ≥ 4`. -/
theorem zeroCostFormula_satisfiable_iff {k : Nat} (hk : 4 ≤ k) (g : Graph) :
    Satisfiable (zeroCostFormula g k) ↔ HasAssignment g k 0 := by sorry

/-- The size of the zero-cost formula: a 2-CNF on fewer than `2kt` variables with at most
`|Γ₁| + 3kt` clauses, where `2|Γ₁| = k(k−3)t`. -/
theorem zeroCostFormula_size (g : Graph) (k : Nat) :
    (∀ cl ∈ zeroCostFormula g k, cl.length = 2 ∧ ∀ l ∈ cl, l.var < 2 * (k * (cycles g k).length)) ∧
    (zeroCostFormula g k).length ≤ (pathConstraints g k).length + 3 * (k * (cycles g k).length) ∧
    2 * (pathConstraints g k).length = k * (k - 3) * (cycles g k).length := by sorry

/-- The exact clause count of the prefix encoding added in the paper:
an edge in `p ≥ 2` cycles has exactly `3p − 4` clause occurrences. -/
theorem prefixClauses_length (g : Graph) (k : Nat) (e : Edge)
    (hp : 2 ≤ (cyclesThrough g k e).length) :
    (prefixClauses g k e).length = 3 * (cyclesThrough g k e).length - 4 := by sorry

/-- The auxiliary variables of an edge in `p` cycles are distinct and number
exactly `p − 1`; zero variables are used when `p ≤ 1`. -/
theorem prefixAuxiliaryVariables_count (g : Graph) (k : Nat) (e : Edge) :
    let vars := (List.range ((cyclesThrough g k e).length - 1)).map (prefixVariable g k e)
    vars.length = (cyclesThrough g k e).length - 1 ∧ vars.Nodup := by sorry

/-- The `k`-cycle core: its edges are exactly the edges on simple `k`-cycles of `g`. -/
theorem mem_kCycleCore_iff (g : Graph) (k : Nat) (e : Edge) :
    e ∈ kCycleCore g k ↔ ∃ c, IsCycle g k c ∧ e ∈ cycleEdges c := by sorry

/-- The `k`-cycle core: its vertices are exactly the vertices on simple `k`-cycles of `g`. -/
theorem mem_vertices_kCycleCore_iff (g : Graph) (k v : Nat) :
    v ∈ vertices (kCycleCore g k) ↔ ∃ c, IsCycle g k c ∧ v ∈ c := by sorry

/-- The core has the same simple `k`-cycles as `g`. -/
theorem isCycle_kCycleCore_iff (g : Graph) (k : Nat) (c : Cycle) :
    IsCycle (kCycleCore g k) k c ↔ IsCycle g k c := by sorry

/-- Restricting to the core changes neither the enumerated simple `k`-cycles nor their order. -/
theorem cycles_kCycleCore (g : Graph) (k : Nat) : cycles (kCycleCore g k) k = cycles g k := by sorry

/-- Restricting to the core changes neither the assignments nor their costs. -/
theorem hasAssignment_kCycleCore_iff (g : Graph) (k B : Nat) :
    HasAssignment (kCycleCore g k) k B ↔ HasAssignment g k B := by sorry

/-- **Algorithm 3, the permitted overlaps**: if Almost 2-SAT keeps the clauses `kept` of `Γ'`,
deleting at most `Ψ` occurrences, the overlaps `𝓘` whose constraint it deletes number at most
`Ψ`, and every truth assignment satisfying `kept` satisfies `Γ_𝓘`. -/
theorem deletedOverlaps_spec (g : Graph) (k Ψ : Nat) (kept : CNF)
    (hsub : kept.Sublist (almostFormula g k Ψ))
    (hlen : (almostFormula g k Ψ).length ≤ kept.length + Ψ) :
    (deletedOverlaps g k kept).length ≤ Ψ ∧
      ∀ σ : Assignment, evalCNF σ kept = true →
        evalCNF σ (permittedFormula g k (deletedOverlaps g k kept)) = true := by sorry

/-- **Algorithm 3, the recovery loop**: if `σ` satisfies `Γ₁` (and `k ≥ 4`), then for every
cycle `C = C_i` the chosen `ρ(C)` is a vertex of `C` with `W_C ⊆ E(C, ρ(C))`, and the recovered
path is `τ(C) = E(C) \\ E(C, ρ(C))`. -/
theorem recoveredPath_spec {k : Nat} (hk : 4 ≤ k) (g : Graph) (σ : Assignment)
    (hσ : evalCNF σ (pathConstraints g k) = true) {i : Nat} (hi : i < (cycles g k).length) :
    omittedVertex g k σ i ∈ kCycle g k i ∧
      (∀ e ∈ markedEdges g k σ i, incident (omittedVertex g k σ i) e = true) ∧
      ∀ e, e ∈ recoveredPath g k σ i ↔
        e ∈ cycleEdges (kCycle g k i) ∧ incident (omittedVertex g k σ i) e = false := by sorry

/-- **Algorithm 3, path recovery**: from any truth assignment satisfying `Γ_𝓘`, the recovered
paths form a cycle-path assignment of cost at most `|𝓘|` (for `k ≥ 4`). -/
theorem recoverAssignment_correct {k : Nat} (hk : 4 ≤ k) (g : Graph)
    (permitted : List (Nat × Nat × Edge)) (σ : Assignment)
    (hσ : evalCNF σ (permittedFormula g k permitted) = true) :
    ValidChoices ((cycles g k).map selectedOptions) (recoverAssignment g k σ) ∧
      cost (recoverAssignment g k σ) ≤ permitted.length := by sorry

/-- **Corollary 5, path recovery**: from a truth assignment satisfying the zero-cost formula,
the recovery loop gives a cycle-path assignment of cost `0` (for `k ≥ 4`). -/
theorem recoverAssignment_zeroCost {k : Nat} (hk : 4 ≤ k) (g : Graph) (σ : Assignment)
    (hσ : evalCNF σ (zeroCostFormula g k) = true) :
    ValidChoices ((cycles g k).map selectedOptions) (recoverAssignment g k σ) ∧
      cost (recoverAssignment g k σ) = 0 := by sorry

/-- **Algorithm 3, the case `Ψ = 0`**: 2-SAT on `Γ_∅` suffices; it is satisfiable iff an
assignment of cost `0` exists (for `k ≥ 4`). -/
theorem permittedFormula_nil_satisfiable_iff {k : Nat} (hk : 4 ≤ k) (g : Graph) :
    Satisfiable (permittedFormula g k []) ↔ HasAssignment g k 0 := by sorry

/-- **Algorithm 3**, correctness (for `k ≥ 4`), run on the `k`-cycle core: for a solution of
Almost 2-SAT on `(Γ', Ψ)`, at most `Ψ` overlaps are deleted, `Γ_𝓘` is satisfiable and every
solution of it is recovered into an assignment of `g` of cost at most `Ψ`; if Almost 2-SAT
fails, there is no such assignment; for `Ψ = 0`, the same with 2-SAT on `Γ_∅`. -/
theorem algorithm3_correct {k : Nat} (hk : 4 ≤ k) (g : Graph) (Ψ : Nat) :
    (∀ kept : CNF, kept.Sublist (almostFormula (kCycleCore g k) k Ψ) →
      (almostFormula (kCycleCore g k) k Ψ).length ≤ kept.length + Ψ → Satisfiable kept →
        (deletedOverlaps (kCycleCore g k) k kept).length ≤ Ψ ∧
        Satisfiable (permittedFormula (kCycleCore g k) k (deletedOverlaps (kCycleCore g k) k kept)) ∧
        ∀ σ : Assignment,
          evalCNF σ (permittedFormula (kCycleCore g k) k (deletedOverlaps (kCycleCore g k) k kept)) = true →
            ValidChoices ((cycles g k).map selectedOptions) (recoverAssignment (kCycleCore g k) k σ) ∧
            cost (recoverAssignment (kCycleCore g k) k σ) ≤ Ψ) ∧
    (¬ AlmostSatisfiable (almostFormula (kCycleCore g k) k Ψ) Ψ → ¬ HasAssignment g k Ψ) ∧
    (∀ σ : Assignment, evalCNF σ (permittedFormula (kCycleCore g k) k []) = true →
      ValidChoices ((cycles g k).map selectedOptions) (recoverAssignment (kCycleCore g k) k σ) ∧
      cost (recoverAssignment (kCycleCore g k) k σ) = 0) ∧
    (¬ Satisfiable (permittedFormula (kCycleCore g k) k []) → ¬ HasAssignment g k 0) := by sorry

/-- The test of Algorithm 3 is monotone in `Ψ` (for `k ≥ 4`). -/
theorem almostSatisfiable_mono {k : Nat} (hk : 4 ≤ k) (g : Graph) {Ψ Ψ' : Nat} (h : Ψ ≤ Ψ') :
    AlmostSatisfiable (almostFormula g k Ψ) Ψ → AlmostSatisfiable (almostFormula g k Ψ') Ψ' := by sorry

/-- The search by increasing `Ψ` terminates: Almost 2-SAT accepts `(Γ', Ψ)` for some `Ψ` (for
`k ≥ 4`). -/
theorem exists_almostSatisfiable {k : Nat} (hk : 4 ≤ k) (g : Graph) :
    ∃ Ψ, AlmostSatisfiable (almostFormula g k Ψ) Ψ := by sorry

/-- **Computing `OPT` by increasing `Ψ`**: the first `Ψ` for which Almost 2-SAT accepts
`(Γ', Ψ)` is `OPT` (for `k ≥ 4`). -/
theorem isOptimalCost_iff_least_accepted {k : Nat} (hk : 4 ≤ k) (g : Graph) (Ψ : Nat) :
    IsOptimalCost g k Ψ ↔
      AlmostSatisfiable (almostFormula g k Ψ) Ψ ∧
        ∀ Ψ', Ψ' < Ψ → ¬ AlmostSatisfiable (almostFormula g k Ψ') Ψ' := by sorry

/-- **Computing `OPT` by increasing `Ψ`**: with any decision procedure `test` for the test of
Algorithm 3, the search over `Ψ = 0, 1, 2, …` stops and returns `OPT` (for `k ≥ 4`). -/
theorem searchOptimum_correct {k : Nat} (hk : 4 ≤ k) (g : Graph) (test : Nat → Bool)
    (htest : ∀ Ψ, test Ψ = true ↔ AlmostSatisfiable (almostFormula g k Ψ) Ψ) :
    (searchOptimum g k test).isSome = true ∧
      ∀ C, searchOptimum g k test = some C ↔ IsOptimalCost g k C := by sorry"""


def challenge_text() -> str:
    parts = [
        HEADER,
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
        library(SECTION5, "NPHardness/CycleRepresentatives.lean", ["cycleRepresentatives"]),
        library(SECTION5, "NPHardness/Enumerate.lean", ["vertices", "neighbors", "walksFrom", "rawCycles", "cycles"]),
        library(SECTION5, "NPHardness/CostSearch.lean", ["selectedOptions", "ValidChoices"]),
        library(SECTION5, "NPHardness/CPAP.lean", ["HasAssignment"]),
        library(ROOT, "BoundedCost/Encoding.lean", [
            "kCycle", "pathVariable", "cycleEdgeAt", "edgePosition", "edgeVariable", "disjointEdges",
            "pathConstraints", "candidateOverlaps", "overlapClause", "permittedFormula", "almostFormula",
            "AlmostSatisfiable", "edgesOnCycles", "cyclesThrough", "prefixOffset", "prefixVariable",
            "prefixClauses", "zeroCostFormula",
        ]),
        library(ROOT, "BoundedCost/Algorithm3Core.lean", ["kCycleCore"]),
        library(ROOT, "BoundedCost/Algorithm3Recovery.lean", [
            "markedEdges", "incident", "omittedPosition", "omittedVertex", "recoveredPath",
            "recoverAssignment", "deletedOverlaps",
        ]),
        library(ROOT, "BoundedCost/Algorithm3Search.lean", ["IsOptimalCost", "firstOptionCost", "searchOptimum"]),
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
        holes = len(re.findall(r"\bsorry\b", text))
        print(f"Generated Challenge.lean (independent statement; {holes} intentional theorem holes, "
              f"{len(text.splitlines())} lines).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
