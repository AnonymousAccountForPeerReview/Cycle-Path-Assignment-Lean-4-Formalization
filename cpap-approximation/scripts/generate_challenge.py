#!/usr/bin/env python3
"""Generate the independent, Init-only Challenge.

The cycle-path assignment problem (`Edge` through `HasAssignment`) and the edge
load `load` are copied verbatim, with their documentation comments and in their
original order, from the Section 5 formalization of the same manuscript,
read from `NPHardness/` of the Lake dependency `cpap-np-hardness` (located through `lake-manifest.json`); the Solution imports that
library through the Lake dependency `cpap-np-hardness` (which requires the
NP-completeness foundation `NPCompleteness-Lean4`). Algorithm 1, the fractional
solutions, Algorithm 2 and the expectation of independent rounding are copied
from `Approximation/`. Each declaration is taken with the documentation comment that
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


# Lean shares, within one module, auxiliary `match` functions of the same shape. In
# the libraries, the declarations below live in modules other than those of the
# Section 5 declarations whose matchers have the same shape, and each has its own
# matcher; in this single-module Challenge they would reuse the earlier one and
# elaborate to a different term. The option below (which only disables code
# generation for the matcher) gives the copied declaration a fresh matcher with the
# library's name and value. Comparator checks the result.
FRESH_MATCHER = set()
FRESH_MATCHER_PREFIX = "set_option bootstrap.genMatcherCode false in\n"

# Documentation comments for the Section 5 declarations copied without one.
DOCS = {
    "load": "`l(e)`, the load of the edge `e`: the number of the paths `ps` containing it (each counted as often as it contains `e`).",
}


HEADER = """module

public import Init

/-!
# Approximation algorithms for cycle-path assignment: Lemma 13 and Theorems 14, 17, 18

For the cycle-path assignment problem `CPAP(G, k)` of the accompanying paper
"Cycle-Path Assignment", on the enumerated `k`-cycles of a graph `g` (`t` of them, each
giving a path of `k − 2` edges), the theorems at the end state:

* Algorithm 1, the greedy assignment (`greedy`, and every run `GreedyRun` of it with any
  tie-breaking), is a cycle-path assignment, and for every assignment `qs` (in particular an
  optimal one, of cost `OPT`): with `S = ∑_e l(e)²` the sum of squared loads of the greedy
  assignment and `S' = ∑_e l'(e)²` that of `qs`, `(S − S')² ≤ 4 S S'`, i.e.
  `S ≤ (3 + 2√2) S'` (Lemma 13); with `Q = (k − 2) t`, `A = 2 ALG + Q` and `B = 2 c(qs) + Q`,
  `(A − B)² ≤ 4 A B`, i.e. `ALG ≤ (3 + 2√2) OPT + (1 + √2)(k − 2) t` (Theorem 14); and in
  integers `2 ALG ≤ 12 OPT + 5 (k − 2) t`;
* for an optimal fractional solution `R` of the convex relaxation (given with a common
  denominator `D`: `OptimalFractional`), independent randomized rounding has expected cost
  `E[c(τ)] ≤ OPT + (k − 2) t / k`, stated as `k D^t E[c(τ)] ≤ D^t (k c(qs) + (k − 2) t)`
  with `expectedCost R = D^t E[c(τ)]` (Theorem 17);
* Algorithm 2, the derandomization by conditional expectation (`conditionalRounding`, and
  every run `RoundingRun` of it), is a cycle-path assignment of cost
  `c(τ) ≤ OPT + (k − 2) t / k`, stated as `k c(τ) ≤ k c(qs) + (k − 2) t` (Theorem 18).

The polynomial-time solvability of the relaxation (Lemma 16) and the running times of the
algorithms (Lemma 15 for Algorithm 1) are not formalized here. Numbers are those of the paper
of the manuscript.

* The cycle-path assignment problem (`Edge` through `HasAssignment`) and the edge load
  `load` are copied verbatim, with their order, from the formalization of Section 5 of the
  same manuscript (Lake dependency `cpap-np-hardness`); a documentation comment is added where
  that library has none. For fixed `k`, the simple `k`-cycles of a graph are enumerated once
  each, by edge set; an assignment chooses one vertex of each to omit, leaving a path of
  `k - 2` edges (`selectedOptions`); its cost is the number of edges shared by pairs of
  chosen paths, `∑_e binom(l(e), 2)` (Definition 1).
* `pathLoad ps p = ∑_{e ∈ p} l(e)` is the cost increase of adding `p`; `chooseMin` picks a
  minimizer; `greedy` is Algorithm 1 and `GreedyRun` its runs.
* A fractional solution lists, for each cycle, its options and their weights (numerators
  over `D`); `weightedSum` is `∑_P x_P f(P)` (times `D`); `optionLoad`, `fractionalLoad`
  and `meanLoad` are `D p_{C,e}`, `D λ_e` and `D μ_e`; `relaxationObjective` is `2 D²` times
  the objective `∑_e (λ_e² − λ_e)/2`; `OptimalFractional` compares it with every fractional
  solution of the same instance after clearing denominators; `rounded` is `D^{|R|}` times the
  expectation over the product distribution.

Only Lean core is imported. `scripts/generate_challenge.py` generates this file
from the two libraries; `Solution.lean` proves the theorems without importing it.
-/

@[expose] public section"""

TARGETS = """/-- **Algorithm 1** on the `k`-cycles of `g` is a run of Algorithm 1, and every run of
Algorithm 1 (any tie-breaking) is a cycle-path assignment. -/
theorem greedy_is_assignment (g : Graph) (k : Nat) :
    GreedyRun [] ((cycles g k).map selectedOptions) (greedy ((cycles g k).map selectedOptions)) ∧
      ∀ ps, GreedyRun [] ((cycles g k).map selectedOptions) ps →
        ValidChoices ((cycles g k).map selectedOptions) ps := by sorry

/-- **Lemma 13.** For a run `ps` of Algorithm 1 on the `k`-cycles of `g` and any assignment
`qs`, with `S = ∑_e l(e)²` and `S' = ∑_e l'(e)²`: `(S − S')² ≤ 4 S S'`, i.e.
`S ≤ (3 + 2√2) S'`. -/
theorem greedy_sq_load_bound {g : Graph} {k : Nat} (hg : g.Nodup) {ps qs : List (List Edge)}
    (hrun : GreedyRun [] ((cycles g k).map selectedOptions) ps)
    (hq : ValidChoices ((cycles g k).map selectedOptions) qs) :
    ((g.map fun e => load ps e * load ps e).sum - (g.map fun e => load qs e * load qs e).sum) *
      ((g.map fun e => load ps e * load ps e).sum - (g.map fun e => load qs e * load qs e).sum) ≤
    4 * ((g.map fun e => load ps e * load ps e).sum * (g.map fun e => load qs e * load qs e).sum) := by
  sorry

/-- **Theorem 14.** With `Q = (k − 2) t` the total load, `A = 2 ALG + Q` and `B = 2 c(qs) + Q`:
`(A − B)² ≤ 4 A B`, i.e. `A ≤ (3 + 2√2) B`, which rearranges to
`ALG ≤ (3 + 2√2) c(qs) + (1 + √2)(k − 2) t`; with `qs` optimal, `c(qs) = OPT`. -/
theorem greedy_cost_bound {g : Graph} {k : Nat} (hg : g.Nodup) {ps qs : List (List Edge)}
    (hrun : GreedyRun [] ((cycles g k).map selectedOptions) ps)
    (hq : ValidChoices ((cycles g k).map selectedOptions) qs) :
    (2 * cost ps + (k - 2) * (cycles g k).length - (2 * cost qs + (k - 2) * (cycles g k).length)) *
      (2 * cost ps + (k - 2) * (cycles g k).length - (2 * cost qs + (k - 2) * (cycles g k).length)) ≤
    4 * ((2 * cost ps + (k - 2) * (cycles g k).length) *
      (2 * cost qs + (k - 2) * (cycles g k).length)) := by
  sorry

/-- Theorem 14 in integers: `2 ALG ≤ 12 c(qs) + 5 (k − 2) t` (as `3 + 2√2 < 6`). -/
theorem greedy_cost_integer_bound {g : Graph} {k : Nat} (hg : g.Nodup) {ps qs : List (List Edge)}
    (hrun : GreedyRun [] ((cycles g k).map selectedOptions) ps)
    (hq : ValidChoices ((cycles g k).map selectedOptions) qs) :
    2 * cost ps ≤ 12 * cost qs + 5 * ((k - 2) * (cycles g k).length) := by
  sorry

/-- **Algorithm 2** on a fractional solution for the `k`-cycles of `g` is a run of Algorithm 2,
and every run of Algorithm 2 (any tie-breaking) is a cycle-path assignment. -/
theorem rounding_is_assignment {g : Graph} {k : Nat} (D : Nat)
    {R : List (List (List Edge) × List Nat)}
    (hR : R.map Prod.fst = (cycles g k).map selectedOptions) :
    RoundingRun D [] R (conditionalRounding D R) ∧
      ∀ ps, RoundingRun D [] R ps → ValidChoices ((cycles g k).map selectedOptions) ps := by
  sorry

/-- **Theorem 17.** Independent randomized rounding of an optimal fractional solution has
expected cost at most `c(qs) + (k − 2) t / k` for every assignment `qs`: with
`expectedCost R = D^t E[c(τ)]`, `k D^t E[c(τ)] ≤ D^t (k c(qs) + (k − 2) t)`. -/
theorem randomized_rounding_cost_bound {g : Graph} {k D : Nat} (hg : g.Nodup)
    {R : List (List (List Edge) × List Nat)}
    (hR : R.map Prod.fst = (cycles g k).map selectedOptions) (hopt : OptimalFractional g D R)
    {qs : List (List Edge)} (hq : ValidChoices ((cycles g k).map selectedOptions) qs) :
    k * expectedCost R ≤
      D ^ (cycles g k).length * (k * cost qs + (k - 2) * (cycles g k).length) := by
  sorry

/-- **Theorem 18.** A run `ps` of Algorithm 2 on an optimal fractional solution of the
relaxation for the `k`-cycles of `g` has cost at most `c(qs) + (k − 2) t / k` for every
assignment `qs`: `k c(ps) ≤ k c(qs) + (k − 2) t`; with `qs` optimal, `c(ps) ≤ OPT + (k − 2) t / k`. -/
theorem conditional_rounding_cost_bound {g : Graph} {k D : Nat} (hg : g.Nodup)
    {R : List (List (List Edge) × List Nat)}
    (hR : R.map Prod.fst = (cycles g k).map selectedOptions) (hopt : OptimalFractional g D R)
    {ps qs : List (List Edge)} (hrun : RoundingRun D [] R ps)
    (hq : ValidChoices ((cycles g k).map selectedOptions) qs) :
    k * cost ps ≤ k * cost qs + (k - 2) * (cycles g k).length := by
  sorry"""


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
        library(SECTION5, "NPHardness/LoadCost.lean", ["load"]),
        library(ROOT, "Approximation/Loads.lean", ["pathLoad"]),
        library(ROOT, "Approximation/Greedy.lean", ["chooseMin", "greedyFrom", "greedy", "GreedyRun"]),
        library(ROOT, "Approximation/Weighted.lean", ["weightedSum"]),
        library(ROOT, "Approximation/Rounding.lean", [
            "optionLoad", "fractionalLoad", "meanLoad", "meanLoadSum", "roundFrom", "conditionalRounding",
            "RoundingRun", "rounded", "expectedCost", "FractionalSolution", "relaxationObjective",
            "OptimalFractional",
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
        print("Generated Challenge.lean (independent statement; seven intentional theorem holes).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
