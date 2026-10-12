#!/usr/bin/env python3
"""Generate the independent, Init-only Challenge (PCP theorem, MaxSNP, APX).

This is a layout-aware extractor for the named declarations in this project,
not a general Lean parser or a replacement for the official Comparator.
Each declaration is copied with the documentation comment that immediately
precedes it in the source, so the Challenge and the library share docstrings.
Other comments are dropped. `--check` detects drift without changing a file.
In particular, keep `step` before `run`: Lean reuses its generated matcher when
elaborating `run`, and the independent statement must reproduce those
auxiliary declaration names too.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]


def without_comments(source: str) -> str:
    """Remove nested Lean comments, preserving newlines and quoted strings."""
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
    r"^(?:@\[[^\n]*\]\s*)?(?:(?:public|private|protected|noncomputable|unsafe)\s+)*"
    r"(?:def|abbrev|structure|inductive|theorem|lemma|instance|namespace|end|"
    r"section|open|set_option|attribute|notation|macro|syntax|example|mutual)\b",
    re.M,
)
DECLARATION = re.compile(
    r"(?:@\[[^\n]*\]\s*)?(?:(?:public|private|protected|noncomputable|unsafe)\s+)*"
    r"(?:def|abbrev|structure|inductive)\s+([\w'.]+)\b"
)


DOCSTRING_BEFORE = re.compile(r"/--(?:(?!-/).)*-/\s*\Z", re.S)


def docstring_before(original: str, start: int) -> str:
    """The documentation comment ending just before offset `start`, if any."""
    match = DOCSTRING_BEFORE.search(original, 0, start)
    return match.group(0).rstrip() + "\n" if match else ""


DERIVING = re.compile(r"\n[ \t]*deriving [^\n]*")


def declarations(path: str, names: list[str], sep: str = "\n\n") -> str:
    original = (ROOT / path).read_text(encoding="utf-8")
    # `without_comments` preserves offsets, so positions agree with `original`.
    source = without_comments(original)
    starts = [match.start() for match in BOUNDARY.finditer(source)]
    found: dict[str, str] = {}
    for start, end in zip(starts, starts[1:] + [len(source)]):
        chunk = source[start:end].strip()
        match = DECLARATION.match(chunk)
        if match is None:
            continue
        name = match.group(1)
        if name in found:
            raise ValueError(f"Ambiguous declaration {name!r} in {path}")
        # Remove trailing whitespace left by erased comments.
        body = "\n".join(line.rstrip() for line in chunk.splitlines()).strip()
        # `deriving` clauses only add instances, which the theorems do not mention.
        body = DERIVING.sub("", body)
        found[name] = docstring_before(original, start) + body
    missing = [name for name in names if name not in found]
    if missing:
        raise ValueError(f"Missing declarations in {path}: {', '.join(missing)}")
    return sep.join(found[name] for name in names)


HEADER = open(ROOT / 'scripts' / 'challenge_header.txt', encoding='utf-8').read()
THEOREMS = open(ROOT / 'scripts' / 'challenge_theorems.txt', encoding='utf-8').read()


def challenge_text() -> str:
    machine = "Complexity/Machine.lean"
    classes = "Complexity/Classes.lean"
    sat = "Complexity/SAT.lean"
    pcp = "Complexity/PCP/Defs.lean"
    approx = "Complexity/Approx/Defs.lean"
    pair = "\n"
    parts = [
        HEADER,
        declarations(machine, ["Symbol", "Move", "Tape"]),
        "namespace Tape",
        declarations(machine, ["read", "write", "move", "ofInput", "bits", "output"]),
        "end Tape",
        declarations(machine, [
            "Instruction", "Machine", "Config", "initial", "step", "run", "runInput",
        ]),
        declarations(classes, ["Word", "Language"], pair),
        declarations(classes, [
            "powerBound", "pairWords", "Accepts", "PolynomialTimeMachine", "PolyTime", "InP",
            "InNP",
        ]),
        "end Complexity\n\nnamespace Complexity.SAT",
        declarations(sat, ["Word", "Assignment"], pair),
        declarations(sat, ["Literal"]),
        declarations(sat, ["Clause", "CNF"], pair),
        declarations(sat, [
            "evalLiteral", "evalClause", "evalCNF", "Satisfiable", "IsThreeCNF",
            "writeNat", "writeValues", "writeList", "encodeLiteral",
        ]),
        declarations(sat, ["encodeClause", "encode"], pair),
        "end Complexity.SAT\n\nnamespace Complexity",
        "/-! ## Probabilistically checkable proofs -/",
        declarations(pcp, ["PEqNP"]),
        "namespace SAT",
        declarations(pcp, ["satCount", "assignmentOf"]),
        "end SAT",
        declarations(pcp, ["allWords", "QueriesAtMost", "InPCP", "GapReduction"]),
        "/-! ## Optimization problems and approximation -/",
        declarations(approx, ["OptProblem"]),
        "namespace OptProblem",
        declarations(approx, ["IsOpt", "WithinRatio", "ApproxAlgorithm", "ApproximableWithin"]),
        "end OptProblem",
        declarations(approx, ["unary", "UniformPolyTime", "ComputableNat"]),
        "namespace OptProblem",
        declarations(approx, ["HasPTAS"]),
        "end OptProblem",
        "/-! ## NPO -/",
        declarations(approx, ["natBitsFuel", "natBits", "NPO"]),
        "/-! ## L-reductions and MaxSNP -/",
        declarations(approx, [
            "absDiff", "LReducible", "QF", "Relations", "Relations.holds", "QF.eval", "tuples",
            "encodeRelations", "Relations.Fits", "QF.WellFormed", "maxSNP0", "InMaxSNP",
            "MaxSNPHard", "MaxSNPComplete",
        ]),
        "/-! ## MAX-3-SAT and 3-OCCURRENCE MAX-3-SAT -/",
        declarations(approx, [
            "max3SAT", "SAT.occurrences", "SAT.IsThreeOcc", "max3SAT3",
        ]),
        "/-! ## APX and PTAS-reductions -/",
        declarations(approx, ["InAPX", "PTASReducible", "APXHard", "APXComplete"]),
        THEOREMS,
    ]
    return "\n\n".join(part.strip() for part in parts) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if Challenge.lean needs regeneration")
    args = parser.parse_args()
    text = challenge_text()
    destination = ROOT / "Challenge.lean"
    if args.check:
        if not destination.exists() or destination.read_text(encoding="utf-8") != text:
            print("Challenge.lean differs from its source declarations; regenerate it.", file=sys.stderr)
            return 1
        print("Challenge.lean matches its selected source declarations.")
    else:
        destination.write_text(text, encoding="utf-8")
        print("Generated Challenge.lean (independent statement; one intentional hole per theorem).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
