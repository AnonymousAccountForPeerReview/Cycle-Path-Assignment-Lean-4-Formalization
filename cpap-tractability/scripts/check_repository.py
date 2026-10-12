#!/usr/bin/env python3
"""Static checks of the repository, to run after `lake build`.

1. The NP-completeness foundation is required at its pinned commit and the sibling
   formalizations of this repository by path (`scripts/dependencies.py` locates them),
   in lakefile.toml and lake-manifest.json, and no copy of any is vendored.
2. Challenge.lean is up to date with its sources and imports only `Init`.
3. comparator.json and formalization.yaml name the same compared theorems.
4. TractabilityAudit has exactly one axiom guard for every named declaration in
   Tractability/, imports every guard module, and names only standard axioms.
5. Every Lean source starts with `module` and is at most 10,000 lines.

Proof checking is done by `lake build` and `lake comparator`, not here.
"""
from __future__ import annotations

import json
from pathlib import Path
import re
import subprocess
import sys

from generate_challenge import without_comments
from dependencies import dependency_dir
from lean_declarations import library_declarations

ROOT = Path(__file__).resolve().parents[1]
LIBRARY = "Tractability"
AUDIT = "TractabilityAudit"
# The foundation is NPCompleteness-Lean4 on GitHub; its owner is not checked (the published
# repository may use a mirror).
FOUNDATION_URL_RE = r"https://github\.com/[\w.-]+/NPCompleteness-Lean4(?:\.git)?"
FOUNDATION_REV = "3e603e795b44fedcf7d6dd65b7d1e30547ead925"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def fail(message: str) -> None:
    raise SystemExit(f"check_repository: {message}")


def check_pin() -> None:
    lakefile = (ROOT / "lakefile.toml").read_text()
    foundation = re.search(r'name = "np-completeness"\s*\ngit = "([^"]*)"\s*\nrev = "([^"]*)"', lakefile)
    if (not foundation or not re.fullmatch(FOUNDATION_URL_RE, foundation.group(1))
            or foundation.group(2) != FOUNDATION_REV):
        fail("lakefile.toml does not require the NP-completeness foundation at its pinned commit")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    packages = {p["name"].strip("«»"): p for p in manifest["packages"]}
    p = packages.get("np-completeness")
    if not p or p.get("url") != foundation.group(1) or p.get("rev") != FOUNDATION_REV:
        fail("lake-manifest.json does not pin np-completeness to the required commit")
    for name, library in {'cpap-np-hardness': 'NPHardness'}.items():
        path = re.search(rf'name = "{name}"\s*\npath = "([^"]*)"', lakefile)
        q = packages.get(name)
        if not path or not q or q.get("type") != "path" or Path(q.get("dir", "")) != Path(path.group(1)):
            fail(f"lakefile.toml and lake-manifest.json do not require {name} by the same path")
        if not (dependency_dir(ROOT, name) / library).is_dir():
            fail(f"the sources of {name} ({library}/) are not at {dependency_dir(ROOT, name)}")
    for name in ("Complexity", "Complexity.lean", "NPHardness", "NPHardness.lean"):
        if (ROOT / name).exists():
            fail(f"a copy of a dependency ({name}) is vendored; it must come from Lake")


def check_challenge() -> None:
    subprocess.run([sys.executable, str(ROOT / "scripts/generate_challenge.py"), "--check"], check=True)
    text = (ROOT / "Challenge.lean").read_text()
    imports = re.findall(r"^(?:public\s+)?import\s+(\S+)", text, re.M)
    if imports != ["Init"]:
        fail(f"Challenge.lean must import only Init, found {imports}")


def check_targets() -> None:
    config = json.loads((ROOT / "comparator.json").read_text())
    metadata = (ROOT / "formalization.yaml").read_text()
    declared = re.findall(r"^\s*- declaration:\s*(\S+)\s*$", metadata, re.M)
    if sorted(declared) != sorted(config["theorem_names"]):
        fail("formalization.yaml main_results differ from comparator.json theorem_names")
    challenge = (ROOT / "Challenge.lean").read_text()
    holes = len(re.findall(r"\bsorry\b", challenge))
    if holes != len(config["theorem_names"]):
        fail(f"Challenge.lean has {holes} sorry holes for {len(config['theorem_names'])} targets")


def check_audit() -> None:
    declared = {d.name for d in library_declarations(ROOT, LIBRARY)}
    paths = [ROOT / f"{AUDIT}.lean"] + sorted((ROOT / AUDIT).glob("*.lean"))
    text = "\n".join(p.read_text() for p in paths)
    guards = re.findall(r"^#print axioms\s+([\w.'?!]+)", text, re.M)
    if len(guards) != len(set(guards)):
        fail("duplicate axiom guards")
    if set(guards) != declared:
        missing = sorted(declared - set(guards))[:5]
        extra = sorted(set(guards) - declared)[:5]
        fail(f"axiom guards do not match the {LIBRARY} declarations (missing {missing}, extra {extra})")
    root_imports = set(re.findall(r"^import\s+(\S+)", (ROOT / f"{AUDIT}.lean").read_text(), re.M))
    for p in paths[1:]:
        if f"{AUDIT}.{p.stem}" not in root_imports:
            fail(f"{AUDIT}.lean does not import {p.stem}")
    for block in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", text):
        if not {a.strip() for a in block.split(",")} <= STANDARD_AXIOMS:
            fail(f"a guard names a nonstandard axiom: {block}")
    print(f"{len(guards)} axiom guards cover every named {LIBRARY} declaration")


def check_sources() -> None:
    for p in sorted(ROOT.rglob("*.lean")):
        rel = p.relative_to(ROOT)  # (the absolute path itself may contain `work`)
        if ".lake" in rel.parts or "work" in rel.parts:
            continue
        lines = p.read_text().splitlines()
        if p.is_symlink() or not lines or lines[0] != "module":
            fail(f"{p.relative_to(ROOT)} must be a regular file starting with `module`")
        if len(lines) > 10000:
            fail(f"{p.relative_to(ROOT)} exceeds 10,000 lines")
        code = without_comments(p.read_text())
        if re.search(r"\b(native_decide|admit)\b|^\s*(?:private\s+)?axiom\s", code, re.M):
            fail(f"{p.relative_to(ROOT)} uses native_decide, admit or an axiom")
        if p.name != "Challenge.lean" and re.search(r"\bsorry\b", code):
            fail(f"{p.relative_to(ROOT)} contains sorry")


def main() -> int:
    check_pin()
    check_challenge()
    check_targets()
    check_audit()
    check_sources()
    print("All static checks passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
