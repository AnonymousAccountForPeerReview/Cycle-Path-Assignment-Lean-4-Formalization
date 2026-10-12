"""Locate the source directories of the Lake dependencies, from `lake-manifest.json`.

A dependency required by path (`"type": "path"`, as the sibling formalizations of the same
manuscript are in the published layout) lives in its `"dir"`, relative to the package; a
dependency fetched by git (`"type": "git"`) lives in `<packagesDir>/<name>` (by default
`.lake/packages/<name>`). The scripts that read dependency sources (the Challenge generator,
the repository check) go through `dependency_dir`, so they work in both layouts.
"""
from __future__ import annotations

import json
from pathlib import Path


def read_manifest(root: Path) -> dict:
    return json.loads((root / "lake-manifest.json").read_text(encoding="utf-8"))


def manifest_packages(manifest: dict) -> dict[str, dict]:
    """The packages of a manifest, by name (without the guillemets `«»`)."""
    return {p["name"].strip("«»"): p for p in manifest["packages"]}


def dependency_dir(root: Path, name: str) -> Path:
    """The source directory of the dependency `name` of the package at `root`."""
    manifest = read_manifest(root)
    packages = manifest_packages(manifest)
    if name not in packages:
        raise ValueError(f"{name} is not a dependency in lake-manifest.json")
    package = packages[name]
    kind = package.get("type")
    if kind == "path":
        return (root / package["dir"]).resolve()
    if kind == "git":
        return root / manifest.get("packagesDir", ".lake/packages") / name
    raise ValueError(f"unsupported dependency type {kind!r} for {name} in lake-manifest.json")
