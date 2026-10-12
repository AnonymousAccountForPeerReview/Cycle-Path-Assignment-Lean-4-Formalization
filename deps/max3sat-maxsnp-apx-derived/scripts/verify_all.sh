#!/usr/bin/env bash
# Run the mechanical verification of this repository locally.
#
#   scripts/verify_all.sh [--paranoid]
#
# Runs the repository checks, the Mathlib cache download, the default build
# (Solution), the Challenge build, and the sandboxed `lake comparator` with
# NanoDa. (`lake check` is not run: it would replay all of
# Mathlib through the kernel; Comparator replays the compared theorems.) With --paranoid, Comparator
# also runs every other checker bundled with Lean (leanchecker-paranoid,
# lean4lean, con-leche and con-ron). Needs elan, python3 and bubblewrap (bwrap);
# PyYAML enables the metadata checks. Logs go to .lake/verify/.
set -euo pipefail

cd "$(dirname "$0")/.."
comparator_flags=()
if [[ "${1:-}" == "--paranoid" ]]; then
  comparator_flags+=(--paranoid)
elif [[ $# -gt 0 ]]; then
  echo "usage: $0 [--paranoid]" >&2
  exit 2
fi

logs=.lake/verify
mkdir -p "$logs"
# Comparator finds NanoDa and the other checkers on PATH; they ship with Lean.
PATH="$(lean --print-prefix)/bin:$PATH"
export PATH

step() {
  local name=$1
  shift
  echo "== $name: $*"
  if ! "$@" > "$logs/$name.log" 2>&1; then
    tail -n 40 "$logs/$name.log"
    echo "FAILED: $name (full log in $logs/$name.log)" >&2
    exit 1
  fi
  tail -n 3 "$logs/$name.log"
}

step checks python3 scripts/check_repository.py
step cache lake exe cache get
step build lake build
step challenge lake build Challenge
step comparator lake comparator --config comparator.json "${comparator_flags[@]}"
echo "All checks passed."
