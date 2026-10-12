#!/usr/bin/env bash
# Check a derived tree against the upstream commit and NPCompleteness-Lean4:
#
#   verify_derived_pcp.sh UPSTREAM_CLONE NP_COMPLETENESS_CHECKOUT DERIVED
#
# * every upstream file not under `Complexity/`, other than `lakefile.toml`, is in the derived
#   tree, and is byte-identical to the upstream one once the `import` lines naming
#   `ComplexityExt.*` modules are turned back into `Complexity.*`;
# * every upstream `Complexity/X.lean` is either byte-identical to np-completeness's
#   `Complexity/X.lean` (and absent from the derived tree), or present, after the same
#   rewriting, as `ComplexityExt/X.lean`;
# * the derived tree has no other file except DERIVED.md, derive_pcp.sh and
#   verify_derived_pcp.sh;
# * the documentation and metadata (README.md, formalization.yaml, docs/, .github/workflows/
#   and the repository-check scripts scripts/check_*.py and scripts/*.sh, renamed in the
#   derived tree) are edited after derivation (DERIVED.md) and are not compared.
set -euo pipefail
UPSTREAM_REV=10079b2a14bd0df47d2a24364133f6008b9c207f
UP=$(cd "$1" && pwd); NP=$(cd "$2" && pwd); D=$(cd "$3" && pwd)
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
git -C "$UP" archive "$UPSTREAM_REV" | tar -x -C "$T"
undo() {
  perl -0pe 's/^((?:public[ \t]+)?(?:meta[ \t]+)?import[ \t]+(?:all[ \t]+)?)ComplexityExt\./${1}Complexity./mg' "$1"
}
fail=0; n_same=0; n_np=0; n_moved=0; n_doc=0
while IFS= read -r f; do
  f=${f#./}
  case "$f" in
    lakefile.toml) continue ;;
    README.md|formalization.yaml|docs/*|.github/workflows/*|scripts/check_*.py|scripts/*.sh)
      n_doc=$((n_doc + 1)) ;;
    Complexity/*)
      rest=${f#Complexity/}
      if [ -f "$NP/$f" ] && cmp -s "$T/$f" "$NP/$f"; then
        [ -e "$D/$f" ] && { echo "present but provided by np-completeness: $f"; fail=1; }
        n_np=$((n_np + 1))
      elif [ -f "$D/ComplexityExt/$rest" ] && cmp -s <(undo "$D/ComplexityExt/$rest") "$T/$f"; then
        n_moved=$((n_moved + 1))
      else
        echo "mismatch: $f"; fail=1
      fi ;;
    *)
      if [ -f "$D/$f" ] && cmp -s <(undo "$D/$f") "$T/$f"; then n_same=$((n_same + 1))
      else echo "mismatch: $f"; fail=1; fi ;;
  esac
done < <(cd "$T" && find . -type f | sort)
while IFS= read -r f; do
  f=${f#./}
  case "$f" in
    DERIVED.md|derive_pcp.sh|verify_derived_pcp.sh|lakefile.toml) ;;
    README.md|formalization.yaml|docs/*|.github/workflows/*|scripts/check_*.py|scripts/*.sh) ;;
    ComplexityExt/*) [ -f "$T/Complexity/${f#ComplexityExt/}" ] || { echo "extra: $f"; fail=1; } ;;
    *) [ -f "$T/$f" ] || { echo "extra: $f"; fail=1; } ;;
  esac
done < <(cd "$D" && find . -type f -not -path './.git/*' -not -path './.lake/*' | sort)
echo "unchanged: $n_same, provided by np-completeness: $n_np, moved: $n_moved, documentation (not compared): $n_doc"
[ "$fail" = 0 ] && [ "$n_np" = 75 ] && [ "$n_moved" = 12 ] && echo OK
