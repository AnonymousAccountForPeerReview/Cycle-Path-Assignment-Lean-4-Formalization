#!/usr/bin/env bash
# Derive the packaging of Max3SAT-MaxSNP-APX-Lean4 that shares a Lake workspace with
# NPCompleteness-Lean4.
#
#   derive_pcp.sh UPSTREAM_CLONE NP_COMPLETENESS_CHECKOUT OUT
#
# UPSTREAM_CLONE is a clone of the upstream repository Max3SAT-MaxSNP-APX-Lean4
# containing commit $UPSTREAM_REV; NP_COMPLETENESS_CHECKOUT is NPCompleteness-Lean4 at
# $NP_REV. Nothing in either is modified: the upstream tree is exported with `git archive`.
#
# Lake resolves an import by module name alone: every package whose libraries match the
# name provides the module. NPCompleteness-Lean4's library `Complexity` (default roots)
# matches every module `Complexity.*`, so in a shared workspace the upstream library
# `Complexity` (globs `Complexity.+`) would provide each of its modules a second time.
# Hence:
#   1. the 75 upstream `Complexity/` files that are byte-identical to NPCompleteness-Lean4
#      are removed (that package provides them);
#   2. the 12 remaining `Complexity/` modules, which NPCompleteness-Lean4 does not have, are
#      moved under the module prefix `ComplexityExt` (file moves, and the corresponding
#      `import` lines rewritten; no declaration, namespace or other line changes);
#   3. `lakefile.toml` requires np-completeness at $NP_REV and declares the library
#      `ComplexityExt` instead of `Complexity`;
#   4. DERIVED.md is added.
# The documentation and metadata are then edited by hand (see DERIVED.md).
# `verify_derived_pcp.sh` checks that undoing step 2 gives back the upstream files byte for
# byte.
set -euo pipefail

UPSTREAM_REV=10079b2a14bd0df47d2a24364133f6008b9c207f
NP_REV=3e603e795b44fedcf7d6dd65b7d1e30547ead925

UP=$(cd "$1" && pwd)
NP=$(cd "$2" && pwd)
OUT=$3

[ "$(git -C "$NP" rev-parse HEAD)" = "$NP_REV" ] || { echo "np-completeness is not at $NP_REV" >&2; exit 1; }

rm -rf "$OUT"
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)
git -C "$UP" archive "$UPSTREAM_REV" | tar -x -C "$OUT"
cd "$OUT"

# 1. Remove the byte-identical files.
removed=0
while IFS= read -r f; do
  if [ -f "$NP/$f" ] && cmp -s "$f" "$NP/$f"; then
    rm "$f"
    removed=$((removed + 1))
  fi
done < <(find Complexity -name '*.lean' | sort)
[ "$removed" = 75 ] || { echo "expected 75 identical files, found $removed" >&2; exit 1; }

# 2. Move the remaining modules under `ComplexityExt`.
mods=$(cd Complexity && find . -name '*.lean' | sed 's|^\./||; s|\.lean$||; s|/|.|g' | sort)
[ "$(echo "$mods" | wc -l)" = 12 ] || { echo "expected 12 remaining modules" >&2; exit 1; }
for m in $mods; do
  if [ -f "$NP/Complexity/$(echo "$m" | tr . /).lean" ]; then
    echo "module Complexity.$m also exists in np-completeness" >&2; exit 1
  fi
done
find Complexity -type d -empty -delete
[ -z "$(find Complexity -type f -not -name '*.lean')" ] || { echo "unexpected non-Lean file under Complexity/" >&2; exit 1; }
mv Complexity ComplexityExt
pattern=$(echo "$mods" | sed 's/\./\\./g' | paste -sd'|')
find . -name '*.lean' -print0 | xargs -0 perl -0pi -e \
  "s/^((?:public[ \\t]+)?(?:meta[ \\t]+)?import[ \\t]+(?:all[ \\t]+)?)Complexity\\.(${pattern})[ \\t]*\$/\${1}ComplexityExt.\${2}/mg"

# 3. The Lake configuration.
perl -0pi -e 's/\[\[require\]\]\nname = "mathlib"/[[require]]\nname = "np-completeness"\ngit = "https:\/\/github.com\/ANONYMIZED\/NPCompleteness-Lean4"\nrev = "'"$NP_REV"'"\n\n[[require]]\nname = "mathlib"/' lakefile.toml
perl -0pi -e 's/\[\[lean_lib\]\]\nname = "Complexity"\nglobs = \["Complexity\.\+"\]/[[lean_lib]]\nname = "ComplexityExt"\nglobs = ["ComplexityExt.+"]/' lakefile.toml
grep -q 'name = "ComplexityExt"' lakefile.toml
grep -q 'name = "np-completeness"' lakefile.toml
grep -q 'name = "Complexity"' lakefile.toml && { echo "library Complexity still declared" >&2; exit 1; }

# 4. DERIVED.md.
{
  cat <<EOF
# Derived packaging of Max3SAT-MaxSNP-APX-Lean4

This tree is the upstream repository Max3SAT-MaxSNP-APX-Lean4 at commit
\`$UPSTREAM_REV\`, repackaged by \`derive_pcp.sh\` so that it can share a Lake workspace with
the NP-completeness foundation NPCompleteness-Lean4 at commit \`$NP_REV\`, on which the STACS 2027
formalization already depends.

Lake resolves an import by module name: every package whose libraries match the name provides
the module, and two packages cannot both provide one (each \`.olean\` records its package).
NPCompleteness-Lean4's library \`Complexity\` matches every module name \`Complexity.*\`.

The only changes:

* the 75 upstream \`Complexity/\` files that are byte-identical to NPCompleteness-Lean4 at
  \`$NP_REV\` are removed (checked byte for byte with \`cmp\`); that package provides them;
* the 12 other \`Complexity/\` modules, which NPCompleteness-Lean4 does not have, are moved under
  the module prefix \`ComplexityExt\` (\`Complexity/X.lean\` becomes \`ComplexityExt/X.lean\`), and
  the \`import\` lines naming them are rewritten accordingly; declarations and namespaces are
  unchanged (they stay in \`Complexity\`, \`Complexity.Reg\`, ...);
* \`lakefile.toml\` requires np-completeness at \`$NP_REV\` and declares the library
  \`ComplexityExt\` (globs \`ComplexityExt.+\`) in place of \`Complexity\`;
* the documentation and metadata (\`README.md\`, \`formalization.yaml\`, \`docs/\`,
  \`.github/workflows/\`) are edited after derivation, one upstream CI workflow is dropped, and the
  upstream repository-check scripts are renamed \`scripts/check_repository.py\` and
  \`scripts/verify_all.sh\`; \`verify_derived_pcp.sh\` does not compare these files;
* this file is added.

Undoing the move and the import rewriting gives back every other upstream file byte for byte
(\`verify_derived_pcp.sh\`). The moved modules:

EOF
  for m in $mods; do echo "* \`Complexity.$m\` → \`ComplexityExt.$m\`"; done
  echo
  echo "Files whose \`import\` lines were rewritten:"
  echo
  (cd "$OUT" && grep -rlE "^(public[ \t]+)?(meta[ \t]+)?import[ \t]+(all[ \t]+)?ComplexityExt\." --include='*.lean' . | sed 's|^\./||' | sort | sed 's/^/* `/; s/$/`/')
} > DERIVED.md
echo "derived tree in $OUT ($removed files removed, 12 modules moved)"
