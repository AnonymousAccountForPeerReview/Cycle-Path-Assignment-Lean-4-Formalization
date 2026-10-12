#!/usr/bin/env python3
"""Regenerate exact axiom guards after building the current Runtimes library.

Every named declaration of the library's modules (the import closure of
`Runtimes.lean`, `lean_declarations.py`) is queried, in one batch: a single Lean
process imports the library once and runs `#print axioms` for each declaration. The
same process lists the declarations that the library's modules define; any of them
that the source scanner missed, other than those Lean or an attribute generates
(equation lemmas, constructors' injectivity, `@[mk_iff]` lemmas, anonymous instances,
syntax), aborts the run. Unknown output, missing declarations, duplicates and
nonstandard axioms abort before RuntimesAudit.lean is replaced.

Run `lake build Runtimes` first; afterwards `lake build RuntimesAudit` checks the guards.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess

from lean_declarations import kernel_name, library_declarations, library_modules, plain

LIBRARY = 'Runtimes'
AUDIT = 'RuntimesAudit'
CHUNK = 1200
STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}

# Lists, from the environment, the declarations defined by the library's modules, with
# their kind; declarations Lean generates with structure (auxiliary recursors,
# `noConfusion`, constructors, recursors, projections, matchers, internal names) are left
# out here, the others generated declarations in `generated` below. Under the module
# system an imported theorem is seen without its proof, as an `axiomInfo`: it is listed as
# a theorem. (A declared axiom would be named by `#print axioms`, which the guards record,
# and `check_repository.py` rejects the keyword in every source.)
LIST_DECLARATIONS = '''
open Lean in
run_cmd do
  let env ← getEnv
  let mut out : Array String := #[]
  for h : i in [0:env.header.moduleNames.size] do
    let mod := env.header.moduleNames[i]
    unless (`{library}).isPrefixOf mod do continue
    for n in env.header.moduleData[i]!.constNames do
      let userName := privateToUserName n
      if userName.isInternalDetail || isAuxRecursor env n || isNoConfusion env n then continue
      if (env.getProjectionFnInfo? n).isSome || Meta.isMatcherCore env n then continue
      -- Splitters have a fresh private prefix; their originating matcher is
      -- recorded under the user name (Lean.Meta.Match.mkMatcherEqns).
      if userName.getString! == "splitter" &&
          (Meta.isMatcherCore env n.getPrefix || Meta.isMatcherCore env userName.getPrefix) then continue
      let some ci := env.find? n | continue
      let kind := match ci with
        | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .inductInfo _ => "inductive"
        | .opaqueInfo _ => "opaque" | .axiomInfo _ => "theorem" | .quotInfo _ => "quot"
        | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
      if kind == "constructor" || kind == "recursor" then continue
      let kind := if ci.type.isConstOf ``ParserDescr || ci.type.isConstOf ``TrailingParserDescr
        then "syntax" else kind
      out := out.push s!"{{kind}} {{n}}"
  IO.FS.writeFile "{output}" (String.intercalate "\\n" out.toList ++ "\\n")
'''

# Last name components of declarations that Lean generates (equation lemmas, structure
# eta and injectivity lemmas, `sizeOf` lemmas, constructor indices, `congr` lemmas,
# structural recursion auxiliaries, functional induction principles).
GENERATED_LAST = {'eq_def', 'congr_simp', 'inj', 'injEq', 'sizeOf_spec', 'ctorIdx', 'ctorElimType',
                  'noConfusionType', 'below', 'brecOn', 'binductionOn', 'induct', 'induct_unfolding',
                  'fun_cases', 'mutual_induct', 'eq_iff', 'ext_iff', 'ext'}


def generated(name: str, kind: str, scanned: dict[str, str]) -> bool:
    """Whether a declaration missing from the scanner's list is generated, not written."""
    parts = name.split('.')
    last = parts[-1]
    if kind == 'syntax':
        return True
    if last in GENERATED_LAST or re.fullmatch(r'eq_\d+', last):
        return True
    if len(parts) > 1 and parts[-2] in {'brecOn', 'binductionOn'}:
        return True
    if kind == 'def' and last.startswith('inst'):
        return True  # an anonymous instance, named by Lean
    # Deriving generates a method auxiliary under its anonymous instance. Only
    # accept the exact class method for an explicitly scanned source datatype.
    if kind == 'def' and len(parts) > 1:
        for instance, method in {'instRepr': 'repr', 'instDecidableEq': 'decEq',
                                 'instBEq': 'beq', 'instInhabited': 'default'}.items():
            parent = parts[-2]
            if last == method and parent.startswith(instance):
                datatype = '.'.join(parts[:-2] + [parent[len(instance):]])
                if scanned.get(datatype) in {'structure', 'inductive', 'class', 'class inductive'}:
                    return True
    # `@[mk_iff] structure Foo` generates `foo_iff`, in the same namespace.
    m = re.fullmatch(r'(.*)_iff', last)
    if m and m[1]:
        stem = '.'.join(parts[:-1] + [m[1][0].upper() + m[1][1:]])
        if scanned.get(stem) in {'structure', 'inductive', 'class', 'class inductive'}:
            return True
    # the extensionality lemmas of `@[ext] structure Foo`
    if last in {'ext', 'ext_iff'} and scanned.get('.'.join(parts[:-1])) == 'structure':
        return True
    return False


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.parse_args()
    root = Path(__file__).resolve().parents[1]
    work = root/'work'
    work.mkdir(exist_ok=True)
    declared = library_declarations(root, LIBRARY)
    names = [kernel_name(d) for d in declared]
    if len(names) != len(set(names)):
        raise RuntimeError('Duplicate declaration names')
    listing = work/'lean-declarations.txt'
    source = work/'AxiomPrint.lean'
    imports = '\n'.join('import all '+m for m in [LIBRARY, *library_modules(root, LIBRARY)])
    source.write_text(f'module\n\n{imports}\nmeta import Lean.Elab.Command\n\n'
                      'set_option maxRecDepth 100000\n\n' +
                      '\n'.join('#print axioms '+d.name for d in declared)+'\n' +
                      LIST_DECLARATIONS.format(library=LIBRARY, output=listing))
    # `lake env` puts every dependency's build directory (cpap-outerplanar, cpap-tractability,
    # cpap-bounded-cost, cpap-approximation and, through them, cpap-np-hardness, cpap-minor-free,
    # np-completeness and Mathlib with its dependencies) on the search path.
    cmd = ['lake', 'env', 'lean', str(source)]
    r = subprocess.run(cmd, cwd=root, text=True,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (work/'axioms-current.log').write_text(r.stdout)
    if r.returncode:
        raise RuntimeError(f'Lean axiom query failed ({r.returncode}); see work/axioms-current.log')
    # Every declaration the library defines is either scanned or generated.
    scanned = {kernel_name(d): d.kind for d in declared}
    unscanned = []
    for line in listing.read_text().splitlines():
        kind, name = line.split(' ', 1)
        if kind == 'quot':
            raise RuntimeError(f'The library declares a quotient primitive: {name}')
        if name not in scanned and not generated(name, kind, scanned):
            unscanned.append(name)
    if unscanned:
        raise RuntimeError(f'Declarations missed by the scanner: {unscanned[:10]}')
    # Pretty-printed axiom lists can wrap for long qualified names. Preserve
    # the exact text for #guard_msgs, while treating one message as one record.
    lines = []
    for line in r.stdout.strip().splitlines():
        if line.startswith("'"):
            lines.append(line)
        elif lines and 'depends on axioms: [' in lines[-1] and not lines[-1].endswith(']'):
            lines[-1] += '\n'+line
        else:
            raise RuntimeError(f'Unexpected axiom-report text: {line}')
    if len(lines) != len(names):
        raise RuntimeError('Unexpected axiom-report line count')
    records = []
    blocks = []
    for declaration, name, line in zip(declared, names, lines, strict=True):
        m = re.fullmatch(r"'(\S+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])", line)
        if not m or m[1] != plain(name):
            raise RuntimeError(f'Unexpected report for {name}: {line}')
        axioms = [] if m[2] is None else [a.strip() for a in m[2].split(',')]
        if not set(axioms) <= STANDARD_AXIOMS:
            raise RuntimeError(f'Nonstandard axioms: {name}: {axioms}')
        records.append({'declaration': plain(name), 'axioms': axioms})
        blocks.append(f'/-- info: {line} -/\n#guard_msgs in\n#print axioms {declaration.name}\n')
    header = f'''module

{imports}

/-!
Exact-message axiom guards for every explicitly named {LIBRARY} declaration.
Each guard fails if its transitive axiom report changes. The generator rejects
axioms outside propext, Classical.choice, and Quot.sound before writing this
file. Regenerate with scripts/generate_audit.py.
-/

set_option maxRecDepth 100000

'''
    # Keep generated regular Lean files well below the 10,000-line cap of a source file.
    # The root imports every chunk, so ordinary `lake build RuntimesAudit` checks all
    # guards. Each chunk is self-contained and has at most CHUNK declarations.
    audit_dir = root/AUDIT
    audit_dir.mkdir(exist_ok=True)
    modules = []
    for i in range(0, len(blocks), CHUNK):
        name = f'Guards{i // CHUNK:03d}'
        modules.append(f'{AUDIT}.{name}')
        (audit_dir/f'{name}.lean').write_text(header+'\n'.join(blocks[i:i+CHUNK]))
    expected = {m.split('.')[-1]+'.lean' for m in modules}
    for old in audit_dir.glob('Guards[0-9][0-9][0-9].lean'):
        if old.name not in expected:
            old.unlink()
    (root/f'{AUDIT}.lean').write_text('module\n\n'+
        '\n'.join('import '+m for m in modules)+'\n\n'+
        '/-! Complete exact-axiom audit; generated guards are split to obey\n'+
        'the per-source line cap. Regenerate with scripts/generate_audit.py. -/\n')
    (root/'proofs').mkdir(exist_ok=True)
    (root/'proofs/axiom-audit.json').write_text(json.dumps({
        'method': 'Kernel #print axioms with exact #guard_msgs assertions',
        'permitted_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
        'library_modules': len(library_modules(root, LIBRARY)),
        'guard_modules': modules,
        'declarations': records}, indent=2, ensure_ascii=False)+'\n')
    print(f'Generated {len(records)} exact axiom guards for the {len(library_modules(root, LIBRARY))} '
          f'modules of {LIBRARY}')


if __name__ == '__main__':
    main()
