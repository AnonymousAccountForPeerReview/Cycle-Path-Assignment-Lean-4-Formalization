#!/usr/bin/env python3
"""Regenerate exact axiom guards after building the current NPHardness module.

Every named declaration is queried. Unknown output, missing declarations,
duplicates, and nonstandard axioms abort before NPHardnessAudit.lean is replaced.
"""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
from lean_declarations import section5_declarations


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    args = ap.parse_args()
    root = Path(__file__).resolve().parents[1]
    work = root/'work'
    work.mkdir(exist_ok=True)
    names = [d.name for d in section5_declarations(root)]
    if len(names) != len(set(names)):
        raise RuntimeError('Duplicate declaration names')
    source = work/'AxiomPrint.lean'
    source.write_text('module\n\nimport NPHardness\n\nset_option maxRecDepth 100000\n\n'+
                      '\n'.join('#print axioms '+n for n in names)+'\n')
    # `lake env` puts the build directories of every dependency on the search path, in the
    # git and in the path layout alike.
    cmd = ['lake', 'env', 'lean', str(source)]
    r = subprocess.run(cmd, cwd=root, text=True,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (work/'axioms-current.log').write_text(r.stdout)
    if r.returncode:
        raise RuntimeError(f'Lean axiom query failed ({r.returncode}); see work/axioms-current.log')
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
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    records = []
    blocks = []
    for name, line in zip(names, lines, strict=True):
        m = re.fullmatch(r"'([\w.'?!]+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])", line)
        if not m or m[1] != name:
            raise RuntimeError(f'Unexpected report for {name}: {line}')
        axioms = [] if m[2] is None else [a.strip() for a in m[2].split(',')]
        if not set(axioms) <= allowed:
            raise RuntimeError(f'Nonstandard axioms: {name}: {axioms}')
        records.append({'declaration': name, 'axioms': axioms})
        blocks.append(f'/-- info: {line} -/\n#guard_msgs in\n#print axioms {name}\n')
    header = '''module

import NPHardness

/-!
Exact-message axiom guards for every explicitly named NPHardness declaration.
Each guard fails if its transitive axiom report changes. The generator rejects
axioms outside propext, Classical.choice, and Quot.sound before writing this
file. Regenerate with scripts/generate_audit.py.
-/

set_option maxRecDepth 100000

'''
    # Keep generated regular Lean files well below the 10,000-line cap.
    # The root imports every chunk, so ordinary `lake build NPHardnessAudit` checks all
    # guards. Each chunk is self-contained and has at most 1,200 declarations.
    audit_dir = root/'NPHardnessAudit'
    audit_dir.mkdir(exist_ok=True)
    modules = []
    for i in range(0, len(blocks), 1200):
        name = f'Guards{i // 1200:03d}'
        modules.append(f'NPHardnessAudit.{name}')
        (audit_dir/f'{name}.lean').write_text(header+'\n'.join(blocks[i:i+1200]))
    expected = {m.split('.')[-1]+'.lean' for m in modules}
    for old in audit_dir.glob('Guards[0-9][0-9][0-9].lean'):
        if old.name not in expected:
            old.unlink()
    (root/'NPHardnessAudit.lean').write_text('module\n\n'+
        '\n'.join('import '+m for m in modules)+'\n\n'+
        '/-! Complete exact-axiom audit; generated guards are split to obey\n'+
        'the 10,000-line per-source cap. Regenerate with scripts/generate_audit.py. -/\n')
    (root/'proofs/axiom-audit.json').write_text(json.dumps({
        'method': 'Kernel #print axioms with exact #guard_msgs assertions',
        'permitted_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
        'guard_modules': modules,
        'declarations': records}, indent=2)+'\n')
    print(f'Generated {len(records)} exact axiom guards')


if __name__ == '__main__':
    main()
