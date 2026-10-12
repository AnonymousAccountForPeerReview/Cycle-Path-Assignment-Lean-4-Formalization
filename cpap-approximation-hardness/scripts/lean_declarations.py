"""Discover explicitly named declarations, retaining their Lean namespaces.

This is a conservative scanner for this repository, not a Lean parser. Lean
subsequently resolves every discovered name in the axiom guards.
Unsupported private declarations and unbalanced scopes fail closed.
"""
from dataclasses import dataclass
from pathlib import Path
import re

from generate_challenge import without_comments


@dataclass(frozen=True)
class Declaration:
    name: str
    kind: str
    source: str
    line: int


def declarations(path: Path):
    scopes = []
    namespace = []
    source = without_comments(path.read_text())
    result = []
    for lineno, line in enumerate(source.splitlines(), 1):
        line = line.strip()
        line = re.sub(r"^(?:@\[[^\]]*\]\s*)+", "", line)
        m = re.match(r"namespace\s+([\w.']+)\s*$", line)
        if m:
            # Lean opens one scope per dotted component. `end C` can close
            # just C after `namespace A.B.C`, leaving namespace A.B active.
            for component in m[1].split('.'):
                scopes.append(("namespace", component, namespace.copy()))
                namespace.append(component)
            continue
        m = re.match(r"(?:(?:public|noncomputable)\s+)?section(?:\s+([\w.']+))?\s*$", line)
        if m:
            scopes.append(("section", m[1], namespace.copy()))
            continue
        if line == "mutual":
            scopes.append(("mutual", None, namespace.copy()))
            continue
        m = re.match(r"end(?:\s+([\w.']+))?\s*$", line)
        if m:
            if not scopes:
                raise ValueError(f"Unmatched end in {path}:{lineno}")
            closing = m[1].split('.') if m[1] else [None]
            for component in reversed(closing):
                if not scopes:
                    raise ValueError(f"Unmatched end in {path}:{lineno}")
                kind, name, old_namespace = scopes.pop()
                if component and component != name:
                    raise ValueError(f"Mismatched end in {path}:{lineno}: {component} vs {name}")
                if len(closing) > 1 and kind != 'namespace':
                    raise ValueError(f"Qualified end crosses a section in {path}:{lineno}")
                namespace = old_namespace
            continue
        m = re.match(r"((?:(?:public|private|protected|noncomputable|unsafe)\s+)*)"
                     r"(theorem|lemma|def|abbrev|structure|inductive)\s+([\w.'?!]+)", line)
        if m:
            if "private" in m[1].split():
                raise ValueError(f"Private declarations are not supported, in {path}:{lineno}")
            name = m[3]
            if name.startswith('_root_.'):
                name = name[len('_root_.'):]
            else:
                name = '.'.join(namespace + [name])
            result.append(Declaration(name, m[2], str(path), lineno))
    # An unnamed public/noncomputable section deliberately runs to end of file.
    if any(kind != 'section' or name for kind, name, _ in scopes):
        raise ValueError(f"Unclosed named scope in {path}")
    return result


def library_declarations(root: Path, library: str):
    """Every named declaration of `root/<library>/**/*.lean`, in file order."""
    result = [d for p in sorted((root / library).rglob('*.lean')) for d in declarations(p)]
    names = [d.name for d in result]
    if len(names) != len(set(names)):
        raise ValueError(f'Duplicate fully qualified {library} declaration names')
    return result
