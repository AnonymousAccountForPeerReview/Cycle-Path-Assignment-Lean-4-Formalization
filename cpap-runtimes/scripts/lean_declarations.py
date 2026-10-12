"""Discover the library's modules and its explicitly named declarations.

The library is the transitive closure of the `import`s of `Runtimes.lean` within the
`Runtimes` namespace of modules, so a module joins it (and its declarations need axiom
guards) as soon as it is imported. `stray_modules` lists the `.lean` files under
`Runtimes/` that the closure does not reach.

The declaration scanner is conservative, not a Lean parser; Lean subsequently resolves
every discovered name in the axiom guards, and `generate_audit.py` checks that it misses
no declaration of the built library. Private declarations retain their user names and
the module needed to identify Lean's internal private prefix. Unbalanced scopes and an
unclosed `mutual` block fail closed; namespaces and sections left open at
the end of a file are closed there, as Lean closes them (`Runtimes/ZeroCostGen.lean` leaves
its namespace open). Names keep their source spelling (`«forall»`); `plain` removes the
guillemets, as Lean prints names.
"""
from dataclasses import dataclass
from pathlib import Path
import re

from generate_challenge import without_comments

IDENT = r"(?:«[^»\n]*»|[\w'?!])(?:«[^»\n]*»|[\w.'?!])*"
IMPORT = re.compile(r"^(?:public\s+|private\s+|meta\s+)*import\s+(?:all\s+)?(\S+)", re.M)


@dataclass(frozen=True)
class Declaration:
    name: str
    kind: str
    source: str
    line: int
    private: bool = False
    module: str = ""


def plain(name: str) -> str:
    """The name as Lean prints it (`A.«forall»` is printed `A.forall`)."""
    return name.replace("«", "").replace("»", "")


def split_name(name: str) -> list[str]:
    """Split a dotted name into components, keeping `«…»` components whole."""
    return re.findall(r"«[^»]*»|[^.«]+", name)


def kernel_name(declaration: Declaration) -> str:
    """Lean's actual constant name, including its specified private-module prefix."""
    name = plain(declaration.name)
    return f'_private.{declaration.module}.0.{name}' if declaration.private else name


def declarations(path: Path, module: str | None = None):
    scopes = []
    namespace = []
    source = without_comments(path.read_text())
    result = []
    for lineno, line in enumerate(source.splitlines(), 1):
        line = line.strip()
        line = re.sub(r"^(?:@\[[^\]]*\]\s*|set_option\s+[\w.]+\s+\S+\s+in\s+)+", "", line)
        m = re.match(rf"namespace\s+({IDENT})\s*$", line)
        if m:
            # Lean opens one scope per dotted component. `end C` can close
            # just C after `namespace A.B.C`, leaving namespace A.B active.
            for component in split_name(m[1]):
                scopes.append(("namespace", component, namespace.copy()))
                namespace.append(component)
            continue
        m = re.match(rf"(?:(?:public|noncomputable)\s+)?section(?:\s+({IDENT}))?\s*$", line)
        if m:
            scopes.append(("section", m[1], namespace.copy()))
            continue
        if line == "mutual":
            scopes.append(("mutual", None, namespace.copy()))
            continue
        m = re.match(rf"end(?:\s+({IDENT}))?\s*$", line)
        if m:
            if not scopes:
                raise ValueError(f"Unmatched end in {path}:{lineno}")
            closing = split_name(m[1]) if m[1] else [None]
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
        m = re.match(r"((?:(?:public|private|protected|noncomputable|unsafe|scoped|local)\s+)*)"
                     r"(theorem|lemma|def|abbrev|opaque|structure|class\s+inductive|inductive|class|instance)"
                     rf"(?:\s+\(priority\s*:=\s*\w+\))?\s+({IDENT})", line)
        if m:
            private = "private" in m[1].split()
            name = m[3]
            if name.startswith('_root_.'):
                name = name[len('_root_.'):]
            else:
                name = '.'.join(namespace + [name])
            result.append(Declaration(name, ' '.join(m[2].split()), str(path), lineno,
                                      private, module or path.stem))
    # Lean closes the namespaces and sections still open at the end of a file (an unnamed
    # `public section` deliberately runs to the end); a `mutual` block must be closed.
    if any(kind == 'mutual' for kind, _, _ in scopes):
        raise ValueError(f"Unclosed mutual block in {path}")
    return result


def module_path(root: Path, module: str) -> Path:
    return root.joinpath(*module.split('.')).with_suffix('.lean')


def library_modules(root: Path, library: str) -> list[str]:
    """The modules `library.*` reachable from `library.lean` by imports, in sorted order."""
    seen: set[str] = set()
    todo = [library]
    while todo:
        module = todo.pop()
        if module in seen:
            continue
        seen.add(module)
        path = module_path(root, module)
        if not path.is_file():
            raise ValueError(f"{module} is imported but {path.relative_to(root)} does not exist")
        for imported in IMPORT.findall(without_comments(path.read_text())):
            if imported.startswith(library + '.'):
                todo.append(imported)
    seen.discard(library)
    return sorted(seen)


def stray_modules(root: Path, library: str) -> list[Path]:
    """The `.lean` files under `library/` that `library.lean` does not (transitively) import."""
    reached = {module_path(root, m) for m in library_modules(root, library)}
    return [p for p in sorted((root / library).rglob('*.lean'))
            if p not in reached and '.rsync-tmp' not in p.relative_to(root).parts]


def library_declarations(root: Path, library: str):
    """Every named declaration of the library's modules, in module order."""
    result = [d for m in library_modules(root, library) for d in declarations(module_path(root, m), m)]
    names = [kernel_name(d) for d in result]
    if len(names) != len(set(names)):
        raise ValueError(f'Duplicate fully qualified {library} declaration names')
    return result
