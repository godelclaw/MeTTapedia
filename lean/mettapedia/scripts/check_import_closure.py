#!/usr/bin/env python3
"""Check internal imports and, optionally, coverage by named build roots.

Coverage means source reachability, not proof qualification. An uncovered module
may be useful mathematics; this tool never changes imports or removes files.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path


# Lean module headers allow nested comments, Unicode/escaped identifiers, and
# `public meta import all`. Stop at the first body command, so strings and
# documentation examples in the body cannot create spurious import edges.
IDENT = r"(?:«[^»]+»|[^\W\d][\w'!?₀-₉]*)"
TOKEN = re.compile(rf"{IDENT}(?:\.{IDENT})*|\S", re.UNICODE)


def header_tokens(text: str):
    offset = 0
    line = 1
    while offset < len(text):
        if text[offset].isspace() or text[offset] == "\ufeff":
            line += text[offset] == "\n"
            offset += 1
        elif text.startswith("--", offset):
            end = text.find("\n", offset)
            offset = len(text) if end < 0 else end
        elif text.startswith("/-", offset):
            depth = 1
            offset += 2
            while depth and offset < len(text):
                if text.startswith("/-", offset):
                    depth += 1
                    offset += 2
                elif text.startswith("-/", offset):
                    depth -= 1
                    offset += 2
                else:
                    line += text[offset] == "\n"
                    offset += 1
            if depth:
                raise ValueError("unterminated header comment")
        else:
            match = TOKEN.match(text, offset)
            assert match is not None
            yield line, match.group()
            offset = match.end()


def parse_imports(text: str) -> list[tuple[int, str]]:
    tokens = iter(header_tokens(text))
    current = next(tokens, None)
    for directive in ("module", "prelude"):
        if current is not None and current[1] == directive:
            current = next(tokens, None)
    imports: list[tuple[int, str]] = []
    while current is not None:
        for modifier in ("public", "meta"):
            if current is not None and current[1] == modifier:
                current = next(tokens, None)
        if current is None or current[1] != "import":
            break
        current = next(tokens, None)
        if current is not None and current[1] == "all":
            current = next(tokens, None)
        if current is None or not re.fullmatch(rf"{IDENT}(?:\.{IDENT})*", current[1]):
            raise ValueError("missing module name after import")
        number, name = current
        # Escaped identifiers name the same module as the unescaped spelling.
        name = re.sub(r"«([^»]+)»", r"\1", name)
        imports.append((number, name))
        current = next(tokens, None)
    return imports


def module_name(source_root: Path, path: Path) -> str:
    return ".".join(path.relative_to(source_root).with_suffix("").parts)


def imported_modules(path: Path) -> list[tuple[int, str]]:
    return parse_imports(path.read_text(encoding="utf-8"))


def reachable(graph: dict[str, list[str]], roots: list[str]) -> set[str]:
    seen: set[str] = set()
    pending = list(roots)
    while pending:
        name = pending.pop()
        if name not in seen and name in graph:
            seen.add(name)
            pending.extend(graph[name])
    return seen


def source_files(project_root: Path, tracked: bool) -> list[Path]:
    if tracked:
        result = subprocess.run(
            ["git", "ls-files", "-z", "--", "Mettapedia.lean", "Mettapedia/"],
            cwd=project_root, check=True, stdout=subprocess.PIPE,
        )
        return sorted(project_root / name.decode() for name in result.stdout.split(b"\0")
                      if name.endswith(b".lean"))
    sources = list((project_root / "Mettapedia").rglob("*.lean"))
    if (project_root / "Mettapedia.lean").is_file():
        sources.append(project_root / "Mettapedia.lean")
    return sorted(sources)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project-root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--tracked", action="store_true", help="inventory Git-tracked sources only")
    parser.add_argument("--root", action="append", default=[], help="build root (repeatable)")
    parser.add_argument("--report", type=Path, help="write full coverage and source hashes as JSON")
    parser.add_argument("--require-covered", action="store_true", help="fail if any source is uncovered")
    args = parser.parse_args()
    if args.require_covered and not args.root:
        parser.error("--require-covered needs at least one --root")
    project_root = args.project_root.resolve()
    sources = source_files(project_root, args.tracked)
    available = {module_name(project_root, path): path for path in sources}
    dangling: list[tuple[str, int, str]] = []
    errors: list[str] = []
    graph: dict[str, list[str]] = {}
    hashes: dict[str, str] = {}
    for name, path in available.items():
        relative = str(path.relative_to(project_root))
        try:
            hashes[relative] = hashlib.sha256(path.read_bytes()).hexdigest()
            imports = imported_modules(path)
        except (OSError, ValueError) as error:
            errors.append(f"{relative}: {error}")
            continue
        graph[name] = []
        for line_number, imported in imports:
            if imported == "Mettapedia" or imported.startswith("Mettapedia."):
                graph[name].append(imported)
                if imported not in available:
                    dangling.append((relative, line_number, imported))
    missing_roots = sorted(set(args.root) - available.keys())
    covered = reachable(graph, args.root)
    uncovered = sorted(available.keys() - covered) if args.root else []
    summary = {
        "inventory": "tracked" if args.tracked else "filesystem",
        "roots": args.root,
        "sources": len(available), "covered": len(covered),
        "uncovered": uncovered, "missing_roots": missing_roots,
        "dangling": dangling, "errors": errors, "source_sha256": hashes,
    }
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    for error in errors:
        print(error, file=sys.stderr)
    for path, line_number, imported in dangling:
        print(f"{path}:{line_number}: unresolved internal import {imported}", file=sys.stderr)
    for root in missing_roots:
        print(f"missing build root: {root}", file=sys.stderr)
    print(f"Imports: {len(available)} sources, {len(dangling)} dangling edges, {len(errors)} read/parse errors")
    if args.root:
        print(f"Coverage: {len(covered)} reachable, {len(uncovered)} outside the named roots")
        for group, count in Counter(".".join(name.split(".")[:3]) for name in uncovered).most_common(10):
            print(f"  {group}: {count}")
        if uncovered:
            print("Uncovered sources need review; they are not classified as junk.")
    return int(bool(errors or dangling or missing_roots or (args.require_covered and uncovered)))


if __name__ == "__main__":
    raise SystemExit(main())
