#!/usr/bin/env python3
"""Check that every internal MeTTapedia import resolves in the source tree."""

from __future__ import annotations

import re
import sys
from pathlib import Path


IMPORT_LINE = re.compile(r"^\s*import\s+(.+?)\s*(?:--.*)?$")
MODULE_NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$")


def module_name(source_root: Path, path: Path) -> str:
    return ".".join(path.relative_to(source_root).with_suffix("").parts)


def imported_modules(path: Path) -> list[tuple[int, str]]:
    imports: list[tuple[int, str]] = []
    for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        match = IMPORT_LINE.match(line)
        if match is None:
            continue
        for token in match.group(1).split():
            if MODULE_NAME.fullmatch(token):
                imports.append((line_number, token))
    return imports


def main() -> int:
    project_root = Path(__file__).resolve().parents[1]
    sources = sorted((project_root / "Mettapedia").rglob("*.lean"))
    root_umbrella = project_root / "Mettapedia.lean"
    if root_umbrella.is_file():
        sources.append(root_umbrella)

    available = {module_name(project_root, path) for path in sources}
    dangling: list[tuple[str, int, str]] = []
    for path in sources:
        for line_number, imported in imported_modules(path):
            if imported.startswith("Mettapedia.") and imported not in available:
                dangling.append((str(path.relative_to(project_root)), line_number, imported))

    if dangling:
        for path, line_number, imported in dangling:
            print(f"{path}:{line_number}: unresolved internal import {imported}")
        targets = {imported for _, _, imported in dangling}
        print(
            f"FAILED: {len(dangling)} dangling import edge(s) "
            f"over {len(targets)} missing module(s)",
            file=sys.stderr,
        )
        return 1

    print(f"OK: {len(available)} MeTTapedia module(s), zero dangling internal imports")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
