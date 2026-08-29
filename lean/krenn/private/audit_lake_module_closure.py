#!/usr/bin/env python3
"""Fail closed when the Krenn Lake module manifest drifts from its import closure.

The project predates a common Lean module prefix: many helper modules are flat
siblings.  Lake therefore cannot discover their import closure from a small set
of prefix globs.  ``lakefile.lean`` carries an explicit, auditable closure.  This
checker recomputes that closure from tracked source bytes and rejects omissions,
extras, missing local imports, or unsafe whole-directory compression.
"""

from __future__ import annotations

from collections import defaultdict, deque
from pathlib import Path
import re
import subprocess
import sys
from typing import NoReturn


ROOT = Path(__file__).resolve().parent.parent
LAKEFILE = ROOT / "lakefile.lean"
EXTRA_DIRECTORY_SEEDS = ("KrennComponent57",)

IMPORT_RE = re.compile(
    r"\s*(?:(?:public|private)\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.]+)"
)


def fail(message: str) -> NoReturn:
    raise SystemExit("LAKE CLOSURE AUDIT FAILED: " + message)


def tracked_lean_files() -> list[str]:
    result = subprocess.run(
        ["git", "ls-files", "*.lean"],
        cwd=ROOT,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    )
    return [path for path in result.stdout.splitlines() if path != "lakefile.lean"]


def module_name(path: str) -> str:
    if not path.endswith(".lean"):
        fail(f"not a Lean source path: {path}")
    return path[:-5].replace("/", ".")


def declaration_body(source: str, name: str, next_name: str) -> str:
    marker = f"def {name}"
    next_marker = f"def {next_name}"
    if source.count(marker) != 1 or source.count(next_marker) != 1:
        fail(f"expected one declaration each for {name} and {next_name}")
    return source.split(marker, 1)[1].split(next_marker, 1)[0]


def quoted_names(body: str) -> set[str]:
    return set(re.findall(r"`([A-Za-z0-9_.]+)", body))


def main() -> int:
    files = tracked_lean_files()
    module_to_file = {module_name(path): path for path in files}
    if len(module_to_file) != len(files):
        fail("two tracked paths map to the same Lean module")

    source = LAKEFILE.read_text(encoding="utf-8")
    roots = quoted_names(
        declaration_body(source, "krennRoots", "krennClosureModules")
    )
    declared_modules = quoted_names(
        declaration_body(source, "krennClosureModules", "krennClosureDirectories")
    )
    directory_body = source.split("def krennClosureDirectories", 1)[1].split(
        "@[default_target]", 1
    )[0]
    declared_directories = quoted_names(directory_body)

    imports: dict[str, list[str]] = {}
    for module, relative in module_to_file.items():
        found: list[str] = []
        for line in (ROOT / relative).read_text(
            encoding="utf-8", errors="strict"
        ).splitlines():
            match = IMPORT_RE.match(line)
            if match:
                found.append(match.group(1))
        imports[module] = found

    seeds = set(roots)
    for directory in EXTRA_DIRECTORY_SEEDS:
        prefix = directory + "."
        seeds.update(module for module in module_to_file if module.startswith(prefix))

    queue = deque(sorted(seeds))
    reachable: set[str] = set()
    missing_local: set[str] = set()
    while queue:
        module = queue.popleft()
        if module in reachable:
            continue
        reachable.add(module)
        if module not in module_to_file:
            missing_local.add(module)
            continue
        for imported in imports[module]:
            if imported in module_to_file and imported not in reachable:
                queue.append(imported)

    if missing_local:
        fail("missing seeded/local modules: " + ", ".join(sorted(missing_local)))

    modules_by_directory: dict[str, set[str]] = defaultdict(set)
    for module, relative in module_to_file.items():
        if "/" in relative:
            modules_by_directory[relative.split("/", 1)[0]].add(module)

    expanded = set(declared_modules)
    for directory in declared_directories:
        if directory not in modules_by_directory:
            fail(f"directory glob has no tracked Lean files: {directory}")
        members = modules_by_directory[directory]
        unreachable = members - reachable
        if unreachable:
            fail(
                f"directory glob {directory} includes {len(unreachable)} "
                "unreachable module(s)"
            )
        expanded.update(members)

    missing = reachable - expanded
    extra = expanded - reachable
    if missing:
        fail(
            f"{len(missing)} reachable module(s) omitted; first: "
            + ", ".join(sorted(missing)[:10])
        )
    if extra:
        fail(
            f"{len(extra)} unreachable module(s) declared; first: "
            + ", ".join(sorted(extra)[:10])
        )

    print("LAKE CLOSURE AUDIT: PASS")
    print(f"tracked_modules={len(module_to_file)}")
    print(f"root_seeds={len(roots)}")
    print(f"reachable_modules={len(reachable)}")
    print(f"one_module_globs={len(declared_modules)}")
    print(f"whole_directory_globs={len(declared_directories)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
