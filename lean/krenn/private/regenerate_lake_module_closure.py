#!/usr/bin/env python3
"""Regenerate the Krenn Lake module manifest from the tracked import closure.

``audit_lake_module_closure.py`` fails closed when ``lakefile.lean``'s declared
closure drifts from the real import closure of the declared roots.  This program
is its inverse: it recomputes that closure from the same tracked source bytes
and rewrites the two manifest declarations, compressing to a whole-directory
glob exactly where every tracked module in the directory is reachable.

Run it after adding or removing a root, then re-run the auditor.
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
PER_LINE = 4

IMPORT_RE = re.compile(
    r"\s*(?:(?:public|private)\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.]+)"
)


def fail(message: str) -> NoReturn:
    raise SystemExit("LAKE CLOSURE REGEN FAILED: " + message)


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
    return path[:-5].replace("/", ".")


def quoted_names(body: str) -> set[str]:
    return set(re.findall(r"`([A-Za-z0-9_.]+)", body))


def render(names: list[str], indent: str = "    ") -> str:
    lines = []
    for start in range(0, len(names), PER_LINE):
        chunk = names[start : start + PER_LINE]
        lines.append(indent + ", ".join("`" + name for name in chunk) + ",")
    if lines:
        lines[-1] = lines[-1][:-1] + "]"
    else:
        lines.append(indent + "]")
    return "\n".join(lines)


def main() -> int:
    files = tracked_lean_files()
    module_to_file = {module_name(path): path for path in files}
    source = LAKEFILE.read_text(encoding="utf-8")

    roots_body = source.split("def krennRoots", 1)[1].split(
        "def krennClosureModules", 1
    )[0]
    roots = quoted_names(roots_body)

    imports: dict[str, list[str]] = {}
    for module, relative in module_to_file.items():
        found: list[str] = []
        for line in (ROOT / relative).read_text(encoding="utf-8").splitlines():
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

    directories = sorted(
        directory
        for directory, members in modules_by_directory.items()
        if members and members <= reachable
    )
    covered: set[str] = set()
    for directory in directories:
        covered |= modules_by_directory[directory]
    singles = sorted(reachable - covered)

    new_modules = "def krennClosureModules : Array Lean.Name := #[\n" + render(singles) + "\n\n"
    new_directories = "def krennClosureDirectories : Array Lean.Name := #[\n" + render(
        directories
    ) + "\n\n"

    head, rest = source.split("def krennClosureModules", 1)
    _, rest = rest.split("def krennClosureDirectories", 1)
    _, tail = rest.split("@[default_target]", 1)
    LAKEFILE.write_text(
        head + new_modules + new_directories + "@[default_target]" + tail,
        encoding="utf-8",
    )

    print("LAKE CLOSURE REGEN: OK")
    print(f"root_seeds={len(roots)}")
    print(f"reachable_modules={len(reachable)}")
    print(f"one_module_globs={len(singles)}")
    print(f"whole_directory_globs={len(directories)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
