#!/usr/bin/env python3
"""Regenerate the Lean module that makes every manuscript citation a build obligation.

A ``\\Sverified{Fully.Qualified.Name}`` marker in the manuscripts asserts that
a declaration is machine-checked.  Nothing enforced that.  The lane's build
gate was a hand-maintained import list, the manuscripts grew their own way, and
the two drifted: at the time this script was written, 242 directly cited
modules were outside every declared build target, so the markers could not
have been falsified by a build failure.

This script closes that gap mechanically.  It harvests the markers, resolves
each to the module that declares it, reduces the result to a minimal antichain
under the import relation, and writes that as the import list of a single
generated Lean module.  The lane aggregator imports it, so a green lane build
now means exactly: every declaration the manuscripts call verified elaborates.

Usage:
    gen_citation_ledger.py            rewrite the ledger
    gen_citation_ledger.py --check    exit 1 if the ledger is stale
"""

from __future__ import annotations

import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
TEX_ROOT = os.path.join(REPO, "papers", "benxiv")
LEAN_ROOT = os.path.join(REPO, "lean", "mettapedia")
LEDGER = os.path.join(
    LEAN_ROOT, "Mettapedia", "GraphTheory", "FourColor", "CitationLedger.lean"
)
LEDGER_MODULE = "Mettapedia.GraphTheory.FourColor.CitationLedger"
AGGREGATOR = "Mettapedia.GraphTheory.FourColor"

MARKER = re.compile(r"\\Sverified\{([^}]+)\}")
DECL = r"(?:theorem|lemma|def|abbrev|instance|structure|inductive)"


def harvest_markers() -> set[str]:
    names: set[str] = set()
    for dirpath, _dirnames, filenames in os.walk(TEX_ROOT):
        for name in filenames:
            if not name.endswith(".tex"):
                continue
            with open(os.path.join(dirpath, name), encoding="utf-8") as handle:
                names.update(MARKER.findall(handle.read()))
    return names


def read_imports() -> dict[str, list[str]]:
    """Map every module in the Lean tree to the modules it imports."""
    graph: dict[str, list[str]] = {}

    def add(path: str, module: str) -> None:
        with open(path, encoding="utf-8") as handle:
            graph[module] = [
                line.split()[1]
                for line in handle
                if line.strip().startswith("import ")
            ]

    root = os.path.join(LEAN_ROOT, "Mettapedia.lean")
    if os.path.exists(root):
        add(root, "Mettapedia")
    for dirpath, _dirnames, filenames in os.walk(os.path.join(LEAN_ROOT, "Mettapedia")):
        for name in filenames:
            if not name.endswith(".lean"):
                continue
            path = os.path.join(dirpath, name)
            module = os.path.relpath(path, LEAN_ROOT)[: -len(".lean")].replace(os.sep, ".")
            add(path, module)
    return graph


DECL_LINE = re.compile(
    rf"^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
    rf"{DECL}\s+([A-Za-z_][A-Za-z0-9_'.!?]*)",
    re.MULTILINE,
)


def declaration_index(graph: dict[str, list[str]]) -> dict[str, set[str]]:
    """Map each declared short name to the modules declaring it.

    A prefix match on the marker is not enough on its own: `Mettapedia` is
    itself a module, so a marker naming a declaration in a namespace that has
    no module of its own would otherwise resolve to the whole library root and
    drag every target into this lane.  Resolution therefore always confirms
    that the chosen module actually declares the name.
    """
    index: dict[str, set[str]] = {}
    for module in graph:
        path = os.path.join(LEAN_ROOT, module.replace(".", os.sep) + ".lean")
        if not os.path.exists(path):
            continue
        with open(path, encoding="utf-8") as handle:
            for declared in DECL_LINE.findall(handle.read()):
                index.setdefault(declared.split(".")[-1], set()).add(module)
    return index


def resolve(name: str, modules: set[str], index: dict[str, set[str]]) -> str | None:
    """Find the module declaring `name`."""
    parts = name.split(".")
    short = parts[-1]
    candidates = index.get(short, set())
    if not candidates:
        return None
    # Prefer the module whose path is the longest prefix of the marker.
    for cut in range(len(parts) - 1, 0, -1):
        candidate = ".".join(parts[:cut])
        if candidate in candidates:
            return candidate
    if len(candidates) == 1:
        return next(iter(candidates))
    # Ambiguous short name: take the declaring module sharing the most leading
    # components with the marker, breaking remaining ties by module path.
    def agreement(module: str) -> tuple[int, str]:
        own = module.split(".")
        shared = 0
        for a, b in zip(own, parts):
            if a != b:
                break
            shared += 1
        return (shared, module)

    return max(sorted(candidates), key=agreement)


def reachable(module: str, graph: dict[str, list[str]]) -> set[str]:
    seen: set[str] = set()
    stack = list(graph.get(module, []))
    while stack:
        current = stack.pop()
        if current in seen:
            continue
        seen.add(current)
        stack.extend(d for d in graph.get(current, []) if d not in seen)
    return seen


def minimal_antichain(wanted: set[str], graph: dict[str, list[str]]) -> list[str]:
    """Drop every module already implied by another wanted module."""
    covered: set[str] = set()
    for module in wanted:
        covered |= reachable(module, graph)
    return sorted(m for m in wanted if m not in covered)


def render(entries: list[str], unresolved: list[str]) -> str:
    body = "".join(f"import {m}\n" for m in entries)
    tail = """
/-!
# Citation ledger

Generated by `papers/benxiv/tools/gen_citation_ledger.py`.  Do not edit by hand.

Every `\\Sverified` marker in the manuscripts asserts that a declaration is
machine-checked.  This module imports, transitively, every module that declares
one, so that a green build of the Four-Colour lane is the same event as every
one of those assertions elaborating.  Without it the markers were unfalsifiable:
the lane's build gate and the manuscripts' citation set were maintained
separately and had drifted apart by hundreds of modules.

Adding a marker to a manuscript therefore adds a build obligation here.  Run
the generator to pick it up; run it with `--check` to detect drift.
-/
"""
    if unresolved:
        tail += "\n-- Markers that resolve to no module in this tree:\n"
        tail += "".join(f"--   {name}\n" for name in unresolved)
    return body + tail


def main() -> int:
    check = "--check" in sys.argv
    graph = read_imports()
    modules = set(graph)
    index = declaration_index(graph)

    cited: set[str] = set()
    unresolved: list[str] = []
    for name in sorted(harvest_markers()):
        module = resolve(name, modules, index)
        if module is None:
            unresolved.append(name)
        else:
            cited.add(module)

    # The ledger must not import the aggregator that imports it.
    cited.discard(AGGREGATOR)
    cited.discard(LEDGER_MODULE)

    entries = minimal_antichain(cited, graph)
    text = render(entries, unresolved)

    current = ""
    if os.path.exists(LEDGER):
        with open(LEDGER, encoding="utf-8") as handle:
            current = handle.read()

    if check:
        if current != text:
            print("citation ledger is stale; run gen_citation_ledger.py", file=sys.stderr)
            return 1
        print(f"citation ledger current: {len(entries)} imports covering {len(cited)} cited modules")
        return 0

    with open(LEDGER, "w", encoding="utf-8") as handle:
        handle.write(text)
    print(f"wrote {len(entries)} imports covering {len(cited)} cited modules")
    if unresolved:
        print(f"{len(unresolved)} markers resolve to no module", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
