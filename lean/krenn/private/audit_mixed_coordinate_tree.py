#!/usr/bin/env python3
"""Fail-closed audit of a mixed-arity frozen coordinate tree.

Each inventory may split any positive number of distinct coordinates, hence
has exactly ``2^n`` branches.  Refinements are keyed by dotted branch tags.
Every terminal system is hash-checked, and any available strict certificate
is replayed against that terminal system.  Missing leaves remain explicitly
open; an incomplete tree never receives a complete verdict.
"""

from __future__ import annotations

import os
import argparse
import hashlib
import itertools
import json
import sys
from pathlib import Path

KRENN_ROOT = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
sys.path.insert(0, str(KRENN_ROOT))

from strict_certificate_checker import check_c4  # noqa: E402


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def resolve(base: Path, value: str) -> Path:
    path = Path(value)
    return path.resolve() if path.is_absolute() else (base / path).resolve()


def verify_inventory(path: Path, parent_sha256: str) -> list[Path]:
    inventory_path = path / "inventory.json"
    value = load(inventory_path)
    coordinates = value.get("coordinates")
    rows = value.get("branches")
    if value.get("format") != "krenn-frozen-coordinate-branch-inventory-v1":
        raise RuntimeError(f"unsupported inventory: {inventory_path}")
    if not isinstance(coordinates, list) or not coordinates or not all(
        isinstance(item, str) for item in coordinates
    ) or len(coordinates) != len(set(coordinates)):
        raise RuntimeError(f"invalid coordinate list: {inventory_path}")
    expected_bits = [
        list(bits) for bits in itertools.product((0, 1), repeat=len(coordinates))
    ]
    if value.get("branch_count") != len(expected_bits) or not isinstance(
        rows, list
    ) or len(rows) != len(expected_bits):
        raise RuntimeError(f"branch count is not 2^n: {inventory_path}")
    if value.get("source_system_file_sha256") != parent_sha256:
        raise RuntimeError(f"inventory is not bound to its parent: {inventory_path}")
    if [row.get("branch") for row in rows] != list(range(len(rows))):
        raise RuntimeError(f"branch numbering drift: {inventory_path}")
    if [row.get("nonzero_bits") for row in rows] != expected_bits:
        raise RuntimeError(f"branch patterns are not exhaustive: {inventory_path}")
    systems: list[Path] = []
    for row in rows:
        system = path / f"branch_{row['branch']}" / "system.json"
        if sha256(system) != row.get("system_file_sha256"):
            raise RuntimeError(f"branch file hash drift: {system}")
        if load(system).get("system_sha256") != row.get("system_sha256"):
            raise RuntimeError(f"branch semantic hash drift: {system}")
        systems.append(system)
    return systems


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("spec", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    spec_path = args.spec.resolve()
    spec = load(spec_path)
    if spec.get("format") != "krenn-mixed-coordinate-tree-spec-v1":
        raise RuntimeError("unsupported mixed-coordinate tree spec")
    base = spec_path.parent
    source = resolve(base, spec["source_system"])
    root = resolve(base, spec["root_inventory"])
    refinements = spec.get("refinements")
    if not isinstance(refinements, dict):
        raise RuntimeError("refinements must be an object")

    roots = verify_inventory(root, sha256(source))
    leaves = [(f"b{index}", system) for index, system in enumerate(roots)]
    applied: set[str] = set()
    inventories = {"root": sha256(root / "inventory.json")}
    while True:
        changed = False
        next_leaves: list[tuple[str, Path]] = []
        for tag, system in leaves:
            raw_child = refinements.get(tag)
            if raw_child is None:
                next_leaves.append((tag, system))
                continue
            if tag in applied:
                raise RuntimeError(f"refinement cycle at {tag}")
            child = resolve(base, raw_child)
            children = verify_inventory(child, sha256(system))
            inventories[tag] = sha256(child / "inventory.json")
            applied.add(tag)
            next_leaves.extend(
                (f"{tag}.{index}", child_system)
                for index, child_system in enumerate(children)
            )
            changed = True
        leaves = next_leaves
        if not changed:
            break
    if applied != set(refinements):
        raise RuntimeError("refinement map contains unreachable tags")

    rows = []
    for tag, system in leaves:
        leaf = system.parent
        row: dict[str, object] = {
            "tag": tag,
            "system_file_sha256": sha256(system),
            "system_semantic_sha256": load(system).get("system_sha256"),
            "verdict": "open_no_strict_certificate",
        }
        for candidate in (
            leaf / "lift.renamed.stdout",
            leaf / "lift.stdout",
            leaf / "native30/lift.stdout",
        ):
            if not candidate.is_file():
                continue
            try:
                replay = check_c4(system, candidate)
            except Exception:
                continue
            row.update({
                "verdict": "strict_exact_identity",
                "certificate": str(candidate.relative_to(base)),
                "certificate_sha256": sha256(candidate),
                "strict_replay": replay,
            })
            break
        rows.append(row)
    closed = sum(row["verdict"] == "strict_exact_identity" for row in rows)
    payload = {
        "format": "krenn-mixed-coordinate-tree-audit-v1",
        "spec_sha256": sha256(spec_path),
        "source_system_file_sha256": sha256(source),
        "inventory_sha256": inventories,
        "refinement_count": len(applied),
        "leaves": rows,
        "summary": {
            "terminal_leaf_count": len(rows),
            "strict_exact_identities": closed,
            "open_leaf_count": len(rows) - closed,
            "complete": closed == len(rows),
        },
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(payload["summary"], sort_keys=True))
    print("manifest_sha256=" + sha256(args.output))
    return 0 if payload["summary"]["complete"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
