#!/usr/bin/env python3
"""Seed a full selected-tree build checkpoint from disjoint checked subtrees.

The full-tree serial importer is intentionally conservative: a checkpoint
must name every generated source and every matching `.olean`.  This helper
can reuse prior fresh checks of disjoint subtrees only after proving that they
belong to the same complete frozen tree and have exactly the same generated
source and object hashes.  It never treats an audit receipt as a proof of a
different root wrapper.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from build_lean_selected_subtree_serial import (
    LEAN_ROOT,
    atomic_json_write,
    lean_source,
    sha256,
    subtree_source,
)


def source_record(path: Path) -> dict[str, str]:
    if not path.is_file():
        raise RuntimeError(f"missing generated Lean source: {path}")
    return {"source": str(path.relative_to(LEAN_ROOT)), "source_sha256": sha256(path)}


def same_checked_object(left: dict[str, object], right: dict[str, object]) -> bool:
    """Compare the provenance-bearing portion of two module checks.

    Independent serial audits naturally record different wall-clock durations
    for the shared root module.  Duration is diagnostic metadata, not proof
    provenance: accepting a reused object must depend only on the exact
    source and compiled-object bindings.  Keep this comparison deliberately
    narrow and explicit so a changed source or `.olean` can never be merged
    merely because the module path happens to agree.
    """
    fields = ("source", "source_sha256", "olean", "olean_sha256")
    return all(left.get(field) == right.get(field) for field in fields)


def required_sources(component: int, full_manifest: dict) -> list[Path]:
    tags = full_manifest.get("terminal_leaves")
    if not isinstance(tags, list) or not tags or not all(isinstance(tag, str) for tag in tags):
        raise RuntimeError("full manifest terminal leaves malformed")
    return [
        lean_source(component, "Root"),
        *(lean_source(component, "SelectedLeaf", tag) for tag in tags),
        *(lean_source(component, "SelectedBridge", tag) for tag in tags),
        subtree_source(component, ""),
    ]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("component", type=int)
    parser.add_argument("full_manifest", type=Path)
    parser.add_argument("checkpoint", type=Path)
    parser.add_argument("subtree_audits", nargs="+", type=Path)
    args = parser.parse_args()

    full_manifest_path = args.full_manifest.resolve()
    full_manifest = json.loads(full_manifest_path.read_text())
    if full_manifest.get("format") != "krenn-selected-subtree-export-v1":
        raise RuntimeError("full manifest format drift")
    if full_manifest.get("component") != args.component or full_manifest.get("prefix") != "":
        raise RuntimeError("full manifest is not the requested component root")
    source_paths = required_sources(args.component, full_manifest)
    records = [source_record(path) for path in source_paths]
    records_by_name = {record["source"]: record for record in records}
    if len(records_by_name) != len(records):
        raise RuntimeError("full generated source list contains a duplicate")
    full_manifest_sha256 = sha256(full_manifest_path)

    checks_by_source: dict[str, dict[str, object]] = {}
    audit_summaries = []
    for audit_path_arg in args.subtree_audits:
        audit_path = audit_path_arg.resolve()
        audit = json.loads(audit_path.read_text())
        if audit.get("format") != "krenn-selected-subtree-serial-build-v1":
            raise RuntimeError(f"subtree audit format drift: {audit_path}")
        if audit.get("mode") != "fresh-sequential-kernel-check":
            raise RuntimeError(f"subtree audit is not a completed fresh check: {audit_path}")
        scope = audit.get("scope", {})
        if scope.get("component") != args.component:
            raise RuntimeError(f"subtree audit component mismatch: {audit_path}")
        if audit.get("tree_manifest_sha256") != full_manifest.get("manifest_sha256"):
            raise RuntimeError(f"subtree audit tree-manifest mismatch: {audit_path}")
        if audit.get("root_system_file_sha256") != full_manifest.get("root_system_file_sha256"):
            raise RuntimeError(f"subtree audit root-source mismatch: {audit_path}")
        module_checks = audit.get("module_checks")
        if not isinstance(module_checks, list) or not module_checks:
            raise RuntimeError(f"subtree audit has no module checks: {audit_path}")
        accepted = 0
        for check in module_checks:
            if not isinstance(check, dict):
                raise RuntimeError(f"malformed module check: {audit_path}")
            source = check.get("source")
            source_sha = check.get("source_sha256")
            olean = check.get("olean")
            olean_sha = check.get("olean_sha256")
            if not all(isinstance(item, str) for item in (source, source_sha, olean, olean_sha)):
                raise RuntimeError(f"malformed module check fields: {audit_path}")
            # A subtree wrapper is intentionally *not* inherited by the
            # full-root wrapper.  Leaves and their bridges are.
            if source not in records_by_name:
                if source.startswith(f"KrennComponent{args.component}/SelectedSubtree"):
                    continue
                raise RuntimeError(f"subtree check not a source of the full tree: {source}")
            if records_by_name[source]["source_sha256"] != source_sha:
                raise RuntimeError(f"generated source hash mismatch for {source}")
            olean_path = LEAN_ROOT / olean
            if not olean_path.is_file() or sha256(olean_path) != olean_sha:
                raise RuntimeError(f"checked object missing or drifted for {source}")
            prior = checks_by_source.get(source)
            if prior is not None:
                if not same_checked_object(prior, check):
                    raise RuntimeError(f"incompatible duplicate subtree check for {source}")
            else:
                checks_by_source[source] = check
                accepted += 1
        audit_summaries.append({
            "audit": str(audit_path),
            "audit_sha256": sha256(audit_path),
            "accepted_module_checks": accepted,
        })

    if not checks_by_source:
        raise RuntimeError("no reusable full-tree modules were proven")
    ordered_checks = [checks_by_source[record["source"]]
                      for record in records if record["source"] in checks_by_source]
    payload = {
        "format": "krenn-selected-subtree-build-checkpoint-v1",
        "manifest_sha256": full_manifest_sha256,
        "source_records": records,
        "module_checks": ordered_checks,
        "complete": len(ordered_checks) == len(records),
        "seed": {
            "format": "krenn-selected-subtree-checkpoint-seed-v1",
            "full_manifest": str(full_manifest_path),
            "full_manifest_sha256": full_manifest_sha256,
            "subtree_audits": audit_summaries,
        },
    }
    atomic_json_write(args.checkpoint.resolve(), payload)
    print(json.dumps({
        "component": args.component,
        "full_source_count": len(records),
        "reused_module_count": len(ordered_checks),
        "remaining_module_count": len(records) - len(ordered_checks),
        "checkpoint": str(args.checkpoint.resolve()),
        "checkpoint_sha256": sha256(args.checkpoint.resolve()),
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
