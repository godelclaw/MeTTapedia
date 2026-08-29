#!/usr/bin/env python3
"""Sequentially kernel-check a generated component root connector.

The selected-tree audit establishes that a finite carrier tree has no common
zero.  This runner checks the distinct semantic attachment from the frozen
case-0 equations into that tree: normalization, tree adapter, linear root
bridge, bounded root blocks, and the final component contradiction.

It refuses to run unless the complete selected-tree audit and every generated
provenance manifest agree on the same component and frozen root-system hash.
Like the selected-tree runner, it invokes Lean one module at a time and writes
hash-bound resumable receipts.  Thus a green result means exactly one named
component connector is kernel checked; it does not claim the whole case-0
table or the Krenn theorem.
"""

from __future__ import annotations

import argparse
import json
import tempfile
from pathlib import Path
from typing import Any

from build_lean_selected_subtree_serial import LEAN_ROOT, run_module, sha256


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def read_json(path: Path, label: str) -> dict[str, Any]:
    require(path.is_file(), f"missing {label}: {path}")
    value = json.loads(path.read_text())
    require(isinstance(value, dict), f"malformed {label}: {path}")
    return value


def source_record(path: Path) -> dict[str, str]:
    require(path.is_file(), f"missing generated Lean source: {path}")
    return {
        "source": str(path.relative_to(LEAN_ROOT)),
        "source_sha256": sha256(path),
    }


def atomic_json_write(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    encoded = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    with tempfile.NamedTemporaryFile(
        mode="w", encoding="utf-8", dir=path.parent,
        prefix=path.name + ".", suffix=".tmp", delete=False,
    ) as handle:
        handle.write(encoded)
        temporary = Path(handle.name)
    temporary.replace(path)


def require_selected_tree_audit(component: int, path: Path) -> dict[str, Any]:
    """Validate the already kernel-checked selected tree and its OLean files."""
    audit = read_json(path, "selected-tree audit")
    require(audit.get("format") == "krenn-selected-subtree-serial-build-v1",
            "selected-tree audit format drift")
    scope = audit.get("scope")
    require(isinstance(scope, dict) and scope.get("component") == component,
            "selected-tree audit component mismatch")
    require(scope.get("prefix") == "root",
            "component connector requires a complete root selected tree")
    require(audit.get("mode") == "fresh-sequential-kernel-check",
            "selected-tree audit was not a fresh kernel check")
    require(audit.get("checkpoint_complete") is True,
            "selected-tree audit checkpoint is not complete")
    source_records = audit.get("source_records")
    checks = audit.get("module_checks")
    require(isinstance(source_records, list) and source_records,
            "selected-tree audit source records missing")
    require(isinstance(checks, list) and len(checks) == len(source_records),
            "selected-tree audit module coverage is incomplete")
    expected: dict[str, str] = {}
    for row in source_records:
        require(isinstance(row, dict), "selected-tree source record malformed")
        source, digest = row.get("source"), row.get("source_sha256")
        require(isinstance(source, str) and isinstance(digest, str),
                "selected-tree source record fields malformed")
        require(source not in expected, "selected-tree source record duplicated")
        path_source = LEAN_ROOT / source
        require(path_source.is_file() and sha256(path_source) == digest,
                f"selected-tree source drift: {source}")
        expected[source] = digest
    actual: set[str] = set()
    for row in checks:
        require(isinstance(row, dict), "selected-tree module check malformed")
        source, source_digest = row.get("source"), row.get("source_sha256")
        olean, olean_digest = row.get("olean"), row.get("olean_sha256")
        require(all(isinstance(x, str)
                    for x in (source, source_digest, olean, olean_digest)),
                "selected-tree module check fields malformed")
        require(source in expected and source not in actual,
                "selected-tree module check coverage malformed")
        require(expected[source] == source_digest,
                f"selected-tree source digest mismatch: {source}")
        path_olean = LEAN_ROOT / olean
        require(path_olean.is_file() and sha256(path_olean) == olean_digest,
                f"selected-tree OLean drift: {olean}")
        actual.add(source)
    require(actual == set(expected), "selected-tree module check coverage drift")
    manifest_path = Path(audit.get("selected_subtree_manifest", ""))
    require(manifest_path.is_file(), "selected-tree manifest is missing")
    require(sha256(manifest_path) == audit.get("selected_subtree_manifest_sha256"),
            "selected-tree manifest hash drift")
    manifest = read_json(manifest_path, "selected-tree manifest")
    require(manifest.get("component") == component and manifest.get("prefix") == "",
            "selected-tree manifest scope mismatch")
    return audit


def connector_sources(component: int, chunks: dict[str, Any]) -> list[Path]:
    namespace = chunks.get("namespace")
    chunk_count = chunks.get("chunk_count")
    require(isinstance(namespace, str) and isinstance(chunk_count, int) and chunk_count > 0,
            "root-chunk manifest shape malformed")
    stem = namespace.replace(".", "")
    return [
        LEAN_ROOT / f"KrennComponent{component}Normalization.lean",
        LEAN_ROOT / f"KrennComponent{component}Tree.lean",
        LEAN_ROOT / f"KrennComponent{component}RootBridge.lean",
        *(LEAN_ROOT / f"{stem}Chunk{index}.lean" for index in range(chunk_count)),
        LEAN_ROOT / f"{stem}.lean",
    ]


def provenance_context(component: int, selected_audit: Path,
                       adapter: Path, normalization: Path,
                       bridge: Path, chunks: Path) -> dict[str, str | int]:
    return {
        "component": component,
        "selected_tree_audit_sha256": sha256(selected_audit),
        "adapter_manifest_sha256": sha256(adapter),
        "normalization_manifest_sha256": sha256(normalization),
        "root_bridge_manifest_sha256": sha256(bridge),
        "root_chunks_manifest_sha256": sha256(chunks),
    }


def validated_checkpoint(path: Path, context: dict[str, str | int],
                         records: list[dict[str, str]]) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    payload = read_json(path, "root-connector checkpoint")
    require(payload.get("format") == "krenn-component-root-connector-checkpoint-v1",
            "root-connector checkpoint format drift")
    require(payload.get("context") == context,
            "root-connector checkpoint provenance drift")
    require(payload.get("source_records") == records,
            "root-connector checkpoint source drift")
    checks = payload.get("module_checks")
    require(isinstance(checks, list), "root-connector checkpoint checks malformed")
    sources = {record["source"] for record in records}
    accepted: list[dict[str, Any]] = []
    seen: set[str] = set()
    for row in checks:
        require(isinstance(row, dict), "root-connector checkpoint row malformed")
        source, olean = row.get("source"), row.get("olean")
        source_digest, olean_digest = row.get("source_sha256"), row.get("olean_sha256")
        require(all(isinstance(x, str)
                    for x in (source, olean, source_digest, olean_digest)),
                "root-connector checkpoint fields malformed")
        require(source in sources and source not in seen,
                "root-connector checkpoint coverage malformed")
        seen.add(source)
        if sha256(LEAN_ROOT / source) != source_digest:
            raise RuntimeError(f"root-connector checkpoint source hash drift: {source}")
        path_olean = LEAN_ROOT / olean
        if path_olean.is_file() and sha256(path_olean) == olean_digest:
            accepted.append(row)
    return accepted


def write_checkpoint(path: Path, context: dict[str, str | int],
                     records: list[dict[str, str]], checks: list[dict[str, Any]],
                     complete: bool) -> None:
    atomic_json_write(path, {
        "format": "krenn-component-root-connector-checkpoint-v1",
        "context": context,
        "source_records": records,
        "module_checks": checks,
        "complete": complete,
    })


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("component", type=int)
    parser.add_argument("--selected-tree-audit", type=Path, required=True)
    parser.add_argument("--tree-adapter", type=Path, required=True)
    parser.add_argument("--normalization", type=Path, required=True)
    parser.add_argument("--root-bridge", type=Path, required=True)
    parser.add_argument("--root-chunks", type=Path, required=True)
    parser.add_argument("--build", action="store_true")
    parser.add_argument("--timeout-seconds", type=int, default=120)
    parser.add_argument("--checkpoint", type=Path)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    require(args.component > 0, "component must be positive")
    require(args.timeout_seconds > 0, "timeout must be positive")
    selected_path = args.selected_tree_audit.resolve()
    adapter_path = args.tree_adapter.resolve()
    normalization_path = args.normalization.resolve()
    bridge_path = args.root_bridge.resolve()
    chunks_path = args.root_chunks.resolve()
    selected = require_selected_tree_audit(args.component, selected_path)
    adapter = read_json(adapter_path, "tree-adapter manifest")
    normalization = read_json(normalization_path, "normalization manifest")
    bridge = read_json(bridge_path, "root-bridge manifest")
    chunks = read_json(chunks_path, "root-chunk manifest")
    require(adapter.get("format") == "krenn-selected-tree-adapter-export-v1"
            and adapter.get("component") == args.component,
            "tree-adapter manifest mismatch")
    require(normalization.get("format") == "krenn-component-normalization-export-v2"
            and normalization.get("external_component_index") == args.component
            and normalization.get("lean_component_index") == args.component - 1,
            "normalization manifest component mismatch")
    require(bridge.get("format") == "krenn-component-root-bridge-export-v2"
            and bridge.get("external_component_index") == args.component,
            "root-bridge manifest component mismatch")
    require(chunks.get("format") == "krenn-component-root-chunks-export-v2"
            and chunks.get("external_component_index") == args.component,
            "root-chunk manifest component mismatch")
    root_hash = selected.get("root_system_file_sha256")
    require(isinstance(root_hash, str), "selected-tree root hash missing")
    require(adapter.get("root_system_file_sha256") == root_hash,
            "tree-adapter/root-system hash mismatch")
    require(chunks.get("reduced_component_file_sha256") == root_hash,
            "root-chunk/root-system hash mismatch")
    selected_manifest_path = Path(selected["selected_subtree_manifest"])
    selected_manifest = read_json(selected_manifest_path, "selected-tree manifest")
    require(adapter.get("selected_manifest_sha256") == sha256(selected_manifest_path),
            "tree-adapter/selected-manifest hash mismatch")
    require(adapter.get("selected_wrapper_sha256")
            == selected_manifest.get("wrapper_sha256"),
            "tree-adapter/selected-wrapper hash mismatch")
    require(normalization.get("raw_generators") == bridge.get("raw_generators"),
            "normalization/root-bridge raw-generator count mismatch")
    expected_tree_module = f"KrennComponent{args.component}Tree"
    expected_tree_namespace = f"Krenn.Component{args.component}.Tree"
    expected_normalization_namespace = f"Krenn.Component{args.component}Normalization"
    expected_bridge_namespace = f"Krenn.Component{args.component}RootBridge"
    expected_chunk_namespace = f"Krenn.Component{args.component}RootCommonZero"
    require(chunks.get("tree_module") == expected_tree_module
            and chunks.get("tree_namespace") == expected_tree_namespace,
            "root-chunk/tree namespace mismatch")
    require(chunks.get("normalization_namespace") == expected_normalization_namespace
            and chunks.get("bridge_namespace") == expected_bridge_namespace
            and chunks.get("namespace") == expected_chunk_namespace,
            "root-chunk connector namespace mismatch")
    sources = connector_sources(args.component, chunks)
    records = [source_record(path) for path in sources]
    context = provenance_context(args.component, selected_path, adapter_path,
                                 normalization_path, bridge_path, chunks_path)
    result: dict[str, Any] = {
        "format": "krenn-component-root-connector-serial-build-v1",
        "scope": {
            "component": args.component,
            "claim": "only this hash-bound root connector",
        },
        "context": context,
        "selected_tree_scope": selected["scope"],
        "source_records": records,
        "mode": "source-audit-only",
    }
    if args.build:
        checkpoint = args.checkpoint.resolve() if args.checkpoint is not None else None
        checks = (validated_checkpoint(checkpoint, context, records)
                  if checkpoint is not None else [])
        checked_sources = {row["source"] for row in checks}
        fresh: list[dict[str, Any]] = []
        if checkpoint is not None:
            write_checkpoint(checkpoint, context, records, checks, False)
        for source in sources:
            relative = str(source.relative_to(LEAN_ROOT))
            if relative in checked_sources:
                print(f"reusing {relative}", flush=True)
                continue
            print(f"checking {relative}", flush=True)
            row = run_module(args.component, source, args.timeout_seconds)
            checks.append(row)
            fresh.append(row)
            if checkpoint is not None:
                write_checkpoint(checkpoint, context, records, checks, False)
        if checkpoint is not None:
            write_checkpoint(checkpoint, context, records, checks, True)
        result.update({
            "mode": "fresh-sequential-kernel-check",
            "module_checks": checks,
            "fresh_module_count": len(fresh),
            "reused_module_count": len(checks) - len(fresh),
            "fresh_elapsed_seconds": round(
                sum(float(row["elapsed_seconds"]) for row in fresh), 3),
            "complete_check_elapsed_seconds": round(
                sum(float(row["elapsed_seconds"]) for row in checks), 3),
            "checkpoint": str(checkpoint) if checkpoint is not None else None,
            "checkpoint_complete": checkpoint is not None,
        })
    encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.receipt is not None:
        receipt = args.receipt.resolve()
        receipt.parent.mkdir(parents=True, exist_ok=True)
        receipt.write_text(encoded)
        print(f"wrote {receipt}")
    print(encoded, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
