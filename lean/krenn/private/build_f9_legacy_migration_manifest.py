#!/usr/bin/env python3
"""Build a fail-closed migration ledger for the 317 legacy f9 closures."""

from __future__ import annotations

import os
import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

KRENN_ROOT = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
sys.path.insert(0, str(KRENN_ROOT))

from audit_carrier_tree_semantics import verify_tree  # noqa: E402
from certify_carrier_tree import expand as expand_carrier_tree  # noqa: E402
from strict_certificate_checker import check_c4  # noqa: E402


ROW = re.compile(r"\[case (\d+) .*\] nodes=(\d+) .* -> CLOSED")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--log", type=Path)
    source.add_argument("--prior-manifest", type=Path)
    parser.add_argument("--artifact-root", type=Path, required=True)
    parser.add_argument("--lean-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--pilot", type=int, action="append", default=[])
    args = parser.parse_args()

    closures: dict[int, int] = {}
    prior_attached: set[int] = set()
    if args.log is not None:
        historical_log_sha256 = sha256(args.log)
        for line in args.log.read_text(encoding="utf-8").splitlines():
            match = ROW.search(line)
            if match is None:
                continue
            case, nodes = map(int, match.groups())
            if case in closures:
                raise ValueError(f"duplicate legacy closure row for case {case}")
            closures[case] = nodes
    else:
        prior = json.loads(args.prior_manifest.read_text(encoding="utf-8"))
        if prior.get("format") != "krenn-f9-legacy-migration-v1":
            raise ValueError("prior manifest has the wrong format")
        if prior.get("historical_closed_count") != 317:
            raise ValueError("prior manifest does not bind 317 historical closures")
        if prior.get("support") != [[0, 1], [0, 2], [0, 3], [0, 4], [1, 5]]:
            raise ValueError("prior manifest has the wrong support")
        prior_rows = prior.get("cases")
        if not isinstance(prior_rows, list) or len(prior_rows) != 317:
            raise ValueError("prior manifest does not contain 317 case rows")
        for row in prior_rows:
            case = row.get("case_index")
            nodes = row.get("historical_trace_nodes")
            if not isinstance(case, int) or not isinstance(nodes, int):
                raise ValueError("prior manifest has a malformed historical row")
            if case in closures:
                raise ValueError(f"duplicate prior-manifest row for case {case}")
            closures[case] = nodes
            if row.get("migration_status") == (
                "official_normalized_case_zero_sorry_lean"
            ):
                prior_attached.add(case)
        historical_log_sha256 = prior.get("historical_log_sha256")
        if not isinstance(historical_log_sha256, str) or not re.fullmatch(
            r"[0-9a-f]{64}", historical_log_sha256
        ):
            raise ValueError("prior manifest has no valid historical-log digest")
    if len(closures) != 317:
        raise ValueError(f"expected exactly 317 legacy closures, got {len(closures)}")
    requested = prior_attached | set(args.pilot)
    if requested - set(closures):
        raise ValueError("a requested pilot is not one of the 317 closed cases")

    rows: list[dict[str, object]] = []
    for case, nodes in sorted(closures.items()):
        row: dict[str, object] = {
            "case_index": case,
            "historical_trace_nodes": nodes,
            "migration_status": "pending_compact_certificate",
        }
        if case in requested:
            if case == 1:
                artifact = KRENN_ROOT / "x5_0415_trace_prototype/frozen_case1"
            else:
                artifact = args.artifact_root / f"case{case}"
            system = artifact / "system.json"
            nested_receipt_path = (
                args.lean_root / "private" /
                f"x5_case{case}_nested_reflection_receipt.json"
            )
            if nested_receipt_path.is_file():
                nested = json.loads(nested_receipt_path.read_text(encoding="utf-8"))
                if nested.get("format") != (
                    "krenn-x5-nested-tree-lean-reflection-v1"
                ) or nested.get("case") != case:
                    raise ValueError(f"case {case} nested receipt format drift")
                selected = args.lean_root / f"KrennX5Case{case}Selected.lean"
                bridge = args.lean_root / f"KrennX5Case{case}Bridge.lean"
                tree_spec = artifact / "tree_spec_v1.json"
                tree_manifest = artifact / "tree_manifest_v1.json"
                if not selected.is_file() or not bridge.is_file() or not \
                        tree_spec.is_file() or not tree_manifest.is_file():
                    raise ValueError(f"case {case} nested proof package is incomplete")
                frozen = json.loads(system.read_text(encoding="utf-8"))
                tree = json.loads(tree_manifest.read_text(encoding="utf-8"))
                verify_tree(tree_spec)
                terminal_leaves, coverage = expand_carrier_tree(tree_spec)
                if nested.get("source_system_file_sha256") != sha256(system) or \
                        nested.get("source_system_semantic_sha256") != \
                        frozen.get("system_sha256") or \
                        nested.get("tree_spec_sha256") != sha256(tree_spec) or \
                        nested.get("tree_manifest_sha256") != sha256(tree_manifest) or \
                        nested.get("selected_module_sha256") != sha256(selected) or \
                        nested.get("bridge_module_sha256") != sha256(bridge):
                    raise ValueError(f"case {case} nested proof provenance drift")
                leaves = tree.get("leaves")
                if tree.get("summary", {}).get("complete") is not True or not \
                        isinstance(leaves, list) or len(leaves) != \
                        nested.get("leaf_count") or tree.get("coverage") != coverage:
                    raise ValueError(f"case {case} nested tree coverage drift")
                for leaf_row, (tag, leaf_dir) in zip(
                    leaves, terminal_leaves, strict=True
                ):
                    certificate = leaf_dir / leaf_row.get(
                        "certificate_file", "lift.stdout"
                    )
                    leaf_system = leaf_dir / "system.json"
                    replay = check_c4(leaf_system, certificate)
                    if leaf_row.get("tag") != tag or \
                            leaf_row.get("verdict") != "strict_exact_identity" or \
                            leaf_row.get("system_file_sha256") != \
                            sha256(leaf_system) or \
                            leaf_row.get("certificate_sha256") != \
                            sha256(certificate) or \
                            leaf_row.get("strict_replay") != replay:
                        raise ValueError(
                            f"case {case} nested leaf receipt drift: {tag}"
                        )
                row.update({
                    "migration_status":
                        "official_normalized_case_zero_sorry_lean",
                    "proof_kind": "exhaustive_carrier_tree",
                    "system_file_sha256": sha256(system),
                    "system_semantic_sha256": frozen["system_sha256"],
                    "tree_manifest_sha256": sha256(tree_manifest),
                    "strict_leaf_count": len(leaves),
                    "max_multiplier_degree": max(
                        leaf["strict_replay"]["max_multiplier_degree"]
                        for leaf in leaves
                    ),
                    "selected_rows_0based": nested["root_selected_indices"],
                    "lean_selected_module_sha256": sha256(selected),
                    "lean_bridge_module_sha256": sha256(bridge),
                    "nested_reflection_receipt_sha256":
                        sha256(nested_receipt_path),
                })
                rows.append(row)
                continue
            # Rational Singular output is normalized by the separate,
            # strict-replayed denominator-clearing step.  Prefer that proof
            # object when present; otherwise use the original integer lift.
            template = artifact / "certificate_template.txt"
            normalized = artifact / "certificate_strict.txt"
            certificate = (template if template.is_file()
                           else normalized if normalized.is_file()
                           else artifact / "lift_direct/lift.stdout")
            verdict = check_c4(system, certificate)
            selected = args.lean_root / f"KrennX5Case{case}Selected.lean"
            bridge = args.lean_root / f"KrennX5Case{case}Bridge.lean"
            if not selected.is_file() or not bridge.is_file():
                raise ValueError(f"pilot {case} is missing generated Lean modules")
            row.update({
                "migration_status": "official_normalized_case_zero_sorry_lean",
                "system_file_sha256": verdict["system_file_sha256"],
                "system_semantic_sha256": json.loads(
                    system.read_text(encoding="utf-8")
                )["system_sha256"],
                "certificate_file_sha256": verdict["certificate_file_sha256"],
                "selected_rows_0based": [
                    value - 1 for value in verdict["nonzero_multiplier_indices_1based"]
                ],
                "max_multiplier_degree": verdict["max_multiplier_degree"],
                "lean_selected_module_sha256": sha256(selected),
                "lean_bridge_module_sha256": sha256(bridge),
            })
        rows.append(row)

    payload = {
        "format": "krenn-f9-legacy-migration-v1",
        "support": [[0, 1], [0, 2], [0, 3], [0, 4], [1, 5]],
        "historical_log_sha256": historical_log_sha256,
        "historical_closed_count": len(closures),
        "lean_attached_count": sum(
            row["migration_status"] == "official_normalized_case_zero_sorry_lean"
            for row in rows
        ),
        "pending_count": sum(
            row["migration_status"] == "pending_compact_certificate"
            for row in rows
        ),
        "cases": rows,
    }
    args.output.write_text(json.dumps(payload, sort_keys=True, indent=2) + "\n")
    print(json.dumps({
        "cases": len(rows),
        "lean_attached": payload["lean_attached_count"],
        "manifest_sha256": sha256(args.output),
        "pending": payload["pending_count"],
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
