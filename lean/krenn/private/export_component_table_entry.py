#!/usr/bin/env python3
"""Emit one provenance-bound Lean entry for the all-collapse component table.

The component root connector is checked separately before this script is
allowed to emit a table entry.  The generated Lean theorem is deliberately
tiny: it transports that named connector to the corresponding ``Fin 67``
slot.  The JSON receipt binds the emitted wrapper to the fresh connector
audit and to the source and olean it audited.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


HERE = Path(__file__).resolve()
LEAN_ROOT = HERE.parents[1]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def read_json(path: Path, label: str) -> dict[str, Any]:
    require(path.is_file(), f"missing {label}: {path}")
    value = json.loads(path.read_text())
    require(isinstance(value, dict), f"malformed {label}: {path}")
    return value


def validate_root_connector_audit(component: int, audit_path: Path) -> dict[str, str]:
    audit = read_json(audit_path, "root-connector audit")
    require(audit.get("format") == "krenn-component-root-connector-serial-build-v1",
            "root-connector audit format drift")
    scope = audit.get("scope")
    require(isinstance(scope, dict) and scope.get("component") == component,
            "root-connector audit component mismatch")
    require(audit.get("mode") == "fresh-sequential-kernel-check",
            "root-connector audit was not a fresh kernel check")
    require(audit.get("checkpoint_complete") is True,
            "root-connector audit is incomplete")

    expected_source = f"KrennComponent{component}RootCommonZero.lean"
    source_path = LEAN_ROOT / expected_source
    require(source_path.is_file(), "root common-zero source is absent")
    source_sha = sha256(source_path)

    source_records = audit.get("source_records")
    checks = audit.get("module_checks")
    require(isinstance(source_records, list) and isinstance(checks, list),
            "root-connector audit lacks source/module records")
    require(len(source_records) == len(checks) and source_records,
            "root-connector audit module coverage is incomplete")
    expected: dict[str, str] = {}
    for row in source_records:
        require(isinstance(row, dict), "root-connector source record is malformed")
        source, digest = row.get("source"), row.get("source_sha256")
        require(isinstance(source, str) and isinstance(digest, str)
                and source not in expected,
                "root-connector source record fields are malformed")
        source_file = LEAN_ROOT / source
        require(source_file.is_file() and sha256(source_file) == digest,
                f"root-connector source drift: {source}")
        expected[source] = digest
    checked: dict[str, dict[str, Any]] = {}
    for row in checks:
        require(isinstance(row, dict), "root-connector module check is malformed")
        source, digest = row.get("source"), row.get("source_sha256")
        olean_text, olean_sha = row.get("olean"), row.get("olean_sha256")
        require(all(isinstance(value, str)
                    for value in (source, digest, olean_text, olean_sha))
                and source in expected and source not in checked
                and expected[source] == digest,
                "root-connector module check fields are malformed")
        olean_path = LEAN_ROOT / olean_text
        require(olean_path.is_file() and sha256(olean_path) == olean_sha,
                f"root-connector olean drift: {source}")
        checked[source] = row
    require(set(checked) == set(expected),
            "root-connector module check coverage drift")
    require(expected.get(expected_source) == source_sha,
            "root common-zero source hash is not covered by the audit")
    check = checked[expected_source]
    olean_text = check["olean"]
    olean_sha = check["olean_sha256"]
    return {
        "root_source": expected_source,
        "root_source_sha256": source_sha,
        "root_olean": olean_text,
        "root_olean_sha256": olean_sha,
    }


def render(component: int) -> str:
    lean_index = component - 1
    namespace = "Krenn.FrozenCase0AllCollapseAssembly"
    root_namespace = f"Krenn.Component{component}RootCommonZero"
    theorem = f"component{component}_refutes_selected"
    return "\n".join([
        "import KrennAllCollapseAssembly",
        f"import KrennComponent{component}RootCommonZero",
        "",
        "/-! A provenance-bound concrete entry in the all-collapse table. -/",
        "",
        f"namespace {namespace}",
        "",
        "open Krenn.CollapseReductionReflection",
        "open Krenn.CollapseComponentContainment",
        "open Krenn.CollapseComponentContainmentData",
        "",
        f"/-- External component {component} occupies zero-based table slot {lean_index}. -/",
        f"theorem {theorem}",
        "    {R : Type*} [Field R] [CharZero R] :",
        f"    RefutesSelectedComponent (R := R) ({lean_index} : Fin 67) := by",
        "  intro full base selectedVanish",
        f"  exact {root_namespace}.no_base_common_zero_on_component{component}",
        "    full base selectedVanish",
        "",
        f"end {namespace}",
        "",
        f"#print axioms {namespace}.{theorem}",
        "",
    ])


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("component", type=int)
    parser.add_argument("root_connector_audit", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--receipt", type=Path, required=True)
    args = parser.parse_args()
    require(1 <= args.component <= 67,
            "external component must lie in the 67-entry table")

    audit_path = args.root_connector_audit.resolve()
    validated = validate_root_connector_audit(args.component, audit_path)
    output = args.output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(render(args.component))
    receipt = {
        "format": "krenn-component-table-entry-export-v1",
        "component": args.component,
        "lean_table_index": args.component - 1,
        "root_connector_audit": str(audit_path),
        "root_connector_audit_sha256": sha256(audit_path),
        "output": str(output),
        "output_sha256": sha256(output),
        **validated,
    }
    receipt_path = args.receipt.resolve()
    receipt_path.parent.mkdir(parents=True, exist_ok=True)
    receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps(receipt, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
