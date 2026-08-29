#!/usr/bin/env python3
"""Expose a complete selected-row tree through the standard component-tree API.

The selected-row exporter keeps a shared root module and proves one recursive
tree wrapper over its terminal certificates.  The older semantic connector
expects a ``Krenn.ComponentN.Tree`` namespace containing the root equations,
their common-zero predicate, and one component contradiction.  This exporter
constructs that tiny adapter only after binding it to a complete selected-root
receipt and the exact frozen root system.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


HERE = Path(__file__).resolve()
LEAN_ROOT = HERE.parents[1]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("case_root", type=Path)
    parser.add_argument("component", type=int)
    parser.add_argument("selected_manifest", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()

    require(args.component > 0, "component index must be positive")
    case_root = args.case_root.resolve()
    manifest_path = args.selected_manifest.resolve()
    require(manifest_path.is_file(), "selected-tree receipt is absent")
    manifest = json.loads(manifest_path.read_text())
    require(manifest.get("format") == "krenn-selected-subtree-export-v1",
            "selected-tree receipt format drift")
    require(manifest.get("component") == args.component,
            "selected-tree receipt component mismatch")
    require(manifest.get("prefix") == "",
            "adapter requires the complete selected root, not a subtree")

    wrapper = LEAN_ROOT / f"KrennComponent{args.component}" / "SelectedSubtreeROOT.lean"
    require(str(wrapper) == manifest.get("wrapper"), "selected wrapper path drift")
    require(wrapper.is_file(), "selected wrapper is absent")
    require(sha256(wrapper) == manifest.get("wrapper_sha256"),
            "selected wrapper hash drift")

    spec_path = case_root / f"component{args.component:02d}_tree_spec.json"
    require(spec_path.is_file(), "component tree specification is absent")
    spec = json.loads(spec_path.read_text())
    shared_root = case_root.parents[1]
    source_path = Path(spec["source_system"])
    if not source_path.is_absolute():
        source_path = shared_root / source_path
    source_path = source_path.resolve()
    source = json.loads(source_path.read_text())
    require(sha256(source_path) == manifest.get("root_system_file_sha256"),
            "selected-tree receipt/root-system hash mismatch")
    variables = source.get("variables")
    equations = source.get("equations")
    require(isinstance(variables, list) and isinstance(equations, list),
            "frozen root system lacks variables or equations")

    namespace = f"Krenn.Component{args.component}.Tree"
    selected_namespace = f"Krenn.Component{args.component}.SelectedSubtreeROOT"
    lines = [
        f"import KrennComponent{args.component}.Root",
        f"import KrennComponent{args.component}.SelectedSubtreeROOT",
        "",
        "/-! A provenance-bound adapter from the complete selected-row tree to",
        "the common component-tree interface used by the semantic connector. -/",
        "",
        f"namespace {namespace}",
        "",
        f"abbrev rootEquations := Krenn.Component{args.component}.Root.rootEquations",
        f"abbrev RootCommonZero {{R : Type*}} [CommRing R]",
        f"    (values : Fin {len(variables)} → R) : Prop :=",
        f"  Krenn.Component{args.component}.Root.RootCommonZero values",
        "",
        f"theorem component{args.component}HasNoCommonZero {{R : Type*}} [Field R] [CharZero R]",
        f"    (values : Fin {len(variables)} → R) (rootZero : RootCommonZero values) : False := by",
        f"  exact {selected_namespace}.subtreeROOTImpossible values rootZero",
        "",
        f"end {namespace}",
        "",
        f"#print axioms {namespace}.component{args.component}HasNoCommonZero",
        "",
    ]
    output = args.output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n".join(lines))
    receipt = {
        "format": "krenn-selected-tree-adapter-export-v1",
        "component": args.component,
        "selected_manifest": str(manifest_path),
        "selected_manifest_sha256": sha256(manifest_path),
        "selected_wrapper": str(wrapper),
        "selected_wrapper_sha256": sha256(wrapper),
        "root_system": str(source_path),
        "root_system_file_sha256": sha256(source_path),
        "root_variable_count": len(variables),
        "root_equation_count": len(equations),
        "output": str(output),
        "output_sha256": sha256(output),
    }
    if args.receipt is not None:
        receipt_path = args.receipt.resolve()
        receipt_path.parent.mkdir(parents=True, exist_ok=True)
        receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps(receipt, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
