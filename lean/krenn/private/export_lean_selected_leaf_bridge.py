#!/usr/bin/env python3
"""Generate one semantic bridge from a shared carrier root to a selected leaf.

This is the compact counterpart to the full parent-equation leaf importer:
the leaf module stores only certificate-selected rows, while this wrapper
proves each such row from the shared root family and the explicit branch
zero/inverse equations.  The final `simpa` checks the actual polynomial
equality in Lean rather than trusting the routing metadata.
"""

from __future__ import annotations

import os
import argparse
import json
import sys
from pathlib import Path

SHARED_KRENN = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
if str(SHARED_KRENN) not in sys.path:
    sys.path.insert(0, str(SHARED_KRENN))

from certify_carrier_tree import expand
from export_lean_carrier_tree import (
    bits,
    coordinate_indices,
    extend_values,
    inventory_path,
    load,
    parts,
    path_inventories,
    path_parameters,
)
from export_lean_sparse_certificate import certificate_multipliers
from strict_certificate_checker import symbols_for


ROOT = SHARED_KRENN


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("component", type=int)
    parser.add_argument("tag")
    parser.add_argument("output", type=Path)
    parser.add_argument("--root-namespace", required=True)
    parser.add_argument("--leaf-namespace", required=True)
    parser.add_argument("--certificate", type=Path,
                        help="strict certificate selected by the tree manifest")
    args = parser.parse_args()
    case = ROOT / "allcollapse_case_artifacts" / "case_0"
    # Canonical frozen artifact names are zero-padded (`component01`, not
    # `component1`).  Keep the Lean namespace unpadded, but resolve the
    # provenance-bearing external spec through its canonical filename.
    spec_path = case / f"component{args.component:02d}_tree_spec.json"
    spec = load(spec_path)
    leaves, _ = expand(spec_path)
    leaf_dir = dict(leaves).get(args.tag)
    if leaf_dir is None:
        raise ValueError(f"not a terminal tag: {args.tag}")
    root = load((ROOT / spec["source_system"]).resolve())
    root_variables = root["variables"]
    root_equations = len(root["equations"])
    leaf = load(leaf_dir / "system.json")
    certificate = (args.certificate.resolve() if args.certificate is not None
                   else leaf_dir / "lift.reordered.stdout")
    if not certificate.is_file():
        raise FileNotFoundError(certificate)
    multipliers = certificate_multipliers(certificate, symbols_for(leaf["variables"]))
    selected = [i for i, multiplier in enumerate(multipliers) if not multiplier.is_zero]
    if not selected:
        raise ValueError("certificate has no selected equations")

    parameters = [
        f"    (values : Fin {len(root_variables)} → R)",
        f"    (rootZero : {args.root_namespace}.RootCommonZero values)",
    ] + ["    " + row for row in path_parameters(args.tag, spec, root_variables)]
    theorem = "selectedLeaf" + args.tag.upper().replace("B", "B").replace(".", "_") + "Impossible"
    lines = [
        f"import KrennComponent{args.component}.Root",
        f"import KrennComponent{args.component}.SelectedLeaf{args.tag.upper().replace('B', 'B').replace('.', '_')}",
        "",
        "/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/",
        "",
        f"namespace Krenn.Component{args.component}.SelectedBridge{args.tag.upper().replace('B', 'B').replace('.', '_')}",
        "",
        "open Krenn.SparseCertificate",
        "open MvPolynomial",
        "",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 5000000",
        "",
        f"theorem {theorem} {{R : Type*}} [Field R] [CharZero R]",
        *parameters,
        "    : False := by",
    ]

    current = "values"
    current_size = len(root_variables)
    value_names: list[str] = []
    for depth, branch in enumerate(parts(args.tag)):
        inverse_names = [f"d{depth}Inverse{offset}"
                         for offset, bit in enumerate(bits(branch)) if bit]
        next_name = f"values{depth + 1}"
        lines.extend(extend_values(
            next_name, current, current_size, inverse_names,
            current_size + len(inverse_names),
        ))
        current, current_size = next_name, current_size + len(inverse_names)
        value_names.append(next_name)
    if current_size != len(leaf["variables"]):
        raise ValueError(
            f"{args.tag}: assignment size {current_size} != leaf variables {len(leaf['variables'])}"
        )

    lines.extend([
        f"  apply {args.leaf_namespace}.selectedHasNoCommonZero {current}",
        "  intro index",
        "  fin_cases index",
    ])
    context = [
        "sub_eq_add_neg", *value_names,
        f"{args.root_namespace}.rootEquations",
        f"{args.leaf_namespace}.selectedEquations",
        "SparsePoly.toPoly", "SparseTerm.toPoly",
    ]
    depth = len(parts(args.tag))
    for equation_index in selected:
        if equation_index < root_equations:
            source = f"rootZero ⟨{equation_index}, by decide⟩"
        else:
            level, offset = divmod(equation_index - root_equations, 3)
            if level >= depth:
                raise ValueError(f"{args.tag}: selected equation outside branch path")
            source = f"d{level}Equation{offset}"
        lines.append(f"  · simpa [{', '.join(context)}] using {source}")
    lines.extend([
        "",
        f"#print axioms Krenn.Component{args.component}.SelectedBridge{args.tag.upper().replace('B', 'B').replace('.', '_')}.{theorem}",
        "",
        f"end Krenn.Component{args.component}.SelectedBridge{args.tag.upper().replace('B', 'B').replace('.', '_')}",
        "",
    ])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("\n".join(lines))
    print(json.dumps({
        "component": args.component,
        "tag": args.tag,
        "root_equations": root_equations,
        "selected_equations": len(selected),
        "leaf_variables": len(leaf["variables"]),
        "branch_depth": depth,
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
