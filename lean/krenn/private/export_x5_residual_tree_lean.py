#!/usr/bin/env python3
"""Reflect one strict one-level X=5 residual carrier tree into Lean.

The external tree is first revalidated by the strict residual checker.  Lean
receives only the parent equations actually used by a leaf certificate, the
selected leaf identities, and the exhaustive three-coordinate field split.
The generated official bridge reconstructs each selected parent equation from
``EqSystemN 6 3`` and the frozen normalized-case hypotheses.
"""

from __future__ import annotations

import os
import argparse
import hashlib
import itertools
import json
import re
import subprocess
import sys
from pathlib import Path

KRENN_ROOT = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
HERE = Path(__file__).resolve().parent
LEAN_ROOT = HERE.parent
sys.path.insert(0, str(KRENN_ROOT))
sys.path.insert(0, str(HERE))

from certify_carrier_tree import expand  # noqa: E402
from certify_x5_residual import valid_carrier_tree_certificate  # noqa: E402
from export_f9_case_bridge_lean import (  # noqa: E402
    edge_term,
    official_colourings,
    parse_variable,
)
from export_lean_sparse_certificate import (  # noqa: E402
    certificate_multipliers,
    lean_poly,
    vector_definition,
)
from strict_certificate_checker import (  # noqa: E402
    frozen_poly,
    symbols_for,
    validate_variable_names,
)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def branch_bits(branch: int) -> list[int]:
    return [(branch >> shift) & 1 for shift in (2, 1, 0)]


def case_dir(case: int) -> Path:
    return KRENN_ROOT / "x5_frontier_artifacts" / f"0415_case{case:03d}"


def module_root(case: int) -> str:
    return f"KrennX5ResidualCase{case}"


def namespace_root(case: int) -> str:
    return f"Krenn.X5ResidualCase{case}"


def leaf_module(case: int, branch: int) -> str:
    return f"{module_root(case)}.LeafB{branch}"


def leaf_namespace(case: int, branch: int) -> str:
    return f"{namespace_root(case)}.LeafB{branch}"


def selected_indices(system_path: Path, certificate_path: Path) -> list[int]:
    system = load(system_path)
    multipliers = certificate_multipliers(
        certificate_path, symbols_for(tuple(system["variables"]))
    )
    return [index for index, value in enumerate(multipliers) if not value.is_zero]


def extend_values(base_size: int, inverse_names: list[str], total_size: int) -> list[str]:
    if not inverse_names:
        return [f"  let childValues : Fin {total_size} → R := values"]
    lines = [
        f"  let childValues : Fin {total_size} → R := fun index =>",
        f"    if inside : index.val < {base_size} then",
        "      values ⟨index.val, inside⟩",
    ]
    for offset, inverse in enumerate(inverse_names):
        if offset + 1 == len(inverse_names):
            lines.append(f"    else {inverse}")
        else:
            lines.extend([
                f"    else if at{offset} : index.val = {base_size + offset} then",
                f"      {inverse}",
            ])
    return lines


def branch_parameters(branch: int, coordinate_indices: list[int]) -> list[str]:
    parameters: list[str] = []
    for offset, (bit, index) in enumerate(
        zip(branch_bits(branch), coordinate_indices, strict=True)
    ):
        if bit:
            parameters.extend([
                f"    (inverse{offset} : R)",
                f"    (branchEquation{offset} : values {index} * inverse{offset} - 1 = 0)",
            ])
        else:
            parameters.append(f"    (branchEquation{offset} : values {index} = 0)")
    return parameters


def branch_argument_names(branch: int) -> list[str]:
    result: list[str] = []
    for offset, bit in enumerate(branch_bits(branch)):
        if bit:
            result.extend([f"inverse{offset}", f"branchEquation{offset}"])
        else:
            result.append(f"branchEquation{offset}")
    return result


def emit_leaf_theorem(
    case: int,
    branch: int,
    leaf_dir: Path,
    selected: list[int],
    root_positions: dict[int, int],
    root_variable_count: int,
    root_equation_count: int,
    coordinate_indices: list[int],
) -> list[str]:
    leaf_system = load(leaf_dir / "system.json")
    inverse_names = [
        f"inverse{offset}" for offset, bit in enumerate(branch_bits(branch)) if bit
    ]
    expected_variables = root_variable_count + len(inverse_names)
    if len(leaf_system["variables"]) != expected_variables:
        raise ValueError(
            f"case {case} b{branch}: variable extension is not the one-level schema"
        )
    lines = [
        f"/-- Strict contradiction for residual case {case}, branch b{branch}. -/",
        f"theorem leafB{branch}Impossible {{R : Type*}} [Field R] [CharZero R]",
        f"    (values : Fin {root_variable_count} → R)",
        "    (rootZero : RootSelectedZero values)",
        *branch_parameters(branch, coordinate_indices),
        "    : False := by",
        *extend_values(root_variable_count, inverse_names, expected_variables),
        f"  apply {leaf_namespace(case, branch)}.selectedHasNoCommonZero childValues",
        "  intro index",
        "  fin_cases index",
    ]
    context = [
        "sub_eq_add_neg",
        "childValues",
        "rootSelectedEquations",
        f"{leaf_namespace(case, branch)}.selectedEquations",
        "SparsePoly.toPoly",
        "SparseTerm.toPoly",
    ]
    for equation_index in selected:
        if equation_index < root_equation_count:
            position = root_positions[equation_index]
            source = f"rootZero ⟨{position}, by decide⟩"
        else:
            offset = equation_index - root_equation_count
            if offset not in range(3):
                raise ValueError(
                    f"case {case} b{branch}: selected row outside parent+three schema"
                )
            source = f"branchEquation{offset}"
        lines.append(f"  · simpa [{', '.join(context)}] using {source}")
    lines.append("")
    return lines


def leaf_call(
    branch: int, coordinate_indices: list[int], zero_names: list[str]
) -> list[str]:
    arguments = ["values", "rootZero"]
    for offset, (bit, index) in enumerate(
        zip(branch_bits(branch), coordinate_indices, strict=True)
    ):
        if bit:
            arguments.extend([
                f"(values {index})⁻¹",
                f"(by simp [{zero_names[offset]}])",
            ])
        else:
            arguments.append(zero_names[offset])
    return arguments


def emit_root_split(
    case: int, coordinate_indices: list[int], root_variable_count: int
) -> list[str]:
    lines = [
        "/-- The eight frozen carrier branches exhaust the residual case. -/",
        "theorem rootImpossible {R : Type*} [Field R] [CharZero R]",
        f"    (values : Fin {root_variable_count} → R)",
        "    (rootZero : RootSelectedZero values) : False := by",
    ]

    def recurse(offset: int, branch: int, zero_names: list[str], indent: str) -> None:
        index = coordinate_indices[offset]
        zero_name = f"zeroC{offset}"
        lines.append(f"{indent}by_cases {zero_name} : values {index} = 0")
        for is_zero in (True, False):
            next_branch = branch if is_zero else branch | (1 << (2 - offset))
            next_zeros = [*zero_names, zero_name]
            lines.append(f"{indent}·")
            if offset < 2:
                recurse(offset + 1, next_branch, next_zeros, indent + "  ")
            else:
                args = " ".join(leaf_call(next_branch, coordinate_indices, next_zeros))
                lines.append(f"{indent}  exact leafB{next_branch}Impossible {args}")

    recurse(0, 0, [], "  ")
    lines.extend([
        "",
        f"theorem case{case}SelectedHasNoCommonZero",
        f"    (values : Fin {root_variable_count} → ℂ) : ¬ RootSelectedZero values := by",
        "  intro rootZero",
        "  exact rootImpossible values rootZero",
        "",
        f"#print axioms {namespace_root(case)}.Tree.case{case}SelectedHasNoCommonZero",
        "",
    ])
    return lines


def normalization_lines(system: dict, case: int) -> tuple[list[str], list[str], list[str]]:
    problem = system["problem"]
    support = {tuple(edge) for edge in problem["mixed_support"]}
    fixed = [(tuple(edge), int(i), int(j)) for edge, i, j in problem["fixed_entries"]]
    zero = [(tuple(edge), int(i), int(j)) for edge, i, j in problem["zero_entries"]]
    outside = sorted({(u, v) for u in range(6) for v in range(u + 1, 6)} - support)
    fields: list[str] = []
    simp: list[str] = []
    for (u, v), i, j in fixed:
        name = f"fixed_{u}{v}_{i}{j}"
        fields.append(f"  {name} : {edge_term(u, v, i, j)} = 1")
        simp.append(f"hcase.{name}")
    for (u, v), i, j in zero:
        name = f"zero_{u}{v}_{i}{j}"
        fields.append(f"  {name} : {edge_term(u, v, i, j)} = 0")
        simp.append(f"hcase.{name}")
    for u, v in outside:
        name = f"outside{u}{v}"
        fields.append(
            f"  {name} : ∀ i j, i ≠ j → {edge_term(u, v, 'i', 'j')} = 0"
        )
        simp.append(f"hcase.{name}")
    return fields, simp, [str(case)]


def emit_bridge(
    case: int,
    system: dict,
    root_selected: list[int],
    root_polys_count: int,
) -> str:
    namespace = namespace_root(case) + ".Bridge"
    tree_namespace = namespace_root(case) + ".Tree"
    names = validate_variable_names(system["variables"])
    symbols = symbols_for(names)
    colourings = official_colourings(system, root_selected, symbols)
    fields, case_simp, _ = normalization_lines(system, case)
    lines = [
        "import KrennOfficialBridge",
        f"import {module_root(case)}.Tree",
        "",
        f"namespace {namespace}",
        "",
        "open MonochromaticQuantumGraph",
        "open Krenn.OfficialBridge",
        "open Krenn.SparseCertificate",
        "open MvPolynomial",
        "",
        "def entry (W : WeightsN 6 3 ℂ) (u v : Fin 6) (i j : Fin 3) : ℂ :=",
        "  W (MonochromaticQuantumGraph.mkEdge u v i j)",
        "",
        "structure NormalizedCase (W : WeightsN 6 3 ℂ) : Prop where",
        *fields,
        "",
        f"def values (W : WeightsN 6 3 ℂ) : Fin {len(names)} → ℂ := ![",
    ]
    for offset, name in enumerate(names):
        u, v, i, j = parse_variable(name)
        comma = "," if offset + 1 < len(names) else ""
        lines.append(f"  entry W {u} {v} {i} {j}{comma}")
    lines.extend([
        "]",
        "",
    ])
    for offset, colouring in enumerate(colourings):
        values = ", ".join(map(str, colouring))
        lines.append(f"private def c{offset} : Fin 6 → Fin 3 := ![{values}]")
    lines.extend([
        "",
        "set_option maxRecDepth 100000 in",
        "set_option maxHeartbeats 5000000 in",
        "theorem selectedRootEquations_vanish (W : WeightsN 6 3 ℂ)",
        "    (hEq : EqSystemN 6 3 W) (hcase : NormalizedCase W) :",
        f"    {tree_namespace}.RootSelectedZero (values W) := by",
        "  intro index",
    ])
    for offset in range(root_polys_count):
        lines.append(f"  have r{offset} := hEq c{offset}")
    rows = " ".join(f"r{offset}" for offset in range(root_polys_count))
    lines.append(f"  rw [official_pmSum_eq_pm15] at {rows}")
    simp_values = [
        "pm15", "w", *(f"c{i}" for i in range(root_polys_count)),
        "allEqual", "allEqualList", "vertices", *case_simp,
    ]
    lines.append(
        "  simp [-mul_eq_zero, " + ", ".join(simp_values) + f"] at {rows}"
    )
    lines.append("  fin_cases index")
    eval_simp = (
        f"{tree_namespace}.rootSelectedEquations, "
        "SparsePoly.toPoly, SparseTerm.toPoly, values, entry, "
        "Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one"
    )
    for offset in range(root_polys_count):
        lines.extend([
            f"  · simp [-mul_eq_zero, {eval_simp}]",
            f"    linear_combination r{offset}",
        ])
    lines.extend([
        "",
        "theorem noNormalizedCase (W : WeightsN 6 3 ℂ)",
        "    (hEq : EqSystemN 6 3 W) (hcase : NormalizedCase W) : False := by",
        f"  exact ({tree_namespace}.case{case}SelectedHasNoCommonZero (values W))",
        "    (selectedRootEquations_vanish W hEq hcase)",
        "",
        f"#print axioms {namespace}.noNormalizedCase",
        "",
        f"end {namespace}",
        "",
    ])
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("case", type=int)
    parser.add_argument("--lean-root", type=Path, default=LEAN_ROOT)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    directory = case_dir(args.case)
    closure = valid_carrier_tree_certificate(directory)
    if closure is None:
        raise ValueError(f"case {args.case} is not a unique strict carrier-tree closure")
    spec_path = directory / closure["carrier_tree_spec"]
    manifest_path = directory / closure["carrier_tree_manifest"]
    spec = load(spec_path)
    if spec.get("refinements") != {}:
        raise ValueError("this exporter intentionally accepts only one-level trees")
    manifest = load(manifest_path)
    leaves, coverage = expand(spec_path)
    if manifest.get("coverage") != coverage or len(leaves) != 8:
        raise ValueError("tree coverage/arity drift")
    rows = {row["tag"]: row for row in manifest["leaves"]}
    leaf_dirs = {tag: path for tag, path in leaves}
    if set(rows) != {f"b{i}" for i in range(8)} or set(rows) != set(leaf_dirs):
        raise ValueError("tree does not contain exactly b0..b7")

    root_path = directory / "system.json"
    root = load(root_path)
    root_names = validate_variable_names(root["variables"])
    root_symbols = symbols_for(root_names)
    root_equation_count = len(root["equations"])
    inventory = load((KRENN_ROOT / spec["root_inventory"] / "inventory.json").resolve())
    coordinates = inventory.get("coordinates")
    if not isinstance(coordinates, list) or len(coordinates) != 3:
        raise ValueError("root inventory does not declare three coordinates")
    coordinate_indices = [root_names.index(name) for name in coordinates]

    leaf_selected: dict[int, list[int]] = {}
    root_selected_set: set[int] = set()
    for branch in range(8):
        leaf = leaf_dirs[f"b{branch}"]
        certificate = leaf / "lift.stdout"
        selected = selected_indices(leaf / "system.json", certificate)
        leaf_selected[branch] = selected
        root_selected_set.update(i for i in selected if i < root_equation_count)
    root_selected = sorted(root_selected_set)
    root_positions = {value: index for index, value in enumerate(root_selected)}
    root_equations = [frozen_poly(row, root_symbols) for row in root["equations"]]

    output_dir = args.lean_root / module_root(args.case)
    output_dir.mkdir(parents=True, exist_ok=True)
    for branch in range(8):
        leaf = leaf_dirs[f"b{branch}"]
        subprocess.run([
            sys.executable,
            str(HERE / "export_lean_selected_certificate.py"),
            str(leaf / "system.json"),
            str(leaf / "lift.stdout"),
            str(output_dir / f"LeafB{branch}.lean"),
            "--namespace", leaf_namespace(args.case, branch),
        ], check=True)

    tree_namespace = namespace_root(args.case) + ".Tree"
    lines = [
        *(f"import {leaf_module(args.case, branch)}" for branch in range(8)),
        "",
        f"namespace {tree_namespace}",
        "",
        "open Krenn.SparseCertificate",
        "open MvPolynomial",
        "",
        f"def rootVariableCount : Nat := {len(root_names)}",
        "",
        *vector_definition(
            "rootSelectedIndices", len(root_selected), f"Fin {root_equation_count}",
            [str(index) for index in root_selected],
        ),
        "",
        *vector_definition(
            "rootSelectedEquations", len(root_selected),
            f"SparsePoly (Fin {len(root_names)})",
            [lean_poly(root_equations[index]) for index in root_selected],
        ),
        "",
        "def RootSelectedZero {R : Type*} [CommRing R]",
        f"    (values : Fin {len(root_names)} → R) : Prop :=",
        f"  ∀ index : Fin {len(root_selected)},",
        "    eval₂Hom (Int.castRingHom R) values",
        "      (rootSelectedEquations index).toPoly = 0",
        "",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 5000000",
        "",
    ]
    for branch in range(8):
        lines.extend(emit_leaf_theorem(
            args.case, branch, leaf_dirs[f"b{branch}"], leaf_selected[branch],
            root_positions, len(root_names), root_equation_count,
            coordinate_indices,
        ))
    lines.extend(emit_root_split(args.case, coordinate_indices, len(root_names)))
    lines.append(f"end {tree_namespace}")
    lines.append("")
    tree_path = output_dir / "Tree.lean"
    tree_path.write_text("\n".join(lines), encoding="utf-8")

    bridge_path = output_dir / "Bridge.lean"
    bridge_path.write_text(
        emit_bridge(args.case, root, root_selected, len(root_selected)),
        encoding="utf-8",
    )
    receipt = {
        "format": "krenn-x5-residual-lean-reflection-v1",
        "case": args.case,
        "source_system_file_sha256": digest(root_path),
        "source_system_semantic_sha256": root["system_sha256"],
        "tree_spec_sha256": digest(spec_path),
        "tree_manifest_sha256": digest(manifest_path),
        "root_selected_indices": root_selected,
        "root_selected_count": len(root_selected),
        "leaf_count": 8,
        "leaf_modules": {
            f"b{branch}": digest(output_dir / f"LeafB{branch}.lean")
            for branch in range(8)
        },
        "tree_module_sha256": digest(tree_path),
        "bridge_module_sha256": digest(bridge_path),
        "exporter_sha256": digest(Path(__file__)),
    }
    if args.receipt is not None:
        args.receipt.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps(receipt, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
