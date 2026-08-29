#!/usr/bin/env python3
"""Reflect an arbitrary strict X=5 carrier tree into the legacy Lean API.

The historical X=5 registry expects a pair of modules named
``KrennX5CaseNSelected`` and ``KrennX5CaseNBridge``.  A direct certificate
already has that shape, but a certificate tree previously required the
separate residual-case API and was limited to one split level.  This exporter
closes that interface gap without weakening either side:

* every terminal certificate is replayed against its exact frozen leaf;
* the frozen tree coverage and parent/child semantics are checked first;
* Lean reconstructs every inverse extension and exhausts all eight children
  at every internal node; and
* the official bridge proves precisely the selected frozen root equations
  from ``EqSystemN 6 3`` and the normalized-case hypotheses.

Discovery remains external.  The generated sparse identities and recursive
cover are checked again by Lean.
"""

from __future__ import annotations

import os
import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path


KRENN_ROOT = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
HERE = Path(__file__).resolve().parent
LEAN_ROOT = HERE.parent
sys.path.insert(0, str(KRENN_ROOT))
sys.path.insert(0, str(HERE))

from audit_carrier_tree_semantics import verify_tree  # noqa: E402
from certify_carrier_tree import expand  # noqa: E402
from export_lean_carrier_tree import (  # noqa: E402
    bits,
    call_new_branch,
    coordinate_indices,
    extend_values,
    inventory_path,
    parts,
    path_argument_names,
    path_parameters,
)
from export_lean_sparse_certificate import (  # noqa: E402
    certificate_multipliers,
    lean_poly,
    vector_definition,
)
from export_x5_residual_tree_lean import emit_bridge as emit_residual_bridge  # noqa: E402
from strict_certificate_checker import (  # noqa: E402
    check_c4,
    frozen_poly,
    symbols_for,
    validate_variable_names,
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def certificate_filename(row: dict) -> str:
    """Return the manifest-selected proof object, including the v1 default."""
    value = row.get("certificate_file", "lift.stdout")
    require(isinstance(value, str) and value != "", "certificate filename malformed")
    return value


def suffix(tag: str) -> str:
    return tag.upper().replace(".", "_")


def leaf_module(case: int, tag: str) -> str:
    return f"KrennX5Case{case}Tree.Leaf{suffix(tag)}"


def leaf_namespace(case: int, tag: str) -> str:
    return f"Krenn.X5Case{case}Tree.Leaf{suffix(tag)}"


def leaf_theorem(tag: str) -> str:
    return "leaf" + suffix(tag).title().replace("_", "") + "Impossible"


def node_theorem(tag: str) -> str:
    return "rootImpossible" if not tag else (
        "node" + suffix(tag).title().replace("_", "") + "Impossible"
    )


def selected_indices(system_path: Path, certificate_path: Path) -> list[int]:
    system = load(system_path)
    multipliers = certificate_multipliers(
        certificate_path, symbols_for(tuple(system["variables"]))
    )
    return [index for index, value in enumerate(multipliers) if not value.is_zero]


def validate_tree(case_dir: Path, spec_path: Path, manifest_path: Path) -> tuple[
    dict, dict, list[tuple[str, Path]], dict[str, dict]
]:
    """Recheck coverage, connectivity, receipt hashes, and every identity."""
    semantic_audit = verify_tree(spec_path)
    spec = load(spec_path)
    manifest = load(manifest_path)
    leaves, coverage = expand(spec_path)
    require(manifest.get("format") == "krenn-exact-carrier-tree-v1",
            "tree manifest format drift")
    require(manifest.get("coverage") == coverage,
            "tree manifest/spec coverage drift")
    require(manifest.get("summary") == {
        "strict_exact_identities": len(leaves),
        "selected_leaf_count": len(leaves),
        "complete": True,
    }, "tree manifest is not complete")
    rows = manifest.get("leaves")
    require(isinstance(rows, list) and len(rows) == len(leaves),
            "tree leaf receipt count drift")
    by_tag = {row.get("tag"): row for row in rows if isinstance(row, dict)}
    require(len(by_tag) == len(rows), "tree leaf tags are absent or duplicated")
    for tag, leaf in leaves:
        row = by_tag.get(tag)
        require(row is not None, f"missing receipt for terminal tag {tag}")
        system = leaf / "system.json"
        certificate_name = certificate_filename(row)
        certificate = leaf / certificate_name
        require(system.is_file() and certificate.is_file(),
                f"{tag}: frozen proof object absent")
        require(row.get("verdict") == "strict_exact_identity",
                f"{tag}: non-strict terminal verdict")
        require(row.get("system_file_sha256") == sha256(system),
                f"{tag}: system hash drift")
        require(row.get("certificate_sha256") == sha256(certificate),
                f"{tag}: certificate hash drift")
        require(row.get("strict_replay") == check_c4(system, certificate),
                f"{tag}: strict replay receipt drift")
    require(isinstance(semantic_audit, dict), "semantic tree audit malformed")
    require(case_dir.joinpath("system.json").is_file(), "root system absent")
    return spec, manifest, leaves, by_tag


def emit_leaf_adapter(
    case: int,
    tag: str,
    leaf_dir: Path,
    selected: list[int],
    spec: dict,
    root_variables: list[str],
    root_equation_count: int,
    root_positions: dict[int, int],
) -> list[str]:
    namespace = leaf_namespace(case, tag)
    leaf_system = load(leaf_dir / "system.json")
    parameters = [
        f"    (values : Fin {len(root_variables)} → R)",
        "    (rootZero : RootSelectedZero values)",
        *("    " + parameter
          for parameter in path_parameters(tag, spec, root_variables)),
    ]
    lines = [
        f"/-- Frozen compatibility and contradiction for terminal chart `{tag}`. -/",
        f"theorem {leaf_theorem(tag)} {{R : Type*}} [Field R] [CharZero R]",
        *parameters,
        "    : False := by",
    ]
    current = "values"
    current_size = len(root_variables)
    value_names: list[str] = []
    for depth, branch in enumerate(parts(tag)):
        inverses = [
            f"d{depth}Inverse{offset}"
            for offset, bit in enumerate(bits(branch)) if bit
        ]
        next_name = f"values{depth + 1}"
        lines.extend(extend_values(
            next_name, current, current_size, inverses,
            current_size + len(inverses),
        ))
        current = next_name
        current_size += len(inverses)
        value_names.append(next_name)
    require(current_size == len(leaf_system["variables"]),
            f"{tag}: assignment/leaf variable count drift")
    lines.extend([
        f"  apply {namespace}.selectedHasNoCommonZero {current}",
        "  intro index",
        "  fin_cases index",
    ])
    context = [
        "sub_eq_add_neg", *value_names, "rootSelectedEquations",
        f"{namespace}.selectedEquations", "SparsePoly.toPoly",
        "SparseTerm.toPoly",
    ]
    depth = len(parts(tag))
    for equation_index in selected:
        if equation_index < root_equation_count:
            source = f"rootZero ⟨{root_positions[equation_index]}, by decide⟩"
        else:
            level, offset = divmod(equation_index - root_equation_count, 3)
            require(level < depth,
                    f"{tag}: selected equation lies outside its branch path")
            source = f"d{level}Equation{offset}"
        lines.append(f"  · simpa [{', '.join(context)}] using {source}")
    return [*lines, ""]


def emit_node(
    case: int,
    tag: str,
    spec: dict,
    root_variables: list[str],
    terminal_tags: set[str],
) -> list[str]:
    depth = len(parts(tag))
    inventory = load(inventory_path(spec, tag))
    indices = coordinate_indices(inventory, root_variables)
    parameters = [
        f"    (values : Fin {len(root_variables)} → R)",
        "    (rootZero : RootSelectedZero values)",
        *("    " + parameter
          for parameter in path_parameters(tag, spec, root_variables)),
    ]
    lines = [
        f"/-- Exhaustive reflection for carrier chart `{tag or 'root'}`. -/",
        f"theorem {node_theorem(tag)} {{R : Type*}} [Field R] [CharZero R]",
        *parameters,
        "    : False := by",
    ]

    def recurse(offset: int, branch_bits: list[int], zero_names: list[str],
                indent: str) -> None:
        index = indices[offset]
        zero_name = f"zeroD{depth}C{offset}"
        lines.append(f"{indent}by_cases {zero_name} : values {index} = 0")
        for is_zero in (True, False):
            new_bits = [*branch_bits, 0 if is_zero else 1]
            new_zeros = [*zero_names, zero_name]
            lines.append(f"{indent}·")
            if offset < 2:
                recurse(offset + 1, new_bits, new_zeros, indent + "  ")
                continue
            branch = new_bits[0] * 4 + new_bits[1] * 2 + new_bits[2]
            child = f"b{branch}" if not tag else f"{tag}.{branch}"
            target = leaf_theorem(child) if child in terminal_tags else node_theorem(child)
            arguments = ["values", "rootZero", *path_argument_names(tag)]
            arguments.extend(call_new_branch(depth, branch, indices, new_zeros))
            lines.append(f"{indent}  exact {target} " + " ".join(arguments))

    recurse(0, [], [], "  ")
    return [*lines, ""]


def official_bridge(case: int, root: dict, selected: list[int]) -> str:
    """Reuse the established bridge generator, changing only module names."""
    text = emit_residual_bridge(case, root, selected, len(selected))
    text = text.replace(
        f"KrennX5ResidualCase{case}.Tree", f"KrennX5Case{case}Selected"
    )
    text = text.replace(
        f"Krenn.X5ResidualCase{case}.Tree", f"Krenn.X5Case{case}Selected"
    )
    text = text.replace(
        f"Krenn.X5Case{case}Selected.case{case}SelectedHasNoCommonZero",
        f"Krenn.X5Case{case}Selected.selectedHasNoCommonZero",
    )
    text = text.replace(
        f"Krenn.X5ResidualCase{case}.Bridge", f"Krenn.X5Case{case}Bridge"
    )
    return text


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("case", type=int)
    parser.add_argument("case_dir", type=Path)
    parser.add_argument("--spec", type=Path)
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--lean-root", type=Path, default=LEAN_ROOT)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    require(args.case > 0, "case index must be positive")
    case_dir = args.case_dir.resolve()
    spec_path = (args.spec or case_dir / "tree_spec_v1.json").resolve()
    manifest_path = (args.manifest or case_dir / "tree_manifest_v1.json").resolve()
    spec, manifest, leaves, rows = validate_tree(
        case_dir, spec_path, manifest_path
    )
    root_path = case_dir / "system.json"
    root = load(root_path)
    root_variables = validate_variable_names(root["variables"])
    root_symbols = symbols_for(root_variables)
    root_equation_count = len(root["equations"])
    root_equations = [frozen_poly(row, root_symbols) for row in root["equations"]]

    selected_by_tag: dict[str, list[int]] = {}
    root_selected_set: set[int] = set()
    for tag, leaf in leaves:
        certificate = leaf / certificate_filename(rows[tag])
        selected = selected_indices(leaf / "system.json", certificate)
        selected_by_tag[tag] = selected
        root_selected_set.update(
            index for index in selected if index < root_equation_count
        )
    root_selected = sorted(root_selected_set)
    root_positions = {index: position for position, index in enumerate(root_selected)}
    terminal_tags = set(selected_by_tag)

    output_dir = args.lean_root / f"KrennX5Case{args.case}Tree"
    output_dir.mkdir(parents=True, exist_ok=True)
    leaf_hashes: dict[str, str] = {}
    for ordinal, (tag, leaf) in enumerate(leaves, 1):
        output = output_dir / f"Leaf{suffix(tag)}.lean"
        subprocess.run([
            sys.executable, str(HERE / "export_lean_selected_certificate.py"),
            str(leaf / "system.json"),
            str(leaf / certificate_filename(rows[tag])), str(output),
            "--namespace", leaf_namespace(args.case, tag),
        ], check=True)
        leaf_hashes[tag] = sha256(output)
        print(f"[{ordinal}/{len(leaves)}] {tag}", flush=True)

    namespace = f"Krenn.X5Case{args.case}Selected"
    lines = [*(f"import {leaf_module(args.case, tag)}" for tag, _ in leaves), ""]
    lines.extend([
        f"namespace {namespace}", "", "open Krenn.SparseCertificate",
        "open MvPolynomial", "",
        *vector_definition(
            "rootSelectedIndices", len(root_selected),
            f"Fin {root_equation_count}", [str(index) for index in root_selected],
        ), "",
        *vector_definition(
            "rootSelectedEquations", len(root_selected),
            f"SparsePoly (Fin {len(root_variables)})",
            [lean_poly(root_equations[index]) for index in root_selected],
        ), "",
        "def RootSelectedZero {R : Type*} [CommRing R]",
        f"    (values : Fin {len(root_variables)} → R) : Prop :=",
        f"  ∀ index : Fin {len(root_selected)},",
        "    eval₂Hom (Int.castRingHom R) values",
        "      (rootSelectedEquations index).toPoly = 0", "",
        "set_option maxRecDepth 100000", "set_option maxHeartbeats 5000000", "",
    ])
    leaf_dirs = dict(leaves)
    for tag, _leaf in leaves:
        lines.extend(emit_leaf_adapter(
            args.case, tag, leaf_dirs[tag], selected_by_tag[tag], spec,
            list(root_variables), root_equation_count, root_positions,
        ))
    internal = sorted(spec["refinements"], key=lambda tag: (-len(parts(tag)), parts(tag)))
    for tag in internal:
        lines.extend(emit_node(
            args.case, tag, spec, list(root_variables), terminal_tags
        ))
    lines.extend(emit_node(
        args.case, "", spec, list(root_variables), terminal_tags
    ))
    lines.extend([
        f"theorem selectedHasNoCommonZero (values : Fin {len(root_variables)} → ℂ) :",
        "    ¬ RootSelectedZero values := by",
        "  intro rootZero", "  exact rootImpossible values rootZero", "",
        f"#print axioms {namespace}.selectedHasNoCommonZero", "",
        f"end {namespace}", "",
    ])
    selected_path = args.lean_root / f"KrennX5Case{args.case}Selected.lean"
    selected_path.write_text("\n".join(lines), encoding="utf-8")
    bridge_path = args.lean_root / f"KrennX5Case{args.case}Bridge.lean"
    bridge_path.write_text(
        official_bridge(args.case, root, root_selected), encoding="utf-8"
    )

    receipt = {
        "format": "krenn-x5-nested-tree-lean-reflection-v1",
        "case": args.case,
        "source_system_file_sha256": sha256(root_path),
        "source_system_semantic_sha256": root["system_sha256"],
        "tree_spec_sha256": sha256(spec_path),
        "tree_manifest_sha256": sha256(manifest_path),
        "root_selected_indices": root_selected,
        "root_selected_count": len(root_selected),
        "leaf_count": len(leaves),
        "internal_node_count": len(spec["refinements"]) + 1,
        "leaf_modules": leaf_hashes,
        "selected_module_sha256": sha256(selected_path),
        "bridge_module_sha256": sha256(bridge_path),
        "exporter_sha256": sha256(Path(__file__)),
    }
    if args.receipt is not None:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(
            json.dumps(receipt, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    print(json.dumps(receipt, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
