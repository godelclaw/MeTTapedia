#!/usr/bin/env python3
"""Export one bounded carrier subtree using selected-row certificates.

The normal carrier exporter repeats the shared root equations in every leaf.
For a deep tree that makes elaboration scale with root-size times leaf-count.
This exporter keeps the root once, reflects only the rows used by each leaf
certificate, and emits a small recursive wrapper whose `simpa` proofs bind
those selected rows back to the frozen root and branch equations.

It intentionally exports a named subtree, not an entire component.  That
makes scale testing honest: a successful build proves exactly that subtree and
does not silently claim the remaining branches.
"""

from __future__ import annotations

import os
import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

SHARED = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
if str(SHARED) not in sys.path:
    sys.path.insert(0, str(SHARED))

from certify_carrier_tree import expand
from export_lean_carrier_tree import (
    bits,
    call_new_branch,
    coordinate_indices,
    inventory_path,
    load,
    parts,
    path_argument_names,
    path_parameters,
)


# Keep the exporter relocatable inside the private Lean checkout.  This file
# lives at ``<lean-root>/private/export_lean_selected_subtree.py``.
LEAN_ROOT = Path(__file__).resolve().parents[1]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def suffix(tag: str) -> str:
    return tag.upper().replace(".", "_")


def subtree_suffix(tag: str) -> str:
    """A stable module suffix for a selected subtree, including the root."""
    return "ROOT" if not tag else suffix(tag)


def leaf_namespace(component: int, tag: str) -> str:
    return f"Krenn.Component{component}.SelectedLeaf{suffix(tag)}"


def leaf_module(component: int, tag: str) -> str:
    return f"KrennComponent{component}.SelectedLeaf{suffix(tag)}"


def bridge_namespace(component: int, tag: str) -> str:
    return f"Krenn.Component{component}.SelectedBridge{suffix(tag)}"


def bridge_module(component: int, tag: str) -> str:
    return f"KrennComponent{component}.SelectedBridge{suffix(tag)}"


def bridge_theorem(component: int, tag: str) -> str:
    return f"{bridge_namespace(component, tag)}.selectedLeaf{suffix(tag)}Impossible"


def node_stem(tag: str) -> str:
    return ("rootImpossible" if not tag else
            "node" + suffix(tag).title().replace("_", "") + "Impossible")


def is_descendant(tag: str, prefix: str) -> bool:
    return not prefix or tag == prefix or tag.startswith(prefix + ".")


def emit_node(component: int, tag: str, spec: dict, root_variables: list[str],
              terminal_tags: set[str]) -> list[str]:
    """Emit one three-coordinate recursive chart splitter."""
    depth = len(parts(tag))
    inventory = load(inventory_path(spec, tag))
    indices = coordinate_indices(inventory, root_variables)
    parameters = [
        f"    (values : Fin {len(root_variables)} → R)",
        f"    (rootZero : Krenn.Component{component}.Root.RootCommonZero values)",
    ]
    parameters.extend("    " + value
                      for value in path_parameters(tag, spec, root_variables))
    lines = [
        f"/-- Exhaustive selected-row reflection for chart `{tag}`. -/",
        f"theorem {node_stem(tag)} {{R : Type*}} [Field R] [CharZero R]",
        *parameters,
        "    : False := by",
    ]

    def recurse(offset: int, branch_bits: list[int], zero_names: list[str],
                indent: str) -> None:
        index = indices[offset]
        zero_name = f"zeroD{depth}C{offset}"
        lines.append(f"{indent}by_cases {zero_name} : values {index} = 0")
        for is_zero, bullet in ((True, "·"), (False, "·")):
            next_bits = branch_bits + [0 if is_zero else 1]
            next_zeros = zero_names + [zero_name]
            if offset < 2:
                lines.append(f"{indent}{bullet}")
                recurse(offset + 1, next_bits, next_zeros, indent + "  ")
                continue
            branch = next_bits[0] * 4 + next_bits[1] * 2 + next_bits[2]
            child = f"b{branch}" if not tag else f"{tag}.{branch}"
            target = (bridge_theorem(component, child)
                      if child in terminal_tags else node_stem(child))
            arguments = ["values", "rootZero", *path_argument_names(tag)]
            arguments.extend(call_new_branch(depth, branch, indices, next_zeros))
            lines.append(f"{indent}{bullet} exact {target} " + " ".join(arguments))

    recurse(0, [], [], "  ")
    return [*lines, ""]


def run(command: list[str]) -> None:
    subprocess.run(command, check=True)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("component", type=int)
    parser.add_argument(
        "prefix",
        help="non-terminal chart prefix, e.g. b0; use root for the whole tree",
    )
    parser.add_argument("--lean-root", type=Path, default=LEAN_ROOT)
    parser.add_argument("--emit", action="store_true",
                        help="generate leaf and bridge modules before the wrapper")
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    args.lean_root = args.lean_root.resolve()
    prefix = "" if args.prefix == "root" else args.prefix
    if prefix and not parts(prefix):
        raise ValueError("subtree prefix must be root or a non-root branch tag")
    case = SHARED / "allcollapse_case_artifacts" / "case_0"
    slug = f"component{args.component:02d}"
    spec_path = case / f"{slug}_tree_spec.json"
    manifest_path = case / f"{slug}_tree_manifest.json"
    spec = load(spec_path)
    manifest = load(manifest_path)
    if manifest.get("summary", {}).get("complete") is not True:
        raise ValueError("tree manifest is incomplete")
    leaves, coverage = expand(spec_path)
    if manifest.get("coverage") != coverage:
        raise ValueError("tree manifest/spec coverage drift")
    leaf_dirs = dict(leaves)
    rows = {row["tag"]: row for row in manifest["leaves"]}
    if set(rows) != set(leaf_dirs):
        raise ValueError("tree leaf inventory drift")
    selected_tags = sorted(
        [tag for tag in rows if is_descendant(tag, prefix)], key=parts
    )
    if not selected_tags:
        raise ValueError(f"no terminal leaves below {prefix}")
    if prefix and prefix not in spec["refinements"]:
        raise ValueError(f"{prefix} is terminal; use a leaf bridge directly")
    internal = sorted(
        [tag for tag in spec["refinements"]
         if is_descendant(tag, prefix)
         and any(is_descendant(leaf, tag) for leaf in selected_tags)],
        key=lambda tag: (-len(parts(tag)), parts(tag)),
    )
    if not prefix:
        internal.append("")
    root_system = load((SHARED / spec["source_system"]).resolve())
    root_variables = root_system["variables"]
    target_dir = args.lean_root / f"KrennComponent{args.component}"
    target_dir.mkdir(parents=True, exist_ok=True)

    if args.emit:
        for ordinal, tag in enumerate(selected_tags, 1):
            leaf = leaf_dirs[tag]
            row = rows[tag]
            leaf_output = target_dir / f"SelectedLeaf{suffix(tag)}.lean"
            bridge_output = target_dir / f"SelectedBridge{suffix(tag)}.lean"
            run([
                sys.executable, str(LEAN_ROOT / "private" /
                                    "export_lean_sparse_selected_certificate.py"),
                str(leaf / "system.json"), str(leaf / row["certificate_file"]),
                str(leaf_output), "--namespace", leaf_namespace(args.component, tag),
            ])
            run([
                sys.executable, str(LEAN_ROOT / "private" /
                                    "export_lean_selected_leaf_bridge.py"),
                str(args.component), tag, str(bridge_output), "--root-namespace",
                f"Krenn.Component{args.component}.Root", "--leaf-namespace",
                leaf_namespace(args.component, tag), "--certificate",
                str(leaf / row["certificate_file"]),
            ])
            print(f"[{ordinal}/{len(selected_tags)}] {tag}", flush=True)

    missing = [tag for tag in selected_tags if not
               (target_dir / f"SelectedBridge{suffix(tag)}.lean").is_file()]
    if missing:
        raise ValueError(f"missing selected bridge modules: {missing}")

    module_suffix = subtree_suffix(prefix)
    lines = [f"import KrennComponent{args.component}.Root"]
    lines.extend(f"import {bridge_module(args.component, tag)}"
                 for tag in selected_tags)
    lines.extend([
        "", f"namespace Krenn.Component{args.component}.SelectedSubtree{module_suffix}",
        "", "set_option maxRecDepth 100000", "set_option maxHeartbeats 5000000", "",
    ])
    terminal_set = set(selected_tags)
    for tag in internal:
        lines.extend(emit_node(args.component, tag, spec, root_variables, terminal_set))
    theorem = f"subtree{module_suffix}Impossible"
    root_call = f"  exact {node_stem(prefix)} values rootZero"
    path_arguments = " ".join(path_argument_names(prefix))
    if path_arguments:
        root_call += " " + path_arguments
    lines.extend([
        f"/-- The frozen carrier subtree rooted at `{prefix}` has no common zero. -/",
        f"theorem {theorem} {{R : Type*}} [Field R] [CharZero R]",
        f"    (values : Fin {len(root_variables)} → R)",
        f"    (rootZero : Krenn.Component{args.component}.Root.RootCommonZero values)",
        *("    " + value for value in path_parameters(prefix, spec, root_variables)),
        "    : False := by",
        root_call,
        "",
        f"#print axioms Krenn.Component{args.component}.SelectedSubtree{module_suffix}.{theorem}",
        "", f"end Krenn.Component{args.component}.SelectedSubtree{module_suffix}", "",
    ])
    output = target_dir / f"SelectedSubtree{module_suffix}.lean"
    output.write_text("\n".join(lines))
    receipt = {
        "format": "krenn-selected-subtree-export-v1",
        "component": args.component,
        "prefix": prefix,
        "spec_sha256": sha256(spec_path),
        "manifest_sha256": sha256(manifest_path),
        "root_system_file_sha256": sha256((SHARED / spec["source_system"]).resolve()),
        "terminal_leaves": selected_tags,
        "internal_nodes": internal,
        "wrapper": str(output),
        "wrapper_sha256": sha256(output),
    }
    if args.receipt is not None:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps(receipt, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
