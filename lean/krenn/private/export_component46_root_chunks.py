#!/usr/bin/env python3
"""Export a component root connector as bounded Lean proof chunks.

The original one-module proof has 640 exact sparse-polynomial `simpa` steps.
Its mathematics is small, but elaborating all of them in one declaration can
exceed a bounded compile window.  This exporter keeps the same checked map,
then emits independent blocks plus a lightweight assembly module.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

import sympy as sp

from export_component46_root_common_zero import canonical, compose_component, json_canonical, sha256


def source_map(case_root: Path, external_component: int):
    sys.path.insert(0, str(case_root.parents[1]))
    from freeze_collapse_components import parse_components
    from strict_certificate_checker import frozen_poly, symbols_for

    base_path = case_root / "system.json"
    base = json.loads(base_path.read_text())
    names = base["variables"]
    symbols = symbols_for(names)
    base_equations = [frozen_poly(terms, symbols).as_expr() for terms in base["equations"]]
    components = parse_components(case_root / "minass.stdout", dict(zip(names, symbols, strict=True)))
    lean_component = external_component - 1
    if not 0 <= lean_component < len(components):
        raise ValueError(f"external component {external_component} is out of range")
    raw_component = components[lean_component]
    composed, residual = compose_component(raw_component)
    if len(base_equations) != 747:
        raise ValueError("frozen case-0 equation count drift")

    reduced_path = (case_root / "components_reduced_v2"
                    / f"component_{external_component:02d}" / "system.json")
    reduced = json.loads(reduced_path.read_text())
    reduced_symbols = symbols_for(reduced["variables"])
    target = [json_canonical(terms) for terms in reduced["equations"]]
    if len(reduced_symbols) != 75 - len(composed):
        raise ValueError("reduced root vocabulary does not match linear elimination")

    sources = {}
    for index, equation in enumerate(base_equations):
        normalized = sp.expand(equation.xreplace(composed))
        if normalized != 0:
            sources.setdefault(canonical(normalized, reduced_symbols), []).append(("base", index))
    for index, equation in enumerate(raw_component):
        normalized = sp.expand(equation.xreplace(composed))
        if normalized != 0:
            sources.setdefault(canonical(normalized, reduced_symbols), []).append(("component", index))

    chosen = []
    for index, equation in enumerate(target):
        options = sources.get(equation, [])
        base_options = [option for option in options if option[0] == "base"]
        component_options = [option for option in options if option[0] == "component"]
        if base_options:
            chosen.append(min(base_options, key=lambda option: option[1]))
        elif component_options:
            chosen.append(min(component_options, key=lambda option: option[1]))
        else:
            raise ValueError(f"no raw provenance for reduced equation {index}")

    return base_path, reduced_path, chosen, len(reduced_symbols)


def opens(normalization_namespace: str, bridge_namespace: str) -> list[str]:
  return [
    "open MvPolynomial",
    "open Krenn.SparseCertificate",
    "open Krenn.LatticeCombinationReflection",
    "open Krenn.CollapseReductionReflection",
    "open Krenn.CollapseComponentContainment",
    "open Krenn.CollapseComponentContainmentData",
    "open Krenn.FrozenCase0CollapseLayer",
    f"open {normalization_namespace}",
    f"open {bridge_namespace}",
  ]


def branch_lines(kind: str, source: int, tree_namespace: str,
                 root_leaf_namespace: str | None) -> list[str]:
    # Older component trees define their root equation vector by aliasing a
    # distinguished leaf's parent equations.  Selected-row trees instead
    # carry a direct generated root module.  The semantic proof only needs
    # the root vector itself; include the legacy alias in simp precisely when
    # it is how that vector is defined.
    legacy_parent = (
        f", {root_leaf_namespace}.parentEquations"
        if root_leaf_namespace is not None else ""
    )
    # A selected-row tree exposes its root vector through an adapter alias
    # rather than a legacy LeafB0 parent vector.  `simp` unfolds an abbrev
    # only one layer here, so include that direct implementation explicitly.
    # (Every current tree namespace ends in `.Tree`; fail loudly if that
    # interface convention changes instead of silently generating weak proof
    # scripts.)
    if root_leaf_namespace is None:
        if not tree_namespace.endswith(".Tree"):
            raise ValueError("direct-root tree namespace must end in .Tree")
        direct_root = f", {tree_namespace[:-len('.Tree')]}.Root.rootEquations"
    else:
        direct_root = ""
    base_simp = (
        f"{tree_namespace}.rootEquations{legacy_parent}{direct_root}, "
        "Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, "
        "rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg"
    )
    component_simp = (
        f"{tree_namespace}.rootEquations{legacy_parent}{direct_root}, "
        "rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate, "
        "monomial_add, monomial_single_one, SparsePoly.toPoly, SparseTerm.toPoly, "
        "rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg"
    )
    if kind == "base":
        return [
            f"  · have source := base {source}",
            "    rw [identified] at source",
            f"    simp [{base_simp}] at source ⊢",
            "    convert source using 1 <;> ac_rfl",
        ]
    return [
        f"  · have source := rawZero {source}",
        "    rw [identified] at source",
        f"    simp [{component_simp}] at source ⊢",
        "    convert source using 1 <;> ac_rfl",
    ]


def render_chunk(block: int, start: int, entries: list[tuple[str, int]], output: Path,
                 external_component: int, lean_component: int, root_variables: int,
                 namespace: str, normalization_namespace: str,
                 bridge_namespace: str, tree_namespace: str,
                 bridge_module: str, root_leaf_namespace: str | None) -> None:
    count = len(entries)
    lines = [
        f"import {bridge_module}",
        "",
        f"namespace {namespace}.Chunk{block}",
        "",
        *opens(normalization_namespace, bridge_namespace),
        "",
        "set_option linter.unusedSimpArgs false",
        "set_option linter.unreachableTactic false",
        "set_option linter.unusedTactic false",
        "set_option linter.unnecessarySeqFocus false",
        "",
        "set_option maxRecDepth 100000 in",
        "set_option maxHeartbeats 1500000 in",
        "theorem rootBlock_of_base_and_component {R : Type*} [CommRing R]",
        "    (full : Fin 75 → R) (base : Krenn.FrozenCase0System.CommonZero full)",
        f"    (selectedVanish : ∀ generator ∈ componentGenerators {lean_component},",
        "      generatorEval (reduceRaw (rawValues full)) generator = 0) :",
        f"    ∀ offset : Fin {count}, eval₂Hom (Int.castRingHom R) (rootValues full)",
        f"      ({tree_namespace}.rootEquations ⟨{start} + offset.val, by omega⟩).toPoly = 0 := by",
        "  have collapse := raw_collapse_of_base_common_zero full base",
        "  have rawZero : ∀ index, rawGeneratorEval (rawValues full) index = 0 :=",
        f"    rawComponent{external_component}_vanishes (rawValues full) collapse selectedVanish",
        "  have identified := full_eq_reconstruct_of_raw_component full rawZero",
        "  intro offset",
        "  fin_cases offset",
    ]
    for kind, source in entries:
        lines.extend(branch_lines(kind, source, tree_namespace, root_leaf_namespace))
    lines.extend(["", f"end {namespace}.Chunk{block}", ""])
    output.write_text("\n".join(lines))


def render_wrapper(block_count: int, chunk_size: int, output: Path, base_sha: str,
                   reduced_sha: str, map_sha: str, root_equation_count: int,
                   external_component: int, lean_component: int, namespace: str,
                   normalization_namespace: str, bridge_namespace: str,
                   tree_namespace: str) -> None:
    module_prefix = namespace.replace(".", "")
    imports = [f"import {module_prefix}Chunk{block}" for block in range(block_count)]
    lines = [
        *imports,
        "",
        "/-! The light assembly layer for the independently checked root blocks. -/",
        f"namespace {namespace}",
        "",
        *opens(normalization_namespace, bridge_namespace),
        "",
        f'def frozenBaseFileSHA256 : String := "{base_sha}"',
        f'def reducedComponentFileSHA256 : String := "{reduced_sha}"',
        f'def proofMapSHA256 : String := "{map_sha}"',
        "",
        "set_option maxRecDepth 100000 in",
        "set_option maxHeartbeats 5000000 in",
        "theorem rootCommonZero_of_base_and_component {R : Type*} [CommRing R]",
        "    (full : Fin 75 → R) (base : Krenn.FrozenCase0System.CommonZero full)",
        f"    (selectedVanish : ∀ generator ∈ componentGenerators {lean_component},",
        "      generatorEval (reduceRaw (rawValues full)) generator = 0) :",
        f"    {tree_namespace}.RootCommonZero (rootValues full) := by",
        "  intro index",
        "  fin_cases index",
    ]
    for index in range(root_equation_count):
        block = index // chunk_size
        offset = index % chunk_size
        lines.append(
            f"  · simpa using ({namespace}.Chunk{block}.rootBlock_of_base_and_component full base selectedVanish ⟨{offset}, by decide⟩)"
        )
    lines.extend([
        "",
        f"/-- Component {external_component} is now an end-to-end frozen-system contradiction. -/",
        f"theorem no_base_common_zero_on_component{external_component} {{R : Type*}} [Field R] [CharZero R]",
        "    (full : Fin 75 → R) (base : Krenn.FrozenCase0System.CommonZero full)",
        f"    (selectedVanish : ∀ generator ∈ componentGenerators {lean_component},",
        "      generatorEval (reduceRaw (rawValues full)) generator = 0) : False := by",
        f"  exact {tree_namespace}.component{external_component}HasNoCommonZero (rootValues full)",
        "    (rootCommonZero_of_base_and_component full base selectedVanish)",
        "",
        f"end {namespace}",
        "",
        f"#print axioms {namespace}.rootCommonZero_of_base_and_component",
        f"#print axioms {namespace}.no_base_common_zero_on_component{external_component}",
        "",
    ])
    output.write_text("\n".join(lines))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("case_root", type=Path)
    parser.add_argument("output", type=Path)
    # Forty equations is the established canonical block size for the
    # component-46 connector and keeps later high-degree components within
    # the same elaboration envelope.
    parser.add_argument("--chunk-size", type=int, default=40)
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--component-one-based", type=int, default=46)
    parser.add_argument("--namespace")
    parser.add_argument("--normalization-namespace")
    parser.add_argument("--bridge-namespace")
    parser.add_argument("--tree-namespace")
    parser.add_argument("--tree-module")
    parser.add_argument("--root-leaf-namespace")
    parser.add_argument(
        "--root-equations-direct", action="store_true",
        help="the tree namespace exposes rootEquations directly rather than via LeafB0.parentEquations",
    )
    args = parser.parse_args()
    if args.chunk_size < 1:
        raise ValueError("chunk size must be positive")
    external_component = args.component_one_based
    if external_component < 1:
        raise ValueError("component index must be positive")
    lean_component = external_component - 1
    namespace = args.namespace or f"Krenn.Component{external_component}RootCommonZero"
    normalization_namespace = (
        args.normalization_namespace
        or f"Krenn.Component{external_component}Normalization"
    )
    bridge_namespace = (
        args.bridge_namespace or f"Krenn.Component{external_component}RootBridge"
    )
    tree_namespace = args.tree_namespace or f"Krenn.Component{external_component}.Tree"
    tree_module = args.tree_module or f"KrennComponent{external_component}Tree"
    if args.root_equations_direct and args.root_leaf_namespace is not None:
        raise ValueError("root leaf namespace and direct-root mode are mutually exclusive")
    root_leaf_namespace = (
        None if args.root_equations_direct else
        args.root_leaf_namespace or f"Krenn.Component{external_component}.LeafB0"
    )
    root = args.case_root.resolve()
    base_path, reduced_path, chosen, root_variables = source_map(root, external_component)
    chunk_count = (len(chosen) + args.chunk_size - 1) // args.chunk_size
    for block in range(chunk_count):
        start = block * args.chunk_size
        render_chunk(
            block, start, chosen[start:start + args.chunk_size],
            args.output.parent / f"{namespace.replace('.', '')}Chunk{block}.lean",
            external_component, lean_component, root_variables, namespace,
            normalization_namespace, bridge_namespace, tree_namespace,
            bridge_namespace.replace(".", ""), root_leaf_namespace,
        )
    map_sha = hashlib.sha256(
        json.dumps(chosen, separators=(",", ":"), sort_keys=False).encode()
    ).hexdigest()
    render_wrapper(
        chunk_count, args.chunk_size, args.output, sha256(base_path),
        sha256(reduced_path), map_sha, len(chosen), external_component,
        lean_component, namespace, normalization_namespace, bridge_namespace,
        tree_namespace,
    )
    manifest = {
        "format": "krenn-component-root-chunks-export-v2",
        "namespace": namespace,
        "normalization_namespace": normalization_namespace,
        "bridge_namespace": bridge_namespace,
        "tree_namespace": tree_namespace,
        "tree_module": tree_module,
        "root_leaf_namespace": root_leaf_namespace,
        "root_equations_direct": args.root_equations_direct,
        "base_file_sha256": sha256(base_path),
        "reduced_component_file_sha256": sha256(reduced_path),
        "proof_map_sha256": map_sha,
        "external_component_index": external_component,
        "root_equation_count": len(chosen),
        "chunk_size": args.chunk_size,
        "chunk_count": chunk_count,
        "base_provenance_count": sum(kind == "base" for kind, _ in chosen),
        "component_provenance": [
            {"root_index": index, "raw_component_index": source}
            for index, (kind, source) in enumerate(chosen) if kind == "component"
        ],
    }
    if args.manifest:
        args.manifest.write_text(json.dumps(manifest, sort_keys=True, indent=2) + "\n")
    print(json.dumps(manifest, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
