#!/usr/bin/env python3
"""Emit a semantic bridge into one external component carrier tree.

This is deliberately a serializer, not a prover.  It reconstructs the
component's ordered linear elimination from the frozen minimal-prime input,
checks the 61-variable root vocabulary, then emits finite Lean data and
proofs.  Lean rechecks the equations and all evaluation identities.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import sympy as sp


RAW_COORDINATE = [
    10, 11, 13, 14, 15, 18, 19, 21, 22, 23,
    26, 27, 29, 30, 31, 34, 35, 37, 38, 39,
    54, 55, 57, 58, 59, 62, 63, 65, 66, 67,
]


def parse_component_with_composed_substitutions(
    component: list[sp.Expr],
) -> tuple[list[sp.Expr], list[tuple[sp.Symbol, sp.Expr]], dict[sp.Symbol, sp.Expr], dict[sp.Symbol, int]]:
    """Exact copy of the eliminator, retaining pivot provenance."""
    current: list[tuple[sp.Expr, int]] = [
        (sp.expand(generator), index)
        for index, generator in enumerate(component)
        if generator != 0
    ]
    substitutions: list[tuple[sp.Symbol, sp.Expr]] = []
    composed: dict[sp.Symbol, sp.Expr] = {}
    pivot_source: dict[sp.Symbol, int] = {}
    while True:
        choice = None
        variables = sorted(
            {symbol for generator, _ in current for symbol in generator.free_symbols},
            key=sp.default_sort_key,
        )
        for index, (generator, source) in enumerate(current):
            for variable in variables:
                coefficient = sp.expand(generator.coeff(variable))
                if coefficient.free_symbols or coefficient == 0:
                    continue
                remainder = sp.expand(generator - coefficient * variable)
                if variable in remainder.free_symbols:
                    continue
                choice = (index, variable, sp.expand(-remainder / coefficient), source)
                break
            if choice is not None:
                break
        if choice is None:
            break
        index, variable, replacement, source = choice
        substitutions.append((variable, replacement))
        pivot_source[variable] = source
        composed = {
            old: sp.expand(value.subs(variable, replacement))
            for old, value in composed.items()
        }
        composed[variable] = replacement
        current = [
            (sp.expand(generator.subs(variable, replacement)), old_source)
            for offset, (generator, old_source) in enumerate(current)
            if offset != index
        ]
        current = [(generator, source) for generator, source in current if generator != 0]
    return [generator for generator, _ in current], substitutions, composed, pivot_source


def product_expression(indices: list[int], powers: list[int] | None = None, value_name: str = "full") -> str:
    if powers is None:
        powers = [1] * len(indices)
    parts = []
    for index, power in zip(indices, powers, strict=True):
        atom = f"{value_name} {index}"
        parts.append(atom if power == 1 else f"({atom}) ^ {power}")
    if not parts:
        return "1"
    return " * ".join(parts)


def raw_expression(
    expression: sp.Expr,
    raw_symbols: list[sp.Symbol],
    full_index: dict[str, int],
) -> str:
    positive: list[tuple[tuple[int, ...], int]] = []
    negative: list[tuple[tuple[int, ...], int]] = []
    for exponent, coefficient in sp.Poly(expression, *raw_symbols, domain=sp.ZZ).terms():
        if coefficient == 1:
            positive.append((tuple(exponent), int(coefficient)))
        elif coefficient == -1:
            negative.append((tuple(exponent), int(coefficient)))
        else:
            raise ValueError(f"non-unit coefficient in raw generator: {expression}")
    if len(positive) != 1 or len(negative) > 1:
        raise ValueError(f"not an oriented monomial/binomial: {expression}")
    def term(exponent: tuple[int, ...]) -> str:
        indices: list[int] = []
        powers: list[int] = []
        for position, power in enumerate(exponent):
            if power:
                indices.append(full_index[str(raw_symbols[position])])
                powers.append(power)
        return product_expression(indices, powers)
    right = "0" if not negative else term(negative[0][0])
    return f"{term(positive[0][0])} - {right}"


def expression_on_coordinates(
    expression: sp.Expr,
    coordinate_index: dict[str, int],
    value_name: str,
) -> str:
    if expression == 0:
        return "0"
    if not expression.free_symbols:
        if expression == 1:
            return "1"
        if expression == -1:
            return "-1"
        raise ValueError(f"unexpected constant replacement: {expression}")
    polynomial = sp.Poly(expression, *sorted(expression.free_symbols, key=sp.default_sort_key), domain=sp.ZZ)
    terms = polynomial.terms()
    if not terms:
        return "0"
    rendered: list[str] = []
    symbols = list(polynomial.gens)
    for exponent, coefficient in terms:
        if coefficient not in (1, -1):
            raise ValueError(f"non-unit replacement coefficient: {expression}")
        indices: list[int] = []
        powers: list[int] = []
        for symbol, power in zip(symbols, exponent, strict=True):
            if power:
                indices.append(coordinate_index[str(symbol)])
                powers.append(power)
        body = product_expression(indices, powers, value_name)
        if body == "1":
            rendered.append("1" if coefficient == 1 else "-1")
        elif coefficient == 1:
            rendered.append(body)
        else:
            rendered.append(f"-({body})")
    return " + ".join(rendered)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("case_root", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--component-one-based", type=int, default=46)
    parser.add_argument("--namespace")
    parser.add_argument("--normalization-namespace")
    parser.add_argument("--tree-module")
    parser.add_argument(
        "--manifest", type=Path,
        help="optional JSON receipt for the emitted source",
    )
    args = parser.parse_args()
    external_component = args.component_one_based
    if external_component < 1:
        raise ValueError("component index must be positive")
    lean_component = external_component - 1
    namespace = args.namespace or f"Krenn.Component{external_component}RootBridge"
    normalization_namespace = (
        args.normalization_namespace
        or f"Krenn.Component{external_component}Normalization"
    )
    tree_module = args.tree_module or f"KrennComponent{external_component}Tree"
    root = args.case_root.resolve()
    sys.path.insert(0, str(root.parents[1]))
    from freeze_collapse_components import parse_components
    from replay_collapse_component_cover import derive_reduced_system
    from strict_certificate_checker import frozen_poly, symbols_for

    base = json.loads((root / "system.json").read_text())
    full_names: list[str] = base["variables"]
    full_index = {name: index for index, name in enumerate(full_names)}
    if len(full_names) != 75 or len(full_index) != 75:
        raise ValueError("frozen full vocabulary drift")
    raw_symbols, determinants, _, _ = derive_reduced_system()
    raw_symbols = sorted(
        {symbol for determinant in determinants for symbol in determinant.free_symbols},
        key=sp.default_sort_key,
    )
    if [full_index[str(symbol)] for symbol in raw_symbols] != RAW_COORDINATE:
        raise ValueError("raw-to-full coordinate map drift")
    components = parse_components(root / "minass.stdout", dict(zip(full_names, symbols_for(full_names), strict=True)))
    if lean_component >= len(components):
        raise ValueError(f"external component {external_component} is out of range")
    component = components[lean_component]
    residual, substitutions, composed, pivot_source = parse_component_with_composed_substitutions(component)
    reduced_path = root / "components_reduced_v2" / f"component_{external_component:02d}" / "system.json"
    reduced = json.loads(reduced_path.read_text())
    freeze = json.loads(reduced_path.with_name("freeze_manifest.json").read_text())
    reduced_names: list[str] = reduced["variables"]
    root_coordinate = [full_index[name] for name in reduced_names]
    if len(root_coordinate) != 75 - len(substitutions) or len(set(root_coordinate)) != len(root_coordinate):
        raise ValueError("reduced root vocabulary does not match linear elimination")
    root_index = {name: index for index, name in enumerate(reduced_names)}
    eliminated = sorted(set(range(75)) - set(root_coordinate))
    if (len(eliminated) != len(substitutions)
            or set(full_names[index] for index in eliminated)
            != {str(v) for v, _ in substitutions}):
        raise ValueError("eliminated-variable vocabulary drift")

    # The 14 original pivot equations, written in the exact raw-normalizer
    # orientation.  Their final right-hand sides come from the composed map.
    pivot_rows: list[tuple[int, int, str, str, str]] = []
    for variable, replacement in substitutions:
        source = pivot_source[variable]
        full_coordinate = full_index[str(variable)]
        original_relation = raw_expression(component[source], raw_symbols, full_index)
        coefficient = sp.expand(component[source].coeff(variable))
        source_remainder = sp.expand(component[source] - coefficient * variable)
        source_replacement = expression_on_coordinates(
            sp.expand(-source_remainder / coefficient), full_index, "full"
        )
        final_replacement = expression_on_coordinates(composed[variable], full_index, "full")
        pivot_rows.append((full_coordinate, source, original_relation,
                           source_replacement, final_replacement))
    pivot_by_full = {coordinate: (source, relation, discovery, final)
                     for coordinate, source, relation, discovery, final in pivot_rows}
    dependencies: dict[int, set[int]] = {}
    for coordinate, source, _, _, _ in pivot_rows:
        variable = full_names[coordinate]
        dependencies[coordinate] = {
            full_index[str(symbol)]
            for symbol in component[source].free_symbols
            if str(symbol) != variable and full_index[str(symbol)] in pivot_by_full
        }
    elimination_order: list[int] = []
    remaining = set(pivot_by_full)
    while remaining:
        ready = sorted(
            coordinate for coordinate in remaining
            if dependencies[coordinate].issubset(elimination_order)
        )
        if not ready:
            raise ValueError(f"cyclic linear-elimination dependencies: {remaining}")
        elimination_order.extend(ready)
        remaining.difference_update(ready)

    lines = [
        f"import {normalization_namespace.replace('.', '')}",
        "import KrennFrozenCase0CollapseLayer",
        "import KrennFrozenCase0System",
        f"import {tree_module}",
        "",
        "/-!",
        "The semantic seam from a full frozen case-0 valuation through the",
        f"external component-{external_component} linear elimination.  The generated finite data",
        "are rechecked by Lean; source hashes below are provenance only.",
        "-/",
        "",
        f"namespace {namespace}",
        "",
        "open MvPolynomial",
        "open Krenn.SparseCertificate",
        "open Krenn.LatticeCombinationReflection",
        "open Krenn.CollapseReductionReflection",
        "open Krenn.FrozenCase0CollapseLayer",
        f"open {normalization_namespace}",
        "",
        f'def reducedRootSystemSHA256 : String := "{reduced["system_sha256"]}"',
        f'def reducedRootFileSHA256 : String := "{freeze["system_file_sha256"]}"',
        "",
        f"def rootCoordinate : Fin {len(root_coordinate)} → Fin 75 := ![",
        "  " + ", ".join(map(str, root_coordinate)),
        "]",
        "",
        f"noncomputable def rootValues {{R : Type*}} (full : Fin 75 → R) : Fin {len(root_coordinate)} → R :=",
        "  fun coordinate => full (rootCoordinate coordinate)",
        "",
        "noncomputable def reconstructFull {R : Type*} [CommRing R]",
        f"    (values : Fin {len(root_coordinate)} → R) : Fin 75 → R := ![",
    ]
    inverse_root = {full: root for root, full in enumerate(root_coordinate)}
    for full in range(75):
        name = full_names[full]
        if name in {str(variable) for variable, _ in substitutions}:
            expr = expression_on_coordinates(
                composed[next(variable for variable, _ in substitutions if str(variable) == name)],
                root_index,
                "values",
            )
        else:
            expr = f"values {inverse_root[full]}"
        lines.append("  " + expr + ("," if full != 74 else ""))
    lines.extend([
        "]",
        "",
        "set_option maxRecDepth 100000 in",
        "theorem full_eq_reconstruct_of_raw_component {R : Type*} [CommRing R]",
        "    (full : Fin 75 → R) (rawZero : ∀ index,",
        "      rawGeneratorEval (rawValues full) index = 0) :",
        "    full = reconstructFull (rootValues full) := by",
    ])
    # Preserve all raw pivot equations in their source orientation.
    for full_coordinate, source, relation, _, _ in pivot_rows:
        lines.extend([
            f"  have rawRelation{full_coordinate} : {relation} = 0 := by",
            f"    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,",
            f"      monomial_add, monomial_single_one] using rawZero {source}",
        ])
    # Compose in the actual eliminator order.  The exact final target is
    # derived by rewriting older components, then simplifying the relation.
    for full_coordinate in elimination_order:
        source, relation, discovery_replacement, final_replacement = pivot_by_full[full_coordinate]
        lines.append(f"  have eliminated{full_coordinate} : full {full_coordinate} = {final_replacement} := by")
        prior = sorted(dependencies[full_coordinate])
        if prior:
            lines.extend([
                "    calc",
                f"      full {full_coordinate} = {discovery_replacement} :=",
                f"        sub_eq_zero.mp rawRelation{full_coordinate}",
                f"      _ = {final_replacement} := by",
                "        simp [" + ", ".join(f"eliminated{coordinate}" for coordinate in prior) + "]",
            ])
        else:
            lines.append(f"    exact sub_eq_zero.mp rawRelation{full_coordinate}")
    lines.extend([
        "  funext coordinate",
        "  fin_cases coordinate <;>",
        "    simp [reconstructFull, rootValues, rootCoordinate, *]",
        "",
        f"end {namespace}",
        "",
        f"#print axioms {namespace}.full_eq_reconstruct_of_raw_component",
        "",
    ])
    args.output.write_text("\n".join(lines))
    manifest = {
        "format": "krenn-component-root-bridge-export-v2",
        "external_component_index": external_component,
        "linear_eliminations": len(substitutions),
        "raw_generators": len(component),
        "root_variables": len(root_coordinate),
    }
    if args.manifest is not None:
        args.manifest.parent.mkdir(parents=True, exist_ok=True)
        args.manifest.write_text(json.dumps(manifest, sort_keys=True) + "\n")
    print(json.dumps(manifest, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
