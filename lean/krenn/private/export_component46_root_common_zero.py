#!/usr/bin/env python3
"""Serialize the exact 640-equation component-46 root connector to Lean.

For every root equation, the output names one frozen source equation (or one
of the five indispensable residual component equations), rewrites the full
valuation through the proved 14-step elimination, and lets Lean check the
resulting equality literally.  The script discovers the map but is not part
of the trusted proof.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

import sympy as sp


def canonical(expression: sp.Expr, variables: list[sp.Symbol]) -> tuple[tuple[int, tuple[int, ...]], ...]:
    return tuple(
        (int(coefficient), tuple(int(power) for power in exponent))
        for exponent, coefficient in sp.Poly(expression, *variables, domain=sp.ZZ).terms()
    )


def json_canonical(terms: list[list[object]]) -> tuple[tuple[int, tuple[int, ...]], ...]:
    return tuple(
        (int(coefficient), tuple(int(power) for power in exponent))
        for coefficient, exponent in terms
    )


def compose_component(component: list[sp.Expr]) -> tuple[dict[sp.Symbol, sp.Expr], list[sp.Expr]]:
    """Mirror `freeze_collapse_components.eliminate_linear` exactly."""
    current = [sp.expand(generator) for generator in component if generator != 0]
    composed: dict[sp.Symbol, sp.Expr] = {}
    while True:
        choice = None
        variables = sorted(
            {symbol for generator in current for symbol in generator.free_symbols},
            key=sp.default_sort_key,
        )
        for index, generator in enumerate(current):
            for variable in variables:
                coefficient = sp.expand(generator.coeff(variable))
                if coefficient.free_symbols or coefficient == 0:
                    continue
                remainder = sp.expand(generator - coefficient * variable)
                if variable in remainder.free_symbols:
                    continue
                choice = (index, variable, sp.expand(-remainder / coefficient))
                break
            if choice is not None:
                break
        if choice is None:
            break
        index, variable, replacement = choice
        composed = {
            old: sp.expand(value.subs(variable, replacement))
            for old, value in composed.items()
        }
        composed[variable] = replacement
        current = [
            sp.expand(generator.subs(variable, replacement))
            for offset, generator in enumerate(current)
            if offset != index
        ]
        current = [generator for generator in current if generator != 0]
    return composed, current


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("case_root", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--manifest", type=Path)
    args = parser.parse_args()
    root = args.case_root.resolve()
    sys.path.insert(0, str(root.parents[1]))
    from freeze_collapse_components import parse_components
    from strict_certificate_checker import frozen_poly, symbols_for

    base_path = root / "system.json"
    base = json.loads(base_path.read_text())
    names: list[str] = base["variables"]
    symbols = symbols_for(names)
    base_equations = [frozen_poly(terms, symbols).as_expr() for terms in base["equations"]]
    components = parse_components(root / "minass.stdout", dict(zip(names, symbols, strict=True)))
    raw_component = components[45]
    composed, residual = compose_component(raw_component)
    if len(base_equations) != 747 or len(raw_component) != 23 or len(composed) != 14 or len(residual) != 9:
        raise ValueError("external component-46 shape drift")

    reduced_path = root / "components_reduced_v2/component_46/system.json"
    reduced = json.loads(reduced_path.read_text())
    reduced_symbols = symbols_for(reduced["variables"])
    target = [json_canonical(terms) for terms in reduced["equations"]]
    if len(target) != 640 or len(reduced_symbols) != 61:
        raise ValueError("external component-46 reduced system drift")

    sources: dict[tuple[tuple[int, tuple[int, ...]], ...], list[tuple[str, int]]] = {}
    for index, equation in enumerate(base_equations):
        normalized = sp.expand(equation.xreplace(composed))
        if normalized != 0:
            sources.setdefault(canonical(normalized, reduced_symbols), []).append(("base", index))
    for index, equation in enumerate(raw_component):
        normalized = sp.expand(equation.xreplace(composed))
        if normalized != 0:
            sources.setdefault(canonical(normalized, reduced_symbols), []).append(("component", index))

    chosen: list[tuple[str, int]] = []
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
    base_count = sum(kind == "base" for kind, _ in chosen)
    component_rows = [(index, source) for index, source in enumerate(chosen) if source[0] == "component"]
    expected_component_rows = [(347, ("component", 2)), (346, ("component", 3)),
                               (281, ("component", 4)), (340, ("component", 6)),
                               (339, ("component", 7))]
    if base_count != 635 or sorted(component_rows) != sorted(expected_component_rows):
        raise ValueError(f"unexpected component provenance: base={base_count}, component={component_rows}")

    root_tree = Path("KrennComponent46Tree.lean")
    root_leaf = Path("KrennComponent46LeafB0.lean")
    lines = [
        "import KrennComponent46RootBridge",
        "",
        "/-!",
        "Exact full-system connector for external component 46.  Every branch",
        "below is a literal equality between one of the 640 tree-root equations",
        "and a frozen base or residual component equation after the verified",
        "linear elimination.  The Python map is discovery only; Lean checks the",
        "actual polynomial evaluations.",
        "-/",
        "",
        "namespace Krenn.Component46RootCommonZero",
        "",
        "open MvPolynomial",
        "open Krenn.SparseCertificate",
        "open Krenn.LatticeCombinationReflection",
        "open Krenn.CollapseReductionReflection",
        "open Krenn.CollapseComponentContainment",
        "open Krenn.CollapseComponentContainmentData",
        "open Krenn.FrozenCase0CollapseLayer",
        "open Krenn.Component46Normalization",
        "open Krenn.Component46RootBridge",
        "",
        f'def frozenBaseFileSHA256 : String := "{sha256(base_path)}"',
        f'def reducedComponentFileSHA256 : String := "{sha256(reduced_path)}"',
        f'def treeSourceSHA256 : String := "{sha256(root_tree)}"',
        f'def leafB0SourceSHA256 : String := "{sha256(root_leaf)}"',
        "",
        "set_option maxRecDepth 100000 in",
        "set_option maxHeartbeats 5000000 in",
        "theorem rootCommonZero_of_base_and_component {R : Type*} [CommRing R]",
        "    (full : Fin 75 → R) (base : Krenn.FrozenCase0System.CommonZero full)",
        "    (selectedVanish : ∀ generator ∈ componentGenerators 45,",
        "      generatorEval (reduceRaw (rawValues full)) generator = 0) :",
        "    Krenn.Component46.Tree.RootCommonZero (rootValues full) := by",
        "  have collapse := raw_collapse_of_base_common_zero full base",
        "  have rawZero : ∀ index, rawGeneratorEval (rawValues full) index = 0 :=",
        "    rawComponent46_vanishes (rawValues full) collapse selectedVanish",
        "  have identified := full_eq_reconstruct_of_raw_component full rawZero",
        "  intro index",
        "  fin_cases index",
    ]
    base_simp = (
        "Krenn.Component46.Tree.rootEquations, Krenn.Component46.LeafB0.parentEquations, "
        "Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, "
        "rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg"
    )
    component_simp = (
        "Krenn.Component46.Tree.rootEquations, Krenn.Component46.LeafB0.parentEquations, "
        "rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate, "
        "monomial_add, monomial_single_one, SparsePoly.toPoly, SparseTerm.toPoly, "
        "rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg"
    )
    for kind, source in chosen:
        if kind == "base":
            lines.extend([
                f"  · have source := base {source}",
                "    rw [identified] at source",
                f"    simpa [{base_simp}] using source",
            ])
        else:
            lines.extend([
                f"  · have source := rawZero {source}",
                "    rw [identified] at source",
                f"    simpa [{component_simp}] using source",
            ])
    lines.extend([
        "",
        "/-- A frozen case-0 valuation cannot satisfy the external component-46",
        "root system once its normalized component generators vanish. -/",
        "theorem no_base_common_zero_on_component46 {R : Type*} [Field R] [CharZero R]",
        "    (full : Fin 75 → R) (base : Krenn.FrozenCase0System.CommonZero full)",
        "    (selectedVanish : ∀ generator ∈ componentGenerators 45,",
        "      generatorEval (reduceRaw (rawValues full)) generator = 0) : False := by",
        "  exact Krenn.Component46.Tree.component46HasNoCommonZero (rootValues full)",
        "    (rootCommonZero_of_base_and_component full base selectedVanish)",
        "",
        "end Krenn.Component46RootCommonZero",
        "",
        "#print axioms Krenn.Component46RootCommonZero.rootCommonZero_of_base_and_component",
        "#print axioms Krenn.Component46RootCommonZero.no_base_common_zero_on_component46",
        "",
    ])
    args.output.write_text("\n".join(lines))
    manifest = {
        "format": "krenn-component46-root-common-zero-export-v1",
        "base_file_sha256": sha256(base_path),
        "external_component_index": 46,
        "reduced_component_file_sha256": sha256(reduced_path),
        "root_equation_count": len(chosen),
        "base_provenance_count": base_count,
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
