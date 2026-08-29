#!/usr/bin/env python3
"""Emit an exact raw-to-reduced normalization bridge for one component.

The source component is read from the frozen minimal-prime output.  The
exporter refuses any coefficient, variable, ordering, or normalized-generator
drift before writing a Lean module.  Lean then checks every individual
exponent-map equality; this script is only a serializer.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import sympy as sp


def expr_terms(expression: sp.Expr, variables: list[sp.Symbol]) -> tuple[list[tuple[int, ...]], list[tuple[int, ...]]]:
    positive: list[tuple[int, ...]] = []
    negative: list[tuple[int, ...]] = []
    for exponent, coefficient in sp.Poly(expression, *variables, domain=sp.ZZ).terms():
        if coefficient == 1:
            positive.append(tuple(exponent))
        elif coefficient == -1:
            negative.append(tuple(exponent))
        else:
            raise ValueError(f"non-unit coefficient in component generator: {expression}")
    if len(positive) != 1 or len(negative) > 1:
        raise ValueError(f"not a monomial/binomial generator: {expression}")
    return positive, negative


def exponent_expression(exponent: tuple[int, ...]) -> str:
    summands: list[str] = []
    for index, power in enumerate(exponent):
        if power:
            summands.append(f"Finsupp.single {index} {power}")
    if not summands:
        return "0"
    return " + ".join(summands)


def canonical(terms: list[tuple[tuple[int, ...], int]]) -> tuple[tuple[tuple[int, ...], int], ...]:
    return tuple(sorted(terms))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("case_root", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--component-one-based", type=int, default=46)
    parser.add_argument("--namespace")
    parser.add_argument(
        "--manifest", type=Path,
        help="optional JSON receipt for the emitted source",
    )
    args = parser.parse_args()
    external_component = args.component_one_based
    if external_component < 1:
        raise ValueError("component index must be positive")
    lean_component = external_component - 1
    namespace = args.namespace or f"Krenn.Component{external_component}Normalization"
    root = args.case_root.resolve()
    # case_root = .../krenn/allcollapse_case_artifacts/case_0; the solver
    # helpers live in the enclosing krenn directory.
    sys.path.insert(0, str(root.parents[1]))
    from replay_collapse_component_cover import derive_reduced_system
    from freeze_collapse_components import parse_components

    variables, determinants, _, substitutions = derive_reduced_system()
    all_variables = sorted(
        {symbol for determinant in determinants for symbol in determinant.free_symbols},
        key=sp.default_sort_key,
    )
    components = parse_components(
        root / "minass.stdout", {str(symbol): symbol for symbol in all_variables}
    )
    if lean_component >= len(components):
        raise ValueError(f"external component {external_component} is out of range")
    raw = components[lean_component]
    connector = json.loads(
        (root / "lean_connector_v2" / "connector_certificate.json").read_text()
    )
    if lean_component >= len(connector["components"]):
        raise ValueError(f"Lean component row {lean_component} is out of range")
    selected = connector["components"][lean_component]
    generator_ids: dict[tuple[tuple[tuple[int, ...], int], ...], int] = {}
    for index, generator in enumerate(connector["generators"]):
        generator_ids[canonical([
            (tuple(term["exponents"]), int(term["coefficient"]))
            for term in generator
        ])] = index

    raw_terms = [expr_terms(expression, all_variables) for expression in raw]
    normalized_indices: list[int | None] = []
    for expression in raw:
        normalized = sp.expand(expression.xreplace(substitutions))
        if normalized == 0:
            normalized_indices.append(None)
            continue
        terms = [
            (tuple(exponent), int(coefficient))
            for exponent, coefficient in sp.Poly(normalized, *variables, domain=sp.ZZ).terms()
        ]
        try:
            normalized_indices.append(generator_ids[canonical(terms)])
        except KeyError as error:
            raise ValueError(f"normalized generator missing from connector: {normalized}") from error
    if [index for index in normalized_indices if index is not None] != selected:
        raise ValueError(
            f"raw component {external_component} does not normalize to Lean row "
            f"{lean_component} in order"
        )

    positive_rows = [exponent_expression(positive[0]) for positive, _ in raw_terms]
    negative_rows = [
        "none" if not negative else f"some ({exponent_expression(negative[0])})"
        for _, negative in raw_terms
    ]
    lines = [
        "import KrennCollapseComponentContainmentCore",
        "import KrennCollapseReductionReflection",
        "",
        "/-!",
        f"Exact normalization of external minimal-prime component {external_component} into",
        f"zero-based Lean component row {lean_component}.  All exponent-map equalities are",
        "rechecked by Lean below; this source is generated only for serialization.",
        "-/",
        "",
        f"namespace {namespace}",
        "",
        "open Krenn.LatticeCombinationReflection",
        "open Krenn.CollapseReductionReflection",
        "open Krenn.CollapseComponentContainment",
        "open Krenn.CollapseComponentContainmentData",
        "",
        f"noncomputable def rawPositive : Fin {len(raw)} → Fin 30 →₀ Nat := ![",
    ]
    lines.extend("  " + row + ("," if i + 1 < len(positive_rows) else "")
                 for i, row in enumerate(positive_rows))
    lines.extend([
        "]",
        "",
        f"noncomputable def rawNegative : Fin {len(raw)} → Option (Fin 30 →₀ Nat) := ![",
    ])
    lines.extend("  " + row + ("," if i + 1 < len(negative_rows) else "")
                 for i, row in enumerate(negative_rows))
    lines.extend([
        "]",
        "",
        f"def normalizedIndex : Fin {len(raw)} → Option (Fin {len(connector['generators'])}) := ![",
    ])
    normalized_rows = ["none" if index is None else f"some {index}" for index in normalized_indices]
    lines.extend("  " + row + ("," if i + 1 < len(normalized_rows) else "")
                 for i, row in enumerate(normalized_rows))
    lines.extend([
        "]",
        "",
        f"def selectedIndices : List (Fin {len(connector['generators'])}) := [",
        "  " + ", ".join(map(str, selected)),
        "]",
        "",
        "set_option maxRecDepth 100000 in",
        f"theorem selectedIndices_exact : componentGenerators {lean_component} = selectedIndices := by decide",
        "",
        "noncomputable def rawGeneratorEval {R : Type*} [CommRing R]",
        f"    (values : Fin 30 → R) (index : Fin {len(raw)}) : R :=",
        "  monomial values (rawPositive index) -",
        "    match rawNegative index with",
        "    | none => 0",
        "    | some negative => monomial values negative",
        "",
    ])

    common = [
        "rawToReduced", "Finsupp.mapDomain_add", "Finsupp.mapDomain_single",
        "generatorPositive", "generatorPositiveSupport", "generatorNegative",
        "generatorNegativeSupport", "squarefreeExponent", "Nat.testBit",
        "Nat.shiftRight_eq_div_pow",
    ]
    for source, target in enumerate(normalized_indices):
        if target is None:
            lines.extend([
                "set_option maxRecDepth 100000 in",
                f"theorem rawZeroMap{source:02d} :",
                f"    Finsupp.mapDomain rawToReduced (rawPositive {source}) =",
                f"      Finsupp.mapDomain rawToReduced ((rawNegative {source}).getD 0) := by",
                "  ext coordinate",
                "  fin_cases coordinate <;>",
                "    simp [rawPositive, rawNegative, " + ", ".join(common) + "]",
                "",
            ])
            continue
        lines.extend([
            "set_option maxRecDepth 100000 in",
            f"theorem rawPositiveMap{source:02d} :",
            f"    Finsupp.mapDomain rawToReduced (rawPositive {source}) = generatorPositive {target} := by",
            "  ext coordinate",
            "  fin_cases coordinate <;>",
            "    simp [rawPositive, " + ", ".join(common) + "]",
            "",
        ])
        if raw_terms[source][1]:
            lines.extend([
                "set_option maxRecDepth 100000 in",
                f"theorem rawNegativeMap{source:02d} :",
                f"    Finsupp.mapDomain rawToReduced ((rawNegative {source}).getD 0) =",
                f"      (generatorNegative {target}).getD 0 := by",
                "  ext coordinate",
                "  fin_cases coordinate <;>",
                "    simp [rawNegative, " + ", ".join(common) + "]",
                "",
            ])

    lines.extend([
        "set_option maxRecDepth 100000 in",
        "theorem rawGeneratorNormalizes {R : Type*} [CommRing R]",
        f"    (values : Fin 26 → R) (index : Fin {len(raw)}) :",
        "    rawGeneratorEval (liftReduced values) index =",
        "      match normalizedIndex index with",
        "      | none => 0",
        "      | some generator => generatorEval values generator := by",
        "  fin_cases index",
    ])
    for source, target in enumerate(normalized_indices):
        positive = f"(rawPositive {source})"
        negative = f"((rawNegative {source}).getD 0)"
        if target is None:
            lines.extend([
                f"  · change monomial (fun coordinate => values (rawToReduced coordinate)) {positive} -",
                f"      monomial (fun coordinate => values (rawToReduced coordinate)) {negative} = 0",
                f"    rw [monomial_mapDomain rawToReduced values {positive},",
                f"      monomial_mapDomain rawToReduced values {negative}, rawZeroMap{source:02d}]",
                "    ring",
            ])
        elif raw_terms[source][1]:
            lines.extend([
                f"  · change monomial (fun coordinate => values (rawToReduced coordinate)) {positive} -",
                f"      monomial (fun coordinate => values (rawToReduced coordinate)) {negative} =",
                f"        generatorEval values {target}",
                f"    rw [monomial_mapDomain rawToReduced values {positive},",
                f"      monomial_mapDomain rawToReduced values {negative}, rawPositiveMap{source:02d},",
                f"      rawNegativeMap{source:02d}]",
                "    simp [generatorEval, generatorNegative, generatorNegativeSupport]",
            ])
        else:
            lines.extend([
                f"  · change monomial (fun coordinate => values (rawToReduced coordinate)) {positive} - 0 =",
                f"        generatorEval values {target}",
                f"    rw [monomial_mapDomain rawToReduced values {positive}, rawPositiveMap{source:02d}]",
                "    simp [generatorEval, generatorNegative, generatorNegativeSupport]",
            ])

    lines.extend([
        "",
        "set_option maxRecDepth 100000 in",
        f"theorem rawComponent{external_component}_vanishes {{R : Type*}} [CommRing R]",
        "    (values : Fin 30 → R) (collapse : SatisfiesRawCollapse values)",
        f"    (selectedVanish : ∀ generator ∈ componentGenerators {lean_component},",
        "      generatorEval (reduceRaw values) generator = 0) :",
        "    ∀ index, rawGeneratorEval values index = 0 := by",
        "  have identified : values = liftReduced (reduceRaw values) :=",
        "    raw_eq_liftReduced_reduceRaw values",
        "      (raw_binomial_equalities_of_collapse collapse)",
        "  rw [identified]",
        "  intro index",
        "  rw [rawGeneratorNormalizes]",
        "  fin_cases index",
    ])
    for target in normalized_indices:
        if target is None:
            lines.append("  · simp [normalizedIndex]")
        else:
            lines.append(f"  · exact selectedVanish {target} (by decide)")
    lines.extend([
        "",
        f"end {namespace}",
        "",
        f"#print axioms {namespace}.rawComponent{external_component}_vanishes",
        "",
    ])
    args.output.write_text("\n".join(lines), encoding="utf-8")
    manifest = {
        "format": "krenn-component-normalization-export-v2",
        "raw_generators": len(raw),
        "normalized_generators": len(selected),
        "external_component_index": external_component,
        "lean_component_index": lean_component,
    }
    if args.manifest is not None:
        args.manifest.parent.mkdir(parents=True, exist_ok=True)
        args.manifest.write_text(json.dumps(manifest, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(manifest, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
