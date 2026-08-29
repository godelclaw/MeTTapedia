#!/usr/bin/env python3
"""Attach a strict frozen f9 certificate to official Krenn equations in Lean.

The input certificate is checked exactly before generation.  The exporter
then finds the unique official colouring that produced every selected frozen
generator and emits only those semantic reductions.  Discovery remains
untrusted: Lean re-evaluates each official equation and the separately
generated sparse module replays the integer certificate.
"""

from __future__ import annotations

import os
import argparse
import itertools
import json
import re
import sys
from pathlib import Path

import sympy as sp

KRENN_ROOT = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
sys.path.insert(0, str(KRENN_ROOT))

import f9_pipeline as pipeline  # noqa: E402
from krenn_exact import perfect_matchings  # noqa: E402
from strict_certificate_checker import (  # noqa: E402
    check_c4,
    frozen_poly,
    load_json_strict,
    symbols_for,
    validate_variable_names,
)


def parse_variable(name: str) -> tuple[int, int, int, int]:
    match = re.fullmatch(r"w_(\d)(\d)_(\d)(\d)", name)
    if match is None:
        raise ValueError(f"unsupported frozen variable: {name!r}")
    return tuple(map(int, match.groups()))  # type: ignore[return-value]


def edge_term(u: int, v: int, i: int | str, j: int | str) -> str:
    return (
        "W (MonochromaticQuantumGraph.mkEdge "
        f"{u} {v} {i} {j})"
    )


def official_colourings(
    system: dict[str, object], selected: list[int], symbols: tuple[sp.Symbol, ...]
) -> list[tuple[int, ...]]:
    problem = system["problem"]
    if not isinstance(problem, dict):
        raise ValueError("missing frozen problem metadata")
    support = [tuple(edge) for edge in problem["mixed_support"]]
    fixed_entries = [
        (tuple(edge), int(i), int(j))
        for edge, i, j in problem["fixed_entries"]
    ]
    variables, _ = pipeline.build(support)
    replacement = {variables[entry]: sp.Integer(1) for entry in fixed_entries}
    equations = [frozen_poly(row, symbols) for row in system["equations"]]
    targets = {equations[index].as_expr(): index for index in selected}
    hits: dict[int, list[tuple[int, ...]]] = {index: [] for index in selected}
    matchings = [tuple(sorted(value)) for value in perfect_matchings(6)]
    for colouring in itertools.product(range(3), repeat=6):
        total = sp.Integer(0)
        for matching in matchings:
            term = sp.Integer(1)
            for u, v in matching:
                factor = variables.get(((u, v), colouring[u], colouring[v]))
                if factor is None:
                    term = sp.Integer(0)
                    break
                term *= factor
            total += term
        target = 1 if len(set(colouring)) == 1 else 0
        reduced = sp.expand((total - target).xreplace(replacement))
        index = targets.get(reduced)
        if index is not None:
            hits[index].append(colouring)
    bad = {index: values for index, values in hits.items() if len(values) != 1}
    if bad:
        raise ValueError(f"selected equations do not have unique colourings: {bad}")
    return [hits[index][0] for index in selected]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("system", type=Path)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--certificate-module", required=True)
    parser.add_argument("--certificate-namespace", required=True)
    parser.add_argument("--namespace", required=True)
    args = parser.parse_args()

    verdict = check_c4(args.system, args.certificate)
    selected = [value - 1 for value in verdict["nonzero_multiplier_indices_1based"]]
    system = load_json_strict(args.system)
    if system.get("format") != "krenn-f9-frozen-case-v1":
        raise ValueError("bridge exporter requires a frozen f9 case")
    names = validate_variable_names(system["variables"])
    symbols = symbols_for(names)
    colourings = official_colourings(system, selected, symbols)
    problem = system["problem"]
    support = {tuple(edge) for edge in problem["mixed_support"]}
    fixed = [(tuple(edge), int(i), int(j)) for edge, i, j in problem["fixed_entries"]]
    zero = [(tuple(edge), int(i), int(j)) for edge, i, j in problem["zero_entries"]]
    all_edges = {(u, v) for u in range(6) for v in range(u + 1, 6)}
    outside = sorted(all_edges - support)

    lines = [
        "import KrennOfficialBridge",
        f"import {args.certificate_module}",
        "",
        "/-! Generated semantic attachment for one frozen normalized f9 case. -/",
        "",
        f"namespace {args.namespace}",
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
    ]
    for edge, i, j in fixed:
        u, v = edge
        lines.append(f"  fixed_{u}{v}_{i}{j} : {edge_term(u, v, i, j)} = 1")
    for edge, i, j in zero:
        u, v = edge
        lines.append(f"  zero_{u}{v}_{i}{j} : {edge_term(u, v, i, j)} = 0")
    for u, v in outside:
        lines.append(
            f"  outside{u}{v} : ∀ i j, i ≠ j → {edge_term(u, v, 'i', 'j')} = 0"
        )

    lines.extend([
        "",
        f"def values (W : WeightsN 6 3 ℂ) : Fin {len(names)} → ℂ := ![",
    ])
    for offset, name in enumerate(names):
        u, v, i, j = parse_variable(name)
        comma = "," if offset + 1 < len(names) else ""
        lines.append(f"  entry W {u} {v} {i} {j}{comma}")
    lines.append("]")
    lines.append("")
    for offset, colouring in enumerate(colourings):
        values = ", ".join(map(str, colouring))
        lines.append(f"private def c{offset} : Fin 6 → Fin 3 := ![{values}]")

    count = len(selected)
    lines.extend([
        "",
        "set_option maxRecDepth 100000 in",
        "set_option maxHeartbeats 5000000 in",
        "theorem selectedEquations_vanish (W : WeightsN 6 3 ℂ)",
        "    (hEq : EqSystemN 6 3 W) (hcase : NormalizedCase W) :",
        f"    ∀ index : Fin {count},",
        "      eval₂Hom (Int.castRingHom ℂ) (values W)",
        f"        ({args.certificate_namespace}.selectedEquations index).toPoly = 0 := by",
        "  intro index",
    ])
    for offset in range(count):
        lines.append(f"  have r{offset} := hEq c{offset}")
    rows = " ".join(f"r{offset}" for offset in range(count))
    lines.append(f"  rw [official_pmSum_eq_pm15] at {rows}")
    simp_values = [
        "pm15", "w", *(f"c{i}" for i in range(count)),
        "allEqual", "allEqualList", "vertices",
        *(f"hcase.fixed_{u}{v}_{i}{j}" for (u, v), i, j in fixed),
        *(f"hcase.zero_{u}{v}_{i}{j}" for (u, v), i, j in zero),
        *(f"hcase.outside{u}{v}" for u, v in outside),
    ]
    # Preserve polynomial equalities.  The default simp set contains
    # `mul_eq_zero` over C and would turn useful equations into
    # disjunctions before the algebraic normalizer sees them.
    lines.append(
        "  simp [-mul_eq_zero, "
        + ", ".join(simp_values) + f"] at {rows}"
    )
    lines.append("  fin_cases index")
    eval_simp = (
        f"{args.certificate_namespace}.selectedEquations, "
        "SparsePoly.toPoly, SparseTerm.toPoly, values, entry, "
        "Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one"
    )
    for offset, _colouring in enumerate(colourings):
        # The frozen polynomial and the official pmSum equation can list the
        # same commutative summands in different orders.  `simpa using` is
        # accidentally order-sensitive here; polynomial normalization is the
        # semantic check we actually want for every row, monochromatic or not.
        lines.extend([
            f"  · simp [-mul_eq_zero, {eval_simp}]",
            f"    linear_combination r{offset}",
        ])
    lines.extend([
        "",
        "theorem noNormalizedCase (W : WeightsN 6 3 ℂ)",
        "    (hEq : EqSystemN 6 3 W) (hcase : NormalizedCase W) : False := by",
        f"  exact ({args.certificate_namespace}.selectedHasNoCommonZero (values W))",
        "    (selectedEquations_vanish W hEq hcase)",
        "",
        f"#print axioms {args.namespace}.noNormalizedCase",
        "",
        f"end {args.namespace}",
        "",
    ])
    args.output.write_text("\n".join(lines), encoding="utf-8")
    print(json.dumps({
        "selected_rows": selected,
        "colourings": colourings,
        "variables": len(names),
        "system_file_sha256": verdict["system_file_sha256"],
        "certificate_file_sha256": verdict["certificate_file_sha256"],
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
