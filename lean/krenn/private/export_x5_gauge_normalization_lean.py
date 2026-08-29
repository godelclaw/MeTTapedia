#!/usr/bin/env python3
"""Export checked integral gauge-normalization data for X5 representatives."""

from __future__ import annotations

import os
import argparse
import hashlib
import itertools
import json
import sys
from pathlib import Path
from typing import Any

import sympy as sp


KRENN_ROOT = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
sys.path.insert(0, str(KRENN_ROOT))

import f9_pipeline  # noqa: E402
from audit_x5_0415_closure import (  # noqa: E402
    SUPPORT_TEXT,
    exact_case_representatives,
)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def coordinate(vertex: int, colour: int) -> list[int]:
    row = [0] * 15
    if vertex < 5:
        row[3 * vertex + colour] = 1
    else:
        for other in range(5):
            row[3 * other + colour] = -1
    return row


def determinant(matrix: list[list[int]]) -> int:
    """Fraction-free exact determinant for the small 5 by 5 minors."""
    work = [row[:] for row in matrix]
    sign = 1
    previous = 1
    for pivot_column in range(4):
        pivot_row = next(
            (row for row in range(pivot_column, 5)
             if work[row][pivot_column] != 0),
            None,
        )
        if pivot_row is None:
            return 0
        if pivot_row != pivot_column:
            work[pivot_column], work[pivot_row] = (
                work[pivot_row], work[pivot_column]
            )
            sign = -sign
        pivot = work[pivot_column][pivot_column]
        for row in range(pivot_column + 1, 5):
            for column in range(pivot_column + 1, 5):
                numerator = (
                    work[row][column] * pivot
                    - work[row][pivot_column] * work[pivot_column][column]
                )
                if numerator % previous != 0:
                    raise ValueError("fraction-free determinant lost integrality")
                work[row][column] = numerator // previous
        previous = pivot
    return sign * work[4][4]


def right_inverse(rows: list[list[int]]) -> tuple[list[int], list[list[int]]]:
    for columns in itertools.combinations(range(15), 5):
        minor = [[row[column] for column in columns] for row in rows]
        if abs(determinant(minor)) != 1:
            continue
        inverse_q = sp.Matrix(minor).inv()
        inverse = [[int(inverse_q[row, column]) for column in range(5)]
                   for row in range(5)]
        if any(sp.Rational(inverse_q[row, column]).q != 1
               for row in range(5) for column in range(5)):
            raise ValueError("unimodular minor produced a nonintegral inverse")
        full = [[0] * 5 for _ in range(15)]
        for local_row, global_row in enumerate(columns):
            full[global_row] = inverse[local_row]
        product = sp.Matrix(rows) * sp.Matrix(full)
        if product != sp.eye(5):
            raise ValueError("exported integer matrix is not a right inverse")
        return list(columns), full
    raise ValueError("no unimodular five-column minor")


def lean_vector(values: list[Any], render) -> str:
    return "![" + ", ".join(render(value) for value in values) + "]"


def lean_int(value: int) -> str:
    return str(value) if value >= 0 else f"({value})"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    selection = parser.add_mutually_exclusive_group(required=True)
    selection.add_argument("--case-index", type=int, action="append")
    selection.add_argument("--all", action="store_true")
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()

    representatives, cover = exact_case_representatives()
    requested = ([int(case) for case, _choice, _orbit_size in representatives]
                 if args.all else args.case_index)
    assert requested is not None
    if len(requested) != len(set(requested)):
        raise ValueError("duplicate requested case index")
    by_case = {int(case): (choice, int(orbit_size))
               for case, choice, orbit_size in representatives}
    if set(requested) - set(by_case):
        raise ValueError("requested case is not one of the 336 representatives")
    support = f9_pipeline.parse_X(SUPPORT_TEXT)

    lines = [
        "import KrennGaugeNormalization",
        "",
        "/-! Generated integral gauge-normalization data for audited X5 cases. -/",
        "",
        "namespace Krenn.X5GaugeNormalizationData",
        "",
        "open MonochromaticQuantumGraph",
        "open Krenn.GaugeNormalization",
        "open scoped Matrix",
        "",
        "/- The generated registries contain 336 entries.  This raises only",
        "elaboration recursion depth; every arithmetic proof remains `by decide`. -/",
        "set_option maxRecDepth 100000",
        "",
    ]
    receipt_rows: list[dict[str, Any]] = []
    for case in requested:
        choice, orbit_size = by_case[case]
        entries = [(support[offset], int(i), int(j))
                   for offset, (i, j) in enumerate(choice)]
        rows = []
        for edge, i, j in entries:
            left = coordinate(edge[0], i)
            right = coordinate(edge[1], j)
            rows.append([a + b for a, b in zip(left, right, strict=True)])
        columns, inverse = right_inverse(rows)
        selected = lean_vector(entries, lambda entry:
            "MonochromaticQuantumGraph.mkEdge "
            f"{entry[0][0]} {entry[0][1]} {entry[1]} {entry[2]}")
        table_rows = [inverse[3 * vertex:3 * vertex + 3]
                      for vertex in range(5)]
        table = lean_vector(
            table_rows,
            lambda colours: lean_vector(
                colours, lambda row: lean_vector(row, lean_int)
            ),
        )
        lines += [
            f"def selectedCase{case} : Fin 5 → EdgeN 6 3 := {selected}",
            "",
            f"def rightInverseTableCase{case} : Fin 5 → Fin 3 → Fin 5 → ℤ :=",
            f"  {table}",
            "",
            f"def rightInverseCase{case} : GaugeParameter → Fin 5 → ℤ :=",
            f"  fun parameter => rightInverseTableCase{case} parameter.1 parameter.2",
            "",
            f"theorem rightInverseCase{case}_ok : ∀ k l,",
            f"    ∑ parameter, channelExponent (selectedCase{case} k) parameter *",
            f"      rightInverseCase{case} parameter l = if k = l then 1 else 0 := by",
            "  decide",
            "",
            f"def datumCase{case} : NormalizationDatum :=",
            f"  ⟨{case}, selectedCase{case}, rightInverseCase{case},",
            f"    rightInverseCase{case}_ok⟩",
            "",
        ]
        receipt_rows.append({
            "case_index": case,
            "orbit_size": orbit_size,
            "selected_entries": [
                [list(edge), i, j] for edge, i, j in entries
            ],
            "unimodular_columns_0based": columns,
            "right_inverse": inverse,
            "right_inverse_min": min(min(row) for row in inverse),
            "right_inverse_max": max(max(row) for row in inverse),
        })
    representative_vector = lean_vector(requested, str)
    orbit_size_vector = lean_vector(
        [by_case[case][1] for case in requested], str)
    datum_vector = lean_vector(
        requested, lambda case: f"datumCase{case}")
    orbit_size_total = sum(by_case[case][1] for case in requested)
    lines += [
        f"def representativeCase : Fin {len(requested)} → Fin 1296 :=",
        f"  {representative_vector}",
        "",
        f"def orbitSize : Fin {len(requested)} → Nat :=",
        f"  {orbit_size_vector}",
        "",
        f"def datum : Fin {len(requested)} → NormalizationDatum :=",
        f"  {datum_vector}",
        "",
        "theorem datum_caseIndex : ∀ i,",
        "    (datum i).caseIndex = representativeCase i := by",
        "  decide",
        "",
        f"theorem orbitSize_total : ∑ i, orbitSize i = {orbit_size_total} := by",
        "  decide",
        "",
        "#print axioms Krenn.X5GaugeNormalizationData." +
        f"rightInverseCase{requested[0]}_ok",
        "#print axioms Krenn.X5GaugeNormalizationData.datum_caseIndex",
        "#print axioms Krenn.X5GaugeNormalizationData.orbitSize_total",
        "",
        "end Krenn.X5GaugeNormalizationData",
        "",
    ]
    args.output.write_text("\n".join(lines), encoding="utf-8")
    payload = {
        "format": "krenn-x5-gauge-normalization-lean-v2",
        "support": SUPPORT_TEXT,
        "audited_representative_count": cover["symmetry_representative_count"],
        "audited_labelled_case_count": cover["labelled_case_count"],
        "exported_count": len(receipt_rows),
        "orbit_size_total": orbit_size_total,
        "cases": receipt_rows,
        "output_sha256": digest(args.output),
        "exporter_sha256": digest(Path(__file__)),
    }
    if args.receipt is not None:
        args.receipt.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "exported": len(receipt_rows),
        "output_sha256": payload["output_sha256"],
        "coefficient_min": min(row["right_inverse_min"] for row in receipt_rows),
        "coefficient_max": max(row["right_inverse_max"] for row in receipt_rows),
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
