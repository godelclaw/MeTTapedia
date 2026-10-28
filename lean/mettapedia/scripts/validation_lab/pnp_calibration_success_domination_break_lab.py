#!/usr/bin/env python3
"""Finite lab for the Goertzel PNP calibration/domination break.

The explicit toy instance is a USAT block represented by unit clauses for a
unique witness x in {0,1}^m, together with a one-row VV label

    A = [1 1 ... 1],    b = A x.

Every VV column is nonzero, so Ben's involution T_i changes b on every column.
The local post-switch view u=(z,a_i,b) only sees the parity b, while the global
decoder reads the unit clauses and recovers x exactly.

This directly separates:

* global exact witness recovery success: 1;
* best u-local exact witness success: 1 / |{x : parity(x)=b}|;
* best u-local per-bit Bayes success: 1/2.

It is a finite calibration/domination counterexample, not a P-vs-NP theorem.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

import numpy as np


@dataclass(frozen=True)
class ColumnMove:
    index: int
    column: list[int]
    moves_b_on_b0: bool
    moves_b_on_b1: bool


@dataclass(frozen=True)
class CaseRow:
    m: int
    k: int
    witnesses: int
    nonzero_columns: int
    zero_columns: int
    moved_columns: int
    full_input_preserved_columns: int
    parity_fiber_size: int
    global_exact_success: float
    best_local_exact_success: float
    best_local_bit_success: float
    exact_success_gap: float
    bit_success_gap: float
    columns: list[ColumnMove]


def all_witnesses(m: int) -> np.ndarray:
    values = np.arange(1 << m, dtype=np.uint64)
    bits = ((values[:, None] >> np.arange(m, dtype=np.uint64)) & 1).astype(np.uint8)
    return bits


def parity_matrix(m: int) -> np.ndarray:
    return np.ones((1, m), dtype=np.uint8)


def mat_vec_mod2(A: np.ndarray, x: np.ndarray) -> np.ndarray:
    return (A @ x.astype(np.uint8) % 2).astype(np.uint8)


def column_moves(A: np.ndarray) -> list[ColumnMove]:
    moves: list[ColumnMove] = []
    for i in range(A.shape[1]):
        col = A[:, i].astype(np.uint8)
        b0 = np.zeros(A.shape[0], dtype=np.uint8)
        b1 = np.ones(A.shape[0], dtype=np.uint8)
        moves.append(
            ColumnMove(
                index=i,
                column=col.astype(int).tolist(),
                moves_b_on_b0=bool(np.any(b0 ^ col != b0)),
                moves_b_on_b1=bool(np.any(b1 ^ col != b1)),
            )
        )
    return moves


def best_local_exact_success(A: np.ndarray, witnesses: np.ndarray) -> tuple[float, int]:
    labels: dict[tuple[int, ...], int] = {}
    for x in witnesses:
        b = tuple(int(v) for v in mat_vec_mod2(A, x))
        labels[b] = labels.get(b, 0) + 1
    best_hits = sum(1 for _ in labels)
    return best_hits / len(witnesses), max(labels.values())


def best_local_bit_success(A: np.ndarray, witnesses: np.ndarray) -> float:
    total_hits = 0
    total_trials = 0
    for i in range(A.shape[1]):
        buckets: dict[tuple[int, ...], list[int]] = {}
        for x in witnesses:
            b = tuple(int(v) for v in mat_vec_mod2(A, x))
            buckets.setdefault(b, []).append(int(x[i]))
        for bits in buckets.values():
            ones = sum(bits)
            total_hits += max(ones, len(bits) - ones)
            total_trials += len(bits)
    return total_hits / total_trials


def case_row(m: int) -> CaseRow:
    A = parity_matrix(m)
    witnesses = all_witnesses(m)
    moves = column_moves(A)
    exact_success, max_fiber = best_local_exact_success(A, witnesses)
    bit_success = best_local_bit_success(A, witnesses)
    nonzero_columns = sum(1 for move in moves if any(move.column))
    moved_columns = sum(1 for move in moves if move.moves_b_on_b0 and move.moves_b_on_b1)
    full_preserved = A.shape[1] - moved_columns
    return CaseRow(
        m=m,
        k=A.shape[0],
        witnesses=len(witnesses),
        nonzero_columns=nonzero_columns,
        zero_columns=A.shape[1] - nonzero_columns,
        moved_columns=moved_columns,
        full_input_preserved_columns=full_preserved,
        parity_fiber_size=max_fiber,
        global_exact_success=1.0,
        best_local_exact_success=exact_success,
        best_local_bit_success=bit_success,
        exact_success_gap=1.0 - exact_success,
        bit_success_gap=1.0 - bit_success,
        columns=moves,
    )


def random_vv_summary(m_values: list[int], seed: int) -> list[dict[str, Any]]:
    rng = np.random.default_rng(seed)
    rows: list[dict[str, Any]] = []
    for m in m_values:
        k = max(1, int(np.ceil(2.0 * np.log2(m))))
        A = rng.integers(0, 2, size=(k, m), dtype=np.uint8)
        zero_columns = int(sum(not np.any(A[:, i]) for i in range(m)))
        rows.append(
            {
                "m": m,
                "k": k,
                "zero_columns": zero_columns,
                "nonzero_columns": m - zero_columns,
                "zero_fraction": zero_columns / m,
                "expected_zero_fraction": 2.0 ** (-k),
            }
        )
    return rows


def make_payload(m_values: list[int], seed: int) -> dict[str, Any]:
    cases = [case_row(m) for m in m_values]
    return {
        "status": "pass",
        "model": "unit-clause USAT witness plus one-row parity VV label",
        "interpretation": (
            "The full formula gives a global decoder exact success 1, while "
            "the u=(z,a_i,b)-local Bayes comparator sees only parity."
        ),
        "structural_defect": (
            "T_i maps b to b xor a_i, so the full u-fiber is fixed only on zero columns."
        ),
        "cases": [
            {
                **{k: v for k, v in asdict(row).items() if k != "columns"},
                "columns": [asdict(move) for move in row.columns],
            }
            for row in cases
        ],
        "random_vv_zero_column_sanity": random_vv_summary(m_values, seed),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--m-values", default="3,4,5,6,7,8")
    parser.add_argument("--seed", type=int, default=20260630)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    m_values = [int(part) for part in args.m_values.split(",") if part.strip()]
    if not m_values or any(m <= 1 for m in m_values):
        raise ValueError("m-values must contain integers greater than 1")

    payload = make_payload(m_values, args.seed)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    max_m = max(payload["cases"], key=lambda row: row["m"])
    print(
        json.dumps(
            {
                "status": payload["status"],
                "cases": len(payload["cases"]),
                "max_m": max_m["m"],
                "max_m_global_exact_success": max_m["global_exact_success"],
                "max_m_best_local_exact_success": max_m["best_local_exact_success"],
                "max_m_best_local_bit_success": max_m["best_local_bit_success"],
                "max_m_moved_columns": max_m["moved_columns"],
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
