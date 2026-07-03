#!/usr/bin/env python3
"""Compute the bi-invariant trace-metric curvature on closed su(N) models.

This lab computes the Ricci/Bochner lower eigenvalue for the full finite
su(N) trace/Killing sanity model:

    L = sum_i D_{E_i}^2

where {E_i} is an orthonormal anti-Hermitian basis for su(N) under
<-Tr(AB)>.  This metric is Ad-invariant, so the structure constants are
totally antisymmetric and the computation gives the bi-invariant Einstein
curvature Ric = (N/2) I.  This is a useful finite Lie-algebra arithmetic sanity
check, but it is not the Navier-Stokes-relevant right-invariant Arnold
curvature.

The script also evaluates the literal sine-bracket convention written in the
goal,

    [T_m,T_n] = (N/pi) sin((2*pi/N) (m x n)) T_{m+n},

on nonzero Z_N^2 modes with the Euclidean delta metric.  That convention is
Jacobi-closed, but it degenerates for even N.

Honest scope: this lab does not realize Ben's NS curvature intuition and does
not supply a curvature-dimension input for the SG/Navier-Stokes generator.  The
genuine computation must use the right-invariant Sobolev-weighted H^m metric,
where the structure constants are not totally antisymmetric and Arnold-style
curvature is mixed-sign.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path

import numpy as np


@dataclass
class CurvatureRow:
    model: str
    N: int
    dimension: int
    gram_max_error: float
    bracket_antisymmetry_error: float
    full_antisymmetry_error: float
    jacobi_max_error: float
    unimodularity_trace_max: float
    ricci_min_eigenvalue: float
    ricci_max_eigenvalue: float
    ricci_condition_spread: float
    cd_minus_K_constant: float
    expected_rho: float | None
    max_abs_error_vs_expected: float | None
    status: str


def inner_antihermitian(A: np.ndarray, B: np.ndarray) -> float:
    return float(np.real(-np.trace(A @ B)))


def suN_antihermitian_basis(N: int) -> list[np.ndarray]:
    """Orthonormal anti-Hermitian generalized Gell-Mann basis for su(N)."""
    basis: list[np.ndarray] = []
    root2 = math.sqrt(2.0)

    for a in range(N):
        for b in range(a + 1, N):
            H = np.zeros((N, N), dtype=complex)
            H[a, b] = 1.0 / root2
            H[b, a] = 1.0 / root2
            basis.append(1j * H)

            H = np.zeros((N, N), dtype=complex)
            H[a, b] = -1j / root2
            H[b, a] = 1j / root2
            basis.append(1j * H)

    for k in range(1, N):
        H = np.zeros((N, N), dtype=complex)
        coeff = 1.0 / math.sqrt(k * (k + 1))
        for a in range(k):
            H[a, a] = coeff
        H[k, k] = -k * coeff
        basis.append(1j * H)

    return basis


def structure_constants_from_matrices(basis: list[np.ndarray]) -> tuple[np.ndarray, float]:
    d = len(basis)
    gram = np.array(
        [[inner_antihermitian(A, B) for B in basis] for A in basis], dtype=float
    )
    gram_max_error = float(np.max(np.abs(gram - np.eye(d))))
    constants = np.zeros((d, d, d), dtype=float)
    for i, A in enumerate(basis):
        for j, B in enumerate(basis):
            commutator = A @ B - B @ A
            for k, C in enumerate(basis):
                value = inner_antihermitian(commutator, C)
                if abs(value) > 1e-13:
                    constants[i, j, k] = value
    return constants, gram_max_error


def zn2_modes(N: int) -> list[tuple[int, int]]:
    return [(a, b) for a in range(N) for b in range(N) if not (a == 0 and b == 0)]


def cross(m: tuple[int, int], n: tuple[int, int]) -> int:
    return m[0] * n[1] - m[1] * n[0]


def literal_sine_structure_constants(N: int) -> np.ndarray:
    modes = zn2_modes(N)
    index = {m: i for i, m in enumerate(modes)}
    d = len(modes)
    constants = np.zeros((d, d, d), dtype=float)
    for i, m in enumerate(modes):
        for j, n in enumerate(modes):
            target = ((m[0] + n[0]) % N, (m[1] + n[1]) % N)
            coeff = (N / math.pi) * math.sin((2.0 * math.pi / N) * cross(m, n))
            if target != (0, 0) and abs(coeff) > 1e-13:
                constants[i, j, index[target]] = coeff
    return constants


def jacobi_errors(constants: np.ndarray) -> tuple[float, float]:
    d = constants.shape[0]
    max_error = 0.0
    trace_max = 0.0
    for i in range(d):
        trace_max = max(trace_max, abs(float(np.trace(constants[i]))))
        for j in range(d):
            for k in range(d):
                defect = (
                    constants[j, k] @ constants[i]
                    + constants[k, i] @ constants[j]
                    + constants[i, j] @ constants[k]
                )
                max_error = max(max_error, float(np.linalg.norm(defect)))
    return max_error, trace_max


def ricci_from_structure_constants(constants: np.ndarray) -> np.ndarray:
    """Ricci matrix for the left-invariant metric with this orthonormal frame."""
    connection = 0.5 * (
        constants
        - np.transpose(constants, (1, 2, 0))
        + np.transpose(constants, (2, 0, 1))
    )
    d = constants.shape[0]
    curvature = np.zeros((d, d, d, d), dtype=float)
    for i in range(d):
        for j in range(d):
            for k in range(d):
                curvature[i, j, k, :] = (
                    connection[j, k] @ connection[i]
                    - connection[i, k] @ connection[j]
                    - constants[i, j] @ connection[:, k, :]
                )
    ricci = np.einsum("ijki->jk", curvature)
    return 0.5 * (ricci + ricci.T)


def row_from_constants(
    model: str, N: int, constants: np.ndarray, gram_error: float, expected: float | None
) -> CurvatureRow:
    anti_error = float(np.max(np.abs(constants + np.swapaxes(constants, 0, 1))))
    full_anti_error = float(
        max(
            np.max(np.abs(constants + np.transpose(constants, (0, 2, 1)))),
            np.max(np.abs(constants + np.transpose(constants, (2, 1, 0)))),
        )
    )
    jacobi_error, trace_max = jacobi_errors(constants)
    ricci = ricci_from_structure_constants(constants)
    eigvals = np.linalg.eigvalsh(ricci)
    rho_min = float(eigvals[0])
    rho_max = float(eigvals[-1])
    spread = float(rho_max - rho_min)
    expected_error = None if expected is None else max(abs(rho_min - expected), abs(rho_max - expected))
    status = "closed_positive_curvature"
    if jacobi_error > 1e-8:
        status = "not_closed_jacobi_failure"
    elif rho_min < -1e-8:
        status = "closed_negative_curvature"
    elif rho_min <= 1e-8:
        status = "closed_degenerate_nonnegative_curvature"
    return CurvatureRow(
        model=model,
        N=N,
        dimension=constants.shape[0],
        gram_max_error=gram_error,
        bracket_antisymmetry_error=anti_error,
        full_antisymmetry_error=full_anti_error,
        jacobi_max_error=jacobi_error,
        unimodularity_trace_max=trace_max,
        ricci_min_eigenvalue=rho_min,
        ricci_max_eigenvalue=rho_max,
        ricci_condition_spread=spread,
        cd_minus_K_constant=max(0.0, -rho_min),
        expected_rho=expected,
        max_abs_error_vs_expected=expected_error,
        status=status,
    )


def compute_rows(N_values: list[int]) -> list[CurvatureRow]:
    rows: list[CurvatureRow] = []
    for N in N_values:
        constants, gram_error = structure_constants_from_matrices(suN_antihermitian_basis(N))
        rows.append(row_from_constants("suN_matrix_orthonormal", N, constants, gram_error, N / 2.0))

        literal = literal_sine_structure_constants(N)
        rows.append(row_from_constants("literal_goal_sine_2pi_delta_metric", N, literal, 0.0, None))
    return rows


def markdown_table(rows: list[CurvatureRow], model: str) -> str:
    selected = [row for row in rows if row.model == model]
    lines = [
        "| N | dim | rho_min | rho_max | CD(-K) K | Jacobi max | status |",
        "|---:|---:|---:|---:|---:|---:|---|",
    ]
    for row in selected:
        lines.append(
            f"| {row.N} | {row.dimension} | {row.ricci_min_eigenvalue:.12g} | "
            f"{row.ricci_max_eigenvalue:.12g} | {row.cd_minus_K_constant:.12g} | "
            f"{row.jacobi_max_error:.3g} | {row.status} |"
        )
    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--min-N", type=int, default=2)
    parser.add_argument("--max-N", type=int, default=6)
    parser.add_argument("--json-out", type=Path)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    rows = compute_rows(list(range(args.min_N, args.max_N + 1)))
    payload = {
        "lab": "ns_sun_sine_bracket_curvature_lab",
        "interpretation": {
            "scope": "bi-invariant su(N) trace/Killing curvature sanity check only; not NS-relevant",
            "rho_min": "lowest eigenvalue of the bi-invariant Ricci/Bochner curvature term relative to Gamma",
            "cd_minus_K_constant": "max(0,-rho_min), the K needed for CD(-K,infinity)",
            "retracted_interpretation": "does not realize Ben's NS curvature intuition and does not close the SG/NS CD input",
            "open_input": "compute the right-invariant Sobolev-weighted H^m/Arnold curvature with non-totally-antisymmetric structure constants and connect it to Ben's local H1/H2 generator",
            "verdict_basis": "suN_matrix_orthonormal is the Ad-invariant trace/Killing sanity model; literal sine 2pi row records the convention written in the spec",
        },
        "rows": [asdict(row) for row in rows],
    }
    print("su(N) matrix orthonormal trace/Killing model")
    print(markdown_table(rows, "suN_matrix_orthonormal"))
    print()
    print("literal goal sine 2pi convention with delta metric")
    print(markdown_table(rows, "literal_goal_sine_2pi_delta_metric"))
    print()
    print(
        "scope: bi-invariant sanity check only; not the right-invariant "
        "Sobolev/Arnold NS curvature"
    )
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
