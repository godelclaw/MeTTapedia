#!/usr/bin/env python3
"""Numerical affine BKM Biot-Savart/log-Sobolev constant probe.

For periodic solenoidal test fields, measure the conventional affine shape

    ||grad u||_inf <= C0 + C1 * ||omega||_inf * log(e + H_m(u)).

The samples are Taylor-Green and random solenoidal Fourier fields.  This is
supporting evidence only; it is not a proof of the Biot-Savart/Riesz
log-Sobolev estimate used by the Lean BKM route.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np


@dataclass(frozen=True)
class Grid:
    n: int

    @property
    def spacing(self) -> float:
        return 2.0 * np.pi / self.n

    @property
    def shape(self) -> tuple[int, int, int]:
        return (self.n, self.n, self.n)

    def mesh(self) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
        axis = np.arange(self.n) * self.spacing
        return np.meshgrid(axis, axis, axis, indexing="ij")


def fftfreq_int(n: int) -> np.ndarray:
    return np.fft.fftfreq(n, d=1.0 / n)


def spectral_derivative(f: np.ndarray, axis: int) -> np.ndarray:
    n = f.shape[axis]
    k = fftfreq_int(n)
    shape = [1, 1, 1]
    shape[axis] = n
    multiplier = 1j * k.reshape(shape)
    return np.fft.ifftn(multiplier * np.fft.fftn(f)).real


def gradient(u: np.ndarray) -> np.ndarray:
    return np.stack([[spectral_derivative(u[i], j) for j in range(3)] for i in range(3)])


def curl(u: np.ndarray) -> np.ndarray:
    return np.stack(
        [
            spectral_derivative(u[2], 1) - spectral_derivative(u[1], 2),
            spectral_derivative(u[0], 2) - spectral_derivative(u[2], 0),
            spectral_derivative(u[1], 0) - spectral_derivative(u[0], 1),
        ]
    )


def max_vector_norm(v: np.ndarray) -> float:
    return float(np.max(np.sqrt(np.sum(v * v, axis=0))))


def max_matrix_op_norm(g: np.ndarray) -> float:
    matrices = np.moveaxis(g, (0, 1), (-2, -1)).reshape((-1, 3, 3))
    return float(np.max(np.linalg.svd(matrices, compute_uv=False)[:, 0]))


def sobolev_proxy(u: np.ndarray, order: int) -> float:
    n = u.shape[1]
    kx, ky, kz = np.meshgrid(fftfreq_int(n), fftfreq_int(n), fftfreq_int(n), indexing="ij")
    weight = (1.0 + kx * kx + ky * ky + kz * kz) ** order
    total = 0.0
    for comp in range(3):
        coeff = np.fft.fftn(u[comp]) / (n**3)
        total += float(np.sum(weight * np.abs(coeff) ** 2))
    return float(np.sqrt(total))


def taylor_green(grid: Grid, nu: float, t: float) -> np.ndarray:
    x, y, z = grid.mesh()
    amp = np.exp(-2.0 * nu * t)
    return np.stack(
        [
            amp * np.sin(x) * np.cos(y),
            -amp * np.cos(x) * np.sin(y),
            np.zeros(grid.shape),
        ]
    )


def random_solenoidal(grid: Grid, seed: int, modes: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    x, y, z = grid.mesh()
    coords = (x, y, z)
    field = np.zeros((3,) + grid.shape)
    for _ in range(modes):
        k = rng.integers(-4, 5, size=3)
        if not np.any(k):
            k[0] = 1
        k_float = k.astype(float)
        raw = rng.normal(size=3)
        coeff = raw - np.dot(raw, k_float) / np.dot(k_float, k_float) * k_float
        phase = rng.uniform(0.0, 2.0 * np.pi)
        arg = k[0] * coords[0] + k[1] * coords[1] + k[2] * coords[2] + phase
        field += coeff[:, None, None, None] * np.sin(arg)
    return field / max(max_vector_norm(field), 1.0)


def required_c1(grad_inf: float, log_factor: float, c0: float) -> float:
    if log_factor <= 0.0:
        return 0.0 if grad_inf <= c0 else float("inf")
    return max(0.0, (grad_inf - c0) / log_factor)


def case_metrics(name: str, u: np.ndarray, order: int) -> dict[str, Any]:
    omega_inf = max_vector_norm(curl(u))
    grad_inf = max_matrix_op_norm(gradient(u))
    high = sobolev_proxy(u, order)
    log_factor = omega_inf * np.log(np.e + high)
    one_constant_denominator = 1.0 + log_factor
    return {
        "name": name,
        "gradient_operator_inf": grad_inf,
        "vorticity_inf": omega_inf,
        "sobolev_proxy_order": order,
        "sobolev_proxy": high,
        "affine_log_factor": log_factor,
        "required_C1_if_C0_zero": required_c1(grad_inf, log_factor, 0.0),
        "required_C1_if_C0_one": required_c1(grad_inf, log_factor, 1.0),
        "required_common_C_if_C0_eq_C1": grad_inf / one_constant_denominator,
        "passed": bool(np.isfinite(log_factor) and log_factor >= 0.0),
    }


def check_affine_case(case: dict[str, Any], c0: float, c1: float) -> bool:
    rhs = c0 + c1 * case["affine_log_factor"]
    tol = 1.0e-8 * max(1.0, abs(case["gradient_operator_inf"]), abs(rhs))
    return bool(case["gradient_operator_inf"] <= rhs + tol)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=48)
    parser.add_argument("--nu", type=float, default=0.25)
    parser.add_argument("--order", type=int, default=4)
    parser.add_argument("--random-cases", type=int, default=44)
    parser.add_argument("--random-modes", type=int, default=10)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    grid = Grid(args.n)
    cases = [
        case_metrics("taylor-green", taylor_green(grid, args.nu, 0.4), args.order)
    ]
    cases.extend(
        case_metrics(
            f"random-solenoidal-{20260629 + i}",
            random_solenoidal(grid, 20260629 + i, args.random_modes),
            args.order,
        )
        for i in range(args.random_cases)
    )

    c1_c0_zero = max(case["required_C1_if_C0_zero"] for case in cases)
    c1_c0_one = max(case["required_C1_if_C0_one"] for case in cases)
    c_common = max(case["required_common_C_if_C0_eq_C1"] for case in cases)
    candidate_constants = [
        {
            "name": "C0=0",
            "C0": 0.0,
            "C1": c1_c0_zero,
            "all_cases_pass": all(check_affine_case(case, 0.0, c1_c0_zero) for case in cases),
        },
        {
            "name": "C0=1",
            "C0": 1.0,
            "C1": c1_c0_one,
            "all_cases_pass": all(check_affine_case(case, 1.0, c1_c0_one) for case in cases),
        },
        {
            "name": "C0=C1",
            "C0": c_common,
            "C1": c_common,
            "all_cases_pass": all(check_affine_case(case, c_common, c_common) for case in cases),
        },
    ]

    payload: dict[str, Any] = {
        "status": (
            "pass"
            if all(case["passed"] for case in cases)
            and all(candidate["all_cases_pass"] for candidate in candidate_constants)
            else "fail"
        ),
        "numpy_version": np.__version__,
        "grid": {"N": grid.n, "domain": "periodic [0, 2*pi)^3"},
        "checked_quantity": "||grad u||_inf <= C0 + C1 * ||omega||_inf * log(e + H_m(u))",
        "interpretation": "numerical evidence only; not a Biot-Savart/Riesz proof",
        "candidate_constants": candidate_constants,
        "cases": cases,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                "cases": len(cases),
                "C0_zero_C1": c1_c0_zero,
                "C0_one_C1": c1_c0_one,
                "C_common": c_common,
                "status": payload["status"],
            },
            sort_keys=True,
        )
    )
    if payload["status"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
