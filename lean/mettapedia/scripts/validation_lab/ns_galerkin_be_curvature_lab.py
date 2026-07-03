#!/usr/bin/env python3
"""Galerkin Bakry-Emery curvature diagnostic for divergence-free Fourier modes.

The lab builds a real sine/cosine divergence-free Fourier frame on T^d,
projects Lie brackets back to the finite cutoff, and computes the
left-invariant Bochner/Ricci curvature proxy from the projected structure
constants.

Important honesty note: a Fourier cutoff is not automatically a finite Lie
algebra.  Nonzero bracket residuals or Jacobi defects mean the projected Ricci
matrix is diagnostic evidence, not a formal CD certificate for the SG
generator.  The Lean certificate added next to this lab requires exact closure,
Jacobi, Bochner-realization, and Ricci lower-bound fields.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from itertools import product
from pathlib import Path
from typing import Iterable

import numpy as np


@dataclass(frozen=True)
class ModeLabel:
    wave: tuple[int, ...]
    polarization: int
    trig: str


@dataclass
class CurvatureRow:
    dimension: int
    radius: int
    mode_count: int
    grid_per_axis: int
    sample_points: int
    gram_max_error: float
    antisymmetry_max_error: float
    unimodularity_trace_max: float
    bracket_residual_max: float
    bracket_residual_rms: float
    jacobi_defect_max: float
    jacobi_defect_mean: float
    rho_min_projected_ricci: float
    rho_mean_projected_ricci: float
    K_for_CD_minus_K: float
    certificate_status: str


def canonical_waves(dim: int, radius: int) -> list[tuple[int, ...]]:
    waves: list[tuple[int, ...]] = []
    for k in product(range(-radius, radius + 1), repeat=dim):
        if all(a == 0 for a in k):
            continue
        first_nonzero = next(a for a in k if a != 0)
        if first_nonzero > 0:
            waves.append(tuple(k))
    waves.sort(key=lambda k: (sum(a * a for a in k), k))
    return waves


def perpendicular_polarizations(k: tuple[int, ...]) -> list[np.ndarray]:
    kv = np.array(k, dtype=float)
    kn = float(np.linalg.norm(kv))
    if len(k) == 2:
        return [np.array([-kv[1], kv[0]], dtype=float) / kn]

    if len(k) != 3:
        raise ValueError("only dimensions 2 and 3 are supported")

    unit = kv / kn
    axis = min(np.eye(3), key=lambda e: abs(float(np.dot(e, unit))))
    v1 = axis - float(np.dot(axis, unit)) * unit
    v1 = v1 / float(np.linalg.norm(v1))
    v2 = np.cross(unit, v1)
    v2 = v2 / float(np.linalg.norm(v2))
    return [v1, v2]


def mode_labels(dim: int, radius: int) -> list[ModeLabel]:
    labels: list[ModeLabel] = []
    for wave in canonical_waves(dim, radius):
        for pol_index, _pol in enumerate(perpendicular_polarizations(wave)):
            labels.append(ModeLabel(wave, pol_index, "sin"))
            labels.append(ModeLabel(wave, pol_index, "cos"))
    return labels


def sample_points(dim: int, grid_per_axis: int) -> np.ndarray:
    xs = np.linspace(0.0, 2.0 * math.pi, grid_per_axis, endpoint=False)
    meshes = np.meshgrid(*([xs] * dim), indexing="ij")
    return np.stack([m.ravel() for m in meshes], axis=1)


def frame_arrays(
    dim: int, labels: list[ModeLabel], grid_per_axis: int
) -> tuple[np.ndarray, np.ndarray]:
    pts = sample_points(dim, grid_per_axis)
    point_count = pts.shape[0]
    fields = np.empty((len(labels), point_count, dim), dtype=float)
    gradients = np.empty((len(labels), point_count, dim, dim), dtype=float)
    root_two = math.sqrt(2.0)

    pol_cache: dict[tuple[int, ...], list[np.ndarray]] = {}
    for index, label in enumerate(labels):
        wave = label.wave
        pol_cache.setdefault(wave, perpendicular_polarizations(wave))
        wave_vec = np.array(wave, dtype=float)
        amp = root_two * pol_cache[wave][label.polarization]
        phase = pts @ wave_vec

        if label.trig == "sin":
            value = np.sin(phase)
            deriv_scalar = np.cos(phase)
        elif label.trig == "cos":
            value = np.cos(phase)
            deriv_scalar = -np.sin(phase)
        else:
            raise ValueError(f"unknown trig label {label.trig!r}")

        fields[index] = value[:, None] * amp[None, :]
        for direction in range(dim):
            gradients[index, :, direction, :] = (
                wave_vec[direction] * deriv_scalar[:, None] * amp[None, :]
            )

    return fields, gradients


def projected_structure_constants(
    fields: np.ndarray, gradients: np.ndarray
) -> tuple[np.ndarray, float, float]:
    mode_count = fields.shape[0]
    point_count = fields.shape[1]
    constants = np.zeros((mode_count, mode_count, mode_count), dtype=float)
    residual_squares: list[float] = []

    for a in range(mode_count):
        field_a = fields[a]
        grad_a = gradients[a]
        for b in range(mode_count):
            bracket = np.einsum("md,mdp->mp", field_a, gradients[b])
            bracket -= np.einsum("md,mdp->mp", fields[b], grad_a)
            coeff = np.einsum("mp,cmp->c", bracket, fields) / point_count
            constants[a, b, :] = coeff
            bracket_norm_sq = float(np.mean(np.sum(bracket * bracket, axis=1)))
            projected_norm_sq = float(np.dot(coeff, coeff))
            residual_squares.append(max(0.0, bracket_norm_sq - projected_norm_sq))

    return (
        constants,
        math.sqrt(max(residual_squares, default=0.0)),
        math.sqrt(sum(residual_squares) / max(1, len(residual_squares))),
    )


def ricci_from_structure_constants(constants: np.ndarray) -> np.ndarray:
    # Levi-Civita connection:
    # 2 <nabla_i e_j, e_k> = c_ij^k - c_jk^i + c_ki^j.
    connection = 0.5 * (
        constants
        - np.transpose(constants, (1, 2, 0))
        + np.transpose(constants, (2, 0, 1))
    )
    n = constants.shape[0]
    curvature = np.zeros((n, n, n, n), dtype=float)
    for i in range(n):
        for j in range(n):
            for k in range(n):
                curvature[i, j, k, :] = (
                    connection[j, k] @ connection[i]
                    - connection[i, k] @ connection[j]
                    - constants[i, j] @ connection[:, k, :]
                )
    ricci = np.einsum("ijki->jk", curvature)
    return 0.5 * (ricci + ricci.T)


def jacobi_defects(constants: np.ndarray) -> tuple[float, float]:
    n = constants.shape[0]
    max_defect = 0.0
    sum_defect = 0.0
    count = 0
    for i in range(n):
        for j in range(n):
            for k in range(n):
                defect = (
                    constants[j, k] @ constants[i]
                    + constants[k, i] @ constants[j]
                    + constants[i, j] @ constants[k]
                )
                norm = float(np.linalg.norm(defect))
                max_defect = max(max_defect, norm)
                sum_defect += norm
                count += 1
    return max_defect, sum_defect / max(1, count)


def recommended_grid(dim: int, radius: int, grid_scale: int) -> int:
    # Inner products of bracket products can carry frequencies up to roughly
    # 3R.  This default oversamples that range while keeping the lab small.
    base = max(16, grid_scale * radius)
    if dim == 2:
        return max(32, base)
    return max(12, base)


def compute_row(
    dim: int, radius: int, grid_per_axis: int, closure_tol: float
) -> CurvatureRow:
    labels = mode_labels(dim, radius)
    fields, gradients = frame_arrays(dim, labels, grid_per_axis)
    point_count = fields.shape[1]
    gram = np.einsum("amp,bmp->ab", fields, fields) / point_count
    gram_max_error = float(np.max(np.abs(gram - np.eye(len(labels)))))

    constants, residual_max, residual_rms = projected_structure_constants(
        fields, gradients
    )
    antisymmetry = float(np.max(np.abs(constants + np.swapaxes(constants, 0, 1))))
    unimodularity = float(np.max(np.abs(np.einsum("ijj->i", constants))))
    jacobi_max, jacobi_mean = jacobi_defects(constants)
    ricci = ricci_from_structure_constants(constants)
    eigvals = np.linalg.eigvalsh(ricci)
    rho_min = float(eigvals[0])
    rho_mean = float(np.mean(eigvals))
    closes = residual_max <= closure_tol and jacobi_max <= closure_tol
    status = (
        "certifiable_projected_lie_model"
        if closes
        else "not_certified_projected_bracket_not_closed"
    )
    return CurvatureRow(
        dimension=dim,
        radius=radius,
        mode_count=len(labels),
        grid_per_axis=grid_per_axis,
        sample_points=point_count,
        gram_max_error=gram_max_error,
        antisymmetry_max_error=antisymmetry,
        unimodularity_trace_max=unimodularity,
        bracket_residual_max=residual_max,
        bracket_residual_rms=residual_rms,
        jacobi_defect_max=jacobi_max,
        jacobi_defect_mean=jacobi_mean,
        rho_min_projected_ricci=rho_min,
        rho_mean_projected_ricci=rho_mean,
        K_for_CD_minus_K=max(0.0, -rho_min),
        certificate_status=status,
    )


def abelian_translation_baseline(dim: int) -> dict[str, object]:
    return {
        "dimension": dim,
        "mode_count": dim,
        "description": "constant divergence-free translation modes",
        "structure_constants": "all zero",
        "rho_min": 0.0,
        "K_for_CD_minus_K": 0.0,
        "certificate_status": "certified_flat_abelian_translation_truncation",
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dim", type=int, choices=[2, 3], default=2)
    parser.add_argument("--max-radius", type=int, default=3)
    parser.add_argument("--grid-scale", type=int, default=16)
    parser.add_argument("--closure-tol", type=float, default=1e-8)
    parser.add_argument("--json-out", type=Path)
    parser.add_argument(
        "--no-translation-baseline", action="store_true", default=False
    )
    return parser.parse_args()


def markdown_table(rows: Iterable[CurvatureRow]) -> str:
    header = (
        "| dim | R | modes | grid | rho_min proxy | K for CD(-K) | "
        "bracket residual max | Jacobi max | status |"
    )
    sep = "|---:|---:|---:|---:|---:|---:|---:|---:|---|"
    lines = [header, sep]
    for row in rows:
        lines.append(
            f"| {row.dimension} | {row.radius} | {row.mode_count} | "
            f"{row.grid_per_axis}^{row.dimension} | "
            f"{row.rho_min_projected_ricci:.9g} | "
            f"{row.K_for_CD_minus_K:.9g} | "
            f"{row.bracket_residual_max:.9g} | "
            f"{row.jacobi_defect_max:.9g} | {row.certificate_status} |"
        )
    return "\n".join(lines)


def main() -> None:
    args = parse_args()
    rows: list[CurvatureRow] = []
    for radius in range(1, args.max_radius + 1):
        grid = recommended_grid(args.dim, radius, args.grid_scale)
        rows.append(compute_row(args.dim, radius, grid, args.closure_tol))

    payload: dict[str, object] = {
        "lab": "ns_galerkin_be_curvature_lab",
        "interpretation": (
            "Projected Ricci eigenvalues are diagnostic unless bracket residual "
            "and Jacobi defect are zero/certified."
        ),
        "translation_baseline": None
        if args.no_translation_baseline
        else abelian_translation_baseline(args.dim),
        "rows": [asdict(row) for row in rows],
    }

    print(markdown_table(rows))
    if payload["translation_baseline"] is not None:
        print()
        print(json.dumps(payload["translation_baseline"], sort_keys=True))

    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
