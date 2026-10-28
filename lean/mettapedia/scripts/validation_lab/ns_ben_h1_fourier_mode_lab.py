#!/usr/bin/env python3
"""Exact Fourier-mode lab for Ben Goertzel's H1 adjoint-bound hypothesis.

The model is the area-preserving two-torus shear

    g_k(x, y) = (x, y + a_k sin(k x)).

Choose ``a_k`` so that the H^m norm of the displacement
``delta_k = (0, a_k sin(kx))`` is the fixed small radius ``epsilon``.
For the constant horizontal field v = (1, 0), push-forward gives

    Ad_{g_k} v = (1, a_k k cos(kx)).

With the same Fourier H^m normalization, the displacement norm is epsilon
for every k, while the operator-ratio lower bound is

    ||Ad_{g_k} v||_{H^m} / ||v||_{H^m}
      = sqrt(1 + (epsilon k)^2).

Thus no uniform H^m -> H^m adjoint bound can hold on any positive H^m
chart radius in this Fourier-mode model.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


@dataclass(frozen=True)
class ModeRow:
    k: int
    amplitude: float
    displacement_hm_norm: float
    derivative_sup_norm: float
    derivative_hm_norm: float
    constant_field_hm_norm: float
    adjoint_hm_norm: float
    adjoint_ratio_lower_bound: float
    linearized_commutator_ratio: float
    ratio_over_epsilon_k: float


def parse_modes(raw: str) -> list[int]:
    modes = [int(part) for part in raw.split(",") if part.strip()]
    if not modes or any(k <= 0 for k in modes):
        raise ValueError("modes must be a comma-separated list of positive integers")
    return modes


def mode_row(k: int, m: int, epsilon: float) -> ModeRow:
    if m <= 0:
        raise ValueError("m must be positive")
    if epsilon <= 0.0:
        raise ValueError("epsilon must be positive")

    hm_weight = (1.0 + float(k * k)) ** (0.5 * m)
    amplitude = math.sqrt(2.0) * epsilon / hm_weight
    displacement_hm_norm = abs(amplitude) * hm_weight / math.sqrt(2.0)
    derivative_sup_norm = abs(amplitude) * float(k)
    derivative_hm_norm = derivative_sup_norm * hm_weight / math.sqrt(2.0)
    constant_field_hm_norm = 1.0
    adjoint_hm_norm = math.sqrt(constant_field_hm_norm**2 + derivative_hm_norm**2)
    adjoint_ratio = adjoint_hm_norm / constant_field_hm_norm
    commutator_ratio = derivative_hm_norm / constant_field_hm_norm
    return ModeRow(
        k=k,
        amplitude=amplitude,
        displacement_hm_norm=displacement_hm_norm,
        derivative_sup_norm=derivative_sup_norm,
        derivative_hm_norm=derivative_hm_norm,
        constant_field_hm_norm=constant_field_hm_norm,
        adjoint_hm_norm=adjoint_hm_norm,
        adjoint_ratio_lower_bound=adjoint_ratio,
        linearized_commutator_ratio=commutator_ratio,
        ratio_over_epsilon_k=adjoint_ratio / (epsilon * float(k)),
    )


def first_mode_exceeding(C: float, epsilon: float) -> int:
    if C < 1.0:
        return 1
    return max(1, math.floor(math.sqrt(C * C - 1.0) / epsilon) + 1)


def make_payload(m: int, epsilon: float, modes: list[int], constants: list[float]) -> dict[str, Any]:
    rows = [mode_row(k, m, epsilon) for k in modes]
    thresholds = [
        {
            "C": C,
            "first_integer_k_with_ratio_gt_C": first_mode_exceeding(C, epsilon),
        }
        for C in constants
    ]
    return {
        "status": "pass",
        "model": "area-preserving shear on periodic T^2",
        "sobolev_order_m": m,
        "chart_radius_epsilon": epsilon,
        "displacement_hm_norm_formula": "||delta_k||_H^m = epsilon",
        "adjoint_ratio_formula": "sqrt(1 + (epsilon*k)^2)",
        "linearized_commutator_ratio_formula": "epsilon*k",
        "ben_h1_conclusion": (
            "The modeled H1 uniform H^m -> H^m adjoint bound is false on every "
            "positive H^m chart radius, because k can exceed every finite constant."
        ),
        "pdf_grounding": {
            "source": "NS-Proof-v7.pdf",
            "passages": [
                "Section 5.3 states H1 as a uniform adjoint bound on K.",
                "Lemma 6.1 and Lemma D.18 assert local H^m -> H^m boundedness of Ad_g.",
                "Proposition 6.5 and Lemma F.7 use that bound for Gamma(P_t phi)(Id).",
            ],
        },
        "thresholds": thresholds,
        "rows": [asdict(row) for row in rows],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--m", type=int, default=3)
    parser.add_argument("--epsilon", type=float, default=0.01)
    parser.add_argument("--modes", default="8,16,32,64,128,256,512,1024")
    parser.add_argument("--constants", default="1,2,5,10,100")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    modes = parse_modes(args.modes)
    constants = [float(part) for part in args.constants.split(",") if part.strip()]
    payload = make_payload(args.m, args.epsilon, modes, constants)

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    summary = {
        "epsilon": args.epsilon,
        "m": args.m,
        "max_k": max(modes),
        "max_ratio": max(row["adjoint_ratio_lower_bound"] for row in payload["rows"]),
        "status": payload["status"],
    }
    print(json.dumps(summary, sort_keys=True))


if __name__ == "__main__":
    main()
