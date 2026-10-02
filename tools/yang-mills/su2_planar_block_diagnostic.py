#!/usr/bin/env python3
"""Numerical calibration of exact SU(2) integration on an open planar patch.

This is the TWO-DIMENSIONAL open Wilson model: axial gauge reduces a patch
with A plaquettes to the A-fold Haar convolution of its one-plaquette law.
It is not a truncation asserted to approximate the four-dimensional model.

With t = Re tr(U)/2 and normalized Haar measure, the plaquette density is
exp(beta*t)/M(beta), M(beta)=2 I_1(beta)/beta.  Its convolution eigenvalues
are r_n=I_{n+1}(beta)/I_1(beta); the boundary density is
sum_n (n+1) r_n**A U_n(t), where U_n are SU(2) characters.  The script compares
that spectral calculation with direct and staged product-Haar integration,
and measures the non-Wilson character terms of the resulting logarithm.

All errors reported here are numerical diagnostics, not certified bounds.
Dependencies: numpy, scipy.  Example: python3 su2_planar_block_diagnostic.py
"""

import argparse
import json
import math

import numpy as np
from scipy.special import ive, roots_chebyu
from scipy.stats import qmc


def qmul(a, b):
    a, b = np.broadcast_arrays(a, b)
    out = np.empty_like(a)
    out[..., 0] = a[..., 0] * b[..., 0] - np.sum(a[..., 1:] * b[..., 1:], axis=-1)
    out[..., 1:] = (a[..., :1] * b[..., 1:] + b[..., :1] * a[..., 1:]
                    + np.cross(a[..., 1:], b[..., 1:]))
    return out


def qinv(a):
    return a * np.array([1., -1., -1., -1.])


def haar_quaternions(u):
    """Three independent uniform coordinates to uniform S^3 (scalar first)."""
    a, b = 2 * np.pi * u[..., 1], 2 * np.pi * u[..., 2]
    s, c = np.sqrt(1 - u[..., 0]), np.sqrt(u[..., 0])
    return np.stack([s * np.sin(a), s * np.cos(a), c * np.sin(b), c * np.cos(b)], -1)


def log_m(beta):
    beta = np.asarray(beta, dtype=float)
    safe = np.maximum(beta, 1.e-100)
    return np.where(beta < 1.e-6, beta * beta / 8,
                    np.log(2 * ive(1, safe) / safe) + safe)


def ratios(beta, modes):
    if beta == 0:
        r = np.zeros(modes)
        r[0] = 1.
        return r
    return ive(np.arange(1, modes + 1), beta) / ive(1, beta)


def characters(t, modes):
    t = np.asarray(t)
    c = np.ones((modes,) + t.shape)
    if modes > 1:
        c[1] = 2 * t
    for n in range(2, modes):
        c[n] = 2 * t * c[n-1] - c[n-2]
    return c


def density(t, beta, area, modes=64):
    coeff = np.arange(1, modes+1) * ratios(beta, modes)**area
    return np.tensordot(coeff, characters(t, modes), axes=(0, 0))


def convolution_two(t, beta):
    return np.exp(log_m(beta * np.sqrt(np.maximum(0, 2 + 2*t))) - 2*log_m(beta))


def character_diagnostic(beta, area, nodes):
    t, w = roots_chebyu(nodes)
    w *= 2 / np.pi
    k = density(t, beta, area)
    if np.min(k) <= 0:
        raise ArithmeticError("Character truncation lost positivity")
    h = np.log(k)
    coeff = characters(t, 9) @ (w*h)
    remainder = h - coeff[0] - coeff[1]*2*t
    k_more = density(t, beta, area, modes=96)
    return {
        "beta": beta, "area": area, "quadrature_nodes": nodes,
        "normalization_error": float(abs(np.dot(w, k) - 1)),
        "wilson_loop_mean": float(np.dot(w, t*k)),
        "wilson_loop_character_value": float(ratios(beta, 2)[1]**area),
        "effective_wilson_coefficient": float(2*coeff[1]),
        "log_character_coefficients_n0_to_n8": coeff.tolist(),
        "non_wilson_l2": float(np.sqrt(np.dot(w, remainder**2))),
        "non_wilson_sampled_sup": float(np.max(abs(remainder))),
        "density_modes_64_to_96_max_change": float(np.max(abs(k_more-k))),
    }


def integration_check(beta, t, power, replicates):
    g = np.array([t, np.sqrt(1-t*t), 0., 0.])
    estimates = []
    for seed in range(replicates):
        u = qmc.Sobol(d=9, scramble=True, seed=1900+seed).random_base2(power)
        qs = haar_quaternions(u.reshape(-1, 3, 3))
        qprod = qmul(qmul(qs[:, 0], qs[:, 1]), qs[:, 2])
        fourth = qmul(qinv(qprod), g)
        direct = np.exp(beta*(np.sum(qs[:, :, 0], axis=1) + fourth[:, 0]) - 4*log_m(beta))
        q = qs[:, 0]
        other = qmul(qinv(q), g)
        staged = convolution_two(q[:, 0], beta) * convolution_two(other[:, 0], beta)
        estimates.append([float(direct.mean()), float(staged.mean())])
    arr = np.array(estimates)
    exact = float(density(np.array(t), beta, 4))
    return {
        "beta": beta, "boundary_half_trace": t, "points_per_replicate": 2**power,
        "replicates": replicates, "spectral_value": exact,
        "direct_mean": float(arr[:, 0].mean()), "staged_mean": float(arr[:, 1].mean()),
        "direct_abs_error": float(abs(arr[:, 0].mean()-exact)),
        "staged_abs_error": float(abs(arr[:, 1].mean()-exact)),
        "replicate_standard_error": (arr.std(axis=0, ddof=1)/math.sqrt(replicates)).tolist(),
        "replicate_estimates": estimates,
    }


def gauge_check():
    rng = np.random.default_rng(2709)
    links = haar_quaternions(rng.random((8, 3)))
    gauges = haar_quaternions(rng.random((8, 3)))
    changed = qmul(qmul(gauges, links), qinv(np.roll(gauges, -1, axis=0)))

    def product(xs):
        q = np.array([1., 0., 0., 0.])
        for x in xs:
            q = qmul(q, x)
        return q

    blocks = qmul(links[::2], links[1::2])
    changed_blocks = qmul(changed[::2], changed[1::2])
    expected = qmul(qmul(gauges[::2], blocks), qinv(np.roll(gauges[::2], -1, axis=0)))
    return {
        "ordered_loop_gauge_error": float(abs(product(links)[0]-product(changed)[0])),
        "pair_block_gauge_equivariance_error": float(np.max(abs(changed_blocks-expected))),
        "direct_vs_pair_product_error": float(np.max(abs(product(links)-product(blocks)))),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--powers", nargs="+", type=int, default=[13, 16])
    parser.add_argument("--replicates", type=int, default=4)
    args = parser.parse_args()
    betas = [0., 0.01, 0.1, 0.5, 1., 2., 4., 8., 16.]
    result = {
        "model": "two-dimensional open planar SU(2) Wilson patch, normalized Haar measure",
        "scope": "Numerical calibration only; no four-dimensional or uniform-norm certification",
        "gauge_and_order_checks": gauge_check(),
        "spectral_log_diagnostics": [character_diagnostic(b, a, n)
            for b in betas for a in [4, 16] for n in [128, 256]],
        "direct_staged_checks": [integration_check(b, t, p, args.replicates)
            for b in [0.5, 1., 2.] for t in [-0.5, 0.5] for p in args.powers],
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
