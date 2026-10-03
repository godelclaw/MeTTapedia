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
from scipy.special import ive, roots_chebyu, roots_legendre
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


def pair_conditional_moments(t, beta):
    """Exact conditional trace moments for two planar plaquettes, UV=C.

    A fixed C tilts normalized S^3 Haar measure by the vector
    beta*(1+Re(C), Im(C)).  These are moments of the original plaquettes,
    not substitute observables of the coarse product.
    """
    t = np.asarray(t)
    kappa = beta * np.sqrt(np.maximum(0., 2 + 2*t))
    small = kappa < 1.e-5
    safe = np.maximum(kappa, 1.e-100)
    r_over_k = np.where(small, .25 - kappa*kappa/96,
                        ive(2, safe) / ive(1, safe) / safe)
    mean = beta * (1+t) * r_over_k
    axial_extra = 1 - 4*r_over_k
    second = r_over_k + axial_extra*(1+t)/2
    cross = r_over_k*t + axial_extra*(1+t)/2
    return mean, second, cross


def character_tail_diagnostic(beta, area, modes=64, cutoff=384):
    """Numerical finite tail and an analytic envelope for the remaining tail.

    |U_n(t)| <= n+1. From the Bessel series,
    I_(n+1)(beta)/I_1(beta) <= exp(beta)*(beta/2)^n/(n+1)!.
    After cutoff the resulting weighted terms have a decreasing ratio <=rho.
    The logarithmic infinite-tail envelope avoids underflow. Its floating-point
    evaluation and the finite coefficient sum are not certified arithmetic.
    """
    if beta < 0 or area < 1 or not 0 < modes < cutoff:
        raise ValueError("Require beta >= 0, area >= 1, and 0 < modes < cutoff")
    if beta == 0:
        return {"modes": modes, "infinite_tail_start_degree": cutoff,
                "finite_tail_before_cutoff": 0.,
                "log_infinite_tail_envelope": None,
                "zero_coupling_tail_exactly_zero": True}
    n = np.arange(modes, cutoff)
    finite = float(np.sum((n+1)**2 * ratios(beta, cutoff)[modes:]**area))
    rho = ((cutoff+2)/(cutoff+1))**2 * (beta/(2*(cutoff+2)))**area
    if rho >= 1:
        raise ValueError("Increase the character tail cutoff for this coupling")
    log_bound = (2*math.log(cutoff+1) + area*(beta+cutoff*math.log(beta/2)
                 - math.lgamma(cutoff+2)) - math.log1p(-rho))
    return {"modes": modes, "infinite_tail_start_degree": cutoff,
            "finite_tail_before_cutoff": finite,
            "log_infinite_tail_envelope": log_bound,
            "remaining_envelope_geometric_ratio": rho}


def covariance_diagnostic(beta, nodes):
    """Covariance and variance ledgers for 2 and 4 independent plaquettes.

    This is the axial-gauge representation of an open two-dimensional
    Wilson patch.  Adjacent plaquettes have zero original covariance;
    conditioning on their product can create a nonzero covariance which
    cancels the covariance of their projected means exactly.
    """
    t, w = roots_chebyu(nodes)
    w *= 2 / np.pi
    v, vw = roots_legendre(max(32, nodes//2))
    vw /= 2
    k2 = convolution_two(t, beta)
    m2, second2, cross2 = pair_conditional_moments(t, beta)
    fine_mean = 0. if beta == 0 else float(ive(2, beta)/ive(1, beta))
    fine_second = .25 if beta == 0 else 1 - 3*fine_mean/beta
    fine_var = fine_second - fine_mean*fine_mean
    e2 = lambda f: float(np.dot(w*k2, f))
    retained2 = e2(m2*m2) - fine_mean*fine_mean
    remainder2 = e2(cross2-m2*m2)
    conditional_var2 = e2(second2-m2*m2)

    # Haar A has scalar a and an S^2 direction; the component along Im(C)
    # is uniform on [-1,1].  This retains the noncommutative product order.
    a = t[:, None]
    aw = w[:, None] * vw[None, :]
    k2a = k2[:, None]
    m2a = m2[:, None]
    m4, pair_square4, pair_cross4, density4 = [], [], [], []
    direct_same4 = []
    for c in t:
        b = a*c + np.sqrt(np.maximum(0., (1-a*a)*(1-c*c))) * v[None, :]
        joint = aw*k2a*convolution_two(b, beta)
        den = float(joint.sum())
        m2b, _, _ = pair_conditional_moments(b, beta)
        density4.append(den)
        m4.append(float((joint*m2a).sum())/den)
        pair_square4.append(float((joint*m2a*m2a).sum())/den)
        pair_cross4.append(float((joint*m2a*m2b).sum())/den)
        direct_same4.append(float((joint*cross2[:, None]).sum())/den)
    density4, m4, pair_square4, pair_cross4, direct_same4 = map(
        np.asarray, (density4, m4, pair_square4, pair_cross4, direct_same4))
    e4 = lambda f: float(np.dot(w*density4, f))
    retained4 = e4(m4*m4) - fine_mean*fine_mean
    second_same = e4(pair_square4-m4*m4)
    second_cross = e4(pair_cross4-m4*m4)
    return {
        "beta": beta, "quadrature_nodes": nodes,
        "original_single_plaquette_mean": fine_mean,
        "original_single_plaquette_variance": fine_var,
        "original_distinct_plaquette_covariance": 0.,
        "two_plaquettes": {
            "retained_covariance": retained2,
            "averaged_conditional_covariance": remainder2,
            "covariance_ledger_error": retained2+remainder2,
            "averaged_conditional_variance": conditional_var2,
            "variance_ledger_error": retained2+conditional_var2-fine_var,
        },
        "four_plaquettes_same_first_pair": {
            "retained_covariance": retained4,
            "first_scale_contribution": remainder2,
            "second_scale_contribution": second_same,
            "covariance_ledger_error": retained4+remainder2+second_same,
            "direct_vs_staged_remainder_error": e4(direct_same4-m4*m4)-remainder2-second_same,
            "signed_discarded_sum": remainder2+second_same,
            "absolute_discarded_sum": abs(remainder2)+abs(second_same),
            "absolute_sum_over_fine_variance": (abs(remainder2)+abs(second_same))/fine_var,
            "beta_squared_absolute_sum": beta*beta*(abs(remainder2)+abs(second_same)),
        },
        "four_plaquettes_different_first_pairs": {
            "retained_covariance": retained4,
            "first_scale_contribution": 0.,
            "second_scale_contribution": second_cross,
            "covariance_ledger_error": retained4+second_cross,
        },
        "retained_variance_ratio_two": retained2/fine_var,
        "retained_variance_ratio_four": retained4/fine_var,
        "normalization_error_two": abs(e2(np.ones_like(t))-1),
        "normalization_error_four": abs(e4(np.ones_like(t))-1),
        "four_density_vs_character_max_error": float(np.max(abs(density4-density(t, beta, 4)))),
        "four_density_modes_64_to_128_max_change": float(np.max(abs(
            density(t, beta, 4, modes=128)-density(t, beta, 4, modes=64)))),
        "four_density_modes_128_to_192_max_change": float(np.max(abs(
            density(t, beta, 4, modes=192)-density(t, beta, 4, modes=128)))),
        "four_density_character_tail": character_tail_diagnostic(beta, 4),
    }


def wilson_samples(beta, count, rng):
    """Independent samples of exp(beta*t) times S^3 Haar, beta >= 1.

    Set y=beta*(1-t).  Its density is proportional to
    exp(-y)*sqrt(y)*sqrt(1-y/(2*beta)) on [0,2*beta].  Thus a Gamma(3/2,1)
    proposal with the displayed square-root acceptance factor is exact in
    real arithmetic.  There is no Markov chain or quadrature in the sampler.
    """
    if beta < 1:
        raise ValueError("The weak-coupling sampler requires beta >= 1")
    accepted, trials, remaining = [], 0, count
    while remaining:
        batch = max(256, int(1.5*remaining))
        y = rng.gamma(1.5, 1., batch)
        keep = ((y <= 2*beta)
                & (rng.random(batch) <= np.sqrt(np.maximum(0., 1-y/(2*beta)))))
        values = y[keep][:remaining]
        accepted.append(values)
        remaining -= len(values)
        trials += batch
    t = 1 - np.concatenate(accepted)/beta
    direction = rng.normal(size=(count, 3))
    direction /= np.linalg.norm(direction, axis=1)[:, None]
    return np.column_stack([t, np.sqrt(np.maximum(0., 1-t*t))[:, None]*direction]), trials


def planar_projected_mean(t, beta, area, modes=128):
    """Original plaquette trace conditioned on an ordered area-fold product.

    Differentiate the complete character expansion: m_A = m_1 +
    (1/A) d_beta log(k_A).  No fitted Wilson coupling is used.  Positivity is
    checked at every sampled product; tails with catastrophic cancellation
    are rejected rather than silently clipped.
    """
    n = np.arange(1, modes+1)
    r = ratios(beta, modes)
    dr = (ive(n-1, beta)+ive(n+1, beta))/(2*ive(1, beta))
    dr -= r*(ive(0, beta)+ive(2, beta))/(2*ive(1, beta))
    dr[0] = 0.
    chars = characters(t, modes)
    k = np.tensordot(n*r**area, chars, axes=(0, 0))
    if np.any(k <= 1.e-10):
        raise ArithmeticError("Insufficient character precision at a sampled product")
    numerator = np.tensordot(n*r**(area-1)*dr, chars, axes=(0, 0))
    return ive(2, beta)/ive(1, beta)+numerator/k


def covariance_wilson_sampling(beta, power, replicates, reference):
    """Check the signed ledger by sampling the actual planar Wilson law.

    Center using the exact one-plaquette mean.  The two successive conditional
    means keep all character modes up to the reported truncation.  The signed
    increments are martingale differences; their products estimate the
    averaged conditional covariances directly, under the generated laws.
    """
    count = 2**power
    fine_mean = float(ive(2, beta)/ive(1, beta))
    estimates, sampler_checks = [], []
    truncation_error = 0.
    for seed in range(replicates):
        qs, trials = wilson_samples(beta, 4*count, np.random.default_rng(4200+seed))
        qs = qs.reshape(count, 4, 4)
        a, b = qmul(qs[:, 0], qs[:, 1]), qmul(qs[:, 2], qs[:, 3])
        c = qmul(a, b)
        m2a = pair_conditional_moments(a[:, 0], beta)[0]
        m2b = pair_conditional_moments(b[:, 0], beta)[0]
        m4 = planar_projected_mean(c[:, 0], beta, 4, 128)
        m4_more = planar_projected_mean(c[:, 0], beta, 4, 192)
        truncation_error = max(truncation_error, float(np.max(abs(m4-m4_more))))
        f, g = qs[:, 0, 0], qs[:, 1, 0]
        first = (f-m2a)*(g-m2a)
        second_same = (m2a-m4)**2
        second_cross = (m2a-m4)*(m2b-m4)
        retained = (m4-fine_mean)**2
        original_cov = (f-fine_mean)*(g-fine_mean)
        estimates.append([first.mean(), second_same.mean(), second_cross.mean(),
                          retained.mean(), original_cov.mean(), (first+second_same).mean()])
        sampler_checks.append({"proposals": trials, "returned_samples": 4*count,
            "trace_mean_error": float(qs[:, :, 0].mean()-fine_mean),
            "unit_quaternion_max_error": float(np.max(abs(np.sum(qs*qs, axis=2)-1)))})
    arr = np.asarray(estimates)
    same = reference["four_plaquettes_same_first_pair"]
    cross = reference["four_plaquettes_different_first_pairs"]
    expected = np.array([same["first_scale_contribution"], same["second_scale_contribution"],
        cross["second_scale_contribution"], same["retained_covariance"], 0., same["signed_discarded_sum"]])
    return {"beta": beta, "points_per_replicate": count, "replicates": replicates,
        "seed_base": 4200, "sampling_method": "independent Gamma rejection, no Markov chain",
        "quantities": ["first_same_pair", "second_same_pair", "second_different_pairs",
                       "retained_covariance", "original_covariance", "signed_discarded_sum"],
        "means": arr.mean(axis=0).tolist(), "quadrature_reference": expected.tolist(),
        "absolute_errors": abs(arr.mean(axis=0)-expected).tolist(),
        "replicate_standard_errors": (arr.std(axis=0, ddof=1)/np.sqrt(replicates)).tolist(),
        "projected_mean_modes_128_to_192_max_change": truncation_error,
        "sampler_checks": sampler_checks, "replicate_estimates": estimates}


def covariance_integration_check(beta, t, power, replicates):
    """Independent direct-Haar check of the conditional four-plaquette moments."""
    g = np.array([t, np.sqrt(1-t*t), 0., 0.])
    estimates = []
    for seed in range(replicates):
        u = qmc.Sobol(d=9, scramble=True, seed=3100+seed).random_base2(power)
        qs = haar_quaternions(u.reshape(-1, 3, 3))
        qprod = qmul(qmul(qs[:, 0], qs[:, 1]), qs[:, 2])
        fourth = qmul(qinv(qprod), g)
        weight = np.exp(beta*(qs[:, :, 0].sum(axis=1)+fourth[:, 0])-4*log_m(beta))
        den = weight.mean()
        f, h = qs[:, 0, 0], qs[:, 1, 0]
        mean_f, mean_h = np.mean(weight*f)/den, np.mean(weight*h)/den
        cross = np.mean(weight*f*h)/den
        estimates.append([den, mean_f, mean_h, cross, cross-mean_f*mean_h])
    arr = np.array(estimates)
    a, aw = roots_chebyu(192)
    aw *= 2 / np.pi
    v, vw = roots_legendre(96)
    vw /= 2
    b = a[:, None]*t + np.sqrt((1-a[:, None]**2)*(1-t*t))*v
    joint = aw[:, None]*vw*convolution_two(a, beta)[:, None]*convolution_two(b, beta)
    den = joint.sum()
    m2, _, cross2 = pair_conditional_moments(a, beta)
    mean = float((joint*m2[:, None]).sum()/den)
    cross = float((joint*cross2[:, None]).sum()/den)
    reference = np.array([den, mean, mean, cross, cross-mean*mean])
    return {
        "beta": beta, "boundary_half_trace": t,
        "points_per_replicate": 2**power, "replicates": replicates,
        "quantities": ["density", "projected_F", "projected_G", "projected_FG", "conditional_covariance"],
        "direct_mean": arr.mean(axis=0).tolist(),
        "staged_quadrature_reference": reference.tolist(),
        "absolute_errors": abs(arr.mean(axis=0)-reference).tolist(),
        "replicate_standard_errors": (arr.std(axis=0, ddof=1)/np.sqrt(replicates)).tolist(),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--powers", nargs="+", type=int, default=[13, 16])
    parser.add_argument("--replicates", type=int, default=4)
    parser.add_argument("--covariance", action="store_true",
                        help="Include exact conditional covariance and variance ledgers")
    parser.add_argument("--weak-coupling", action="store_true",
                        help="Probe increasing beta with signed ledgers and direct Wilson sampling")
    parser.add_argument("--betas", nargs="+", type=float, default=[1., 2., 4., 8., 16., 32., 64., 128.])
    parser.add_argument("--nodes", nargs="+", type=int, default=[128, 256])
    args = parser.parse_args()
    if args.replicates < 2:
        parser.error("At least two independent replicates are needed to estimate sampling errors")
    if args.weak_coupling:
        if min(args.betas) < 1:
            parser.error("Weak-coupling sampling requires all beta values >= 1")
        ledgers = [covariance_diagnostic(b, n) for b in args.betas for n in args.nodes]
        references = {b: max((r for r in ledgers if r["beta"] == b),
                              key=lambda r: r["quadrature_nodes"]) for b in args.betas}
        result = {
            "model": "two-dimensional open planar SU(2) Wilson patch, independent axial-gauge plaquettes",
            "scope": "Numerical evidence only; four original plaquettes and two integration steps, not a four-dimensional spatial estimate",
            "normalization": "t=Re(tr(U))/2; raw covariance, covariance divided by Var(t), and beta^2 times covariance are distinct diagnostics",
            "gauge_and_order_checks": gauge_check(),
            "covariance_ledgers": ledgers,
            "direct_wilson_sampling": [covariance_wilson_sampling(b, p, args.replicates, references[b])
                for b in args.betas for p in args.powers],
        }
        print(json.dumps(result, indent=2, allow_nan=False))
        return
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
    if args.covariance:
        result["covariance_ledgers"] = [covariance_diagnostic(b, n)
            for b in betas for n in [64, 128]]
        result["covariance_direct_staged_checks"] = [covariance_integration_check(b, t, p, args.replicates)
            for b in [0.5, 1., 2.] for t in [-0.5, 0.5] for p in args.powers]
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
