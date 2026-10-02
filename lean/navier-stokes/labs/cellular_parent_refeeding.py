#!/usr/bin/env python3
"""Exact residual bounds for feed--return--feed in an actual NS cycle family.

Reuses the complete cellular linear operator and its rational Fourier
algebra. The analytic full nonlinear comparison is given in README.md.
The finite certificate is exact; the PDE argument is not Lean-certified.
"""

import json
from fractions import Fraction as Q

from cellular_transfer_reversal import (
    T, add, scale, linear_operator, norm_squared, sqrt_upper, force,
    real_field, check_canonical_operator, require,
)
from reciprocal_pattern_cycles import hnorm_squared


def seed():
    # The physical field is one tenth of these four polarized cosines.
    polarizations = {(1, 0): (1, -2, -1), (1, -1): (-4, -2, 2),
                     (2, 0): (-3, -5, 6), (2, -1): (4, 10, 2)}
    return {k: tuple(Q(z, 20) for z in v) for k, v in polarizations.items()}


def main():
    c = seed()
    require(force(c) == Q(3, 400), 'first feeding is strictly positive')
    require(norm_squared(c) == Q(11, 10), 'complete initial L2 norm')
    require(hnorm_squared(real_field(c), 3) == Q(259, 2), 'complete initial H3 norm')
    times = [T/2, T]
    values = [{}, {}]
    norm_bound, gradient_bound, laplacian_bound = Q(0), Q(0), Q(0)
    support_counts = []
    for j in range(17):
        for (x, y), z in c.items():
            require(x*z[0]+y*z[1]+z[2] == 0, 'every retained mode is transverse')
        if j in (0, 2, 4):
            check_canonical_operator(c)
        support_counts.append(len(c))
        values = [add(p, scale(t**j, c)) for t, p in zip(times, values)]
        norm_bound += sqrt_upper(norm_squared(c))*T**j
        gradient_bound += 2*sum((abs(x)+abs(y)+1)*sum(abs(z) for z in v)
                                for (x, y), v in c.items())*T**j
        laplacian_bound += sqrt_upper(norm_squared(c, True))*T**j
        c = scale(Q(1, j+1), linear_operator(c))

    # Residual is -17 c17 sigma^16, with no truncation of its spatial support.
    require(norm_bound <= 4, 'uniform polynomial L2 bound')
    require(gradient_bound <= 103, 'uniform full gradient supremum bound')
    require(laplacian_bound <= 31, 'uniform full Laplacian L2 bound')
    require(norm_squared(c)*T**34 <= Q(1, 12000)**2, 'integrated complete residual')
    for p in values:
        require(norm_squared(p) <= Q(11, 10)**2, 'observation-time norm bound')
    require(force(values[0]) <= Q(-1, 100), 'middle polynomial transfer is negative')
    require(force(values[1]) >= Q(1, 200), 'later polynomial transfer is positive')

    reynolds = 200000
    base_error = 3*(Q(1, 12000)+T*31/(reynolds-T))
    require(base_error <= Q(3, 5000), 'complete residual and viscous error')
    error = Q(3, 5000)+3*T*Q(1, 10000)
    require(error == Q(33, 40000) and error <= Q(1, 1000),
            'complete actual nonlinear error over the whole interval')
    require((1+Q(1, 40000))*T < 1, 'energy amplification exponent is below one')
    force_error = (Q(11, 5)+Q(1, 1000))*Q(1, 1000)
    require(Q(-1, 100)+force_error <= Q(-1, 200), 'actual return has negative sign')
    require(Q(1, 200)-force_error >= Q(1, 400), 'actual later feeding has positive sign')
    require(Q(1, 8240000) < Q(1, 30), 'relative perturbation condition')
    require(Q(1, 2)-(4+Q(1, 1000))/30 > Q(1, 3), 'actual parent stays positive')
    require((T/2)/9 == Q(1, 24), 'kinetic loss coefficient between observations')
    print(json.dumps({
        'clock_times': ['0', '3/8', '3/4'],
        'seed_L2_squared': '11/10', 'seed_H3_squared': '259/2',
        'polynomial_degree': 16, 'positive_kz_support_counts': support_counts,
        'observation_positive_kz_modes': [len(p) for p in values],
        'residual_positive_kz_modes': len(c), 'canonical_pressure_degrees': [0, 2, 4],
        'uniform_polynomial_bounds': {'L2': '4', 'gradient_supremum': '103', 'Laplacian_L2': '31'},
        'integrated_residual_bound': '1/12000',
        'minimum_A_over_nu': reynolds,
        'receiver_nonlinearity_condition': '8rho(1+3G0)+824epsilon/A<=1/10000',
        'nonlinear_error_bound': str(error),
        'force_normalized_by_epsilon_squared': ['=3/400', '<=-1/200', '>=1/400'],
        'kinetic_loss_per_observation_interval': '>=nu A/24',
        'power_reserve': '(A+sqrt(Y0)exp(M/2)) Y(t)exp(M exp(-nu t))/nu',
        'status': 'exact finite residual certificate; physical comparison and global cycle construction analytic'
    }, indent=2))


if __name__ == '__main__':
    main()
