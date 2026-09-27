#!/usr/bin/env python3
"""Exact envelope and scaling checks for generated caloric renewal.

The slowly varying envelope is periodic and one-dimensional. It checks
the finite Fourier algebra of localization, not the Schwartz localization
or the uniform local-time argument in the accompanying analytic proof.
All nonlinear outputs are formed before the indicated sharp projections.
"""
from fractions import Fraction as F
from math import comb
import argparse
import json

from fourier_interactions import (A, B, add, inverse_curl, pair, radius_squared,
                                  require, scale, stretching, validate)
from caloric_force import capacity, parent_derivative


CUTOFF_SQUARED = F(14)
PARENTS = ((3, 1, 1), (1, 3, 1), (1, -1, 3))
WEIGHTS = (F(1, 2), F(1), F(1, 2))
POSITIVE_COEFFICIENT = F(15667851179107579904, 95414925477178125)


def high(u, cutoff_squared=CUTOFF_SQUARED):
    return {k: v for k, v in u.items() if radius_squared(k) >= cutoff_squared}


def parents(envelope_scale=None):
    # u = (-partial_y, partial_x, 0)[phi(x/L) psi], not phi times u alone.
    shifts = ((0, F(1)),) if envelope_scale is None else (
        (-1, F(1, 4)), (0, F(1)), (1, F(1, 4)))
    result = {}
    for center, weight in zip(PARENTS, WEIGHTS):
        for sign in (-1, 1):
            for shift, factor in shifts:
                k = tuple(F(sign*x) + (F(shift, envelope_scale)
                          if j == 0 and envelope_scale is not None else 0)
                          for j, x in enumerate(center))
                require(k not in result, 'distinct packet labels at this envelope scale')
                result[k] = (-weight*factor*k[1], weight*factor*k[0], F(0))
    validate(result)
    require(not high(result), 'entire initial tail is empty')
    return result


def renewal(v, nu=F(1), cutoff_squared=CUTOFF_SQUARED):
    return parent_derivative(v, high(B(v, v), cutoff_squared), nu, cutoff_squared)


def envelope_moment(power):
    # Normalized mean of (1 + cos(X)/2)^power.
    return sum((F(comb(power, 2*j)*comb(2*j, j), 16**j)
                for j in range(power//2+1)), F(0))


def check_envelope(length):
    u = parents(length)
    v = high(B(u, u))
    validate(v)
    require(v == high(add(B(u, u), scale(-1, A(u)))),
            'actual first generated tail, including viscosity')
    expected_energy = F(117, 4) + F(3, 8*length*length)
    require(pair(u, u) == expected_energy, 'exact envelope and derivative energy')
    coefficient = renewal(v)
    limit = POSITIVE_COEFFICIENT*envelope_moment(10)
    require(coefficient > 0, 'positive coefficient for this finite envelope')
    require(abs(coefficient/limit-1) < F(1, 100),
            'finite envelope agrees with its predicted leading coefficient')
    return {'envelope_scale': length, 'parent_modes': len(u),
            'child_modes': len(v), 'squared_velocity_norm': str(expected_energy),
            'coefficient_rounded': float(coefficient),
            'coefficient_fraction_bits': [coefficient.numerator.bit_length(),
                                          coefficient.denominator.bit_length()],
            'predicted_limit': str(limit),
            'relative_difference_from_limit': float(coefficient/limit-1)}


def rescale_field(u, amplitude, frequency):
    return {tuple(frequency*x for x in k): tuple(amplitude*x for x in v)
            for k, v in u.items()}


def check_scaling():
    u = parents()
    v = high(B(u, u))
    require(renewal(v) == POSITIVE_COEFFICIENT,
            'cutoff squared fourteen retains the positive coefficient')
    require(high(B(u, u), F(16)) == v, 'initial child matches the original cutoff')
    require(high(B(v, v), F(16)) == high(B(v, v)), 'nonlinear direction has the same gap')
    require(renewal(v, cutoff_squared=F(16)) == renewal(v), 'stretching outputs have the same gap')
    rows = []
    # lambda = r^2 and amplitude = r^3 preserve whole-space squared L2 norm.
    for r, nu in ((F(2), F(1)), (F(3), F(1, 2))):
        lam, amplitude = r*r, r*r*r
        physical = rescale_field(v, amplitude, lam)
        jacobian = lam**-3
        clock_rate = amplitude*lam
        delta = nu/r
        full_a = A(v)
        full_m = inverse_curl(stretching(v))
        physical_a = A(physical)
        physical_m = inverse_curl(stretching(physical))
        material = add(physical_m, scale(-nu, physical_a))
        cost = jacobian*(nu*pair(physical_a, physical_a)+pair(material, material)/nu)
        reduced_material = add(full_m, scale(-delta, full_a))
        reduced_cost = delta**2*pair(full_a, full_a)+pair(reduced_material, reduced_material)
        actual_return = jacobian*renewal(physical, nu, lam**2*CUTOFF_SQUARED)
        require(jacobian*pair(physical, physical) == pair(v, v), 'unit-energy scaling')
        require(jacobian*capacity(physical, nu, lam**2*CUTOFF_SQUARED)
                == lam**3*capacity(v, F(1), CUTOFF_SQUARED)/nu**2,
                'whole-space capacity scaling with volume factor')
        require(actual_return/clock_rate == lam**3*renewal(v)/nu**2,
                'time-integrated fully high renewal scaling')
        require(cost/clock_rate == r**5*reduced_cost/nu,
                'time-integrated full cost, including the viscous square')
        rows.append({'lambda': str(lam), 'viscosity': str(nu),
                     'effective_viscosity': str(delta),
                     'integrated_renewal_multiplier': str(lam**3/nu**2),
                     'integrated_cost_multiplier': str(r**5/nu)})
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--envelopes', nargs='*', type=int, default=[16, 64])
    args = parser.parse_args()
    require(all(length >= 16 for length in args.envelopes), 'envelope scales at least sixteen')
    result = {'status': 'all exact checks passed',
              'scope': 'finite periodic envelope and scaling algebra; not a PDE enclosure',
              'positive_coefficient': str(POSITIVE_COEFFICIENT),
              'envelope_tenth_moment': str(envelope_moment(10)),
              'scaling': check_scaling(),
              'envelopes': [check_envelope(length) for length in args.envelopes]}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
