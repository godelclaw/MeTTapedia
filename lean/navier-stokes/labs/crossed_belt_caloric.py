#!/usr/bin/env python3
"""Exact renewal from two planar families in different dyadic shells.

Finite Fourier arithmetic retains every generated mode before the two
high-output masks. The envelope samples are periodic algebra checks;
whole-space localization and the unforced time interval are analytic
arguments in the accompanying paper, not numerical PDE enclosures.
"""
from fractions import Fraction as F
import argparse
import json

from fourier_interactions import (A, B, add, dot, inverse_curl, pair,
                                  project, radius_squared, require, scale,
                                  stretching, validate)
from caloric_force import derivative, parent_derivative
from caloric_localization import envelope_moment
from belt_caloric import paired


PLANES = {2: ((3, 1, 0), (2, 1, 0), (1, 2, 0)),
          1: ((5, 0, 4), (-1, 0, -4))}
COEFFICIENT = F(5469265097437563, 230433883895600)
CUTOFF_SQUARED = F(4)


def fields(envelope=None, length=None):
    result = {}
    for axis, centers in PLANES.items():
        u = {}
        shifts = ((0, F(1)),) if envelope is None else (
            (-1, F(1, 4)), (0, F(1)), (1, F(1, 4)))
        for center in centers:
            for sign in (-1, 1):
                for shift, weight in shifts:
                    coordinate = axis if envelope == 'normal' else 0
                    k = tuple(F(sign*x)+(F(shift, length)
                              if envelope and j == coordinate else F(0))
                              for j, x in enumerate(center))
                    a = (-k[1], k[0], F(0)) if axis == 2 else (k[2], F(0), -k[0])
                    require(k not in u, 'distinct packet labels')
                    u[k] = tuple(weight*x for x in a)
        validate(u)
        lower, upper = (4, 16) if axis == 2 else (16, 64)
        for k, a in u.items():
            require(lower < radius_squared(k) < upper, 'separate dyadic shells')
            require(a[axis] == 0, 'exact planar velocity polarization')
            if envelope == 'normal':
                require(abs(k[axis]) <= F(1, length), 'thin normal envelope')
            else:
                require(k[axis] == 0, 'exact planar frequency support')
        result[axis] = u
    require(not (result[1].keys() & result[2].keys()), 'disjoint parent spectra')
    return result[2], result[1]


def high(u, floor=CUTOFF_SQUARED):
    return {k: a for k, a in u.items() if radius_squared(k) >= floor}


def renewal(u, nu=F(1), floor=CUTOFF_SQUARED):
    return parent_derivative(u, high(B(u, u), floor), nu, floor)


def colored_expansion(left, right):
    """Count original xy-plane inputs in the full paired quintic expansion."""
    u = add(left, right)
    result = {i: F(0) for i in range(6)}
    counts = {i: 0 for i in range(6)}
    for p, a in u.items():
        for q, b in u.items():
            k = tuple(x+y for x, y in zip(p, q))
            if radius_squared(k) < CUTOFF_SQUARED:
                continue
            source = paired(p, a, q, b)
            if not any(source):
                continue
            for c, v in u.items():
                r = tuple(x-y for x, y in zip(k, c))
                if radius_squared(r) < CUTOFF_SQUARED:
                    continue
                for d, w in u.items():
                    e = tuple(x-y for x, y in zip(r, d))
                    if e not in u:
                        continue
                    direction = project(r, tuple(dot(w, e)*x for x in u[e]))
                    tangent = paired(c, v, r, direction)
                    rate = sum(radius_squared(x) for x in (p, q, c, r))
                    value = dot(source, tangent)/rate
                    color = sum(x in left for x in (p, q, c, d, e))
                    result[color] += value
                    counts[color] += (value != 0)
    require(result == {i: COEFFICIENT if i == 3 else F(0) for i in range(6)},
            'only three xy inputs and two xz inputs contribute')
    return {'coefficients_by_xy_degree': {str(k): str(v) for k, v in result.items()},
            'nonzero_ordered_counts_by_xy_degree': counts}


def base_checks():
    a, b = fields()
    for u in (a, b):
        require(not stretching(u) and not inverse_curl(stretching(u)),
                'each planar family has zero stretching')
        require(renewal(u) == 0, 'each family has zero caloric renewal')
    u = add(a, b)
    require(all(radius_squared(tuple(x+y for x, y in zip(p, q))) != CUTOFF_SQUARED
                for p in u for q in u), 'every carrier output avoids the cutoff boundary')
    require(pair(u, u) == 156 and pair(A(u), A(u)) == 150168, 'base norm constants')
    require(renewal(u) == COEFFICIENT > 0, 'positive mixed renewal')
    require(renewal(u) == renewal(u, floor=F(0)), 'both high masks retain the coefficient')
    require(derivative(u, high(B(u, u)), F(1), CUTOFF_SQUARED) == COEFFICIENT,
            'independent quartic polarization')
    for x, y, nu in ((1, 0, 1), (0, 1, 1), (2, 1, 1), (1, 2, 1),
                     (-1, 1, 1), (1, -1, 1), (F(3, 2), F(-2, 3), F(1, 2))):
        require(renewal(add(scale(F(x), a), scale(F(y), b)), F(nu)) ==
                COEFFICIENT*F(x)**3*F(y)**2/F(nu)**2,
                'amplitude degrees, sign, and viscosity normalization')
    return {'coefficient': str(COEFFICIENT), 'coefficient_rounded': float(COEFFICIENT),
            'squared_velocity_norm': '156', 'squared_laplacian_norm': '150168',
            **colored_expansion(a, b)}


def envelope_check(kind, length):
    require(length >= 32, 'envelope remains in the strict shell gaps')
    a, b = fields(kind, length)
    u = add(a, b)
    result = renewal(u)
    factor = (envelope_moment(3)*envelope_moment(2) if kind == 'normal'
              else envelope_moment(5))
    limit = COEFFICIENT*factor
    require(result > 0 and abs(result/limit-1) < F(1, 100),
            'positive finite envelope with the predicted resonant limit')
    if kind == 'normal':
        require(pair(u, u) == F(156)*envelope_moment(2), 'normal-envelope energy')
    return {'envelope': kind, 'length': length, 'parent_modes': len(u),
            'renewal_rounded': float(result), 'predicted_limit': str(limit),
            'relative_difference': float(result/limit-1),
            'fraction_bits': [result.numerator.bit_length(), result.denominator.bit_length()]}


def scaling_checks():
    rows = []
    # lambda=r^4, delta=r^-2, and q=d^2 keep every check rational.
    for r, d, nu in ((F(2), F(1), F(1)), (F(3), F(2), F(1, 3)),
                     (F(11), F(3), F(5))):
        lam, delta, q = r**4, r**-2, d*d
        amplitude = r**5/d
        eps = nu*lam/amplitude
        interval = delta**3
        physical_time = interval/(amplitude*lam)
        require(amplitude**2*lam**-3*q/delta == 1, 'exact whole-space energy normalization')
        require(eps**2/delta == nu**2*q, 'bounded dimensionless viscous cost')
        require(physical_time == d/r**15, 'shrinking actual physical interval')
        renewal_integral_factor = amplitude**4*lam**-3*interval/nu**2
        cost_integral_factor = amplitude**3*lam**-2*interval/nu
        require(renewal_integral_factor == r*r/(d**4*nu**2), 'integrated renewal exponent')
        require(cost_integral_factor == r/(d**3*nu), 'integrated full cost exponent')
        require(amplitude**5*lam**-2 == r**17/d**5, 'instantaneous renewal exponent')
        require(amplitude**2*lam/delta == r**16/d**2, 'instantaneous dissipation exponent')
        rows.append({'lambda': str(lam), 'delta': str(delta), 'viscosity': str(nu),
                     'physical_time_factor': str(physical_time),
                     'renewal_integral_factor': str(renewal_integral_factor),
                     'full_cost_integral_factor': str(cost_integral_factor)})
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--envelopes', nargs='*', type=int, default=[32, 128])
    args = parser.parse_args()
    report = {'status': 'all exact checks passed',
              'scope': 'finite periodic algebra and scaling; localization and evolution are analytic',
              'base': base_checks(), 'scalings': scaling_checks(),
              'envelopes': [envelope_check(kind, length)
                            for kind in ('normal', 'common_x') for length in args.envelopes]}
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
