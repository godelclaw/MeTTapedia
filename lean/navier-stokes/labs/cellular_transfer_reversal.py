#!/usr/bin/env python3
"""Exact residual certificate for a reversal of internal NS parent transfer.

The degree-eight polynomial keeps every generated Fourier mode. Its exact
residual, together with the analytic energy argument in README.md, controls
an actual nonlinear positive-viscosity history. This script verifies the
finite rational inequalities; PDE existence and the comparison theorem are
analytic, not Lean-certified. No floating-point flow is used as evidence.
"""

import json
import math
from fractions import Fraction as Q

import pressure_history_source as f
from reciprocal_pattern_cycles import mode, require

ZERO = (Q(0), Q(0), Q(0))
T = Q(3, 4)


def add(a, b):
    out = dict(a)
    for k, z in b.items():
        out[k] = tuple(x+y for x, y in zip(out.get(k, ZERO), z))
    return {k: z for k, z in out.items() if any(z)}


def scale(c, a):
    return {k: tuple(c*x for x in z) for k, z in a.items() if c}


def linear_operator(r):
    """L r=-P(v.grad r+r.grad v), represented on the kz=+1 block."""
    out = {}
    for (x, y), z in r.items():
        for direction in (-1, 1):
            value = [direction*x*a/2 for a in z]
            value[0] += z[1]/2
            out = add(out, {(x, y+direction): tuple(value)})
            value = [-direction*y*a/2 for a in z]
            value[1] -= z[0]/2
            out = add(out, {(x+direction, y): tuple(value)})
    for (x, y), z in out.items():
        dot = (x*z[0]+y*z[1]+z[2])/Q(x*x+y*y+1)
        out[(x, y)] = tuple(-a+k*dot for a, k in zip(z, (x, y, 1)))
    return {k: z for k, z in out.items() if any(z)}


def norm_squared(r, laplacian=False):
    # Both conjugate kz blocks are included, with normalized torus volume.
    return 2*sum(sum(z*z for z in v)*(x*x+y*y+1)**(2 if laplacian else 0)
                 for (x, y), v in r.items())


def sqrt_upper(q, denominator=10**12):
    """A rational upper bound, rounded using integer square roots only."""
    numerator = math.isqrt(q.numerator*denominator**2//q.denominator)
    if Q(numerator**2, denominator**2) < q:
        numerator += 1
    result = Q(numerator, denominator)
    require(result >= 0 and result*result >= q, 'outward square-root bound')
    return result


def force(r):
    return sum(z[0]*(r.get((x, y-1), ZERO)[1]+r.get((x, y+1), ZERO)[1]
                     -r.get((x-1, y), ZERO)[1]-r.get((x+1, y), ZERO)[1])
               for (x, y), z in r.items())


def real_field(r):
    full = [{}, {}, {}]
    for (x, y), z in r.items():
        for j, value in enumerate(z):
            if value:
                full[j][(x, y, 1)] = f.QQ_I(value)
                full[j][(-x, -y, -1)] = f.QQ_I(value)
    return full


def check_canonical_operator(r):
    """Independent complete convection/pressure construction."""
    v = [mode((0, 1, 0), 1, True), mode((1, 0, 0), -1, True), {}]
    d = real_field(r)
    cross_pressure = f.green(f.scale(2, f.trace(f.matmul(f.jac(v), f.jac(d)))))
    actual = [f.add(f.scale(-1, f.adv(v, d[j])), f.scale(-1, f.adv(d, v[j])),
                    f.scale(-1, f.diff(cross_pressure, j))) for j in range(3)]
    expected = real_field(linear_operator(r))
    for a, b in zip(actual, expected):
        f.equal(a, b, 'complete linear operator and canonical pressure')
    f.equal(f.trace(f.jac(actual)), {}, 'pressure-corrected linear tangent')
    work = f.dot(d, f.matvec(f.jac(v), d)).get(f.ORIGIN, f.ZERO)
    require(work == f.QQ_I(force(r)), 'independent physical transfer observable')
    pairing = f.dot(d, actual).get(f.ORIGIN, f.ZERO)
    require(pairing == -work, 'linear energy work is opposite parent transfer')


def main():
    c = {(1, 0): (Q(1, 2), Q(0), Q(-1, 2)),
         (1, -1): (Q(1, 2), Q(1, 2), Q(0))}
    require(force(c) == Q(1, 4), 'strictly positive initial transfer')
    endpoint, coefficients = {}, []
    norm_bound, gradient_bound, laplacian_bound = Q(0), Q(0), Q(0)
    for j in range(9):
        for (x, y), z in c.items():
            require(x*z[0]+y*z[1]+z[2] == 0, 'every coefficient is solenoidal')
        if j in (0, 4, 8):
            check_canonical_operator(c)
        coefficients.append(len(c))
        endpoint = add(endpoint, scale(T**j, c))
        norm_bound += sqrt_upper(norm_squared(c))*T**j
        gradient_bound += 2*sum((abs(x)+abs(y)+1)*sum(abs(z) for z in v)
                                for (x, y), v in c.items())*T**j
        laplacian_bound += sqrt_upper(norm_squared(c, True))*T**j
        c = scale(Q(1, j+1), linear_operator(c))

    # p'=L p-9 c9 sigma^8. These bounds hold for every 0<=sigma<=T.
    require(norm_bound <= 3, 'uniform complete polynomial L2 bound')
    require(gradient_bound <= 42, 'uniform complete gradient supremum bound')
    require(laplacian_bound <= Q(51, 5), 'uniform Laplacian L2 bound')
    require(norm_squared(c)*T**18 <= Q(1, 1000)**2, 'integrated Taylor residual')
    require(norm_squared(endpoint) <= Q(7, 5)**2, 'endpoint L2 bound')
    require(force(endpoint) <= Q(-18, 125), 'negative endpoint transfer')

    # mu<=1/(2000-T). Exponential energy amplification is bounded by 3.
    base_error = 3*(Q(1, 1000)+T*Q(51, 5)/(2000-T))
    require(base_error <= Q(3, 200), 'Taylor plus full viscous error')
    error = Q(3, 200)+3*T*Q(1, 300)
    require(error == Q(9, 400), 'complete receiver and nonlinear remainder')
    force_upper = Q(-18, 125)+(Q(14, 5)+error)*error
    require(force_upper <= Q(-1, 16), 'actual normalized transfer is negative')
    require((1+Q(1, 900))*T < 1, 'energy amplification exponent is below one')
    require(Q(1, 75600) <= Q(1, 20), 'feedback condition bounds relative perturbation')
    require(Q(1, 2)-(3+error)/20 > Q(1, 3), 'parent remains positive throughout')
    print(json.dumps({
        'clock_endpoint': str(T), 'polynomial_degree': 8,
        'positive_kz_modes_by_degree': coefficients, 'endpoint_modes': len(endpoint),
        'linear_pressure_cross_checks': [0, 4, 8],
        'uniform_bounds': {'L2': '3', 'gradient_supremum': '42', 'Laplacian_L2': '51/5'},
        'integrated_Taylor_residual_upper': '1/1000',
        'endpoint_polynomial_force_upper': '-18/125',
        'endpoint_polynomial_norm_upper': '7/5',
        'minimum_A_over_nu': 2000,
        'receiver_and_nonlinearity_condition': '6 rho (1+3 G0)+252 epsilon/A<=1/300',
        'base_error_upper': '3/200', 'complete_error_upper': str(error),
        'actual_initial_force': 'epsilon^2/4',
        'actual_endpoint_force_upper': '-epsilon^2/16',
        'normalized_force_upper_before_rounding': str(force_upper),
        'status': 'exact finite residual inequalities; actual nonlinear history and cycle theorem analytic'
    }, indent=2))


if __name__ == '__main__':
    main()
