#!/usr/bin/env python3
"""Exact whole-time pressure feedback and its small-amplitude payment.

Reuse the complete viscous amplitude recurrence and exponential-polynomial
algebra from paired_stretching_history. No time grid or Fourier cutoff is
used. The analytic remainder argument in README.md is required to pass
from these coefficients to actual finite-amplitude NS histories.
"""

import argparse
import json
from fractions import Fraction as Q
from math import factorial

import paired_stretching_history as e
import pressure_history_source as f
from cyclic_pressure_history import velocity_time_jets
from pressure_parent_bellman import trig


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def clean(a):
    return {k: v for k, v in a.items() if v}


def add(*arrays):
    result = {}
    for a in arrays:
        for k, v in a.items():
            result[k] = e.add(result.get(k, {}), v)
    return clean(result)


def scale(c, a):
    return clean({k: e.scale(c, v) for k, v in a.items()})


def multiply(a, b):
    result = {}
    for k, v in a.items():
        for ell, w in b.items():
            q = tuple(x+y for x, y in zip(k, ell))
            result[q] = e.add(result.get(q, {}), e.multiply(v, w))
    return clean(result)


def heat(a):
    result = {k: e.heat_convolution(v, sum(q*q for q in k)) for k, v in a.items()}
    for k, v in result.items():
        require(e.add(e.derivative(v), e.scale(sum(q*q for q in k), v)) == a[k],
                'Every conditional moment solves its complete heat-source equation')
        require(e.jet(v, 0) == 0, 'No conditional history is initialized twice')
    return clean(result)


def transport(u, a):
    # Moment of order r has Fourier coefficient i^r*a; u has i*u_tilde.
    # Thus -u.grad(moment) has normalized coefficient +(u_tilde.q)*a.
    result = {}
    for k, v in u.items():
        for ell, w in a.items():
            factor = e.add(*(e.scale(ell[i], v[i]) for i in range(3)))
            if factor:
                q = tuple(x+y for x, y in zip(k, ell))
                result[q] = e.add(result.get(q, {}), e.multiply(factor, w))
    return clean(result)


def mean_product(a, b):
    return e.add(*(e.multiply(v, b.get(tuple(-x for x in k), {})) for k, v in a.items()))


def check_time_jets(u, pressure, amplitudes, k):
    initial = [f.scale(amplitudes[0], trig(1, 1, 'sin')),
               f.scale(amplitudes[1], trig(2, k, 'sin')),
               f.scale(amplitudes[2], trig(0, 1, 'sin'))]
    literal, literal_p = velocity_time_jets(initial, Q(1), 4)
    for n in range(4):
        for i in range(3):
            field = f.add(*({q: f.II*f.QQ_I(e.jet(a[i], n)) for q, a in level.items()}
                            for level in u[1:]))
            f.equal(field, literal[n][i], 'Independent complete NS time jets')
        p = f.add(*({q: f.QQ_I(e.jet(a, n)) for q, a in level.items()}
                    for level in pressure[1:]))
        f.equal(p, literal_p[n], 'Independent canonical pressure time jets')


def history(k, amplitudes=(1, 1, 1), degree=14):
    require(degree >= 14, 'Retain the first complete feedback correction')
    u, _, pressure = e.amplitude_fields(amplitudes, order=degree-9, radii=(1, k, 1))
    require(not pressure[2], 'The cyclic pressure starts at amplitude degree three')
    check_time_jets(u, pressure, amplitudes, k)
    g = {n: [{q: e.scale(q[i], v) for q, v in pressure[n].items() if q[i]}
             for i in range(3)] for n in range(3, degree-8)}
    first = {}
    for n in range(3, degree-8):
        first[n] = [heat(add(g[n][i], *(transport(u[a], first[n-a][i])
                                       for a in range(1, n-2)))) for i in range(3)]
    second = {}
    for n in range(6, degree-5):
        second[n] = [[heat(add(*(
            add(multiply(first[a][i], g[n-a][j]), multiply(first[a][j], g[n-a][i]))
            for a in first if n-a in g),
            *(transport(u[a], second[n-a][i][j]) for a in range(1, n-5))))
            for j in range(3)] for i in range(3)]
    third = {}
    for n in range(9, degree-2):
        third[n] = [heat(add(*(
            add(scale(2, add(*(multiply(second[a][i][j], g[n-a][j]) for j in range(3)))),
                multiply(add(*(second[a][j][j] for j in range(3))), g[n-a][i]))
            for a in second if n-a in g),
            *(transport(u[a], third[n-a][i]) for a in range(1, n-8)))) for i in range(3)]
    result = {}
    for n in range(12, degree+1):
        source = e.scale(4, e.add(*(mean_product(third[a][i], g[n-a][i])
                                  for a in third if n-a in g for i in range(3))))
        result[n] = e.heat_convolution(source, 0)
        require(e.derivative(result[n]) == source, 'The final accumulated moment keeps its full source')
        require(e.jet(result[n], 0) == 0, 'The fourth moment starts at zero once')
        require(result[n].get((0, 0), Q(0)) == e.integral_infinity(source),
                'Two evaluations of the infinite-time coefficient agree')
        if n % 2:
            require(not result[n], 'Translation symmetry removes every computed odd degree')
    return result


def signed_cascade(a, sign):
    """A finite sequence (d/dt+rate) proves a sign for every t>=0."""
    require(sign in [-1, 1] and bool(a), 'A nonzero oriented exponential polynomial')
    rates = [i for i in sorted({i for i, _ in a}, reverse=True)
             for _ in range(1+max(j for ell, j in a if ell == i))]
    field, first, strict = a, None, 0
    for n, rate in enumerate(rates):
        value = e.jet(field, 0)
        require(sign*value >= 0, ('Every cascade datum has the promised sign', n))
        if value:
            strict += 1
            if first is None:
                first = dict(order=n, derivative=str(value))
        field = e.add(e.derivative(field), e.scale(rate, field))
    require(not field, 'The finite cascade terminates identically')
    return dict(levels=len(rates), first_nonzero=first, strict_data=strict,
                maximum_rate=max(rates), orientation=sign)


def family_checks():
    rows = []
    limits = {1: Q(27539587, 384072192000),
              4: Q(97150482506203, 145010906352284544000000)}
    for k in [1, 4]:
        base = history(k)
        require(base[12].get((0, 0)) == limits[k], 'Exact full original pressure allowance')
        if k == 1:
            # Degree, independent sign symmetry, triangular vanishing and
            # cyclic symmetry determine all three amplitude coefficients.
            parts = [e.scale(Q(1, 3), base[14])]*3
        else:
            doubled_a, doubled_b = history(k, (2, 1, 1)), history(k, (1, 2, 1))
            require(doubled_a[12] == e.scale(16, base[12])
                    and doubled_b[12] == e.scale(16, base[12]),
                    'Leading joint degree is exactly (abc)^4')
            first = e.scale(Q(1, 3), e.add(e.scale(Q(1, 16), doubled_a[14]),
                                           e.scale(-1, base[14])))
            second = e.scale(Q(1, 3), e.add(e.scale(Q(1, 16), doubled_b[14]),
                                            e.scale(-1, base[14])))
            third = e.add(base[14], e.scale(-1, first), e.scale(-1, second))
            parts = [first, second, third]
            doubled_c = history(k, (1, 1, 2))
            require(doubled_c[14] == e.scale(16, e.add(first, second, e.scale(4, third))),
                    'Unused amplitude sample independently checks the proved polynomial basis')
        certificates = []
        for part in parts:
            require(all(e.jet(part, n) == 0 for n in range(10)),
                    'The whole-time correction starts at the known tenth time order')
            d = -e.jet(part, 10)/factorial(10)
            require(d > 0, 'A strictly negative first feedback for each parent amplitude')
            cert = signed_cascade(e.derivative(part), -1)
            require(cert['first_nonzero']['order'] == 9, 'Quantitative small-time margin')
            certificates.append(dict(d=str(d), cascade=cert))
        rows.append(dict(frequency_pattern=[1, k, 1], pressure_stock=str(limits[k]),
            forecast_growth=signed_cascade(e.derivative(base[12]), 1),
            joint_factor='(a*b*c)^4', correction='a^2 F_a+b^2 F_b+c^2 F_c',
            parent_corrections=certificates))
    return rows


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--next-coefficient', action='store_true',
                        help='check the complete degree-sixteen correction instead of the family certificates')
    args = parser.parse_args()
    result = dict(status='all exact checks passed',
                  certification='exact whole-time coefficient signs; actual-flow remainder analytic',
                  scope='a sufficiently small amplitude ball; arbitrary data remain open')
    if args.next_coefficient:
        higher = history(1, degree=16)
        require(all(e.jet(higher[16], n) == 0 for n in range(12)),
                'The next feedback begins at time order twelve')
        require(e.jet(higher[16], 12)/factorial(12) == Q(106168693607, 2059433164800),
                'Strictly positive next complete pressure feedback')
        require(higher[16].get((0, 0)) == Q(
            152490621712563288522860694365656656374065925339476309,
            35951541890842638215113438256286222765113462489088000000000),
            'Exact positive infinite-time next coefficient')
        result['next_coefficient'] = dict(limit=str(higher[16].get((0, 0), Q(0))),
            first_time_coefficient=str(e.jet(higher[16], 12)/factorial(12)),
            positive_derivative=signed_cascade(e.derivative(higher[16]), 1),
            actual_scope='at any fixed positive time, sufficiently small nonzero amplitudes exceed the two-term corrected forecast')
    else:
        result['families'] = family_checks()
    print(json.dumps(result, indent=2))
