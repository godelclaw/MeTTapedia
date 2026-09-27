#!/usr/bin/env python3
"""Exact first generated-tail interactions for the Kida--Pelz datum.

Fourier coefficients use u_hat(k)=i*a(k) and normalized 2*pi-periodic
volume. Every source output is retained. The time coefficients multiply
t^j, without factorials. They are coefficients of the actual unforced
equation, not a closed model of selected modes. No time-remainder bound,
infinite cascade estimate, or Lean certificate is supplied.

The default check uses only Python's standard library. --fft-check also
compares with the independent physical-space Lamb-product and Betchov
implementations, requiring NumPy and SciPy. Checks run under python -O.
"""
import argparse
from fractions import Fraction as F
import itertools
import json

if __package__:
    from .fourier_interactions import (A, B, ZERO, add, pair, pair_source,
        radius_squared, require, scale, validate)
else:
    from fourier_interactions import (A, B, ZERO, add, pair, pair_source,
        radius_squared, require, scale, validate)


def initial_field():
    """sin(x)*(cos(3y)cos(z)-cos(y)cos(3z)), and cyclic components."""
    field = {}
    for j in range(3):
        a, b = (j + 1) % 3, (j + 2) % 3
        for swap, sign in ((False, -1), (True, 1)):
            for signs in itertools.product((-1, 1), repeat=3):
                k = list(signs)
                k[b if swap else a] *= 3
                k = tuple(k)
                v = list(field.get(k, ZERO))
                v[j] += F(sign * signs[j], 8)
                field[k] = tuple(v)
    return {k: v for k, v in field.items() if any(v)}


def tail(u, cutoff):
    return {k: v for k, v in u.items() if radius_squared(k) >= cutoff**2}


def time_coefficients(order=3):
    """c[j][l] is the exact coefficient of t^j * nu^l in the velocity."""
    c = [[initial_field()]]
    for j in range(order):
        row = []
        for degree in range(j + 2):
            terms = []
            for i in range(j + 1):
                for a, u in enumerate(c[i]):
                    b = degree - a
                    if 0 <= b < len(c[j - i]):
                        terms.append(B(u, c[j - i][b]))
            if 0 < degree <= len(c[j]):
                terms.append(scale(-F(1), A(c[j][degree - 1])))
            row.append(scale(F(1, j + 1), add(*terms)))
        c.append(row)
    for row in c:
        for field in row:
            validate(field)
    return c


def cubic(u):
    return pair_source(A(u), u, u)


def cubic_variation(u, v):
    """Coefficient of s in Pi(u+s*v), with all three slots varied."""
    return (pair_source(A(v), u, u) + pair_source(A(u), u, v)
            + pair_source(A(u), v, u))


def exact_check():
    c = time_coefficients()
    u, n, e2, e3 = (row[0] for row in c)
    require(set(map(radius_squared, u)) == {11}, 'initial shell')
    require(pair(u, u) / 2 == F(3, 8), 'initial kinetic energy')
    require(pair(A(u), u) / 2 == F(33, 8), 'initial enstrophy')
    require(pair(u, n) == 0 and cubic(u) == 0, 'initial energy cancellations')
    require(set(map(radius_squared, n)) == {20, 24, 36, 40}, 'complete first source')
    require(not tail(u, 4) and not tail(c[1][1], 4), 'first empty tail')
    w2, w3 = tail(e2, 8), tail(e3, 8)
    w12 = tail(e3, 12)
    require(not tail(n, 8), 'cutoff8 has no first-order seed')
    require(all(not tail(field, 8) for field in c[2][1:]),
            'cutoff8 birth is independent of viscosity')
    require(not tail(e2, 12), 'cutoff12 has no earlier seed')
    require(all(not tail(field, 12) for field in c[3][1:]),
            'cutoff12 birth is independent of viscosity')
    require(cubic(w2) == 0, 'cutoff8 odd-sublattice cubic cancellation')
    require(all(cubic_variation(w2, tail(field, 8)) == 0 for field in c[3][1:]),
            'cutoff8 leading self-work is independent of viscosity')
    coefficients = [cubic(n), cubic_variation(w2, w3), cubic(w12)]
    expected = [F(67, 80), F(731793808705302506334191, 520336916998778880000000),
                F(-3373, 31850496)]
    require(coefficients == expected, 'signed production coefficients')
    fields = [n, w2, w12]
    h1 = [pair(A(v), v) / 2 for v in fields]
    h2 = [pair(A(v), A(v)) for v in fields]
    require(h1 == [F(231, 32), F(12149429, 1843200), F(173693, 2764800)],
            'tail-enstrophy birth coefficients')
    require(h2 == [F(1773, 4), F(288862741, 307200), F(13119731, 691200)],
            'tail-dissipation birth coefficients')
    report = {'status': 'all rational checks passed', 'volume': 'normalized (2*pi)^-3 dx',
        'euler_coefficient_mode_counts': [len(v) for v in (u, n, e2, e3)],
        'first_source_shells': {}, 'tails': [],
        'scope': 'exact Taylor coefficients; no certified interval or uniform history bound'}
    for r in sorted(set(map(radius_squared, n))):
        v = {k: a for k, a in n.items() if radius_squared(k) == r}
        report['first_source_shells'][r] = {'modes': len(v), 'norm_squared': str(pair(v, v))}
    for cutoff, birth, power, v, y, d, p in zip(
            (4, 8, 12), (1, 2, 3), (3, 7, 9), fields, h1, h2, coefficients):
        report['tails'].append({'cutoff': cutoff, 'velocity_birth_order': birth,
            'born_modes': len(v), 'enstrophy_power': 2*birth, 'enstrophy_coefficient': str(y),
            'dissipation_power': 2*birth, 'dissipation_coefficient_over_nu': str(d),
            'self_production_power': power, 'self_production_coefficient': str(p)})
    return c, report


def fft_check(c, n):
    import numpy as np
    if __package__:
        from .kida_pelz_history import KidaPelzFlow
        from .full_history import FullFlow
    else:
        from kida_pelz_history import KidaPelzFlow
        from full_history import FullFlow
    m = KidaPelzFlow(n, 0., [4., 8., 12.])
    volume = (2*np.pi)**3

    def source(u):
        return FullFlow.rhs(m, u)[0]

    def production(u):
        return float(m.self_stretching(u, [0.])[0] / volume)

    def packed(field):
        out = np.zeros_like(m.initial)
        for k, v in field.items():
            out[(slice(None),) + tuple(j % n for j in k)] = 1j*n**3*np.array(v, dtype=float)
        return out

    u0 = m.initial
    u1 = source(u0)
    u2 = (source(u0+u1)-source(u0-u1))/4
    u3 = ((source(u0+u2)-source(u0-u2))/2+source(u1))/3
    errors = [float(np.linalg.norm(u-packed(row[0])) / np.linalg.norm(u))
              for u, row in zip((u0, u1, u2, u3), c)]
    require(max(errors) < 1e-11, 'independent Fourier coefficient check')
    v1 = np.where(m.ksq >= 16, u1, 0)
    v2 = np.where(m.ksq >= 64, u2, 0)
    v3 = np.where(m.ksq >= 64, u3, 0)
    v12 = np.where(m.ksq >= 144, u3, 0)
    actual = [production(v1), (production(v2+v3)-production(v2-v3))/2-production(v3),
              production(v12)]
    expected = [cubic(c[1][0]), cubic_variation(tail(c[2][0], 8), tail(c[3][0], 8)),
                cubic(tail(c[3][0], 12))]
    rate_errors = [float(abs(a-float(b)) / abs(float(b))) for a, b in zip(actual, expected)]
    require(max(rate_errors) < 1e-9, 'independent Betchov coefficient check')
    return {'n': n, 'field_relative_errors': errors, 'production_relative_errors': rate_errors}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fft-check', action='store_true')
    args = parser.parse_args()
    c, report = exact_check()
    if args.fft_check:
        report['independent_fft_checks'] = [fft_check(c, n) for n in (48, 64)]
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
