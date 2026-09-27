#!/usr/bin/env python3
"""Exact thin-pancake asymptotic for the first generated caloric renewal.

Write delta=1/m and retain series modulo delta^11. Frequencies are affine
labels a+b*delta, so distinct modes are not merged when their leading
vectors coincide. All denominators used below have nonzero constant term.
The result is finite rational algebra, not a Lean or time-interval certificate.
"""
from fractions import Fraction as F
import json

from fourier_interactions import require


ORDER = 10
ZERO = (F(0),)*(ORDER+1)
VECTOR_ZERO = (ZERO,)*3


def constant(x):
    return (F(x),)+ZERO[1:]


def add(a, b):
    return tuple(x+y for x, y in zip(a, b))


def negative(a):
    return tuple(-x for x in a)


def multiply(a, b):
    return tuple(sum((a[j]*b[n-j] for j in range(n+1)), F(0))
                 for n in range(ORDER+1))


def divide(a, b):
    require(bool(b[0]), 'analytic series denominator has a nonzero constant term')
    c = []
    for n in range(ORDER+1):
        c.append((a[n]-sum((b[j]*c[n-j] for j in range(1, n+1)), F(0)))/b[0])
    result = tuple(c)
    require(multiply(result, b) == a, 'division identity modulo delta^11')
    return result


def vector_add(a, b):
    return tuple(add(x, y) for x, y in zip(a, b))


def vector_scale(c, a):
    return tuple(multiply(c, x) for x in a)


def dot(a, b):
    out = ZERO
    for x, y in zip(a, b):
        out = add(out, multiply(x, y))
    return out


def cross(a, b):
    return (add(multiply(a[1], b[2]), negative(multiply(a[2], b[1]))),
            add(multiply(a[2], b[0]), negative(multiply(a[0], b[2]))),
            add(multiply(a[0], b[1]), negative(multiply(a[1], b[0]))))


def mode_add(p, q):
    return tuple((a+c, b+d) for (a, b), (c, d) in zip(p, q))


def mode_negative(p):
    return tuple((-a, -b) for a, b in p)


def wave(k):
    return tuple((F(a), F(b))+ZERO[2:] for a, b in k)


def radius_squared(k):
    return dot(wave(k), wave(k))


def high(k):
    # The cutoff squared is 3/2. Integer leading squared radii never equal it.
    # This therefore selects the actual output for every sufficiently small delta.
    return 2*sum(a*a for a, _ in k) >= 3


def trim(field):
    return {k: v for k, v in field.items() if any(any(a) for a in v)}


def field_add(a, b):
    out = dict(a)
    for k, v in b.items():
        out[k] = vector_add(out.get(k, VECTOR_ZERO), v)
    return trim(out)


def validate(field):
    for k, v in field.items():
        require(dot(wave(k), v) == ZERO, 'transversality in the series ring')
        require(field.get(mode_negative(k), VECTOR_ZERO) == tuple(negative(a) for a in v),
                'Fourier reality in the series ring')


def high_nonlinearity(u, v):
    """Form the complete convection before selecting and projecting its output."""
    raw = {}
    for p, a in u.items():
        for q, b in v.items():
            k = mode_add(p, q)
            raw[k] = vector_add(raw.get(k, VECTOR_ZERO), vector_scale(dot(a, wave(q)), b))
    out = {}
    for k, a in raw.items():
        if high(k):
            parallel = divide(dot(wave(k), a), radius_squared(k))
            out[k] = vector_add(a, vector_scale(negative(parallel), wave(k)))
    return trim(out)


def high_heat_blocks(u, v):
    """Ordered inverse-curl stretching, indexed by the complete parent heat rate."""
    out = {}
    for p, a in u.items():
        for q, b in v.items():
            k = mode_add(p, q)
            if not high(k):
                continue
            coefficient = dot(cross(wave(p), a), wave(q))
            value = vector_scale(divide(coefficient, radius_squared(k)), cross(wave(k), b))
            key = (k, add(radius_squared(p), radius_squared(q)))
            out[key] = vector_add(out.get(key, VECTOR_ZERO), value)
    return trim(out)


def exact_asymptotic():
    # Scaled parents: (1,3*delta,delta), (3*delta,1,delta), (1,delta,3*delta).
    parents = (((1, 0), (0, 3), (0, 1)),
               ((0, 3), (1, 0), (0, 1)),
               ((1, 0), (0, 1), (0, 3)))
    u = {}
    for k, weight in zip(parents, (2, 1, 1)):
        kx, ky, _ = wave(k)
        a = (multiply(constant(-weight), ky), multiply(constant(weight), kx), ZERO)
        u[k] = a
        u[mode_negative(k)] = tuple(negative(x) for x in a)
    validate(u)
    require(not any(high(k) for k in u), 'initial high tail is empty')
    v = high_nonlinearity(u, u)
    direction = high_nonlinearity(v, v)
    validate(v)
    validate(direction)
    require((len(v), len(direction)) == (8, 18), 'full high source supports')
    source = high_heat_blocks(v, v)
    tangent = field_add(high_heat_blocks(v, direction), high_heat_blocks(direction, v))

    # Independent source identities remain valid after projection: the receiver is high.
    collapsed = {}
    for (k, _), a in source.items():
        collapsed[k] = vector_add(collapsed.get(k, VECTOR_ZERO), a)
    kinetic, enstrophy_n, enstrophy_m = ZERO, ZERO, ZERO
    for k, a in v.items():
        n = direction.get(k, VECTOR_ZERO)
        kinetic = add(kinetic, dot(a, n))
        enstrophy_n = add(enstrophy_n, multiply(radius_squared(k), dot(a, n)))
        enstrophy_m = add(enstrophy_m,
                         multiply(radius_squared(k), dot(a, collapsed.get(k, VECTOR_ZERO))))
    require(kinetic == ZERO, 'actual kinetic transport cancellation')
    require(enstrophy_n == enstrophy_m, 'actual stretching/source pairing')

    renewal, terms = ZERO, 0
    for (k, r), a in source.items():
        for (l, s), b in tangent.items():
            if k == l:
                renewal = add(renewal, multiply(constant(2), divide(dot(a, b), add(r, s))))
                terms += 1
    expected = (F(0),)*9+(F(52224, 25), -F(7422976, 375))
    require(renewal == expected, 'complete asymptotic through order ten')
    require(renewal[9]/12**5 == F(17, 2025), 'unit squared-L2 normalization')
    return {'series_order': ORDER, 'scaled_frequency_coefficients': [str(x) for x in renewal],
            'raw_leading_coefficient': str(renewal[9]),
            'unit_energy_leading_coefficient': str(renewal[9]/12**5),
            'paired_heat_blocks': terms}


def finite_check(m):
    from fourier_interactions import (A, B, add as field_sum, pair,
        radius_squared as square, scale, validate as validate_field)
    from caloric_force import parent_derivative
    u = {}
    for k, weight in zip(((m, 3, 1), (3, m, 1), (m, 1, 3)), (2, 1, 1)):
        a = (-F(weight*k[1], m), F(weight*k[0], m), F(0))
        u[k] = a
        u[tuple(-x for x in k)] = tuple(-x for x in a)
    validate_field(u)
    cutoff = F(3*m*m, 2)

    def select(field):
        return {k: a for k, a in field.items() if square(k) >= cutoff}

    require(set(map(square, u)) == {m*m+10} and not select(u), 'thin monoshell parents')
    energy = pair(u, u)
    require(energy == 12+F(92, m*m), 'bounded parent squared velocity norm')
    v = select(B(u, u))
    require(v == select(field_sum(B(u, u), scale(-F(1), A(u)))),
            'actual first high derivative has no viscous contribution')
    direction = select(B(v, v))
    coefficient = parent_derivative(v, direction, F(1), cutoff)
    require(coefficient > 0, 'positive fully high coefficient at this finite parameter')
    return {'m': m, 'initial_squared_velocity_norm': str(energy),
            'generated_high_modes': len(v), 'coefficient_at_nu_one': str(coefficient),
            'm_cubed_times_coefficient': float(m**3*coefficient),
            'm_cubed_times_unit_energy_coefficient': float(m**3*coefficient/energy**5)}


def main():
    result = exact_asymptotic()
    result['finite_checks'] = [finite_check(m) for m in (16, 64, 256, 1000000)]
    result['scope'] = ('Exact algebraic first-generation asymptotic; '
                       'no uniform physical-time window or absorption obstruction.')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
