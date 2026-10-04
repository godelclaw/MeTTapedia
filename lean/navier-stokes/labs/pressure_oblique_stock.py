#!/usr/bin/env python3
"""An adverse oblique return consumes additional original pressure stock.

Complete viscous amplitude histories have exact increasing coefficients
through degree fourteen. Brownian four-time integration independently
checks the original cubic forecast's full stock. The analytic uniform
remainder in README.md transfers the result to actual small-data flows.
No arbitrary-amplitude or Lean-certified payment is claimed.
"""

import itertools
import json
from fractions import Fraction as Q
from math import factorial

import paired_stretching_history as e
import pressure_history_source as f
from pressure_impulse_payment import history_from_fields, signed_cascade, require
from pressure_oblique_return import datum
from cyclic_pressure_history import velocity_time_jets


def physical_fields():
    initial = datum(4)
    modes = set().union(*initial)
    require(all(not a.x for row in initial for a in row.values()), 'Real odd initial velocity')
    heat = {q: tuple({(sum(x*x for x in q), 0): Q(str(row[q].y))} if q in row else {}
                     for row in initial) for q in modes}
    velocity, _, pressure = e.evolve_amplitudes(heat, 5)
    literal, literal_p = velocity_time_jets(initial, Q(1), 4)
    for n in range(4):
        for i in range(3):
            actual = f.add(*({q: f.II*f.QQ_I(e.jet(a[i], n)) for q, a in level.items()}
                             for level in velocity[1:]))
            f.equal(actual, literal[n][i], 'Independent complete physical velocity jets')
        actual = f.add(*({q: f.QQ_I(e.jet(a, n)) for q, a in level.items()}
                         for level in pressure[1:]))
        f.equal(actual, literal_p[n], 'Independent canonical pressure jets')
    require(not pressure[2], 'The whole heat-parent pressure vanishes')
    for q, value in pressure[3].items():
        rate = sum(x*x for x in q)
        require(rate in (11, 27), 'The complete original cubic pressure support')
        # K_r(t)=(exp(-r*t)-exp(-19*t))/(19-r)>0 for t>0.
        expected = e.scale(Q(-1, 4*rate), {
            (19, 1): Q(2), (rate, 0): Q(1, 19-rate), (19, 0): Q(-1, 19-rate)})
        require(value == expected, 'Explicit negative cubic-pressure Fourier coefficient for all times')
    require(len(pressure[3]) == 8, 'All original pressure modes are retained')
    return velocity, pressure


def dot(a, b):
    return sum(x*y for x, y in zip(a, b))


def brownian_stock(pressure):
    """Independent ordered-time Brownian expectation; no moment PDE fields."""
    amplitudes = {q: e.scale(-1, a) for q, a in pressure.items()}
    total = Q(0)
    contractions = []
    for a, b, c in itertools.product(pressure, repeat=3):
        d = tuple(-x-y-z for x, y, z in zip(a, b, c))
        if d not in pressure:
            continue
        contraction = dot(a, b)*dot(c, d)+dot(a, c)*dot(b, d)+dot(a, d)*dot(b, c)
        require(contraction > 0, 'Every zero-sum pressure quartet has a positive contraction')
        contractions.append(contraction)
        ab = tuple(x+y for x, y in zip(a, b))
        integral = e.heat_convolution(amplitudes[a], dot(a, a))
        integral = e.heat_convolution(e.multiply(amplitudes[b], integral), dot(ab, ab))
        integral = e.heat_convolution(e.multiply(amplitudes[c], integral), dot(d, d))
        total += 8*contraction*e.integral_infinity(e.multiply(amplitudes[d], integral))
    require(len(contractions) == 216 and min(contractions) == 283,
            'Exhaustive exact support and contraction check')
    return total, dict(quartets=len(contractions), minimum_contraction=min(contractions))


def check():
    velocity, pressure = physical_fields()
    coefficients = history_from_fields(velocity, pressure)
    A, B = coefficients[12], coefficients[14]
    require(not coefficients[13], 'Spatial translation removes the odd amplitude coefficient')
    delta = Q(388474522689518625902918581, 128553647224867666773083481600)
    require(all(e.jet(A, n) == 0 for n in range(8))
            and e.jet(A, 8)/factorial(8) == Q(708361715, 49182515712),
            'Exact forecast origin matches the physical moment jets')
    require(all(e.jet(B, n) == 0 for n in range(10))
            and e.jet(B, 10)/factorial(10) == delta,
            'Full-time correction starts at the established adverse return')
    certificates = [signed_cascade(e.derivative(q), 1) for q in (A, B)]
    require([a['first_nonzero']['order'] for a in certificates] == [7, 9],
            'The sign cascades retain the sharp small-time orders')
    alpha, beta = A[(0, 0)], B[(0, 0)]
    require(alpha > 0 and beta > 0, 'Both limiting stocks are strictly positive')
    independent, quartets = brownian_stock(pressure[3])
    require(independent == alpha, 'Brownian ordered-time integration agrees with conditional moment PDE')
    # All numbers in these displayed brackets are terminating rationals.
    require(Q(4604, 10**15) < alpha < Q(4606, 10**15), 'Readable exact bracket for the original stock')
    require(Q(6608, 10**16) < beta < Q(6610, 10**16), 'Readable exact bracket for the additional stock')
    margin = delta / 3**certificates[1]['maximum_rate']
    require(margin > 0, 'The exact cascade yields a positive uniform time margin')
    return dict(status='all exact checks passed',
                original_stock=str(alpha), additional_stock=str(beta),
                stock_ratio=str(beta/alpha), derivative_certificates=certificates,
                independent_brownian=quartets, uniform_correction_margin=str(margin),
                fields={str(n): e.encode(q) for n, q in coefficients.items()},
                actual_scope='For sufficiently small nonzero amplitudes, an analytic all-time sandwich and stock correction',
                limitation='The amplitude threshold uses a uniform analytic remainder; arbitrary-data payment stays open',
                certification='Exact coefficients and sign certificates; physical transfer is analytic, not Lean-certified')


if __name__ == '__main__':
    print(json.dumps(check(), indent=2), flush=True)
