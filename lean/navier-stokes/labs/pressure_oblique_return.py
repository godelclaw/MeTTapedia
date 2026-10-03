#!/usr/bin/env python3
"""Oblique cyclic parents reverse the matched pressure-history correction.

The original cubic pressure forecast uses the complete heat-Duhamel
generation, not the orthogonal-wave resonance formula. All physical
Fourier outputs and viscosity-polynomial moment terms are retained.
Actual local intervals and global small-data payment are analytic in
README.md. These exact checks are not Lean certificates.
"""

import json
from fractions import Fraction as Q
from math import comb

import sympy as s
import pressure_history_source as f
from cyclic_pressure_history import velocity_time_jets
from cyclic_entropy_depletion import material_jets
from pressure_impulse_return import (NU, RING, impulse_fourth_coefficients,
                                    material_fourth_coefficients, viscosity_jets)


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def wave(q, cosine=False):
    return {q: f.QQ_I(1)/2 if cosine else -f.II/2,
            tuple(-x for x in q): f.QQ_I(1)/2 if cosine else f.II/2}


def datum(shear, frequency=1):
    return [f.add(wave((0, 1, 0)), f.scale(-shear, wave((0, 0, frequency)))),
            wave((0, 0, frequency)), wave((1, shear, 0))]


def cubic_forecast_jets(initial):
    """Derive the first heat-generated pressure independently of full NS jets."""
    linear = [initial]
    for _ in range(3):
        linear.append([f.scale(NU, f.lap(a)) for a in linear[-1]])
    quadratic = [[{}, {}, {}]]
    for n in range(3):
        # For these separated cyclic fields the quadratic heat pressure
        # vanishes identically, so the source is already solenoidal.
        tensor = [[f.add(*(f.scale(comb(n, j), f.mul(linear[j][i], linear[n-j][ell]))
                          for j in range(n+1))) for ell in range(3)] for i in range(3)]
        f.equal(f.tensor_pressure(tensor), {}, 'Complete quadratic heat-pressure jet vanishes')
        source = [f.add(*(f.scale(-comb(n, j), f.adv(linear[j], linear[n-j][i]))
                          for j in range(n+1))) for i in range(3)]
        quadratic.append([f.add(f.scale(NU, f.lap(quadratic[n][i])), source[i])
                          for i in range(3)])
        f.equal(f.trace(f.jac(quadratic[-1])), {}, 'Generated heat-Duhamel field is solenoidal')
    forecast = []
    for n in range(4):
        tensor = [[f.add(*(f.scale(comb(n, j), f.add(
            f.mul(linear[j][i], quadratic[n-j][ell]),
            f.mul(quadratic[j][i], linear[n-j][ell])))
            for j in range(n+1))) for ell in range(3)] for i in range(3)]
        forecast.append(f.tensor_pressure(tensor))
    return forecast


def zero_viscosity(field):
    return f.clean({q: RING.convert(a).get((0,), f.ZERO) for q, a in field.items()})


def signed_parts(velocity, gradient):
    v = [[zero_viscosity(a) for a in row] for row in velocity]
    g = [[zero_viscosity(a) for a in row] for row in gradient]
    jets = [material_jets([row[i] for row in g], v) for i in range(3)]
    A = [f.scale(Q(1, 2), row[1]) for row in jets]
    B = [f.scale(Q(1, 6), row[2]) for row in jets]
    C = [f.scale(Q(1, 24), row[3]) for row in jets]
    aa, ab = f.dot(A, A), f.dot(A, B)
    terms = [f.scale(4, f.mul(aa, f.dot(A, C))),
             f.scale(2, f.mul(aa, f.dot(B, B))), f.scale(4, f.mul(ab, ab))]
    return [q.get(f.ORIGIN, f.ZERO) for q in terms]


def check():
    initial = datum(4)
    f.equal(f.trace(f.jac(initial)), {}, 'Physical incompressible initial datum')
    velocity, pressure = viscosity_jets(initial, 4)
    require(not pressure[0], 'Complete initial pressure is zero')
    p1 = f.add(f.scale(Q(-1, 9), f.mul(wave((1, 5, 0), True), wave((0, 0, 1), True))),
               f.scale(Q(-3, 11), f.mul(wave((1, 3, 0), True), wave((0, 0, 1), True))))
    f.equal(pressure[1], p1, 'Explicit first physical pressure derivative')
    forecast = cubic_forecast_jets(initial)
    for n in range(1, 4):
        cubic = f.clean({q: RING.convert(a).get((n-1,), f.ZERO)*NU**(n-1)
                         for q, a in pressure[n].items()})
        f.equal(forecast[n], cubic, 'Independent forecast equals the entire cubic-amplitude degree')
    gradient = [f.grad(p) for p in pressure]
    actual = impulse_fourth_coefficients(velocity, gradient, NU)
    reference = impulse_fourth_coefficients([[{}, {}, {}] for _ in range(5)],
                                            [f.grad(p) for p in forecast], NU)
    difference = [s.expand(RING.to_sympy(a-b)) for a, b in zip(actual, reference)]
    delta = Q(388474522689518625902918581, 128553647224867666773083481600)
    require(difference == [0, 0, s.Rational(delta.numerator, delta.denominator)],
            'Exact positive first difference at every viscosity')
    parts = signed_parts(velocity, gradient)
    require(all(not a.y for a in parts) and parts[0].x < 0
            and parts[1].x > 0 and parts[2].x > 0,
            'The signed contribution remains favorable but both other costs are positive')
    require(sum(parts, f.ZERO).x == delta, 'Complete material-path decomposition matches moment PDE')
    ratio = (parts[1]+parts[2])/(-parts[0])
    require(ratio.x > 1 and not ratio.y, 'Both positive terms exceed the signed payment')

    # A scaled copy has the same adverse local comparison and an explicit
    # global diffusion payment. Constants refer to normalized torus volume.
    energy = f.dot(initial, initial).get(f.ORIGIN, f.ZERO)
    gradient_square = f.add(*(f.dot(row, row) for row in f.jac(initial))).get(f.ORIGIN, f.ZERO)
    require(energy == f.QQ_I(Q(19, 2)) and gradient_square == f.QQ_I(Q(35, 2)),
            'Exact initial kinetic and gradient resources')
    theta_upper = Q(27*104**2*35**2, 64*128**4)
    require(theta_upper < Q(1, 40), 'pi<4 and lambda<=nu/128 imply a global small-gradient payment')
    radius_coefficient = Q(120)*Q(40, 39)*Q(35, 2)
    require(radius_coefficient == Q(28000, 13), 'Global pressure radius from the original gradient reserve')

    nearby = []
    for shear in (1, 2, 4, 8):
        v, p = velocity_time_jets(datum(shear), Q(0), 4)
        coeff = material_fourth_coefficients(v, [f.grad(a) for a in p])
        require(not p[0] and not coeff[1], 'Each sheared fixture has the same zero-pressure/parity structure')
        require((coeff[2].x > 0) == (shear == 4), 'The exact tested sign depends on geometry')
        nearby.append(dict(shear=shear, time_coefficients=list(map(str, coeff))))
    return dict(actual=list(map(str, actual)), forecast=list(map(str, reference)),
                difference=list(map(str, difference)), signed_parts=list(map(str, parts)),
                positive_cost_to_payment=str(ratio), nearby=nearby,
                small_data=dict(amplitude_condition='0<lambda<=nu/128', theta_upper=str(theta_upper),
                    pressure_radius='(28000/13)*lambda^2/nu'),
                scope='Actual local comparison failure for every positive viscosity; scaled copies are globally regular',
                limitation='Does not refute the larger all-time forecast stock or an arbitrary full-datum allowance',
                certification='Exact algebra and analytic physical transfer; not Lean-certified')


if __name__ == '__main__':
    print(json.dumps(check(), indent=2), flush=True)
