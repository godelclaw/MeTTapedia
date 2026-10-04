#!/usr/bin/env python3
"""Complete cyclic-parent cancellation in generated fourth-moment work.

All Fourier outputs and viscosity terms are retained for arbitrary three
parent strengths. Two coefficient calculations agree exactly. README.md
supplies the analytic actual-flow remainder and the whole heat-tail bound;
these algebraic checks are not a Lean certificate or a PDE integrator.
"""

import hashlib
import itertools
import json
from fractions import Fraction as Q
from math import comb
from pathlib import Path

import sympy as s
import pressure_history_source as f
from heat_remainder_pressure import plus, times, require
from cyclic_pressure_history import velocity_time_jets
from pressure_gradient_stock import weighted_datum
from generated_fourth_moment import pressure, mixed_pressure

RING = f.QQ_I.poly_ring('q', 'a', 'b', 'c', 'nu')
QH, AA, BB, CC, NU = RING.gens
q, a, b, c, nu = s.symbols('q a b c nu')


def zero(expression, label):
    require(s.expand(expression) == 0, label)


def heat(vector):
    return [{k: RING.convert(value)*QH**sum(x*x for x in k)
             for k, value in row.items()} for row in vector]


def average(field):
    return s.expand(RING.to_sympy(RING.convert(field.get(f.ORIGIN, f.ZERO))))


def variation(v, h):
    magnitude, pairing = f.dot(v, v), f.dot(v, h)
    receiver = [f.mul(magnitude, x) for x in v]
    tangent = [f.add(f.mul(magnitude, h[i]), f.scale(2, f.mul(pairing, v[i])))
               for i in range(3)]
    return -average(f.add(f.dot(tangent, f.grad(pressure(v))),
                         f.dot(receiver, f.grad(mixed_pressure(v, h)))))


def second_variation(v, h):
    magnitude, pairing, hh = f.dot(v, v), f.dot(v, h), f.dot(h, h)
    receiver = [f.mul(magnitude, x) for x in v]
    tangent = [f.add(f.mul(magnitude, h[i]), f.scale(2, f.mul(pairing, v[i])))
               for i in range(3)]
    second = [f.add(f.scale(2, f.mul(hh, v[i])), f.scale(4, f.mul(pairing, h[i])))
              for i in range(3)]
    return -average(f.add(f.dot(second, f.grad(pressure(v))),
                         f.scale(2, f.dot(tangent, f.grad(mixed_pressure(v, h)))),
                         f.scale(2, f.dot(receiver, f.grad(pressure(h))))))


def complete_jets(initial, viscosity, order):
    """Polynomial-parameter extension, checked against the rational API below."""
    jets, pressures = [initial], []
    for n in range(order):
        tensor = [[f.add(*(f.scale(comb(n, r), f.mul(jets[r][i], jets[n-r][j]))
                           for r in range(n+1))) for j in range(3)] for i in range(3)]
        p = f.tensor_pressure(tensor)
        gradient_source = f.add(*(f.scale(comb(n, r), f.trace(f.matmul(
            f.jac(jets[r]), f.jac(jets[n-r])))) for r in range(n+1)))
        f.equal(p, f.green(gradient_source), 'Independent differentiated pressure Poisson source')
        pressures.append(p)
        jets.append([f.add(f.scale(viscosity, f.lap(jets[n][i])),
                           f.scale(-1, f.diff(p, i)),
                           f.scale(-1, f.add(*(f.scale(comb(n, r),
                               f.adv(jets[r], jets[n-r][i])) for r in range(n+1)))))
                     for i in range(3)])
        f.equal(f.trace(f.jac(jets[-1])), {}, 'Complete time derivative is solenoidal')
        require(all(not row.get(f.ORIGIN, f.ZERO) for row in jets[-1]),
                'Every complete velocity time derivative has zero mean')
    return jets, pressures


def ordered_coefficients(slots):
    """Expand the ordered five-linear form, independently of its derivatives."""
    pressures = {(i, j): f.tensor_pressure(f.tensor(slots[i], slots[j]))
                 for i in range(3) for j in range(3) if i+j <= 2}
    pairs = {(i, j): f.dot(slots[i], slots[j])
             for i in range(3) for j in range(3) if i+j <= 2}
    advections = {(i, j, k): f.adv(slots[i], pressures[j, k])
                  for i, j, k in itertools.product(range(3), repeat=3) if i+j+k <= 2}
    coefficients = [0, 0, 0]
    counts = [0, 0, 0]
    for indices in itertools.product(range(3), repeat=5):
        degree = sum(indices)
        if degree > 2:
            continue
        i, j, k, ell, m = indices
        coefficients[degree] -= average(f.mul(pairs[i, j], advections[k, ell, m]))
        counts[degree] += 1
    require(counts == [1, 5, 15], 'Every ordered coefficient through physical degree seven is retained')
    return [s.expand(value) for value in coefficients]


def specialize(field, substitutions):
    return f.clean({k: f.QQ_I.from_sympy(RING.to_sympy(RING.convert(value)).subs(substitutions))
                    for k, value in field.items()})


def checks():
    initial = weighted_datum(0, (AA, BB, CC))
    jets, pressures = complete_jets(initial, NU, 3)
    heat_jets = [initial]
    for _ in range(3):
        heat_jets.append([f.scale(NU, f.lap(row)) for row in heat_jets[-1]])
    remainder = [plus(jets[i], times(-1, heat_jets[i])) for i in range(4)]
    require(not any(remainder[0]), 'The generated motion starts at zero, with no reset')
    A, B, C = map(heat, remainder[1:])
    coefficients = [-average(f.mul(f.dot(A, A), f.adv(A, pressure(A)))),
                    s.expand(variation(A, B)/2),
                    s.expand(variation(A, C)/6+second_variation(A, B)/8)]
    ordered = ordered_coefficients([A, times(Q(1, 2), B), times(Q(1, 6), C)])
    for degree, (first, second) in enumerate(zip(coefficients, ordered), 5):
        zero(first-second, ('Derivative and ordered five-linear calculations agree', degree))
    zero(coefficients[0], 'No fifth-order work at any heat age')
    zero(coefficients[1], 'No sixth-order work at any heat age')

    T = a*a*b*b*c*c
    S1 = a**4*b*b+b**4*c*c+c**4*a*a
    S2 = a**4*c*c+a*a*b**4+b*b*c**4
    p1 = 3156*q**8+2200*q**6-6657*q**4+6930
    p2 = 1980*q**10-4095*q**8+5500*q**6-4620*q**4+6930
    p0 = -103950*q**6+54054*q**4+41580
    P = 1980*q**10-939*q**8-26950*q**6+6741*q**4+27720
    wanted = -T*q**8*(p1*S1+p2*S2+p0*T)/5322240
    zero(coefficients[2]-wanted, 'The complete seventh coefficient retains arbitrary parents')
    zero(s.diff(coefficients[2], nu), 'All seventh-coefficient viscosity dependence cancels')
    zero(3*p1+3*p2+p0-3*P, 'Joint cyclic AM-GM decomposition')
    zero(p1-(273+3156*q**8+2200*q**6+6657*(1-q**4)), 'First positive heat polynomial')
    zero(p2-(2310+1980*q**10+1405*q**6+4095*q**6*(1-q**2)+4620*(1-q**4)),
         'Second positive heat polynomial')
    zero(P-(6572+1980*q**10+939*q**6*(1-q**2)+27889*q**4*(1-q**2)+21148*(1-q**4)),
         'Uniform strictly positive joint heat polynomial')
    zero((a**4*b*b)*(b**4*c*c)*(c**4*a*a)-T**3, 'First AM-GM product')
    zero((a**4*c*c)*(a*a*b**4)*(b*b*c**4)-T**3, 'Second AM-GM product')
    margin = s.Rational(3*6572, 5322240)*T*T
    zero(margin-s.Rational(1643, 443520)*(a*b*c)**4, 'Uniform negative work margin')

    self_source = velocity_time_jets(remainder[1], 0, 1)[0][1]
    self7 = s.expand(variation(A, heat(self_source))/3)
    zero(self7+T*q**14*(S1+S2-27*T)/1728, 'Retained self contribution to the third time derivative')
    equal_parents = {a: 1, b: 1, c: 1}
    zero(self7.subs(equal_parents)-s.Rational(7, 576)*q**14, 'Positive isolated self contribution')
    zero(wanted.subs(equal_parents)+q**8*P/1774080, 'Negative complete equal-parent response')
    require(P.subs(q, 1) == 8552, 'Exact physical-age-zero heat coefficient')

    # Specialize every retained mode, not only the final spatial integral.
    cases = []
    for weights, viscosity in (((Q(1), Q(1), Q(1)), Q(1)),
                               ((Q(2), Q(3), Q(1)), Q(2, 7)),
                               ((Q(-1, 4), Q(1), Q(1)), Q(5, 3))):
        substitutions = dict(zip((a, b, c, nu), (*weights, viscosity)))
        literal, literal_p = velocity_time_jets(weighted_datum(0, weights), viscosity, 3)
        for n in range(4):
            for i in range(3):
                f.equal(specialize(jets[n][i], substitutions), literal[n][i],
                        'Independent rational API agrees on every full NS time jet')
        for n in range(3):
            f.equal(specialize(pressures[n], substitutions), literal_p[n],
                    'Independent rational API agrees on every pressure derivative')
        cases.append(dict(weights=list(map(str, weights)), viscosity=str(viscosity),
                          coefficient7_at_heat_zero=str(wanted.subs(substitutions).subs(q, 1))))

    # Exact integration of the positive envelope, including its infinite tail.
    z, C8, rho, t = s.symbols('z C8 rho t', positive=True)
    integral = s.integrate((C8*t**8*q**5-rho*t**7*q**8)/q, (q, 0, z))
    zero(integral.subs(rho, C8*t/z**3)-3*C8*t**8*z**5/40,
         'The complete positive heat tail is integrated at its exact crossover')
    bound = s.Rational(3, 40)*C8**s.Rational(8, 3)*rho**s.Rational(-5, 3)*t**s.Rational(29, 3)
    require(s.simplify((3*C8*t**8*z**5/40).subs(z, (C8*t/rho)**s.Rational(1, 3))-bound) == 0,
            'The whole heat tail has order twenty-nine thirds')

    sources = ['joint_heat_cancellation.py', 'pressure_history_source.py',
               'heat_remainder_pressure.py', 'cyclic_pressure_history.py',
               'pressure_gradient_stock.py', 'generated_fourth_moment.py']
    root = Path(__file__).resolve().parent
    return dict(datum='(a sin y,b sin z,c sin x), real a,b,c with abc nonzero',
                coefficients={str(i): str(s.factor(value)) for i, value in enumerate(coefficients, 5)},
                self_coefficient7=str(s.factor(self7)),
                parent_coefficient7=str(s.factor(wanted-self7)),
                sign_certificate=dict(p1_lower=273, p2_lower=2310, P_lower=6572,
                                      negative_margin=str(margin)),
                rational_specializations=cases,
                velocity_jet_mode_counts=[len(set().union(*v)) for v in jets],
                positive_envelope_integral=str(bound),
                scope='Exact full Fourier identities and polynomial sign certificates; actual local interval and whole-tail remainder analytic in README.md, not Lean-certified',
                source_sha256={name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in sources})


if __name__ == '__main__':
    print(json.dumps(checks(), indent=2))
