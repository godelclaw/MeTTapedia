#!/usr/bin/env python3
"""Whole-fluid pressure renewal exceeds a two-coefficient joint allowance.

All generated Fourier outputs are retained. Exact interpolation is justified
by the even polynomial degree bounds proved in README.md. A separate
positive-viscosity, amplitude-polynomial moment recurrence checks the balanced
case. Actual solution intervals and label identification remain analytic.
"""

import json
from fractions import Fraction as Q
from math import comb, factorial

import sympy as s
import pressure_history_source as f
from cyclic_pressure_history import velocity_time_jets
from cyclic_entropy_depletion import material_jets
from pressure_parent_bellman import trig
from pressure_impulse_return import product_jet
from labelled_pressure_return import complete_three_dimensional_jets


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def seed(delta):
    return [f.add(trig(1, 1, 'sin'), f.scale(delta, trig(2, 1, 'sin'))),
            trig(0, 1, 'sin'), f.scale(delta, trig(0, 1, 'sin'))]


def material_coefficients(delta):
    velocity, pressure = velocity_time_jets(seed(delta), Q(0), 5)
    gradient = [f.grad(p) for p in pressure]
    path = [material_jets([g[i] for g in gradient], velocity) for i in range(3)]
    impulse = [[{}]+[f.scale(Q(1, factorial(n)), path[i][n-1])
                     for n in range(1, 6)] for i in range(3)]
    squares = {n: f.add(*(f.mul(impulse[i][r], impulse[i][n-r])
                          for i in range(3) for r in range(1, 6)
                          if 1 <= n-r <= 5)) for n in range(2, 7)}
    answer = {}
    for n in (4, 5, 6, 7, 8):
        value = f.add(*(f.mul(squares[r], squares[n-r])
                        for r in range(2, 7) if 2 <= n-r <= 6)).get(f.ORIGIN, f.ZERO)
        require(not value.y, 'Real complete material pressure observation')
        answer[n] = Q(str(value.x))
    require(answer[5] == answer[7] == 0, 'Odd material coefficients vanish')
    return [answer[n] for n in (4, 6, 8)]


def family():
    samples = [Q(0), Q(1, 4), Q(1, 2), Q(1), Q(2), Q(4), Q(8)]
    rows = [(delta, material_coefficients(delta)) for delta in samples]
    x = s.symbols('x')
    expected = [
        (5*x**4+14*x**2+5)/16,
        -(x+1)*(90*x**4+105*x**3+323*x**2+105*x+90)/1728,
        (94022775*x**6+311313856*x**5+2842006625*x**4+1021570593*x**3
         +2842006625*x**2+311313856*x+94022775)/14370048000]
    for column, degree in enumerate((4, 5, 6)):
        interpolant = s.interpolate([(s.Rational(d)**2, s.Rational(v[column]))
                                     for d, v in rows[:degree+1]], x)
        require(s.expand(interpolant-expected[column]) == 0,
                'Exact interpolation within the proved even degree bound')
        for delta, values in rows:
            require(expected[column].subs(x, s.Rational(delta)**2) == values[column],
                    'Every computed family point agrees, including unused lower-degree points')

    A, B, D = expected
    numerator = s.factor(A*D-B*B)
    t = s.symbols('t')
    lo, hi = s.Rational(9, 16), s.Rational(16, 9)
    polynomial = s.Poly(numerator.subs(x, lo+(hi-lo)*t), t)
    n = polynomial.degree()
    bernstein = [sum(polynomial.nth(k)*s.binomial(j, k)/s.binomial(n, k)
                     for k in range(j+1)) for j in range(n+1)]
    reconstruction = sum(bernstein[j]*s.binomial(n, j)*t**j*(1-t)**(n-j)
                         for j in range(n+1))
    require(s.expand(reconstruction-polynomial.as_expr()) == 0,
            'Exact Bernstein reconstruction on the entire ratio interval')
    require(all(v > 0 for v in bernstein), 'Strictly positive joint gap across the interval')
    minimum = min(bernstein)
    maximum_A = A.subs(x, hi)
    require(all(v >= 0 for v in s.Poly(s.diff(A, x), x).all_coeffs()),
            'A increases for nonnegative squared ratios')
    require(all(v > 0 for v in s.Poly(-B, x).all_coeffs()),
            'The complete first return is favorable for every nonnegative ratio')
    lower = s.factor(minimum/maximum_A)
    require(lower > 0, 'Uniform positive bound for D-B^2/A')
    require(minimum > s.Rational(1, 128) and maximum_A < s.Rational(25, 4)
            and lower > s.Rational(1, 800), 'Compact uniform gap constants')
    balanced = [v.subs(x, 1) for v in expected]
    require(balanced == [s.Rational(3, 2), s.Rational(-713, 864),
                         s.Rational(71583401, 136857600)], 'Balanced exact coefficients')
    gap = s.factor(balanced[2]-balanced[1]**2/balanced[0])
    require(gap == s.Rational(85044709, 1231718400), 'Balanced whole-fluid excess')
    return dict(squared_ratio='x=delta^2', coefficients=list(map(str, expected)),
                numerator=str(numerator), ratio_interval=['3/4', '4/3'],
                bernstein_minimum=str(minimum), uniform_gap_lower=str(lower),
                convenient_gap_lower='1/800',
                balanced_coefficients=list(map(str, balanced)), balanced_gap=str(gap),
                exact_samples=[dict(delta=str(d), coefficients=list(map(str, v))) for d, v in rows])


def viscous_moments():
    """Independent actual moment equations over QQ(i)[epsilon], at nu=1/2."""
    ring = f.QQ_I.poly_ring('epsilon')
    epsilon = ring.gens[0]
    nu = Q(1, 2)
    initial = [f.scale(epsilon, a) for a in seed(Q(1))]
    velocity, pressure = velocity_time_jets(initial, nu, 5)
    gradient = [f.grad(p) for p in pressure]
    g = [[v[i] for v in gradient] for i in range(3)]

    def step(history, source, n):
        transport = []
        for k in range(n+1):
            if not history[n-k]:
                continue
            require(k < len(velocity), 'Every nonzero advecting time jet is available')
            transport.append(f.scale(comb(n, k), f.adv(velocity[k], history[n-k])))
        return f.add(f.scale(nu, f.lap(history[n])), f.scale(-1, f.add(*transport)), source)

    impulse = [[{}] for _ in range(3)]
    for n in range(5):
        for i in range(3):
            impulse[i].append(step(impulse[i], g[i][n], n))
    second = [[[{}] for _ in range(3)] for _ in range(3)]
    for n in range(6):
        for i in range(3):
            for j in range(3):
                source = f.add(product_jet(impulse[i], g[j], n),
                               product_jet(impulse[j], g[i], n))
                second[i][j].append(step(second[i][j], source, n))
    trace = [f.add(*(second[i][i][n] for i in range(3))) for n in range(7)]
    third = [[{}] for _ in range(3)]
    for n in range(7):
        for i in range(3):
            source = f.add(f.scale(2, f.add(*(product_jet(second[i][j], g[j], n)
                                             for j in range(3)))),
                           product_jet(trace, g[i], n))
            third[i].append(step(third[i], source, n))
    expected = {4: Q(3, 2), 6: Q(-713, 864), 8: Q(71583401, 136857600)}
    result = {}
    for n, coefficient in expected.items():
        field = f.add(*(product_jet(third[i], g[i], n-1) for i in range(3)))
        value = ring.convert(4*field.get(f.ORIGIN, f.ZERO)/factorial(n))
        require(value.get((n+4,), f.ZERO) == f.QQ_I(coefficient),
                'Complete viscous moment equations reproduce the leading coefficient')
        require(all(k[0] % 2 == 0 and k[0] <= n+4 for k in value),
                'Even amplitudes and the time/amplitude degree boundary')
        if n > 4:
            require(value.get((8,), f.ZERO) != 0, 'Lower-amplitude viscous terms were retained')
        result[n] = str(value)
    return dict(viscosity='1/2', complete_time_coefficients=result)


def labels():
    x, y, z, delta = s.symbols('x y z delta', real=True)
    U = s.Matrix([s.sin(y)+delta*s.sin(z), s.sin(x), delta*s.sin(x)])
    chi = s.Rational(1, 2)+s.sin(x)/4
    inverse = {x: -x, y: -y, z: -z}
    for entry in U.subs(inverse, simultaneous=True)+U:
        require(s.trigsimp(entry) == 0, 'Inversion is an exact physical symmetry')
    require(s.trigsimp(chi.subs(inverse, simultaneous=True)-(1-chi)) == 0,
            'Nonconstant original labels are exchanged by the physical symmetry')
    a, b, eps = s.symbols('a b eps')
    global_value = eps**8*a*a/(a-eps*eps*b)
    labelled_sum = 2*eps**8*(a/2)**2/(a/2-eps*eps*b/2)
    require(s.cancel(labelled_sum-global_value) == 0,
            'Joint sum has no pooling loss available to explain the failure')
    return dict(partition=['1/2+sin(x)/4', '1/2-sin(x)/4'], initial_masses=['1/2', '1/2'],
                identity='Phi_+=Phi_-=Phi/2, and the summed rational allowance equals the global one',
                scope='Same actual fluid and all inherited moments; no independent-parent evolution')


if __name__ == '__main__':
    print(json.dumps(dict(family=family(), viscosity_check=viscous_moments(),
        labels=labels(), physical_jets=complete_three_dimensional_jets(),
        status='All exact checks passed',
        limitation='Joint rational allowance fails; arbitrary full-datum regularity remains open'), indent=2))
