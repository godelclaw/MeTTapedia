#!/usr/bin/env python3
"""A rational pressure allowance loses a necessary cost when cores are pooled.

Exact algebra covers smooth radial Euler cores, the finite-viscosity local
rotation check, moment weights and the missing mixture term. The actual
periodic viscous counterexample and its remainder argument are analytic in
README.md. No singular solution or Lean certificate is claimed.
"""

import argparse
import json
from fractions import Fraction as Q
from math import factorial

import sympy as s


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def zero(value, label):
    require(s.cancel(s.expand(value)) == 0, label)


def radial_euler():
    x, y = s.symbols('x y', real=True)
    omega = s.Function('omega')
    # omega(x^2+y^2) is smooth even at the axis; the construction is
    # constant there and flat at its outer boundary.
    w = omega(x*x+y*y)
    u = s.Matrix([-y*w, x*w])
    adv = u.jacobian((x, y))*u
    gp = s.Matrix([x*w*w, y*w*w])
    zero(s.diff(u[0], x)+s.diff(u[1], y), 'Literal incompressibility')
    for v in adv+gp:
        zero(v, 'Complete radial Euler acceleration and pressure')
    zero(s.diff(gp[1], x)-s.diff(gp[0], y), 'Canonical pressure gradient')

    t, r, a = s.symbols('t r a', real=True)
    rotation = s.Matrix([[s.cos(a*t), -s.sin(a*t)],
                         [s.sin(a*t), s.cos(a*t)]])
    initial = s.Matrix([0, a*r])
    impulse = initial-rotation*initial
    square = s.trigsimp(impulse.dot(impulse))
    require(s.trigsimp(square-2*a*a*r*r*(1-s.cos(a*t))) == 0,
            'Exact material pressure impulse of a rotating core')
    quartic = s.series(square**2, t, 0, 10).removeO().expand()
    expected = {4: r**4*a**8, 6: -r**4*a**10/6,
                8: r**4*a**12/80}
    for n, v in expected.items():
        zero(quartic.coeff(t, n)-v, 'Complete pressure-path Taylor coefficient')
    require(all(quartic.coeff(t, n) == 0 for n in (0, 1, 2, 3, 5, 7, 9)),
            'Lower and odd Euler moments vanish')
    return {n: str(v) for n, v in expected.items()}


def viscous_rotation_fixture():
    """Local algebra only: solid rotation is not finite-energy torus data."""
    t, r, a, nu = s.symbols('t r a nu', positive=True)
    mean_square = 2*r*r*a*a*(1-s.cos(a*t))
    # dX=a JX dt+sqrt(2nu)dW, P=a^2 integral X ds. The centred
    # pressure impulse has isotropic covariance variance*I in two dimensions.
    variance = 4*nu*a*(a*t-s.sin(a*t))
    fourth = mean_square**2+8*variance*mean_square+8*variance**2
    polynomial = s.series(fourth, t, 0, 10).removeO().expand()
    for amplitude, time, expected in ((8, 4, r**4),
                                      (10, 6, -r**4/6),
                                      (12, 8, r**4/80)):
        zero(polynomial.coeff(a, amplitude).coeff(t, time)-expected,
             'Viscosity leaves the highest-amplitude leading jet unchanged')
    require(polynomial.coeff(nu, 1).coeff(a, 8).coeff(t, 5) != 0,
            'The check retains a nonzero stochastic viscous correction')
    return dict(variance=str(variance),
                scope='Exact local solid-rotation SDE fixture, not the periodic witness')


def mixture():
    L, M8, M10, M12, C = s.symbols('L M8 M10 M12 C', positive=True)
    x = (2*L*L-3)/(L*L-1)
    y = 1/((L*L-1)*L**8)
    sums = [s.cancel(x+y*L**n) for n in (8, 10, 12)]
    require(sums == [2, 3, L*L+3], 'Fixed first two weighted moments')
    A, B, D = 2*C*M8, -C*M10/2, C*M12*(L*L+3)/80
    gap = s.factor(D-B*B/A)
    lower = C*M10*M10/M8*(L*L-7)/80
    zero(gap-lower-C*(L*L+3)*(M12-M10*M10/M8)/80,
         'Cauchy gives a positive lower bound for every L>=3')
    alpha = Q(15, 16)
    require(alpha**-12 < Q(20, 9), 'A smooth narrow cutoff preserves the single-core sign')
    # M10^2<=M8*M12, and alpha^6/6<=Mj<=1/6. These integral
    # inequalities are proved in README.md, rather than assumed as identities.
    require(Q(1, 80)*alpha**-12-Q(1, 36) < 0,
            'Each isolated core has strictly negative next envelope gap')
    A1, A2 = C*M8*x, C*M8*y*L**8
    B1, B2 = -C*M10*x/6, -C*M10*y*L**10/6
    repaired = C*(L*L+3)*(M12/80-M10*M10/(36*M8))
    zero(D-B1*B1/A1-B2*B2/A2-repaired,
         'Retaining the labelled ratios pays the first combined return')
    z = s.symbols('z', nonnegative=True)
    require(s.Poly((L*L-7).subs(L, z+3), z).all_coeffs() == [1, 6, 2],
            'The entire integer frequency family has a positive gap')
    return dict(radius_sixth_weights=[str(x), str(y)], speed_ratio='L>=3',
                leading_coefficients=list(map(str, (A, B, D))),
                actual_gap=str(gap), positive_lower_bound=str(lower),
                labelled_gap=str(repaired),
                single_core_moment_ratio_upper=str(alpha**-12),
                single_core_threshold='20/9')


def pooling_identity():
    a, b, d, e = s.symbols('a b d e', positive=True)
    difference = a*a/(a+d)+b*b/(b+e)-(a+b)**2/(a+b+d+e)
    lost = (a*e-b*d)**2/((a+d)*(b+e)*(a+b+d+e))
    zero(difference-lost, 'Pooling before division loses the exact variance term')
    t = s.symbols('t')
    series = s.series(difference.subs({a: a*t**4, b: b*t**4,
                                      d: d*t**6, e: e*t**6}), t, 0, 9).removeO()
    zero(series.coeff(t, 8)-(d*d/a+e*e/b-(d+e)**2/(a+b)),
         'The first lost payment is precisely the coefficient variance')
    return str(lost)


def labelled_history():
    q = s.Matrix(s.symbols('q0:3'))
    g = s.Matrix(s.symbols('g0:3'))
    square = q.dot(q)
    derivative = lambda p: sum(g[i]*s.diff(p, q[i]) for i in range(3))
    zero(derivative(s.Integer(1)), 'The original label is not renewed')
    for i in range(3):
        zero(derivative(q[i])-g[i], 'The first source is label density times pressure')
        for j in range(3):
            zero(derivative(q[i]*q[j])-q[i]*g[j]-g[i]*q[j],
                 'Complete second conditional moment source')
        zero(derivative(square*q[i])-2*q[i]*q.dot(g)-square*g[i],
             'Complete contracted third conditional moment source')
    zero(derivative(square**2)-4*square*q.dot(g), 'Complete fourth source')

    x, y, z = s.symbols('x y z')
    u = s.Matrix([s.Function('u')(x, y), s.Function('v')(x, y), 0])
    omega = s.Matrix([0, 0, s.diff(u[1], x)-s.diff(u[0], y)])
    require(u.jacobian((x, y, z))*omega == s.zeros(3, 1),
            'Every planar velocity has identically zero vortex stretching')
    return dict(first_source='rho_i * grad p',
                fourth_source='4 grad p dot T_i',
                composition='Sum unnormalized moments on the same actual velocity and pressure',
                limitation='Component estimates and all subsequent exchanges still need payment')


def cyclic_probe(k=1, amplitudes=(1, 1, 1), harmonic=0):
    """Exact complete material jets; favorable signs are not long-time bounds."""
    import pressure_history_source as f
    from cyclic_pressure_history import velocity_time_jets
    from cyclic_entropy_depletion import material_jets
    from pressure_parent_bellman import trig

    initial = [trig(1, 1, 'sin'),
               f.add(trig(2, k, 'sin'), f.scale(harmonic, trig(2, 3*k, 'sin'))),
               trig(0, 1, 'sin')]
    initial = [f.scale(a, v) for a, v in zip(amplitudes, initial)]
    velocity, pressure = velocity_time_jets(initial, Q(0), 6)
    require(not pressure[0], 'Cyclic pressure starts at its generated parent')
    gradient = [f.grad(p) for p in pressure]
    path = [material_jets([v[i] for v in gradient], velocity) for i in range(3)]
    impulse = [[{}, {}]+[f.scale(Q(1, factorial(n+1)), v[n]) for n in range(1, 6)]
               for v in path]
    squares = {n: f.add(*(f.mul(impulse[i][r], impulse[i][n-r]) for i in range(3)
                         for r in range(2, 7) if 2 <= n-r <= 6)) for n in range(4, 9)}
    coefficients = {}
    for n in (8, 9, 10, 11, 12):
        value = f.add(*(f.mul(squares[r], squares[n-r]) for r in range(4, 9)
                        if 4 <= n-r <= 8)).get(f.ORIGIN, f.ZERO)
        require(not value.y, 'Real complete spatial pressure moment')
        coefficients[n] = Q(str(value.x))
    a, b, c = [coefficients[n] for n in (8, 10, 12)]
    require(coefficients[9] == coefficients[11] == 0, 'Odd reflection jets vanish')
    require(a > 0 and b < 0 and c-b*b/a < 0, 'The tested cyclic profile retains its initial margin')
    return dict(k=k, amplitudes=amplitudes, third_harmonic=str(harmonic),
                coefficients={n: str(v) for n, v in coefficients.items()},
                next_gap=str(c-b*b/a), scope='Initial coefficient only')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cyclic-probes', action='store_true')
    args = parser.parse_args()
    if args.cyclic_probes:
        cases = [(k, (1, 1, 1), 0) for k in (1, 2, 4, 6)]
        cases += [(k, a, 0) for k in (4, 8) for a in ((4, 1, 1), (1, 4, 1), (1, 1, 4))]
        cases += [(1, (1, 1, 1), h) for h in (Q(1, 2), Q(-1, 2), Q(1), Q(-1))]
        for k, a, h in cases:
            print(json.dumps(cyclic_probe(k, a, h)), flush=True)
    else:
        print(json.dumps(dict(radial_euler=radial_euler(),
            viscous_fixture=viscous_rotation_fixture(), mixture=mixture(),
            exact_pooling_loss=pooling_identity(), labelled_history=labelled_history(),
            status='All exact checks passed; actual viscous remainder analytic',
            limitation='Specific pooled rational envelope refuted, not NS regularity'), indent=2))
