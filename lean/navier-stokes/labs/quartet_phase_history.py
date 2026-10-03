#!/usr/bin/env python3
"""Actual quartet phase torque, parent depletion and a fixed-quartet reserve.

Laurent polynomials retain every unit phase, shell amplitude and generated
mode. The all-prefix physical reserve and local comparison are analytic in
README.md; this is an exact algebra checker, not a Lean PDE certificate.
"""

import json
import sympy as sp
from helical_second_return import (
    f, pm, Q, add, scale, cross, projection, conjugate, coefficient, zero,
    phased_parents, nonlinear, padd, velocity_time_jets, certified_interval,
    minus_pair,
)

KEYS = [(12, 0, 16), (-12, 0, 9), (0, 12, 16), (0, -12, 9)]
BASE = phased_parents(f.QQ_I(1))


def inner(v, w):
    return sum((conjugate(a)*b for a, b in zip(v, w)), f.ZERO)


def observe(v):
    return [inner(coefficient(BASE, k), coefficient(v, k))
            / inner(coefficient(BASE, k), coefficient(BASE, k)) for k in KEYS]


def clean(p):
    return {k: c for k, c in p.items() if c}


def plus(*ps):
    result = {}
    for p in ps:
        for k, c in p.items():
            result[k] = result.get(k, f.ZERO)+c
    return clean(result)


def times(c, p):
    return clean({k: c*v for k, v in p.items()})


def shift(p, degree):
    return {tuple(a+b for a, b in zip(k, degree)): c for k, c in p.items()}


def conj(p):
    # On the unit circle conjugate(zeta)=zeta^(-1); the amplitudes are real.
    return {(a, b, -phase): conjugate(c) for (a, b, phase), c in p.items()}


def imag(p):
    return times(-f.II/2, plus(p, times(-1, conj(p))))


def expr(p):
    a, b, z = sp.symbols('a b z')
    return sp.expand(sum((sp.Rational(c.x)+sp.I*sp.Rational(c.y))*a**i*b**j*z**k
                        for (i, j, k), c in p.items()))


def evaluate(p, a, b, z):
    return sum((c*a**i*b**j*z**k for (i, j, k), c in p.items()), f.ZERO)


def exact_dynamics():
    U = {}
    for j, component in enumerate(BASE):
        for k, c in component.items():
            if sum(x*x for x in k) == 225:
                degree = (0, 1, 0)
            elif k == KEYS[2]:
                degree = (1, 0, 1)
            elif k == tuple(-x for x in KEYS[2]):
                degree = (1, 0, -1)
            else:
                degree = (1, 0, 0)
            if degree not in U:
                U[degree] = [{}, {}, {}]
            U[degree][j][k] = c
    born = nonlinear(U, U)
    returned = padd(nonlinear(U, born), nonlinear(born, U))
    for v in born.values():
        if any(observe(v)):
            raise ArithmeticError('The initial source has no original parent mode')
    original = [(1, 0, 0), (0, 1, 0), (1, 0, 1), (0, 1, 0)]
    ratios = []
    for j, degree in enumerate(original):
        observation = clean({k: observe(v)[j] for k, v in returned.items()})
        ratios.append(shift(observation, tuple(-x for x in degree)))
    cosine = {(0, 0, 1): f.QQ_I(Q(1, 2)), (0, 0, -1): f.QQ_I(Q(1, 2))}
    sine = {(0, 0, 1): -f.II/2, (0, 0, -1): f.II/2}
    constant = {(0, 0, 0): f.QQ_I(1)}
    high_real = times(f.QQ_I(Q(1, 307681)), plus(times(-3392375616, constant),
        times(547449408, cosine), times(-2081366100, sine)))
    low_real = times(f.QQ_I(Q(1, 307681)), plus(times(1689009840, constant),
        times(11832480, cosine), times(2024997480, sine)))
    high_imag = times(f.QQ_I(Q(1, 337)), plus(times(2279700, cosine), times(599616, sine)))
    low_imag = times(f.QQ_I(Q(1, 337)), plus(times(-2217960, cosine), times(12960, sine)))
    expected = [shift(plus(high_real, times(f.II, high_imag)), (0, 2, 0)),
                shift(plus(low_real, times(f.II, low_imag)), (2, 0, 0))]
    expected += [conj(expected[0]), conj(expected[1])]
    for found, wanted in zip(ratios, expected):
        if plus(found, times(-1, wanted)):
            raise ArithmeticError('Full Laurent parent-return identity')
    torque = imag(plus(ratios[0], ratios[1], times(-1, ratios[2]), times(-1, ratios[3])))
    upper_high = Q(-3392375616+547449408+2081366100, 307681)
    if upper_high >= 0:
        raise ArithmeticError('Higher-shell parents must deplete for every phase')
    # At zeta=1, a=2,b=1, theta=-arg(quartet) has positive acceleration.
    away = -evaluate(torque, Q(2), Q(1), f.QQ_I(1)).x
    if away != Q(13184280, 337) or away <= 0:
        raise ArithmeticError('Automatic favorable phase drift counterexample')
    return ratios, torque, dict(
        parent_log_second_derivatives=[str(expr(p)) for p in ratios],
        arg_Q_second_derivative=str(expr(torque)),
        theta_second_derivative=str(expr(times(-1, torque))),
        high_parent_log_curvature_upper=str(upper_high)+' * b^2',
        adverse_angle_acceleration=str(away),
        scope='every unit phase and nonzero real amplitudes; actual first derivatives are retained heat decay')


def physical_checks(ratios, torque):
    rows = []
    samples = [(f.QQ_I(1), Q(2), Q(1), Q(1)),
               (-f.II, Q(1), Q(1), Q(3, 2)),
               (f.II, Q(1), Q(2), Q(2)),
               (f.QQ_I(Q(3, 5), Q(4, 5)), Q(2), Q(-1), Q(1))]
    for z, a, b, nu in samples:
        u = [{k: c*(a if sum(x*x for x in k) == 400 else b) for k, c in p.items()}
             for p in phased_parents(z)]
        jets, pressures = velocity_time_jets(u, nu, 2)
        alpha = [observe(v) for v in jets]
        log2 = []
        for j, k in enumerate(KEYS):
            rate = alpha[1][j]/alpha[0][j]
            if rate != -f.QQ_I(nu)*sum(x*x for x in k):
                raise ArithmeticError('Actual first phase derivative is zero')
            value = alpha[2][j]/alpha[0][j]-rate**2
            if value != evaluate(ratios[j], a, b, z):
                raise ArithmeticError('Actual advective/pressure phase return')
            log2.append(value)
        phase2 = sum(sign*v.y for sign, v in zip([1, 1, -1, -1], log2))
        if phase2 != evaluate(torque, a, b, z).x:
            raise ArithmeticError('Actual quartet phase acceleration')
        high = lambda v: [{k: c for k, c in p.items() if k in (KEYS[0], KEYS[2],
                         tuple(-x for x in KEYS[0]), tuple(-x for x in KEYS[2]))} for p in v]
        h0, h1, h2 = [high(v) for v in jets]
        energy2 = 2*pm.mean(f.dot(h1, h1))+2*pm.mean(f.dot(h0, h2))
        heat2 = (800*f.QQ_I(nu).x)**2*pm.mean(f.dot(h0, h0))
        if (energy2-heat2)/2 != 800*f.QQ_I(a*a).x*log2[0].x:
            raise ArithmeticError('Full high-parent modal energy depletion')
        rows.append(dict(phase=str(z), amplitudes=[str(a), str(b)], viscosity=str(nu),
                         arg_Q_second_derivative=str(phase2), theta_second_derivative=str(-phase2),
                         pressure_modes=[len(p) for p in pressures]))
    return rows


def adverse_angular_direction():
    matrix = sp.Matrix.hstack(*(sp.Matrix(k) for k in KEYS))
    if matrix.rank() != 3 or matrix*sp.Matrix([1, 1, -1, -1]) != sp.zeros(3, 1):
        raise ArithmeticError('Primitive quartet resonance')
    # A degree-six translation-invariant polynomial has phase harmonics at most 1:
    # harmonic n needs at least 4*|n| original factors. Odd degrees cannot resonate.
    coefficients = []
    for phase in (f.II, -f.II):
        u = [{k: c*(2 if sum(x*x for x in k) == 400 else 1) for k, c in p.items()}
             for p in phased_parents(phase)]
        bilinear = lambda v, w: projection(cross(v, f.curl(w)))
        born = bilinear(u, u)
        returned = add(bilinear(u, born), bilinear(born, u))
        third = add(bilinear(u, returned), bilinear(returned, u), scale(2, bilinear(born, born)))
        coefficients.append(sp.expand(minus_pair(born, third)/3+minus_pair(returned, returned)/4))
    derivative = sp.expand((coefficients[0]-coefficients[1])/2)
    lower, upper = certified_interval(derivative)
    if not lower > 9*10**11:
        raise ArithmeticError('Increasing phase increases the complete return coefficient')
    return dict(amplitudes=['2', '1'], initial_phase='1',
        theta_second_derivative='13184280/337',
        complete_return_angular_derivative=str(derivative),
        exact_interval=[str(lower), str(upper)],
        scope='angular contribution moves toward larger C; no claim that amplitudes or other modes stay fixed')


def reserve_algebra():
    E, Z, nu, K = sp.symbols('E Z nu K', positive=True)
    R = K*E**sp.Rational(5, 2)/(5*nu)
    zero(sp.diff(R, E)*(-2*nu*Z)+K*E**sp.Rational(3, 2)*Z,
         'full energy pays actual fixed-quartet source')
    lengths = [20, 15, 20, 15]
    normalization = sp.prod(sp.sqrt(2)/r for r in lengths)
    K0 = normalization*sum(lengths)
    if K0 != sp.Rational(7, 2250) or sum(r*r for r in lengths) != 1250:
        raise ArithmeticError('Explicit quartet source and diffusion constants')
    # R'<=-|F|, (|Q|)'+nu*kappa|Q|<=|F| and angular work<=|F|.
    F, Qabs, kappa = sp.symbols('F Qabs kappa', nonnegative=True)
    zero(2*(-F)+(F-nu*kappa*Qabs)+nu*kappa*Qabs+F,
         'one original reserve pays maintenance and weighted angular work')
    return dict(quartet_source_bound='|F|<=K E^(5/2)',
        K=str(K0), diffusion_eigenvalue=1250,
        energy_reserve='R=K E^(5/2)/(5nu)',
        combined_reserve='S=|Q|+2R',
        payment='S_prime+nu*kappa*|Q|+weighted_absolute_phase_velocity<=0',
        scope='all smooth mean-zero unforced periodic prefixes at fixed observation modes',
        OPEN='uniform all-scale control of critical production; neither free external forcing nor a closed quartet')


def main():
    ratios, torque, dynamics = exact_dynamics()
    print(json.dumps(dict(status='all exact checks passed', exact_phase_dynamics=dynamics,
        independent_NS_checks=physical_checks(ratios, torque),
        adverse_angular_direction=adverse_angular_direction(), reserve=reserve_algebra(),
        scope='algebra exact; local and all-prefix PDE conclusions analytic, not new Lean theorems'), indent=2))


if __name__ == '__main__':
    main()
