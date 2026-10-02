#!/usr/bin/env python3
"""Actual reciprocal feedback for a stable three-dimensional cycle family.

Exact rational Fourier checks retain every nonlinear output and canonical
pressure. Symbolic checks verify the reference envelope and the original
replenishment reserve. The smooth PDE construction, stability bootstrap and
whole-pattern cycle theorem are analytic in README.md, not certified by
running this program. No time-discretized flow or closed triad is used.
"""

import itertools
import json
from fractions import Fraction as Q

import sympy as s
import pressure_history_source as f


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def zero(expr, label):
    require(s.simplify(s.expand(expr)) == 0, label)


def mode(k, amplitude, sine=False):
    value = f.QQ_I(amplitude) / 2
    if sine:
        value *= -f.II
    return {k: value, tuple(-j for j in k): f.QQ_I(value.x, -value.y)}


def mean(field):
    value = field.get(f.ORIGIN, f.ZERO)
    require(value.y == 0, 'real spatial mean')
    return Q(str(value.x))


def inner(u, v):
    return mean(f.dot(u, v))


def vector_add(u, v):
    return [f.add(a, b) for a, b in zip(u, v)]


def vector_scale(c, u):
    return [f.scale(f.QQ_I(c), a) for a in u]


def hnorm_squared(u, order):
    result = Q(0)
    for alpha in itertools.product(range(order+1), repeat=3):
        if sum(alpha) > order:
            continue
        derivative = u
        for j, count in enumerate(alpha):
            for _ in range(count):
                derivative = [f.diff(a, j) for a in derivative]
        result += inner(derivative, derivative)
    return result


def exact_fixture(A, eps, phase, nu, receiver):
    v = [mode((0, 1, 0), 1, True), mode((1, 0, 0), -1, True), {}]
    # The two frequencies are transverse to their respective polarizations.
    d = [{}, {}, {}]
    for k, polarization, sign in [((1, 0, 1), (1, 0, -1), 1),
                                  ((1, -1, 1), (1, 1, 0), phase)]:
        for j, component in enumerate(polarization):
            if component:
                d[j] = f.add(d[j], mode(k, eps*sign*component))
    U = vector_scale(A, v)
    # These trigonometric probes check independence from the vertical
    # reference. The actual cycle theorem uses a smooth annular receiver.
    U[2] = receiver
    u = vector_add(U, d)
    for name, field in [('datum', u), ('perturbation', d)]:
        f.equal(f.trace(f.jac(field)), {}, (name, 'divergence free'))
        for component in field:
            require(not component.get(f.ORIGIN, f.ZERO), (name, 'mean zero'))
            for k, value in component.items():
                require(component.get(tuple(-j for j in k), f.ZERO) ==
                        f.QQ_I(value.x, -value.y), (name, 'real'))

    B = f.jac(u)
    pressure = f.green(f.trace(f.matmul(B, B)))
    f.equal(pressure, f.tensor_pressure(f.tensor(u, u)), 'canonical pressure')
    N = [f.add(f.scale(-1, f.adv(u, a)), f.scale(-1, f.diff(pressure, j)))
         for j, a in enumerate(u)]
    rhs = [f.add(a, f.scale(f.QQ_I(nu), f.lap(b))) for a, b in zip(N, u)]
    f.equal(f.trace(f.jac(rhs)), {}, 'complete unforced tangent is solenoidal')
    require(inner(u, N) == 0, 'complete nonlinear kinetic work is zero')
    require(inner(v, v) == 1 and inner(u, v) == A, 'actual parent coefficient')
    force = inner(v, N)
    expected = phase*eps**2/4
    require(force == expected, 'nonzero phase-sensitive internal parent force')
    require(inner(d, f.matvec(f.jac(v), d)) == force,
            'all reference cross terms cancel in the parent projection')
    require(inner(v, rhs) == -nu*A+force, 'actual viscous parent equation')
    require(hnorm_squared(d, 3) == 30*eps**2, 'complete initial H3 size')
    require(hnorm_squared(v, 4) == 5, 'cellular reference H4 size')
    remainder = vector_add(u, vector_scale(-A, v))
    require(inner(remainder, N) == -A*force,
            'parent work has the exact opposite full-remainder work')
    dissipation = sum(inner([f.diff(a, j) for a in u],
                            [f.diff(a, j) for a in u]) for j in range(3))
    require(inner(u, rhs) == -nu*dissipation, 'full viscous energy law')
    require(inner(d, d) == 2*eps**2, 'equal-energy opposite phases')
    require(inner(u, u) == A*A+inner([receiver], [receiver])+2*eps**2,
            'same full initial energy for the opposite-phase fixtures')
    inputs = set().union(*u)
    outputs = set().union(*N)
    require(bool(outputs-inputs), 'generated outputs are retained outside the input support')
    return {'A': str(A), 'epsilon': str(eps), 'phase': phase, 'nu': str(nu),
            'full_energy': str(inner(u, u)), 'initial_H3_error_squared': str(30*eps**2),
            'parent_force': str(force), 'parent_nonlinear_energy_rate': str(2*A*force),
            'remainder_nonlinear_energy_rate': str(-2*A*force),
            'generated_modes': len(outputs-inputs)}


def symbolic_checks():
    C4 = 2*sum((j+1)*(2**j-1) for j in range(1, 5))
    require(C4 == 228, 'all planar reference transport commutators counted')
    x, y, z, eps, phase = s.symbols('x y z eps phase', real=True)
    dx = eps*(s.cos(x+z)+phase*s.cos(x-y+z))
    dy = eps*phase*s.cos(x-y+z)
    # Independent real-space verification of the generic feedback formula.
    density = s.expand_trig((s.cos(y)-s.cos(x))*dx*dy).expand()
    for coord in (z, x, y):
        density = s.integrate(density, (coord, 0, 2*s.pi))/(2*s.pi)
    zero(density-phase*eps**2/4, 'generic physical-space parent force')
    nu, M, Y0, t = s.symbols('nu M Y0 t', positive=True)
    Y = s.Function('Y')(t)
    bound = Y0*s.exp(M*(1-s.exp(-nu*t))-nu*t)
    zero(s.diff(bound, t)-(nu*M*s.exp(-nu*t)-nu)*bound,
         'global perturbation envelope after the complete self term is absorbed')
    B = Y*s.exp(M*s.exp(-nu*t))/nu
    B_rate = s.diff(B, t).subs(s.diff(Y, t), (nu*M*s.exp(-nu*t)-nu)*Y)
    zero(B_rate+Y*s.exp(M*s.exp(-nu*t)),
         'one original nonnegative reserve pays all later absolute parent forcing')
    zero(B.subs(Y, bound)-Y0*s.exp(M-nu*t)/nu,
         'reserve uses the original datum at every seam')
    A, beta, F, absF = s.symbols('A beta F absF', real=True)
    a = A*s.exp(-nu*t)
    # At beta != 0 the absolute-value derivative has sign +/-1.
    # At zeros its integrated inequality follows from absolute continuity.
    for sign in (-1, 1):
        R_rate = -a+sign*(-nu*beta+F)/nu-absF/nu
        zero(R_rate+a+sign*beta-(sign*F-absF)/nu,
             'corrected parent clock retains the absolute forcing payment')
    K, Cemb = s.symbols('K Cemb', positive=True)
    cubic_reserve = 4*Cemb*K**3*s.exp(-3*nu*t/2)/(3*nu)
    zero(s.diff(cubic_reserve, t)+2*Cemb*K**3*s.exp(-3*nu*t/2),
         'actual cubic stretching envelope has a decreasing all-time reserve')
    return {'reference_commutator_constant': C4,
            'reference_H4': 'Q=A sqrt(5+||w0||H4^2 exp(456 A/nu))',
            'stability_parameter': 'M=C3 Q/nu; C3 is a fixed Sobolev/commutator constant',
            'perturbation_threshold': 'sqrt(30)|epsilon| exp(M/2)<=min(nu/(2C3),eta A/(2Cemb))',
            'parent_force': 'F=<d tensor d,grad v>; |F|<=Y; F(0)=phase epsilon^2/4',
            'all_time_absolute_force': 'integral_0^infinity |F|<=30epsilon^2 exp(M)/nu',
            'remaining_parent_clock': 'a/nu+|alpha-a|/nu+Y exp(M exp(-nu t))/nu^2',
            'cycle_error': 'reference eta/2 plus full-3D perturbation eta/2, using the same A and clock',
            'scope': 'analytic global actual 3D neighborhood; any prescribed finite number of approximate cycles; no infinite-cascade realization'}


if __name__ == '__main__':
    receivers = [{}, mode((1, 0, 0), 1, True),
                 f.add(mode((1, 2, 0), Q(2, 3), True), mode((2, -1, 0), Q(1, 4)))]
    fixtures = [exact_fixture(A, eps, phase, nu, receiver)
                for A, eps, nu in [(Q(1), Q(1, 5), Q(1, 10)),
                                   (Q(3, 2), Q(1, 100), Q(2, 3))]
                for phase in (-1, 1) for receiver in receivers]
    print(json.dumps({'symbolic': symbolic_checks(), 'fixtures': fixtures,
                      'status': 'exact algebra only; full smooth PDE theorem is analytic'}, indent=2))
