#!/usr/bin/env python3
"""Exact algebra for an energy-paid controller of reference stretching.

The full NS difference, projected adjoint, generated mean and cubic expansion
are checked on independent Fourier fields. Negative Sobolev estimates and
the actual interval payment are analytic, as stated in README.md.
"""

import json
from fractions import Fraction as Q
import sympy as s

import pressure_history_source as f
from reciprocal_pattern_cycles import inner, mode, vector_add, vector_scale, require
from refeeding_stretching import cubic, linear_cubic_term, nonlinear, vertical_mean
from cellular_parent_refeeding import seed
from cellular_transfer_reversal import real_field


def equal_vectors(a, b, label):
    for x, y in zip(a, b):
        f.equal(x, y, label)


def transpose(a):
    return [list(row) for row in zip(*a)]


def divergence(u):
    return f.add(*(f.diff(a, i) for i, a in enumerate(u)))


def project(u):
    potential = f.green(divergence(u))
    return [f.add(a, f.diff(potential, j)) for j, a in enumerate(u)]


def bilinear(u, v):
    return vector_scale(-1, project([f.adv(u, a) for a in v]))


def linear(u, d):
    return vector_add(bilinear(u, d), bilinear(d, u))


def adjoint(u, psi):
    strain = f.matvec(transpose(f.jac(u)), psi)
    return project([f.add(f.adv(u, a), f.scale(-1, b)) for a, b in zip(psi, strain)])


def stretching_test(u):
    omega = f.curl(u)
    gradient = f.jac(u)
    sym = [[f.add(gradient[i][j], gradient[j][i]) for j in range(3)] for i in range(3)]
    flux = f.tensor(omega, omega)
    return project(vector_add(f.curl(f.matvec(sym, omega)),
                              vector_scale(-1, [divergence(row) for row in flux])))


def gradient_norm_squared(u):
    return sum(inner([f.diff(a, j) for a in u], [f.diff(a, j) for a in u]) for j in range(3))


def physical_checks():
    U = [mode((0, 1, 0), Q(3, 2), True), mode((1, 0, 0), Q(-3, 2), True),
         f.add(mode((1, 1, 0), Q(2, 3)), mode((2, -1, 0), Q(1, 5), True))]
    fixture = f.fixture()
    test = stretching_test(U)
    require(inner(test, test) > 0, 'reference stretching test is nonzero')
    records = []
    for d in [real_field(seed()), fixture, vector_add(real_field(seed()), vector_scale(Q(1, 10), test))]:
        Ld = linear(U, d)
        Nd = bilinear(d, d)
        equal_vectors(Nd, nonlinear(d), 'bilinear projection agrees with canonical pressure')
        equal_vectors(nonlinear(vector_add(U, d)), vector_add(nonlinear(U), vector_add(Ld, Nd)),
                      'full nonlinear difference, including every generated mode')
        first = linear_cubic_term(U, d)
        require(inner(test, d) == first, 'exact first variation as a smooth physical test')
        require(inner(test, d) == inner(test, vertical_mean(d)), 'only actual generated mean is observed')
        require(cubic(vector_add(U, d))-cubic(U)-cubic(d)
                == first+linear_cubic_term(d, U), 'complete mixed cubic expansion')
        psi = vertical_mean(fixture)
        require(inner(psi, Ld) == inner(adjoint(U, psi), d), 'projected transport adjoint sign')
        equal_vectors(vertical_mean(Ld), linear(U, vertical_mean(d)), 'actual mean linearization')
        pairing = inner(d, f.matvec(f.jac(psi), d))
        require(inner(psi, Nd) == pairing, 'quadratic source pairs with adjoint gradient')
        require(inner(d, Nd) == 0, 'no self-advection work in relative energy')
        require(inner(d, Ld) == -inner(d, f.matvec(f.jac(U), d)), 'complete reference energy work')
        nu = Q(2, 7)
        dt = vector_add(vector_scale(nu, [f.lap(a) for a in d]), vector_add(Ld, Nd))
        require(2*inner(d, dt)+2*nu*gradient_norm_squared(d)
                == -2*inner(d, f.matvec(f.jac(U), d)), 'full positive-viscosity relative energy law')
        # The time derivative of <psi,m> retains both endpoints and the
        # PLUS diffusion in the backward adjoint equation.
        theta = Q(-3, 5)
        mt = vertical_mean(dt)
        psit = vector_scale(-1, vector_add(vector_scale(nu, [f.lap(a) for a in psi]),
                                           vector_add(adjoint(U, psi), vector_scale(theta, test))))
        derivative = inner(psit, vertical_mean(d))+inner(psi, mt)
        require(derivative == pairing-theta*first, 'full adjoint source identity with viscosity')
        records.append({'linear_stretching': str(first), 'source_pairing': str(pairing),
                        'quadratic_stretching': str(linear_cubic_term(d, U))})
    require(any(z['linear_stretching'] != '0' for z in records), 'first variation fixture is nonvacuous')
    return records


def scalar_checks():
    h, a, k, j, c, b = s.symbols('h a k j c b', positive=True)
    phi = lambda rate: (s.exp(rate*h)-1)/rate
    p = j*phi(k)
    r = b*s.exp(a*h)+c*j*(phi(k)-phi(a))/(k-a)
    zero = lambda expr, label: require(s.simplify(s.expand(expr)) == 0, label)
    zero(s.diff(p, h)-k*p-j, 'backward mean-observation adjoint')
    zero(s.diff(r, h)-a*r-c*p, 'backward source-to-energy adjoint')
    zero(p.subs(h, 0), 'mean weight terminal value')
    zero(r.subs(h, 0)-b, 'viscous terminal stock')
    n, E, D, nu, L, P, R, slackn, slackE = s.symbols('n E D nu L P R slackn slackE', real=True)
    rate = (-j-k*P)*n+P*(k*n+c*E-slackn)+(-a*R-c*P)*E+R*(a*E-2*nu*D-slackE)
    zero(rate+j*n+6*L*D+(2*nu*R-6*L)*D+P*slackn+R*slackE,
         'complete coupled reserve payment without a target derivative cap')
    zero(2*nu*(3*L/nu)-6*L, 'viscous threshold coefficient')
    value = p*n+r*E
    zero(s.diff(value, h)-(j*n+p*(k*n+c*E)+r*a*E),
         'Bellman identity when the nonpositive dissipation control is zero')
    r_zero_growth = b+c*j*(phi(k)-h)/k
    zero(s.limit(r, a, 0)-r_zero_growth, 'zero reference-growth limit')
    zero(s.diff(r_zero_growth, h)-c*p, 'zero-growth source-to-energy adjoint')
    return 'p_h=k p+j; r_h=a r+c p; terminal p=0, r=3L/nu'


if __name__ == '__main__':
    print(json.dumps({'physical_fixtures': physical_checks(), 'reserve': scalar_checks(),
                     'state': 'vertical mean in H^-3 and full relative L2 energy',
                     'cost': 'absolute mixed stretching; pure g(u-U) remains unpaid',
                     'status': 'exact finite checks; PDE negative-Sobolev comparison and global reference analytic'}, indent=2))
