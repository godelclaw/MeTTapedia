#!/usr/bin/env python3
"""Exact NS tests of positive quadratic pressure/speed storage.

The two entries of the observed vector are e=|u|^2/2 and the canonical
pressure. Every convolution output and the complete pressure derivative
are retained. README.md supplies the analytic local-solution interpretation;
these algebraic checks are not a truncated evolution or a Lean certificate.
"""

import json
from fractions import Fraction as Q

import sympy as s
import pressure_history_source as f
from pressure_impulse_return import mean, require


RING = f.QQ_I.poly_ring('eps')
EPS = RING.gens[0]
eps = s.Symbol('eps')


def mode(k, polarization, real, imag=0):
    coefficient = f.QQ_I(real, imag)/2
    opposite = tuple(-x for x in k)
    return [{k: coefficient*a, opposite: f.QQ_I(coefficient.x, -coefficient.y)*a}
            if a else {} for a in polarization]


def datum():
    fields = [mode((0, 1, -1), (-1, -1, -1), 1),
              mode((0, 1, 0), (-1, 0, 1), 0, -1),
              mode((0, 0, 1), (0, -1, 0), 2),
              [f.scale(EPS, a) for a in mode((1, 1, 0), (1, -1, -1), 1)]]
    return [f.add(*(v[j] for v in fields)) for j in range(3)]


def avg(field):
    result = s.expand(RING.to_sympy(RING.convert(mean(field))))
    require(not result.has(s.I), 'Real exact spatial integral')
    return result


def matrix_strings(matrix):
    return [[str(s.factor(a)) for a in row] for row in matrix.tolist()]


def derivative(u, tangent, p, e):
    """Differentiate the full canonical pressure in two independent forms."""
    f.equal(f.trace(f.jac(tangent)), {}, 'Full solenoidal NS tangent component')
    et = f.dot(u, tangent)
    pt = f.tensor_pressure([[f.add(f.mul(u[i], tangent[j]), f.mul(tangent[i], u[j]))
                             for j in range(3)] for i in range(3)])
    B, Bt = f.jac(u), f.jac(tangent)
    poisson = f.green(f.add(f.trace(f.matmul(Bt, B)), f.trace(f.matmul(B, Bt))))
    f.equal(pt, poisson, 'Pressure time derivative retains all generated modes')
    mixed = avg(f.add(f.mul(et, p), f.mul(e, pt)))
    result = s.Matrix([[2*avg(f.mul(e, et)), mixed], [mixed, 2*avg(f.mul(p, pt))]])
    return result, et, pt


def even_interval(expression):
    """Exact power enclosure on |eps|<=1/8, with no floating arithmetic."""
    lo = hi = s.Rational(0)
    for (power,), coefficient in s.Poly(s.expand(expression), eps).terms():
        require(power % 2 == 0, 'The matrix entries are even polynomials')
        if power == 0:
            lo += coefficient
            hi += coefficient
        elif coefficient >= 0:
            hi += coefficient/s.Integer(8)**power
        else:
            lo += coefficient/s.Integer(8)**power
    return lo, hi


def check():
    u = datum()
    f.equal(f.trace(f.jac(u)), {}, 'Actual incompressible datum')
    require(all(avg(a) == 0 for a in u), 'Zero original spatial mean')
    p = f.tensor_pressure(f.tensor(u, u))
    e = f.scale(Q(1, 2), f.dot(u, u))
    gradient = f.grad(p)
    euler = [f.scale(-1, f.add(f.adv(u, u[i]), gradient[i])) for i in range(3)]
    heat = [f.lap(a) for a in u]
    DE, etE, ptE = derivative(u, euler, p, e)
    DL, etL, _ = derivative(u, heat, p, e)
    G = s.Matrix([[avg(f.mul(e, e)), avg(f.mul(e, p))],
                  [avg(f.mul(e, p)), avg(f.mul(p, p))]])
    expectedE = s.Matrix([[s.Rational(1, 5)-13*eps**2/5, 11*eps**2/18],
                          [11*eps**2/18, s.Rational(27, 20)-592*eps**2/225]])
    expectedL = s.Matrix([[-27*eps**4/4-73*eps**2/2-s.Rational(151, 4),
                           12*eps**2/5+s.Rational(24, 5)],
                          [12*eps**2/5+s.Rational(24, 5),
                           -434*eps**2/75-s.Rational(98, 5)]])
    require(s.simplify(DE-expectedE) == s.zeros(2), 'Exact Euler matrix derivative')
    require(s.simplify(DL-expectedL) == s.zeros(2), 'Exact full viscous matrix derivative')

    # Independent integrated local-energy identities, including transport.
    f.equal(etE, f.scale(-1, f.add(f.adv(u, e), f.adv(u, p))),
            'Complete inviscid kinetic-energy density evolution')
    grad_square = f.add(*(f.mul(a, a) for row in f.jac(u) for a in row))
    f.equal(etL, f.add(f.lap(e), f.scale(-1, grad_square)),
            'Complete viscous kinetic-energy density evolution')
    require(s.expand(DE[0, 0]+2*avg(f.mul(e, f.adv(u, p)))) == 0,
            'Integrated quartic growth is actual pressure work')
    require(s.expand(DE[0, 1]-avg(f.mul(e, f.add(ptE, f.adv(u, p))))) == 0,
            'Mixed derivative retains evolving and advected pressure')
    require(s.expand(DL[0, 0]+2*avg(f.add(f.mul(e, grad_square),
                                           f.dot(f.grad(e), f.grad(e))))) == 0,
            'Quartic viscous loss includes the speed gradient')
    require(avg(etE) == 0 and s.expand(avg(etL)+avg(grad_square)) == 0,
            'Total kinetic energy still decreases')

    # Elementary uniform Sylvester certificates for an entire parameter interval.
    elo, ehi = even_interval(DE[0, 0]), even_interval(DE[1, 1])
    crossE = even_interval(DE[0, 1])
    require(elo[0] >= s.Rational(3, 20) and ehi[0] >= s.Rational(13, 10),
            'Positive Euler diagonal bounds')
    require(max(abs(a) for a in crossE) <= s.Rational(1, 100), 'Small Euler cross term')
    require(s.Rational(3, 20)*s.Rational(13, 10)-s.Rational(1, 100)**2 > 0,
            'Uniform positive-definite Euler rate')
    B = 256*DE+DL
    bounds = [even_interval(B[0, 0]), even_interval(B[1, 1]), even_interval(B[0, 1])]
    require(bounds[0][0] >= 2 and bounds[1][0] >= 315,
            'Full positive-viscosity rate has positive diagonal margins')
    require(max(abs(a) for a in bounds[2]) <= 8 and (2-1)*(315-1)-8**2 > 0,
            'B-I is uniformly positive definite')
    heat_bounds = [even_interval(-DL[0, 0]), even_interval(-DL[1, 1]), even_interval(DL[0, 1])]
    require(heat_bounds[0][0] >= 37 and heat_bounds[1][0] >= 19,
            'Heat decreases both diagonal observations')
    require(max(abs(a) for a in heat_bounds[2]) <= 5 and 37*19-5**2 > 0,
            'The complete heat matrix is negative definite')

    # Reversing the velocity keeps e,p,G and every speed field unchanged,
    # reverses the nonlinear matrix rate and preserves the heat rate.
    # These parity statements are checked by independently recomputing sources.
    opposite = [f.scale(-1, a) for a in u]
    pm = f.tensor_pressure(f.tensor(opposite, opposite))
    f.equal(pm, p, 'Opposite velocities have the identical initial pressure')
    minusE, _, _ = derivative(opposite, euler, pm, e)
    minusL, _, _ = derivative(opposite, [f.scale(-1, a) for a in heat], pm, e)
    require(s.simplify(minusE+DE) == s.zeros(2) and s.simplify(minusL-DL) == s.zeros(2),
            'Same pressure/speed observations have opposite nonlinear feedback')

    # The planar endpoint has an independent all-time pressure-clock payment.
    base = [{k: RING.convert(c).evaluate(EPS, f.QQ_I.zero) for k, c in a.items()}
            for a in u]
    omega = f.curl(base)[0]
    require(avg(f.mul(omega, omega)) == s.Rational(9, 2), 'Original planar parent enstrophy')
    A, nu, c = s.symbols('A nu c', positive=True)
    # A=||omega||2^2 obeys A'<=-2nu A in the planar endpoint.
    reserve = c**2*A**2/(4*nu)
    require(s.simplify(s.diff(reserve, A)*(-2*nu*A)+c**2*A**2) == 0,
            'A vorticity reserve pays the pressure-amplitude clock without smallness')

    return dict(status='All exact checks passed',
                parameter_range='|eps|<=1/8; lambda>=256nu>0',
                gram=matrix_strings(G), euler_rate=matrix_strings(DE), heat_rate=matrix_strings(DL),
                physical_rate='G_prime=lambda^4*(lambda*DE+nu*DL) > nu*lambda^4*Id',
                full_rate_at_eps_one_eighth=matrix_strings(B.subs(eps, s.Rational(1, 8))),
                full_rate_enclosures=[[str(a) for a in b] for b in bounds],
                full_rate_determinant_at_eps_one_eighth=str(s.factor(B.det().subs(eps, s.Rational(1, 8)))),
                kinetic_energy= str(avg(f.dot(u, u))), gradient_squared=str(avg(grad_square)),
                opposite_velocity='Identical e,p,G; negative-definite initial rate lambda^4*(-lambda*DE+nu*DL)',
                planar_payment='If ||HessG p||4<=C_T*||omega||2^2, R=C_T^2*||omega||2^4/(4nu) pays its squared clock',
                scope='Exact full NS initial algebra; short actual intervals and planar all-time payment analytic, not Lean-certified')


if __name__ == '__main__':
    print(json.dumps(check(), indent=2))
