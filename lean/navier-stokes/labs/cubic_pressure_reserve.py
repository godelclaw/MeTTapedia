#!/usr/bin/env python3
"""Exact fixtures for cubic velocity pressure work and a Bernoulli reserve.

The all-time PDE payment, stochastic representation and continuation argument
are analytic in README.md. These checks do not certify those arguments in Lean.
"""

import json
import sympy as sp
from finite_band_renewal import f, pm, Q, harmonic, velocity_time_jets, zero


def equal(p, q, label):
    f.equal(p, q, label)


def grad(p):
    return [f.diff(p, j) for j in range(3)]


def grad_pair(u):
    return sum(pm.mean(f.mul(f.diff(p, j), f.diff(p, j)))
               for p in u for j in range(3))


def convect(u, p):
    return f.dot(u, grad(p))


def trig(k, kind):
    return harmonic(k, kind)


def cellular_pressure():
    sx, sy = trig((1, 0, 0), 'sin'), trig((0, 1, 0), 'sin')
    cx, cy = trig((1, 0, 0), 'cos'), trig((0, 1, 0), 'cos')
    v = [f.mul(sx, cy), f.scale(-1, f.mul(cx, sy)), {}]
    p = f.scale(Q(1, 4), f.add(trig((2, 0, 0), 'cos'), trig((0, 2, 0), 'cos')))
    equal(pm.divergence(v), {}, 'actual incompressibility')
    for j in range(3):
        equal(convect(v, v[j]), f.scale(-1, f.diff(p, j)), 'stationary Euler balance')
        equal(f.lap(v[j]), f.scale(-2, v[j]), 'horizontal viscous eigenvalue')
    equal(f.lap(p), f.scale(-4, p), 'pressure viscous eigenvalue')
    F = convect(v, p)
    equal(F, f.mul(f.mul(cx, cy), f.add(f.mul(sy, sy), f.scale(-1, f.mul(sx, sx)))),
          'explicit pressure work profile')
    if pm.mean(F) != 0 or pm.mean(f.mul(F, F)) != Q(1, 32):
        raise ArithmeticError('Pressure profile mean or square')
    if grad_pair(v) != 1 or pm.mean(f.dot(v, v)) != Q(1, 2):
        raise ArithmeticError('Horizontal norm constants')
    if grad_pair([F]) != Q(5, 16):
        raise ArithmeticError('Pressure profile gradient constant')

    # Both initial vertical profiles have zero mean. No uniform vertical drift
    # is needed to expose the sign of the cubic pressure work.
    M = 16
    profiles = [f.scale(M, f.add(sx, f.scale(sign, f.mul(sx, F)))) for sign in (-1, 1)]
    for w in profiles:
        if pm.mean(w) != 0 or grad_pair([w]) != 163:
            raise ArithmeticError('Mean-zero vertical profile and gradient norm')
        jets, pressures = velocity_time_jets([v[0], v[1], w], Q(3, 7), 1)
        equal(pressures[0], p, 'full NS pressure includes the passive component')
        for j in range(2):
            equal(jets[1][j], f.scale(-Q(6, 7), v[j]), 'actual horizontal NS evolution')
        equal(jets[1][2], f.add(f.scale(Q(3, 7), f.lap(w)), f.scale(-1, convect(v, w))),
              'actual vertical NS evolution retains transport and diffusion')

    # Exact integral of |sin x| F^2: put c=cos x on 0<=x<=pi and
    # use the exact even cosine moments in y. The remaining factor is 1/pi.
    c, d = sp.symbols('c d', real=True)
    polynomial = sp.Poly(sp.integrate(c*c*d*d*(c*c-d*d)**2, (c, -1, 1)), d)
    integral_times_pi = sum(coefficient * sp.binomial(power, power//2) / 2**power
                            for (power,), coefficient in polynomial.terms())
    zero(integral_times_pi-sp.Rational(43, 840), 'weighted pressure profile square')
    z = sp.symbols('z', real=True)
    zero(sp.integrate(z**4*(1-z)**4/(1+z*z), (z, 0, 1))-sp.Rational(22, 7)+sp.pi,
         'positive integral establishes pi < 22/7')
    # pi<22/7, and |sqrt(|v|^2+w^2)-|w||<=|v|. Cauchy--Schwarz
    # bounds the resulting pressure error by ||v||_2 ||F||_2=1/8.
    pressure_lower = M*integral_times_pi*sp.Rational(7, 22)-sp.Rational(1, 8)
    if not pressure_lower > sp.Rational(1, 8):
        raise ArithmeticError('Strict cubic pressure production')
    diffusion_upper = 2*(1+2*M)*(1+163)
    if diffusion_upper != 10824 or sp.Rational(100000, 8) <= diffusion_upper:
        raise ArithmeticError('Positive-viscosity cubic growth margin')

    # Reflection x -> pi-x exchanges the two speed fields and negates F.
    x, y = sp.symbols('x y', real=True)
    Fxy = sp.cos(x)*sp.cos(y)*(sp.sin(y)**2-sp.sin(x)**2)
    zero(sp.trigsimp(Fxy.subs(x, sp.pi-x)+Fxy), 'reflection reverses pressure work')
    speed2 = sp.sin(x)**2*sp.cos(y)**2+sp.cos(x)**2*sp.sin(y)**2
    zero(sp.trigsimp(speed2.subs(x, sp.pi-x)-speed2), 'reflection preserves horizontal speed')
    a, nu, t = sp.symbols('a nu t', positive=True)
    amplitude = a*sp.exp(-2*nu*t)
    gauge = amplitude**2/2
    zero(sp.diff(gauge, t)+2*nu*amplitude**2, 'positive pressure gauge has a paid derivative')
    return dict(mean_zero=True, pressure_profile_square='1/32', weighted_square='43/(840*pi)',
        vertical_gradient_energy=163, pressure_lower=str(pressure_lower),
        unit_diffusion_upper=diffusion_upper,
        actual_cubic_growth='amplitude >= 100000*nu; persists on a nonzero smooth interval',
        opposite_profile='same initial cubic mass and energy; opposite pressure work',
        all_history_reserve='2*sqrt(2)*integral (|u|^2/2+p+a(t)^2/2)^(3/2) - integral |u|^3')


def cyclic_pressure_creation():
    x, y, z = sp.symbols('x y z', real=True)
    A, B, C, nu = sp.symbols('A B C nu', positive=True)
    xyz = (x, y, z)
    u = sp.Matrix([A*sp.sin(y), B*sp.sin(z), C*sp.sin(x)])
    J = u.jacobian(xyz)
    zero(sp.trace(J*J), 'initial canonical pressure is zero')
    lap = lambda p: sum(sp.diff(p, coordinate, 2) for coordinate in xyz)
    ut = nu*u.applyfunc(lap)-J*u
    pt = -2*A*B*C*sp.cos(x)*sp.cos(y)*sp.cos(z)
    zero(sp.expand(-lap(pt)-2*sp.trace(J*ut.jacobian(xyz))), 'complete differentiated pressure Poisson equation')
    for amplitudes, viscosity in [((1, 1, 1), Q(1, 7)), ((2, 3, 5), Q(7, 3))]:
        a, b, c = amplitudes
        field = [f.scale(a, trig((0, 1, 0), 'sin')),
                 f.scale(b, trig((0, 0, 1), 'sin')),
                 f.scale(c, trig((1, 0, 0), 'sin'))]
        jets, pressures = velocity_time_jets(field, viscosity, 2)
        equal(pressures[0], {}, 'cyclic field has zero initial pressure')
        target = f.scale(-2*a*b*c, f.mul(f.mul(trig((1, 0, 0), 'cos'),
            trig((0, 1, 0), 'cos')), trig((0, 0, 1), 'cos')))
        equal(pressures[1], target, 'independent full Fourier pressure derivative')
        expected = [f.add(f.scale(viscosity, f.lap(field[j])),
                    f.scale(-1, convect(field, field[j]))) for j in range(3)]
        for j in range(3):
            equal(jets[1][j], expected[j], 'full cyclic NS initial tangent')
    defect_at_pi = 2*A*B*C-nu*(A*A+B*B+C*C)
    zero((pt-nu*sum(q*q for q in J)).subs({x: sp.pi, y: sp.pi, z: sp.pi})-defect_at_pi,
         'Bernoulli defect exceeds viscosity at large amplitude')
    return dict(initial_pressure=0, pressure_time_derivative=str(pt),
        defect_at_pi=str(defect_at_pi),
        failed_claim='unforced pressure automatically supplies a heat-compatible correction',
        scope='actual smooth positive-viscosity initial jets and ensuing short-time pressure creation; not blowup')


def full_pressure_defect():
    """Check all terms of the defect on a 3D field with nonzero pressure."""
    nu = Q(5, 11)
    sx, sy = trig((1, 0, 0), 'sin'), trig((0, 1, 0), 'sin')
    cx, cy = trig((1, 0, 0), 'cos'), trig((0, 1, 0), 'cos')
    u = [f.add(f.mul(sx, cy), f.scale(2, sy)),
         f.add(f.scale(-1, f.mul(cx, sy)), f.scale(3, trig((0, 0, 1), 'sin'))),
         f.scale(5, sx)]
    equal(pm.divergence(u), {}, 'full defect fixture is incompressible')
    _, pressures = velocity_time_jets(u, nu, 2)
    p, pt = pressures[:2]
    if not p:
        raise ArithmeticError('Full defect must test nonzero pressure feedback')
    lhs = f.scale(-1, f.lap(f.add(pt, f.scale(-nu, f.lap(p)))))
    rhs = {}
    for i in range(3):
        acceleration = f.add(convect(u, u[i]), f.diff(p, i))
        for j in range(3):
            gij, gji = f.diff(u[j], i), f.diff(u[i], j)
            rhs = f.add(rhs, f.scale(-2, f.mul(gij, f.diff(acceleration, j))))
            for k in range(3):
                rhs = f.add(rhs, f.scale(-2*nu, f.mul(f.diff(gij, k), f.diff(gji, k))))
    equal(lhs, rhs, 'pressure defect retains nonlinear, pressure and viscous sources')
    return dict(initial_pressure_modes=len(p), defect_source_modes=len(lhs),
                truncation='none; every convolution output retained')


def entropy_algebra():
    a, b, c = sp.symbols('a b c', real=True)
    v = sp.Matrix([a, b, c])
    r = sp.sqrt(v.dot(v))
    H = sp.hessian(r**3, (a, b, c))
    for i in range(3):
        for j in range(3):
            zero(H[i, j]-3*r*sp.eye(3)[i, j]-3*v[i]*v[j]/r, 'convex cubic diffusion Hessian')
    nu, AA, BB, FF, D, Pi = sp.symbols('nu AA BB FF D Pi', real=True)
    Zprime = 3*sp.sqrt(2)*FF-3*sp.sqrt(2)*nu*AA-3*sp.sqrt(2)*nu*BB/2
    Yprime = 3*Pi-3*nu*D
    remainder = sp.expand(Zprime-Yprime+3*Pi-sp.Rational(3, 2)*nu*D-3*sp.sqrt(2)*FF)
    zero(remainder+sp.Rational(3, 2)*nu*(2*sp.sqrt(2)*AA-D)+3*sp.sqrt(2)*nu*BB/2,
         'reserve inequality retains nonnegative diffusion remainders')
    Jforce, weighted_force = sp.symbols('Jforce weighted_force', real=True)
    forced_remainder = Zprime+3*sp.sqrt(2)*weighted_force-(Yprime+3*Jforce)+3*Pi-sp.Rational(3, 2)*nu*D
    zero(forced_remainder-remainder-3*sp.sqrt(2)*FF-3*sp.sqrt(2)*weighted_force+3*Jforce,
         'forced completion retains its extra weighted force cost')
    return dict(cubic_balance='Y_prime+3*nu*D=3*Pi',
        corrected_reserve='R_prime+3*Pi-(3*nu/2)*D <= 3*sqrt(2)*integral sqrt(Q)*S',
        defect='S=(partial_t-nu*Delta)p+(partial_t+u.grad-nu*Delta)h',
        forced_direct_work='abs(integral |u| u.f) <= ||f||_infinity ||u||_2^2',
        continuation='finite sup Y and integral D imply finite integral ||u||_9^3, then bounded enstrophy',
        OPEN='nonnegative pressure completion with an original-data payment of its complete defect for arbitrary interacting parents')


if __name__ == '__main__':
    print(json.dumps(dict(status='all exact checks passed',
        cellular=cellular_pressure(), cyclic=cyclic_pressure_creation(),
        full_defect=full_pressure_defect(), algebra=entropy_algebra(),
        certification='exact algebra and rational inequalities; PDE histories and continuation remain analytic'), indent=2))
