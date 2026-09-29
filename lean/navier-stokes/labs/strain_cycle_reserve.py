#!/usr/bin/env python3
"""A nonnegative sixth-order resource and actual strain-cycle defects.

The compact-core comparison has a conserved polynomial in five physical
moments. An eigenframe certificate and a quantitative spectral-regime
estimate control its intrinsic compression/turning cost through a whole
history. Actual NS changes the polynomial through explicit pressure and
viscous defects. Complete Fourier tangents check that distinction.

A compact unforced family also has the initial derivatives needed for a
short compression-and-return cycle. Its uniform local-time argument is
analytic, not a time simulation or a Lean theorem. See README.md for the
proof, the spectral hypothesis, and the unproved arbitrary-flow budget.
Requires SymPy and the two neighboring exact-check modules.
"""

import json

import sympy as s

import pressure_history_source as fourier
import transverse_strain_history as transverse

zero = transverse.zero
Q, R, W, V, Z = s.symbols('Q R W V Z', real=True)
MOMENTS = (Q, R, W, V, Z)
COEFFICIENT = s.Rational(63, 190)


def polynomial(q, r, w, v, z, c=COEFFICIENT):
    return (q**3-6*r**2-2*c*q*q*w+c*c*q*w*w+6*c*q*z
            - 6*c*r*v+c*c*v*v/2-2*c*c*w*z)


def moment_values(strain, omega):
    return (s.trace(strain**2), s.trace(strain**3), omega.dot(omega),
            omega.dot(strain*omega), omega.dot(strain**2*omega))


def moment_tangent(strain, omega, strain_rate, omega_rate):
    return (2*s.trace(strain*strain_rate), 3*s.trace(strain**2*strain_rate),
            2*omega.dot(omega_rate),
            2*omega_rate.dot(strain*omega)+omega.dot(strain_rate*omega),
            2*omega_rate.dot(strain**2*omega)
            + omega.dot((strain_rate*strain+strain*strain_rate)*omega))


def moment_defects(strain, omega, error, diffusion):
    return (2*s.trace(strain*error), 3*s.trace(strain**2*error),
            2*omega.dot(diffusion),
            omega.dot(error*omega)+2*diffusion.dot(strain*omega),
            omega.dot((strain*error+error*strain)*omega)
            + 2*diffusion.dot(strain**2*omega))


def reference_rates(a=s.Rational(5, 7), b=s.Rational(3, 20)):
    return (-2*a*R-2*b*V, -a*Q**2/2-3*b*Z+b*W*Q, 2*V,
            (2-a)*Z+a*Q*W/3-2*b*W**2/3,
            (1-a/3)*Q*V+2*(1-a)*R*W/3-4*b*W*V/3)


def invariant_rate(values, rates):
    subst = dict(zip(MOMENTS, values))
    poly = polynomial(*MOMENTS)
    return s.factor(sum(s.diff(poly, x).subs(subst)*v for x, v in zip(MOMENTS, rates)))


def check_invariant_and_defects():
    a, b = s.symbols('a b', real=True)
    poly = polynomial(*MOMENTS, c=6*b/(a+2))
    zero(sum(s.diff(poly, x)*rate for x, rate in zip(MOMENTS, reference_rates(a, b))),
         'general comparison invariant')

    sigma, d, e, z1, z2, amplitude = s.symbols('sigma d e z1 z2 amplitude', real=True)
    strain = s.Matrix([[-sigma/2+d, e, z1], [e, -sigma/2-d, z2], [z1, z2, sigma]])
    omega = s.Matrix([0, 0, amplitude])
    strain_rate = transverse.reference_strain_rate(strain, omega)
    omega_rate = strain*omega
    values = dict(zip(MOMENTS, moment_values(strain, omega)))
    base_rates = moment_tangent(strain, omega, strain_rate, omega_rate)
    for actual, predicted in zip(base_rates, reference_rates()):
        zero(actual-predicted.subs(values), 'matrix comparison moment equation')

    e11, e22, e12, e13, e23 = s.symbols('e11 e22 e12 e13 e23', real=True)
    error = s.Matrix([[e11, e12, e13], [e12, e22, e23], [e13, e23, -e11-e22]])
    diffusion = s.Matrix(s.symbols('f1 f2 f3', real=True))
    full_rates = moment_tangent(strain, omega, strain_rate+error, omega_rate+diffusion)
    defects = moment_defects(strain, omega, error, diffusion)
    for total, base, defect in zip(full_rates, base_rates, defects):
        zero(total-base-defect, 'actual moment defect with moving direction')


def check_eigen_certificate():
    a, b, x, y, z = s.symbols('a b x y z', nonnegative=True)
    eigenvalues = ((2*a+b)/3, (b-a)/3, -(a+2*b)/3)
    q = sum(v*v for v in eigenvalues)
    r = sum(v**3 for v in eigenvalues)
    w = x+y+z
    v = sum(t*mass for t, mass in zip(eigenvalues, (x, y, z)))
    zz = sum(t*t*mass for t, mass in zip(eigenvalues, (x, y, z)))
    h = a+b
    certificate = (h*h*(2*a*b-y)**2/2+h*(b*x+a*z)*(2*a*b+y)+(b*x-a*z)**2/2)
    zero(polynomial(q, r, w, v, zz, c=1)-certificate,
         'nonnegative ordered-eigenframe certificate')
    zero(zz*w-v*v-(a*a*x*y+b*b*y*z+h*h*x*z), 'spectral variance numerator')

    # The spectral hypothesis cannot be discarded. Vorticity becomes weak
    # in this family while the directional turning numerator stays nonzero.
    beta = s.symbols('beta', positive=True)
    weak = {a: 1, b: beta, x: 2*beta, y: 2*beta, z: 0}
    zero(polynomial(q, r, w, v, zz, c=1).subs(weak)-8*beta**3-10*beta**4,
         'weak-vorticity invariant degeneration')
    zero((v/w).subs(weak)-(1+2*beta)/6, 'weak-vorticity directional strain')
    zero(((zz*w-v*v)/w**2).subs(weak)-s.Rational(1, 4),
         'weak-vorticity nonalignment')

    # These identities are the algebraic part of the elementary inequality
    # t*variance^2 <= 8*H when 0<=t<=1, r+s=1 and x+y+z=1.
    # The order estimates and their hypotheses are given in the derivation.
    t, rr, ss, xx, yy, zz = s.symbols('t rr ss xx yy zz', nonnegative=True)
    u = xx+zz
    ell = ss*xx-rr*zz
    mass = ss*xx+rr*zz
    dd = 2*t*rr*ss
    hh = (dd-yy)**2+ell**2+2*mass*(dd+yy)
    zero((xx*zz-rr*ss*u**2-(ss-rr)*u*ell+ell**2).subs(ss, 1-rr),
         'outer-mass identity')
    zero((mass-rr*ss*u-ss*ss*xx-rr*rr*zz).subs(ss, 1-rr),
         'weighted-mass positivity')
    zero(hh-((dd-yy)**2+ell**2+4*t*rr*ss*mass+2*mass*yy),
         'coercivity certificate decomposition')


def check_compact_cycle():
    sigma = s.symbols('sigma', real=True)
    strain = s.Matrix([[-sigma/2, 0, 1], [0, -sigma/2, 0], [1, 0, sigma]])
    omega = s.Matrix([0, 0, 4])
    pressure = transverse.reference_pressure(strain, omega)
    omega_rate = strain*omega
    # The datum is linear in a ball. There omega_t is spatially constant,
    # so the initial material derivative of nu*Delta omega also vanishes.
    # The actual second material vorticity derivative is therefore -P omega.
    omega_second = -pressure*omega
    amplitude_second = ((omega_rate.dot(omega_rate)+omega.dot(omega_second))/4
                        - omega.dot(omega_rate)**2/64)
    zero(amplitude_second-4*(s.Rational(9, 14)*sigma**2+s.Rational(17, 105)),
         'actual compact amplitude acceleration')
    middle = strain.subs(sigma, 0)
    if middle.eigenvals() != {s.Integer(-1): 1, s.Integer(0): 1, s.Integer(1): 1}:
        raise ArithmeticError('unexpected compact central spectrum')
    if not COEFFICIENT*16 > 4:
        raise ArithmeticError('compact cycle must lie strictly inside the spectral regime')
    return {'Omega_initial': '4', 'Omega_rate_initial': '4*sigma',
            'Omega_second_initial': '4*((9/14)*sigma^2+17/105)',
            'central_diameter_squared': '4', 'c_Omega_squared': str(COEFFICIENT*16),
            'central_invariant': str(s.factor(polynomial(*moment_values(middle, omega)))),
            'return_time_for_sigma_minus_epsilon': '(210/17)*epsilon+O(epsilon^2)'}


def check_actual_fourier(sign, nu):
    m = fourier
    u = [m.scale(sign, q) for q in m.fixture()]
    b = m.jac(u)
    p = m.green(m.trace(m.matmul(b, b)))
    ut = [m.add(m.scale(nu, m.lap(u[i])), m.scale(-1, m.adv(u, u[i])),
                m.scale(-1, m.diff(p, i))) for i in range(3)]
    bt = m.jac(ut)
    evaluate = lambda field: s.Rational(str(m.evaluate(field)))
    bv = s.Matrix([[evaluate(q) for q in row] for row in b])
    strain = (bv+bv.T)/2
    omega_fields = m.curl(u)
    omega = s.Matrix(list(map(evaluate, omega_fields)))
    material_b = s.Matrix([[evaluate(m.add(bt[i][j], m.adv(u, b[i][j])))
                            for j in range(3)] for i in range(3)])
    strain_rate = (material_b+material_b.T)/2
    omega_rate = s.Matrix([evaluate(m.add(q, m.adv(u, w)))
                           for q, w in zip(m.curl(ut), omega_fields)])
    pressure = s.Matrix([[evaluate(q) for q in row] for row in m.hess(p)])
    viscosity = s.Rational(str(nu))
    viscous_strain = viscosity*s.Matrix([
        [evaluate(m.lap(m.add(b[i][j], b[j][i])))/2 for j in range(3)] for i in range(3)])
    diffusion = viscosity*s.Matrix([evaluate(m.lap(w)) for w in omega_fields])
    error = transverse.reference_pressure(strain, omega)-pressure+viscous_strain
    values = moment_values(strain, omega)
    direct = invariant_rate(values, moment_tangent(strain, omega, strain_rate, omega_rate))
    defect = invariant_rate(values, moment_defects(strain, omega, error, diffusion))
    zero(direct-defect, 'full actual Fourier invariant defect')
    return {'velocity_sign': sign, 'nu': str(nu), 'invariant': str(s.factor(polynomial(*values))),
            'material_invariant_rate': str(direct)}


if __name__ == '__main__':
    check_invariant_and_defects()
    check_eigen_certificate()
    cases = [check_actual_fourier(sign, nu) for sign in (1, -1)
             for nu in (fourier.QQ_I(0), fourier.QQ_I(1)/100, fourier.QQ_I(2)/7)]
    if not s.Rational(cases[1]['material_invariant_rate']) > 0:
        raise ArithmeticError('positive-viscosity datum must increase the physical invariant')
    if not s.Rational(cases[4]['material_invariant_rate']) < 0:
        raise ArithmeticError('reversed datum must have opposite initial invariant rate')
    print(json.dumps({'status': 'all exact checks passed', 'compact_cycle': check_compact_cycle(),
                      'actual_fourier_checks': cases,
                      'scope': 'conditional comparison invariant; actual signed defects retained'}, indent=2))
