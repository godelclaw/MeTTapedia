#!/usr/bin/env python3
"""Transverse strain, moving vorticity direction, and compression renewal.

Exact angular integration gives the initial pressure of a smooth compact
whole-space strain/swirl family. Its local unforced tangent replenishes a
normalized transverse resource during compression. A separate comparison
inequality bounds one extension episode; persistence of the comparison
pressure is not assumed for actual NS.

The moving-direction identities retain arbitrary actual pressure and both
viscous Laplacians. They are also checked against complete finite Fourier
NS sources, using pressure_history_source.py. No Galerkin time evolution,
global regularity conclusion, or Lean certification is asserted here.
Requires SymPy. Derivations and the analytic local-flow bridge: README.md.
"""

import json

import sympy as s

import pressure_history_source as fourier


def zero(expr, label):
    value = s.factor(s.together(expr))
    if value != 0:
        raise ArithmeticError((label, value))


def matrix_zero(matrix, label):
    for value in matrix:
        zero(value, label)


def dev(matrix):
    return matrix-s.trace(matrix)*s.eye(3)/3


def spin(omega):
    x, y, z = omega
    return s.Matrix([[0, -z, y], [z, 0, -x], [-y, x, 0]])/2


def reference_pressure(strain, omega):
    a = spin(omega)
    return (-s.Rational(2, 7)*strain**2
            - s.Rational(5, 21)*s.trace(strain**2)*s.eye(3)
            + omega.dot(omega)*s.eye(3)/5-omega*omega.T/10
            - s.Rational(2, 5)*(strain*a-a*strain))


def reference_strain_rate(strain, omega):
    a = spin(omega)
    return (-s.Rational(5, 7)*dev(strain**2)
            - s.Rational(3, 20)*dev(omega*omega.T)
            + s.Rational(2, 5)*(strain*a-a*strain))


def sphere_average(poly, coordinates):
    """Normalized spherical average of a polynomial, in exact arithmetic."""
    total = 0
    for powers, coefficient in s.Poly(s.expand(poly), *coordinates).terms():
        if any(power % 2 for power in powers):
            continue
        numerator = s.prod(s.factorial2(power-1) for power in powers)
        total += coefficient*numerator/s.factorial2(sum(powers)+1)
    return s.factor(total)


def radial_integral(poly, variables, moments, label):
    total = 0
    for powers, coefficient in s.Poly(poly, *variables).terms():
        if coefficient == 0:
            continue
        if powers not in moments:
            raise ArithmeticError((label, 'uncancelled radial term', powers))
        total += coefficient*moments[powers]
    return s.factor(total)


def check_compact_pressure():
    x, y, z, p, q = s.symbols('x y z p q', real=True)
    n = s.Matrix([x, y, z])
    strain = s.diag(p, q, -p-q)
    c, d, e, integral = s.symbols('c d e integral', real=True)

    # The vector potential is -(chi/3) x cross Sx. Use chi=F(r^2)
    # while differentiating, so no square-root simplifications are needed.
    radius2 = n.dot(n)
    chi = s.Function('F')(radius2)
    dchi = s.diff(chi, x)/(2*x)
    potential = -chi*n.cross(strain*n)/3
    velocity = s.Matrix([s.diff(potential[2], y)-s.diff(potential[1], z),
                         s.diff(potential[0], z)-s.diff(potential[2], x),
                         s.diff(potential[1], x)-s.diff(potential[0], y)])
    expected = ((chi+2*radius2*dchi/3)*strain*n
                - 2*dchi*n*n.dot(strain*n)/3)
    matrix_zero(velocity-expected, 'compact strain vector potential')
    zero(sum(s.diff(velocity[i], n[i]) for i in range(3)),
         'compact strain incompressibility')

    d2chi = s.diff(dchi, x)/(2*x)
    actual_d = 2*radius2*dchi
    actual_e = actual_d+4*radius2**2*d2chi
    sn = strain*n
    quadratic = n.dot(sn)
    actual_gradient = ((chi+actual_d/3)*strain
                       + (4*actual_d+actual_e)*sn*n.T/(3*radius2)
                       - actual_d*s.eye(3)*quadratic/(3*radius2)
                       - (actual_e-actual_d)*n*n.T*quadratic/(3*radius2**2)
                       - 2*actual_d*n*sn.T/(3*radius2))
    matrix_zero(velocity.jacobian(n)-actual_gradient, 'compact strain gradient')

    # At radius r, n is a unit vector and c=chi, d=r chi', e=r^2 chi''.
    sn = strain*n
    angular_strain = n.dot(sn)
    gradient = ((c+d/3)*strain+(4*d+e)*sn*n.T/3
                - d*s.eye(3)*angular_strain/3
                - (e-d)*n*n.T*angular_strain/3-2*d*n*sn.T/3)
    source = s.trace(gradient**2)
    moments = {(1, 1, 0): -s.Rational(1, 2),
               (1, 0, 1): s.Rational(1, 2)-integral,
               (0, 2, 0): integral, (0, 1, 1): -integral}
    background = s.zeros(3)
    for i in range(3):
        for j in range(3):
            angular_kernel = 3*n[i]*n[j]-(1 if i == j else 0)
            angular = sphere_average(angular_kernel*source, n)
            contact = -s.trace(strain**2)/3 if i == j else 0
            background[i, j] = contact+radial_integral(
                angular, (c, d, e), moments, 'background pressure')
    predicted = (-s.Rational(2, 7)*strain**2
                 - s.Rational(5, 21)*s.trace(strain**2)*s.eye(3))
    matrix_zero(background-predicted, 'full background pressure matrix')

    # Diagonalizing S loses no generality. The core rotation axis remains
    # arbitrary. Its radial support lies wholly within the linear background.
    omega = s.Matrix(s.symbols('omega1 omega2 omega3', real=True))
    a = spin(omega)
    psi, radial_derivative = s.symbols('psi radial_derivative', real=True)
    core_gradient = psi*a+radial_derivative*(a*n)*n.T
    swirl_source = s.trace(core_gradient**2)
    cross_source = 2*s.trace(strain*core_gradient)
    swirl, cross = s.zeros(3), s.zeros(3)
    for i in range(3):
        for j in range(3):
            kernel = 3*n[i]*n[j]-(1 if i == j else 0)
            contact = -s.trace(a*a)/3 if i == j else 0
            swirl[i, j] = contact+radial_integral(
                sphere_average(kernel*swirl_source, n),
                (psi, radial_derivative), {(1, 1): -s.Rational(1, 2)},
                'swirl pressure')
            cross[i, j] = radial_integral(
                sphere_average(kernel*cross_source, n),
                (psi, radial_derivative), {(0, 1): -1}, 'cross pressure')
    matrix_zero(swirl-omega.dot(omega)*s.eye(3)/5+omega*omega.T/10,
                'core swirl pressure matrix')
    matrix_zero(cross+s.Rational(2, 5)*(strain*a-a*strain),
                'core cross pressure matrix')
    matrix_zero(background+swirl+cross-reference_pressure(strain, omega),
                'actual compact initial pressure')
    return {'background_diagonal': [str(s.factor(background[i, i])) for i in range(3)],
            'scope': 'smooth radial cutoffs equal to one at the core; nested supports'}


def invariants(strain, omega, strain_rate, omega_rate):
    """Differentiate normalized invariants without choosing a moving frame."""
    amplitude2 = omega.dot(omega)
    sigma = omega.dot(strain*omega)/amplitude2
    chi = omega.dot(strain**2*omega)/amplitude2
    g = chi-sigma**2
    k = s.trace(strain**2)/2-s.Rational(3, 4)*sigma**2+s.Rational(15, 4)*g
    sigma_rate = (2*omega_rate.dot(strain*omega)
                  + omega.dot(strain_rate*omega)
                  - 2*sigma*omega.dot(omega_rate))/amplitude2
    chi_rate = (2*omega_rate.dot(strain**2*omega)
                + omega.dot((strain_rate*strain+strain*strain_rate)*omega)
                - 2*chi*omega.dot(omega_rate))/amplitude2
    g_rate = chi_rate-2*sigma*sigma_rate
    k_rate = (s.trace(strain*strain_rate)-s.Rational(3, 2)*sigma*sigma_rate
              + s.Rational(15, 4)*g_rate)
    return tuple(map(s.factor, (sigma, g, k, sigma_rate, g_rate, k_rate)))


def defects(strain, omega, error, diffusion):
    amplitude2 = omega.dot(omega)
    sigma = omega.dot(strain*omega)/amplitude2
    z = strain*omega-sigma*omega
    epsilon = omega.dot(diffusion)/amplitude2
    eta = diffusion-epsilon*omega
    f_sigma = omega.dot(error*omega)/amplitude2+2*eta.dot(z)/amplitude2
    f_k = (s.trace(strain*error)
           - s.Rational(3, 2)*sigma*omega.dot(error*omega)/amplitude2
           + s.Rational(15, 2)*z.dot(error*omega)/amplitude2
           + s.Rational(15, 2)*eta.dot(strain*z)/amplitude2
           - s.Rational(21, 2)*sigma*eta.dot(z)/amplitude2)
    return tuple(map(s.factor, (epsilon, f_sigma, f_k)))


def check_moving_direction():
    sigma, d, e, z1, z2 = s.symbols('sigma d e z1 z2', real=True)
    amplitude = s.symbols('amplitude', positive=True)
    strain = s.Matrix([[-sigma/2+d, e, z1], [e, -sigma/2-d, z2], [z1, z2, sigma]])
    omega = s.Matrix([0, 0, amplitude])
    rate = reference_strain_rate(strain, omega)
    _, g, k, sigma_rate, g_rate, k_rate = invariants(strain, omega, rate, strain*omega)
    zero(g-z1*z1-z2*z2, 'nonalignment square')
    zero(k-d*d-e*e-s.Rational(19, 4)*g, 'nonnegative transverse decomposition')
    mixed = d*(z1*z1-z2*z2)+2*e*z1*z2
    delta2_rate = s.trace(strain*rate)-s.Rational(3, 2)*sigma*sigma_rate-g_rate
    zero(g_rate+s.Rational(26, 7)*sigma*g-s.Rational(4, 7)*mixed,
         'moving-direction transfer')
    zero(delta2_rate-s.Rational(10, 7)*sigma*(d*d+e*e)+s.Rational(19, 7)*mixed,
         'transverse anisotropy transfer')
    zero(k_rate-s.Rational(10, 7)*sigma*k+s.Rational(171, 7)*sigma*g,
         'positive transverse resource transfer')
    zero(sigma_rate+s.Rational(5, 14)*sigma**2-s.Rational(10, 21)*k+g/2+amplitude**2/10,
         'strain law with transverse resource')

    e11, e22, e12, e13, e23 = s.symbols('e11 e22 e12 e13 e23', real=True)
    error = s.Matrix([[e11, e12, e13], [e12, e22, e23], [e13, e23, -e11-e22]])
    diffusion = s.Matrix(s.symbols('f1 f2 f3', real=True))
    _, _, _, actual_sigma_rate, _, actual_k_rate = invariants(
        strain, omega, rate+error, strain*omega+diffusion)
    epsilon, f_sigma, f_k = defects(strain, omega, error, diffusion)
    zero(actual_sigma_rate-sigma_rate-f_sigma, 'actual strain defect')
    zero(actual_k_rate-k_rate-f_k, 'actual transverse defect')
    zero(actual_k_rate-s.Rational(10, 7)*(sigma+epsilon)*k
         + s.Rational(171, 7)*sigma*g-f_k+s.Rational(10, 7)*epsilon*k,
         'normalized transverse history')

    w, kappa = s.symbols('w kappa', nonnegative=True)
    barrier = 2090*w**5*sigma**2+154*w**19-s.Rational(8360, 9)*kappa*w**15
    sigma_model = -s.Rational(5, 14)*sigma**2+s.Rational(10, 21)*k-g/2-w**14/10
    barrier_rate = s.diff(barrier, w)*sigma*w/7+s.diff(barrier, sigma)*sigma_model
    zero(barrier_rate-s.Rational(41800, 21)*sigma*w**5*(k-kappa*w**10)
         + 2090*sigma*w**5*g, 'extension episode barrier')
    return {'transfer_coefficient': '171/7', 'barrier_coefficient': '8360/9'}


def check_compact_renewal():
    strain = s.Matrix([[s.Rational(1, 2), 0, 1], [0, s.Rational(1, 2), 0], [1, 0, -1]])
    omega = s.Matrix([0, 0, 1])
    gradient = strain+spin(omega)
    pressure = reference_pressure(strain, omega)
    # The datum is linear in a ball, so all local Laplacians here vanish.
    # Compute the material tangent directly from the actual pressure jet.
    gradient_rate = -gradient**2-pressure
    strain_rate = (gradient_rate+gradient_rate.T)/2
    omega_rate = s.Matrix([gradient_rate[2, 1]-gradient_rate[1, 2],
                           gradient_rate[0, 2]-gradient_rate[2, 0],
                           gradient_rate[1, 0]-gradient_rate[0, 1]])
    matrix_zero(omega_rate-strain*omega, 'actual compact vorticity tangent')
    matrix_zero(strain_rate-reference_strain_rate(strain, omega), 'zero initial pressure defect')
    zero(s.trace(pressure)+s.trace(gradient**2), 'compact pressure Poisson trace')
    sigma, g, k, sigma_rate, _, k_rate = invariants(strain, omega, strain_rate, omega_rate)
    kappa_rate = k_rate-s.Rational(10, 7)*sigma*k
    zero(kappa_rate-s.Rational(171, 7), 'strict compact unforced renewal')
    return {'S': str(strain), 'omega': str(omega), 'P': str(pressure),
            'omega_material_rate': str(omega_rate), 'G': str(g), 'K': str(k),
            'sigma_rate': str(sigma_rate), 'K_rate': str(k_rate), 'kappa_rate': str(kappa_rate)}


def check_actual_fourier(nu):
    m = fourier
    u = m.fixture()
    b = m.jac(u)
    p = m.green(m.trace(m.matmul(b, b)))
    ut = [m.add(m.scale(nu, m.lap(u[i])), m.scale(-1, m.adv(u, u[i])),
                m.scale(-1, m.diff(p, i))) for i in range(3)]
    bt = m.jac(ut)
    evaluate = lambda field: s.Rational(str(m.evaluate(field)))
    bv = s.Matrix([[evaluate(field) for field in row] for row in b])
    strain = (bv+bv.T)/2
    omega_fields = m.curl(u)
    omega = s.Matrix(list(map(evaluate, omega_fields)))
    material_b = s.Matrix([[evaluate(m.add(bt[i][j], m.adv(u, b[i][j])))
                            for j in range(3)] for i in range(3)])
    strain_rate = (material_b+material_b.T)/2
    omega_rate = s.Matrix([evaluate(m.add(q, m.adv(u, w)))
                           for q, w in zip(m.curl(ut), omega_fields)])
    viscosity = s.Rational(str(nu))
    diffusion = viscosity*s.Matrix([evaluate(m.lap(w)) for w in omega_fields])
    matrix_zero(omega_rate-strain*omega-diffusion, 'full Fourier vorticity equation')
    pressure = s.Matrix([[evaluate(field) for field in row] for row in m.hess(p)])
    viscous_strain = viscosity*s.Matrix([
        [evaluate(m.lap(m.add(b[i][j], b[j][i])))/2 for j in range(3)] for i in range(3)])
    error = reference_pressure(strain, omega)-pressure+viscous_strain
    matrix_zero(strain_rate-reference_strain_rate(strain, omega)-error,
                'full Fourier pressure and viscous strain defects')
    sigma, g, k, sigma_rate, _, k_rate = invariants(strain, omega, strain_rate, omega_rate)
    epsilon, f_sigma, f_k = defects(strain, omega, error, diffusion)
    zero(sigma_rate+s.Rational(5, 14)*sigma**2-s.Rational(10, 21)*k
         + g/2+omega.dot(omega)/10-f_sigma, 'actual Fourier strain/resource law')
    zero(k_rate-s.Rational(10, 7)*sigma*k+s.Rational(171, 7)*sigma*g-f_k,
         'actual Fourier transverse history law')
    return {'nu': str(nu), 'G': str(g), 'K': str(k),
            'normalized_rate_times_Omega_10_over_7':
                str(s.factor(k_rate-s.Rational(10, 7)*(sigma+epsilon)*k))}


if __name__ == '__main__':
    print(json.dumps({'status': 'all exact checks passed',
                      'compact_pressure': check_compact_pressure(),
                      'moving_direction': check_moving_direction(),
                      'compact_renewal': check_compact_renewal(),
                      'actual_fourier_checks': [check_actual_fourier(fourier.QQ_I(0)),
                                                check_actual_fourier(fourier.QQ_I(2)/7)],
                      'scope': 'analytic NS bridge and exact algebra; no Lean certification'}, indent=2))
