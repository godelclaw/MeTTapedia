#!/usr/bin/env python3
"""Inherited transported frames and their ordinary-vorticity conversion.

The fast profile, pressure projection and local physical derivatives are
checked symbolically. Uniform release error and actual solution intervals
are analytic in README.md, not certified by this script.
"""

import json
import sympy as s


def zero(expr, label):
    value = s.simplify(s.trigsimp(s.expand(expr)))
    if value != 0:
        raise AssertionError((label, value))


def matrix_zero(matrix, label):
    for i, entry in enumerate(matrix):
        zero(entry, (label, i))


def fast_profile():
    tau = s.symbols('tau', nonnegative=True)
    theta, eps, v1, v2 = s.symbols('theta epsilon v1 v2', real=True)
    nu = s.symbols('nu', positive=True)
    V, e3 = s.Matrix([v1, v2, 0]), s.Matrix([0, 0, 1])
    decay = s.exp(-nu*tau)
    b = -eps*tau*decay*s.sin(theta)
    I0 = (1-(1+2*nu*tau)*decay**2)/(4*nu**2)
    I2 = ((2*nu*tau-1)*decay**2+decay**4)/(4*nu**2)
    c = eps**2*(I0-I2*s.cos(2*theta))
    M = s.eye(3)+b*(V*e3.T+e3*V.T)+c*V*V.T
    B = -eps*decay*s.sin(theta)*V*e3.T
    F = s.eye(3)+b*V*e3.T
    matrix_zero(F.diff(tau)-nu*F.diff(theta, 2)-B*F,
                'the complete fast first-moment frame equation')
    matrix_zero(M.diff(tau)-nu*M.diff(theta, 2)-B*M-M*B.T,
                'the complete fast frame equation')
    matrix_zero(M-F*F.T-(c-b*b)*V*V.T,
                'frame covariance is retained beyond its mean')
    matrix_zero(M.subs(tau, 0)-s.eye(3), 'original frame initialization')
    zero((c-b*b).diff(tau)-nu*(c-b*b).diff(theta, 2)-2*nu*b.diff(theta)**2,
         'positive covariance source in the fast frame')
    zero(I0+I2-(1-decay**2)**2/(4*nu**2), 'finite frame trace allowance')
    zero(s.diff(s.exp(4*nu*tau)*I2, tau)-tau*s.exp(2*nu*tau),
         'nonnegative integral representation of I2')
    zero(s.limit(b, tau, s.oo), 'the off-diagonal channel decays')
    zero(s.limit(c, tau, s.oo)-eps**2/(4*nu**2), 'the parent memory remains')
    zero(s.integrate(decay, (tau, 0, s.oo))-1/nu,
         'the fast parent has a finite integrated strain scale')
    bs, cs = s.symbols('bs cs', real=True)
    Ms = s.eye(3)+bs*(V*e3.T+e3*V.T)+cs*V*V.T
    zero(Ms.det()-1-(cs-bs**2)*V.dot(V), 'frame determinant retains covariance')
    beta = s.symbols('beta', positive=True)
    inherited = s.eye(3)+beta*V*V.T
    inverse = s.eye(3)-beta*V*V.T/(1+beta*V.dot(V))
    matrix_zero(inherited*inverse-s.eye(3), 'exact inherited inverse metric')


def physical_fixture():
    x, y, z = s.symbols('x y z', real=True)
    coords = (x, y, z)
    V = s.cos(z)*s.Matrix([s.cos(y), -s.cos(x), 0])
    phi = s.sin(x)*s.sin(y)
    pressure = -phi/2-phi*s.cos(2*z)/6
    B = V.jacobian(coords)*V
    w = -s.Matrix([s.cos(2*z)*s.diff(phi, x), s.cos(2*z)*s.diff(phi, y),
                   s.sin(2*z)*phi])/3
    grad_p = s.Matrix([s.diff(pressure, c) for c in coords])
    matrix_zero(w+B+grad_p, 'full source retains the canonical pressure')
    zero(s.trace(V.jacobian(coords)), 'horizontal parent is solenoidal')
    zero(s.trace(w.jacobian(coords)), 'released descendant is solenoidal')
    lap = lambda field: field.applyfunc(lambda a: sum(s.diff(a, c, 2) for c in coords))
    curl = lambda field: s.Matrix([s.diff(field[2], y)-s.diff(field[1], z),
                                    s.diff(field[0], z)-s.diff(field[2], x),
                                    s.diff(field[1], x)-s.diff(field[0], y)])
    zeta = curl(w)
    expected = s.sin(2*z)*s.Matrix([-s.sin(x)*s.cos(y), s.cos(x)*s.sin(y), 0])
    matrix_zero(zeta-expected, 'actual curl of the pressure-projected descendant')
    zero(sum(s.diff(pressure, c, 2) for c in coords)+s.trace(B.jacobian(coords)),
         'canonical pressure Poisson equation')

    beta = s.symbols('beta', positive=True)
    Mstar = s.eye(3)+beta*V*V.T
    Qstar = s.eye(3)-beta*V*V.T/(1+beta*V.dot(V))
    qz = (zeta.T*Qstar*zeta)[0]
    h = s.symbols('h', real=True)
    diagonal = {x: h, y: h, z: h}
    zero((qz*(1+2*beta*s.cos(h)**4)-zeta.dot(zeta)).subs(diagonal),
         'sharp inherited directional factor on the diagonal')

    # Viscosity one, epsilon=16: beta=epsilon^2/4=64 and U=64w.
    u, omega = 64*w, 64*zeta
    Mfield = Mstar.subs(beta, 64)
    point = {x: s.pi/6, y: s.pi/6, z: s.pi/6}
    at = lambda field: field.applyfunc(lambda value: s.simplify(value.subs(point)))
    U, om, M = at(u), at(omega), at(Mfield)
    Q = M.inv()
    grad_u = at(u.jacobian(coords))
    grad_om = [at(omega.diff(c)) for c in coords]
    grad_M = [at(Mfield.diff(c)) for c in coords]
    lap_om, lap_M = at(lap(omega)), at(lap(Mfield))
    # Material derivatives supplied by the actual unforced vorticity/frame PDEs.
    Dt_om = lap_om+grad_u*om
    Dt_M = lap_M+grad_u*M+M*grad_u.T
    norm = om.dot(om)
    q = (om.T*Q*om)[0]
    norm_rate = 2*om.dot(Dt_om)
    q_rate = 2*(om.T*Q*Dt_om)[0]-(om.T*Q*Dt_M*Q*om)[0]
    factor = norm/q
    factor_rate = norm_rate/q-norm*q_rate/q**2
    diffusion = sum(((dom-dM*Q*om).T*Q*(dom-dM*Q*om))[0]
                    for dom, dM in zip(grad_om, grad_M))
    lap_q = 0
    adv_q = 0
    for c, dom, dM, uj in zip(coords, grad_om, grad_M, U):
        dd_om, dd_M = at(omega.diff(c, 2)), at(Mfield.diff(c, 2))
        dQ = -Q*dM*Q
        ddQ = 2*Q*dM*Q*dM*Q-Q*dd_M*Q
        lap_q += (2*(om.T*Q*dd_om)[0]+2*(dom.T*Q*dom)[0]
                  +4*(om.T*dQ*dom)[0]+(om.T*ddQ*om)[0])
        adv_q += uj*(2*(om.T*Q*dom)[0]+(om.T*dQ*om)[0])
    zero(q_rate-lap_q+2*diffusion, 'unforced weighted-vorticity diffusion identity')
    zero(norm-1152, 'ordinary vorticity at the inherited state')
    zero(q-s.Rational(1152, 73), 'weighted vorticity at the inherited state')
    zero(factor-73, 'actual inherited conversion factor')
    zero(norm_rate-10752, 'ordinary vorticity increases along the fluid')
    zero(q_rate+s.Rational(760320, 5329), 'weighted vorticity decreases along the fluid')
    zero(factor_rate-s.Rational(4024, 3), 'inherited directional conversion worsens')
    origin = {x: 0, y: 0, z: 0}
    at_origin = lambda field: field.applyfunc(lambda value: s.simplify(value.subs(origin)))
    M0, B0 = at_origin(Mfield), at_origin(u.jacobian(coords))
    matrix_zero(at_origin(u), 'transport vanishes at the frame maximum')
    M0_rate = at_origin(lap(Mfield))+B0*M0+M0*B0.T
    axis = s.Matrix([1, -1, 0])
    maximum = (axis.T*M0*axis)[0]/2
    maximum_rate = (axis.T*M0_rate*axis)[0]/2
    zero(maximum-129, 'initial global frame upper bound is attained')
    zero(maximum_rate-4992, 'the inherited frame bound itself subsequently grows')
    return dict(epsilon=16, viscosity=1, inherited_factor=factor,
                ordinary_vorticity_squared=norm, weighted_vorticity_squared=q,
                ordinary_material_rate=norm_rate, weighted_material_rate=q_rate,
                factor_material_rate=factor_rate, covariant_diffusion=diffusion,
                weighted_eulerian_rate=q_rate-adv_q,
                inherited_frame_maximum=maximum, frame_maximum_rayleigh_rate=maximum_rate)


def main():
    fast_profile()
    result = physical_fixture()
    print(json.dumps(dict(status='all exact checks passed', physical_fixture=result,
                          mean_frame_limit='I',
                          inherited_tensor='I + epsilon^2/(4 nu^2) V tensor V',
                          sharp_fixture_conversion_supremum='1 + epsilon^2/(2 nu^2)',
                          scope='exact leading profile and physical derivatives; uniform release and actual intervals analytic'),
                     default=str, indent=2))


if __name__ == '__main__':
    main()
