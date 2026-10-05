#!/usr/bin/env python3
"""Original-energy payment for the actual pressure-deformation source.

Exact reserve algebra, complete NS initial jets and a localized swirl
identity support the analytic argument in README.md. The critical history
bound remains open. No finite-mode evolution or Lean certificate is claimed.
"""

import hashlib
import json
from pathlib import Path

import sympy as s
import pressure_history_source as f
import aged_joint_memory_payment as am
import recent_pressure_reconstruction as wh
import viscous_pressure_regeneration as vd
from rotational_curl_reserve import require, zero


def reserve_algebra():
    R = s.Rational
    zero(R(1, 4)-R(1, 4)/2-R(3, 4)/6, 'velocity L4 interpolation')
    zero(R(1, 4)+R(3, 4)-1, 'pressure time Holder exponents')
    E, nu, h, CS, Z = s.symbols('E nu h C_S Z', positive=True)
    rp = CS**R(3, 4)*(2*nu)**(-R(3, 4))*h**R(1, 4)*E
    negative_rate = s.diff(rp, h)+2*nu*Z*s.diff(rp, E)
    x = s.symbols('x', nonnegative=True)
    common = CS**R(3, 4)*(2*nu)**(-R(3, 4))*E*h**(-R(3, 4))
    zero(negative_rate.subs(Z, E*x**4/(2*nu*h))/common-(R(1, 4)+x**4),
         'remaining pressure reserve has the full energy derivative')
    zero((R(1, 4)+x**4-x**3)
         -(x-1)**2*(3*x*x+2*x+1)/4-x**4/4,
         'positive polynomial pays the pressure norm without a future bound')

    t = s.symbols('t', real=True)
    coords = s.symbols('x0:3', real=True)
    args = (t,)+coords
    q = s.Function('q')(*args)
    u = [s.Function('u'+str(i))(*args) for i in range(3)]
    op = lambda a: s.diff(a, t)+sum(u[i]*s.diff(a, coords[i]) for i in range(3))-nu*sum(s.diff(a, z, 2) for z in coords)
    zero(op(q*q)-2*q*op(q)+2*nu*sum(s.diff(q, z)**2 for z in coords),
         'complete scalar diffusion has the required favorable sign')

    y, r, G, pressure = s.symbols('y r G pressure', positive=True)
    yp = pressure-nu*G/y
    rp_upper = -pressure
    stock = (y+r)**2
    stock_rate = s.diff(stock, y)*yp+s.diff(stock, r)*rp_upper
    zero(stock_rate+2*nu*G+2*nu*G*r/y,
         'completed scalar history stock pays its full gradient diffusion')
    Q = s.symbols('Q', positive=True)
    source_reserve = s.sqrt(E*Q)/(2*nu)
    source_rate = s.diff(source_reserve, E)*(-2*nu*Z)+s.diff(source_reserve, Q)*(-2*nu*G)
    zero(source_rate+(s.sqrt(Q/E)*Z+s.sqrt(E/Q)*G)/2,
         'joint energy and scalar stock pay deformation source magnitude')
    a, b = s.symbols('a b', nonnegative=True)
    zero((a*a+b*b)/2-a*b-(a-b)**2/2, 'geometric-mean payment')
    return {
        'pressure': '||p_hi||2 <= C_S^(3/4) E^(1/4) Z^(3/4)',
        'remaining_pressure': 'r_p=C_S^(3/4)(2nu)^(-3/4)(H-t)^(1/4)E(t); -r_p_prime>=||p_hi||2',
        'scalar_stock': 'Q=(||q||2+r_p)^2; Q_prime+2nu||grad q||2^2<=0',
        'source_reserve': 'R_F=sqrt(E Q)/(2nu); R_F_prime+||(grad u)^T grad q||1<=0',
        'initial_allowance': 'R_F(0)=C_S^(3/4) H^(1/4) E0^(3/2)/(2nu)^(7/4)',
        'zero_sets': 'The norm and geometric-mean derivatives are interpreted by positive regularization and passage to the limit; the analytic proof states this explicitly.',
        'OPEN': 'An L1 space-time source payment is not the L3_t L9_x solenoidal impulse payment needed for continuation.'}


def source(u, gradient):
    return [f.add(*(f.mul(f.diff(u[j], i), gradient[j]) for j in range(3))) for i in range(3)]


def full_source_evolution():
    t, nu = s.symbols('t nu', real=True)
    x = s.symbols('x0:3', real=True)
    args = (t,)+x
    u = s.Matrix([s.Function('u'+str(i))(*args) for i in range(3)])
    p, phi, q = [s.Function(a)(*args) for a in ('p', 'p_hi', 'q')]
    grad = lambda a: s.Matrix([s.diff(a, z) for z in x])
    op = lambda a: s.diff(a, t)+sum(u[i]*s.diff(a, x[i]) for i in range(3))-nu*sum(s.diff(a, z, 2) for z in x)
    U, g = u.jacobian(x), grad(q)
    F = U.T*g
    ru = u.applyfunc(op)+grad(p)
    rq = op(q)-phi
    cross = sum((U.diff(z).T*g.diff(z) for z in x), s.zeros(3, 1))
    predicted = U.T*grad(phi)-s.hessian(p, x)*g-2*U.T*U.T*g-2*nu*cross
    residual = ru.jacobian(x).T*g+U.T*grad(rq)
    for i in range(3):
        zero(s.expand(op(F[i])-predicted[i]-residual[i]),
             'complete material source equation, including the cross diffusion')
    return {'equation': 'scriptL F=(grad u)^T grad p_hi-(Hess p)grad q-2[(grad u)^T]^2 grad q-2nu sum_k (partial_k grad u)^T partial_k grad q',
            'retained': 'Canonical full pressure Hessian, high pressure input, changing deformation and complete product-diffusion term; no sign is assumed for these terms.'}


def physical_jet(u, name, nu, delayed):
    p = f.tensor_pressure(f.tensor(u, u))
    evolve = lambda a: f.add(f.scale(nu, f.lap(a)), f.scale(-1, f.adv(u, a)))
    ut = [f.add(evolve(u[i]), f.scale(-1, f.diff(p, i))) for i in range(3)]
    pt = f.tensor_pressure(am.matrix_add(f.tensor(ut, u), f.tensor(u, ut)))
    utt = [f.add(evolve(ut[i]), f.scale(-1, f.adv(ut, u[i])), f.scale(-1, f.diff(pt, i))) for i in range(3)]
    ptt = f.tensor_pressure(am.matrix_add(am.matrix_add(f.tensor(utt, u), f.tensor(u, utt)),
                                         [[f.scale(2, a) for a in row] for row in f.tensor(ut, ut)]))
    for label, field in (('u', u), ('u_t', ut), ('u_tt', utt)):
        f.equal(f.trace(f.jac(field)), {}, 'full NS solenoidal '+label)
    p0, p1, p2 = map(am.high, (p, pt, ptt))
    g0, g1, g2 = map(f.grad, (p0, p1, p2))
    A1 = lambda a: f.scale(-1, f.adv(ut, a))
    I2 = [f.add(g1[i], evolve(g0[i])) for i in range(3)]
    I3 = [f.add(g2[i], evolve(I2[i]), f.scale(2, A1(g0[i]))) for i in range(3)]
    q2 = f.add(p1, evolve(p0))
    q3 = f.add(p2, evolve(q2), f.scale(2, A1(p0)))
    d2 = source(u, g0)
    d3 = wh.addv([evolve(a) for a in d2], wh.scalev(2, source(ut, g0)), source(u, f.grad(q2)))
    wh.same_vectors(wh.addv(I2, wh.scalev(-1, f.grad(q2))), d2, 'second full deformation return')
    wh.same_vectors(wh.addv(I3, wh.scalev(-1, f.grad(q3))), d3, 'third full deformation return retains changing parents and diffusion')
    wh.same_vectors(wh.project(I3), wh.project(d3), 'third-order projected reconstruction')

    # Taking curl cancels second velocity derivatives, but not Hessian geometry.
    Hp = f.hess(p1 if delayed else p0)
    U = f.jac(u)
    curl_source = [f.add(*(f.add(f.mul(U[j][2], Hp[j][1]), f.scale(-1, f.mul(U[j][1], Hp[j][2]))) for j in range(3))),
                   f.add(*(f.add(f.mul(U[j][0], Hp[j][2]), f.scale(-1, f.mul(U[j][2], Hp[j][0]))) for j in range(3))),
                   f.add(*(f.add(f.mul(U[j][1], Hp[j][0]), f.scale(-1, f.mul(U[j][0], Hp[j][1]))) for j in range(3)))]
    selected = source(u, f.grad(p1 if delayed else p0))
    wh.same_vectors(f.curl(selected), curl_source, 'curl source retains the complete velocity-gradient and potential-Hessian correlation')
    selected_g = f.grad(p1 if delayed else p0)
    u_hi = [am.high(a) for a in u]
    u_lo = wh.addv(u, wh.scalev(-1, u_hi))
    g_hi = [am.high(a) for a in selected_g]
    g_lo = wh.addv(selected_g, wh.scalev(-1, g_hi))
    wh.same_vectors(wh.addv(source(u_lo, selected_g), source(u_hi, g_lo), source(u_hi, g_hi)),
                    selected, 'complete joint input split retains the fine-fine correlation')
    if delayed:
        f.equal(p, {}, 'cyclic datum initially has no canonical pressure')
        require(bool(pt), 'cyclic fluid generates its own pressure')
        explicit_pt = f.scale(-f.QQ_I(4)/3, f.mul(vd.cosine((1, 0, 0)),
                                f.mul(vd.cosine((0, 1, 0)), vd.cosine((0, 0, 4)))))
        f.equal(pt, explicit_pt, 'full cyclic pressure generation is independent of viscosity at the initial instant')
        wh.same_vectors(wh.project(I2), [{}, {}, {}], 'cyclic second projected return vanishes')
        wh.same_vectors(wh.project(I3), wh.project(selected), 'cyclic third return is generated pressure coupled to original deformation')
        coefficient = am.pairing(wh.project(I3), wh.project(I3))
        order, factor = 6, 36
    else:
        coefficient = am.pairing(wh.project(I2), wh.project(I2))
        order, factor = 4, 4
    require(coefficient.y == 0 and coefficient.x > 0, 'actual first nonzero projected return')
    return {'datum': name, 'nu': str(nu), 'pressure_modes': len(p), 'pressure_tangent_modes': len(pt),
            'pressure_second_tangent_modes': len(ptt), 'first_projected_derivative_norm_squared': str(coefficient),
            'norm_squared_time_order': order, 'norm_squared_leading_coefficient': str(coefficient/factor),
            'retained': 'All Fourier outputs, canonical pressure variations, evolving drift derivatives and viscosity; these are actual PDE jets, not a truncated trajectory.'}


def localized_swirl():
    x, y, z = s.symbols('x y z', real=True)
    rho = x*x+y*y
    radial = s.symbols('rho', nonnegative=True)
    phi = s.Function('phi')(radial, z)
    pressure = phi.subs(radial, rho)
    e = s.exp(-rho-z*z)
    u = [-y*e, x*e, s.S(0)]
    coords = (x, y, z)
    U = s.Matrix([[s.diff(v, a) for a in coords] for v in u])
    zero(s.trace(U), 'localized whole-space swirl is incompressible')
    zero(-s.trace(U*U)-2*s.exp(-2*(rho+z*z))*(1-2*rho), 'nonzero canonical pressure Poisson source')
    g = s.Matrix([s.diff(pressure, a) for a in coords])
    a = U.T*g
    phi_rho = s.diff(phi, radial).subs(radial, rho)
    expected = s.Matrix([2*y*e*phi_rho, -2*x*e*phi_rho, 0])
    for i in range(3):
        zero(a[i]-expected[i], 'axisymmetric pressure gives a pure azimuthal return')
    zero(sum(s.diff(a[i], coords[i]) for i in range(3)), 'the localized return is already divergence-free')
    return {'datum': 'u0=(-y,x,0) exp(-x^2-y^2-z^2)',
            'Poisson': 'Delta p0=2 exp(-2|x|^2)(1-2(x^2+y^2))',
            'return': '(grad u0)^T grad phi=2 exp(-|x|^2) phi_rho (y,-x,0), already solenoidal',
            'nonzero': 'For canonical decaying p0, and its nontrivial high-pass version, phi_rho is not identically zero. Hence the actual projected impulse has a nonzero second derivative.',
            'boundary': 'The pressure existence, decay, injectivity of the high filter, local solution and Taylor remainder are analytic obligations explained in README.md.'}


def scaling():
    R = s.Rational
    zero(3-3-2+2, 'space-time source mass scales as lambda^-2')
    zero(3*(1-R(3, 9))-2, 'critical projected impulse cost is invariant')
    zero(R(1, 4)*(-2)+R(3, 2)*(-1)+2, 'matched-horizon original reserve scales as lambda^-2')
    zero(R(3, 2)*(R(5, 9)-R(1, 9))-R(2, 3), 'critical source propagator singularity')
    zero(R(2, 3)-R(1, 3)-R(1, 3), 'one-dimensional fractional integration time exponents')
    zero(R(3, 2)*(3-R(5, 3))-2, 'critical source norm scales invariantly')
    zero(R(5, 9)-R(1, 18)-R(1, 2), 'coarse-source spatial Holder exponents')
    zero(1+R(1, 18)-R(5, 9)-R(1, 2), 'gradient heat-kernel Young exponents')
    zero(4-R(5, 3)-R(7, 3), 'whole-space derivative heat-kernel scale')
    zero(R(2, 3)-R(1, 2)-R(1, 6), 'finite-horizon time Holder factor')
    return {'physical_scaling': 'u_lambda(t,x)=lambda u(lambda^2 t,lambda x), same positive viscosity',
            'matched_filter': 'L_lambda=L/lambda; q_lambda=q(lambda^2 t,lambda x), F_lambda=lambda^3 F(lambda^2 t,lambda x)',
            'source_mass': 'integral_0^(T/lambda^2) ||F_lambda||1 =lambda^-2 integral_0^T ||F||1',
            'critical_cost': 'integral_0^(T/lambda^2) ||V_lambda||9^3 =integral_0^T ||V||9^3>0',
            'sufficient_source_cost': 'A full-datum bound on integral ||F||_(9/5)^(3/2) would pay integral ||V||9^3 by drift-independent smoothing and one-dimensional fractional integration. This stronger source bound is OPEN.',
            'paid_coarse_source': '||U_lo^T g+U_hi^T g_lo||_(L^(3/2)_t L^(9/5)_x)<=2 K_ell H^(1/6) sqrt(E0) P_H/sqrt(2nu), P_H=r_p(0), K_ell=||grad heat_kernel_(ell^2)||_(9/5).',
            'remaining_joint_source': 'F_fine=U_hi^T g_hi; retain its exact correlations and the same actual transport. Its critical payment is OPEN.',
            'fixed_filter_extension': 'For a fixed physical L, the rescaled base cutoff is lambda L. The WH4--WH5 coarse bound gives convergence to the nonzero full-pressure impulse.',
            'refuted': 'A universal comparison of critical cost with C times any positive power of total source mass, including at fixed physical cutoff.',
            'not_refuted': 'An allowance depending on the full initial datum; global regularity; a finite bound with additional quantitative concentration information.'}


if __name__ == '__main__':
    cyclic = [vd.sine((0, 1, 0)), vd.sine((0, 0, 4)), vd.sine((1, 0, 0))]
    result = {'reserve': reserve_algebra(), 'full_source_evolution': full_source_evolution(),
              'physical_jets': [physical_jet(u, label, nu, delayed)
                                for u, label, delayed in ((f.fixture(), 'genuine 3D pressure datum', False),
                                                         (cyclic, 'initially pressure-free cyclic datum', True))
                                for nu in (f.QQ_I(1), f.QQ_I(2)/7)],
              'localized_swirl': localized_swirl(), 'scaling': scaling(),
              'status': 'Exact algebra and full NS jets passed. Physical reserves, actual intervals and concentration arguments are analytic, not Lean-certified.',
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    print(json.dumps(result, indent=2), flush=True)
