#!/usr/bin/env python3
"""A source-funded reserve for a first generated-parent interval.

Exact identities retain the forecast's spatial flux defect and its
nonlocal time derivative. Scalar error absorption is also certified in
MettapediaNS.RotationalForecastReserve. Physical weighted Taylor bounds
are analytic; neither calculation proves an arbitrary-history estimate.
"""

import json
import sympy as s
from rotational_curl_reserve import zero, require
from rotational_joint_enstrophy import r, z, grad, lap5, weighted_div, velocity


def full_weighted_balance():
    chi, b, w, wt = [s.Function(name)(r, z) for name in ('chi', 'b', 'w', 'wt')]
    nu = s.symbols('nu', nonnegative=True)
    v = velocity(chi)
    a, eta = v[0]/r, -lap5(chi)
    gb = grad(b)
    F = grad(a)-s.Matrix([0, eta])
    h = (eta*eta+gb.dot(gb))/2
    eta_rate = nu*lap5(eta)-v.dot(grad(eta))+s.diff(b*b, z)
    b_rate = nu*lap5(b)-v.dot(gb)-2*a*b
    h_rate = eta*eta_rate+gb.dot(grad(b_rate))
    d = grad(eta).dot(grad(eta))+sum(c*c for c in gb.jacobian((r, z)))+3*gb[0]**2/r**2
    g = a*eta*eta-gb.dot((v.jacobian((r, z))+a*s.eye(2))*gb)
    flux = w*(v*h+b*b*F-nu*grad(h))+nu*h*grad(w)
    rhs = w*(g-nu*d)+b*b*F.dot(grad(w))+h*(wt+v.dot(grad(w))+nu*lap5(w))
    zero(r**3*(wt*h+w*h_rate)+weighted_div(flux)-r**3*rhs,
         'complete weighted local physical balance, with every boundary flux')
    j, ell, q = s.Function('J')(r, z), s.symbols('ell', positive=True), s.symbols('q', real=True)
    psi = q*q/(ell*ell+q*q)
    dp, ddp = s.diff(psi, q), s.diff(psi, q, 2)
    zero(lap5(psi.subs(q, j))-dp.subs(q, j)*lap5(j)
         -ddp.subs(q, j)*grad(j).dot(grad(j)), 'full diffusion chain rule for the actual forecast')
    return {'forecast': 'J=r^3*d_r*(-L5)^-1*d_z(b^2)',
            'forecast_time': 'J_t=r^3*d_r*(-L5)^-1*S_t, with the complete physical source equation',
            'restored_flux': '<b^2*psi_prime(J)*F.grad(J)>_5',
            'weight_rate': 'psi_prime(J)*(J_t+v.grad(J)+nu*L5(J))+nu*psi_second(J)*|grad(J)|^2'}


def normalized_certificate():
    t, H, C, M, gamma = s.symbols('t H C M gamma', positive=True)
    x = s.symbols('x', real=True)
    U, V = s.symbols('U V', nonnegative=True)
    p, q = s.symbols('p q', real=True)
    reserve = 2*(1-x)*p+s.Rational(7, 3)*(1-x)**3*q
    physical = 4*gamma*(H-t)*U/(H*C)+14*gamma*(H-t)**3*V/(3*H*M)
    zero(physical-2*gamma*H**2*reserve.subs({x:t/H,p:U/(C*H**2),q:V/M}),
         'same reserve in physical and normalized coordinates')
    ideal = reserve.subs({p:x*x,q:1})
    cost = s.expand(s.diff(ideal,x)+x)
    zero(cost-(-13*x*x+19*x-7), 'both components pay the leading stretching')
    zero(cost+(26*x-19)**2/52+s.Rational(3,52), 'strict margin at every normalized time')
    zero(2*gamma*H**2*ideal.subs(x,0)-14*gamma*H**2/3, 'finite original allowance')
    zero(ideal.subs(x,1), 'reserve is exhausted at the original horizon')
    eps = s.Rational(9,4472)
    zero(-s.Rational(3,52)+s.Rational(43,3)*eps+s.Rational(3,104),
         'explicit remainder tolerance')
    parent_only=2*(1-x)*x*x
    source_only=s.Rational(7,3)*(1-x)**3
    require((s.diff(parent_only,x)+x).subs(x,s.Rational(1,2))>0,
            'parent-only leading payment fails inside the interval')
    require((s.diff(source_only,x)+x).subs(x,1)>0,
            'source-only cubic clock leaves the final stretching unpaid')
    return {'normalized_payment': str(cost), 'strict_margin': '3/52',
            'five_error_tolerance': str(eps), 'remaining_margin': '3/104',
            'initial_allowance': '14*gamma*H^2/3',
            'scope': 'first interval with five controlled physical Taylor errors; no reserve reset or repeated-renewal bound'}


def previous_phase_test():
    b = s.exp(-r*r-2*z*z)
    chi = z*(1-3*r*r+4*z*z)*b/2
    for phase in (-1, 1):
        I = r**3*s.diff(phase*chi, r)
        zero(I.subs({r:1,z:1})+5*phase*s.exp(-3), 'nonzero initial parent on both phases')
    zero(grad(b).dot(grad(b)).subs({r:1,z:1})-20*s.exp(-6),
         'strictly positive observation density at that parent')
    return {'U_initial': 'strictly positive on both earlier Gaussian phases',
            'V_initial': 'strictly positive: same b and positive generated J at r=z=1',
            'scope': 'local clock payment uses full derivative bounds; no full-horizon assertion'}


if __name__ == '__main__':
    print(json.dumps({'physical_balance':full_weighted_balance(),
                      'certificate':normalized_certificate(),
                      'previous_phases':previous_phase_test()},indent=2))
