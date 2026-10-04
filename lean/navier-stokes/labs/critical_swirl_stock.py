#!/usr/bin/env python3
"""Exact checks for the critical circulation/swirl stock and its compression defect.

The actual local NS interval and integrated payment are analytic arguments
in README.md. No time integration or truncated evolution is substituted.
"""

import hashlib
import json
from pathlib import Path

import sympy as s


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def zero(value, label):
    require(s.simplify(value) == 0, label)


x, y, z = X = s.symbols('x y z', real=True)
r, k, a, b, nu = s.symbols('r k a b nu', positive=True)


def curl(field):
    return s.Matrix([s.diff(field[2], y)-s.diff(field[1], z),
                     s.diff(field[0], z)-s.diff(field[2], x),
                     s.diff(field[1], x)-s.diff(field[0], y)])


def halfplane_gaussian(poly, rate):
    result = 0
    for (nr, nz), coefficient in s.Poly(s.expand(poly), r, z).terms():
        if nz % 2:
            continue
        result += coefficient*s.gamma(s.Rational(nr+1, 2))*s.gamma(s.Rational(nz+1, 2)) / (2*rate**s.Rational(nr+nz+2, 2))
    return s.simplify(result)


def equation_checks():
    radius2 = x*x+y*y+z*z
    meridional = a*s.exp(-radius2)*s.Matrix([x*(2*z*z-1), y*(2*z*z-1), 2*z*(1-x*x-y*y)])
    swirl = b*s.exp(-k*radius2)*s.Matrix([-y, x, 0])
    velocity = meridional+swirl
    J = velocity.jacobian(X)
    zero(s.trace(J), 'the literal smooth Cartesian datum is divergence free')
    zero(meridional.dot(swirl), 'the kinetic channels are orthogonal pointwise')
    omega = curl(velocity)
    plane = {x:r, y:0}
    ur = a*r*(2*z*z-1)*s.exp(-r*r-z*z)
    uz = 2*a*z*(1-r*r)*s.exp(-r*r-z*z)
    sw = b*r*s.exp(-k*(r*r+z*z))
    q = -2*a*r*z*(2*r*r+2*z*z-7)*s.exp(-r*r-z*z)
    zero(omega[1].subs(plane)-q, 'azimuthal vorticity orientation')
    zero(s.diff(ur,r)+s.diff(uz,z)+ur/r, 'physical incompressibility in the meridional plane')

    nonlinear = curl(-J*velocity)
    expected = -s.diff(ur*q,r)-s.diff(uz*q,z)+s.diff(sw*sw,z)/r
    zero(s.expand(nonlinear[1].subs(plane)-expected),
         'complete Cartesian curl of convection equals conservative transport plus swirl source')
    lap_omega = sum(s.diff(omega[1], coordinate, 2) for coordinate in X).subs(plane)
    diffusion = s.diff(q,r,2)+s.diff(q,z,2)+s.diff(q/r,r)
    zero(s.expand(lap_omega-diffusion), 'full vector diffusion retains the radial drift and axis term')
    # Axisymmetry makes the azimuthal pressure gradient zero; curl removes it
    # from the q equation, without prescribing the meridional pressure.
    azimuthal_rhs = (-J*velocity)[1]+nu*sum(s.diff(velocity[1], coordinate, 2) for coordinate in X)
    swirl_rhs = -ur*s.diff(sw,r)-uz*s.diff(sw,z)-ur*sw/r+nu*(s.diff(sw,r,2)+s.diff(sw,z,2)+s.diff(sw,r)/r-sw/r**2)
    zero(s.expand(azimuthal_rhs.subs(plane)-swirl_rhs), 'actual angular velocity equation, including compression')
    return dict(q=str(q), swirl=str(sw),
                equation='q_t+div_2(v q)=nu[Delta_2 q+partial_r(q/r)]+partial_z(s^2)/r')


def integral_checks():
    Y = halfplane_gaussian(b*b*r*r, 2*k)
    radial = halfplane_gaussian(b*b*(1-2*k*r*r)**2, 2*k)
    vertical = halfplane_gaussian(4*k*k*b*b*r*r*z*z, 2*k)
    inverse_radius = halfplane_gaussian(b*b, 2*k)
    compression = halfplane_gaussian(a*b*b*r*r*(1-2*z*z), 1+2*k)
    for actual, expected, label in [
            (Y, s.pi*b*b/(16*k*k), 'unweighted critical swirl stock'),
            (radial, 3*s.pi*b*b/(16*k), 'radial swirl diffusion'),
            (vertical, s.pi*b*b/(16*k), 'vertical swirl diffusion'),
            (inverse_radius, s.pi*b*b/(4*k), 'radial potential diffusion'),
            (compression, s.pi*a*b*b*k/(2*(1+2*k)**3), 'actual meridional compression')]:
        zero(actual-expected, label)
    Yprime = s.factor(3*compression-2*nu*(radial+vertical)-nu*inverse_radius)
    # Independently integrate 2s times its literal angular equation.
    ur_poly = a*r*(2*z*z-1)
    uz_poly = 2*a*z*(1-r*r)
    direct_transport = halfplane_gaussian(-2*b*b*r*(ur_poly*(1-2*k*r*r)-uz_poly*2*k*r*z+ur_poly), 1+2*k)
    direct_diffusion = halfplane_gaussian(2*nu*b*b*r*r*(4*k*k*(r*r+z*z)-10*k), 2*k)
    zero(direct_transport-3*compression, 'the three compression factors survive integration')
    zero(direct_transport+direct_diffusion-Yprime, 'direct and integrated swirl equations agree')

    v = s.symbols('v', nonnegative=True)
    turning = s.Rational(7, 2)
    stock = (s.integrate(v*(7-2*v)*s.exp(-v), (v,0,turning))
             +s.integrate(v*(2*v-7)*s.exp(-v), (v,turning,s.oo)))
    zero(stock-3-22*s.exp(-turning), 'meridional circulation at the original datum')
    source = 2*k*b*b*(-s.integrate(v*s.exp(-2*k*v), (v,0,turning))
                      +s.integrate(v*s.exp(-2*k*v), (v,turning,s.oo)))
    zero(source-b*b*(2*(1+7*k)*s.exp(-7*k)-1)/(2*k), 'signed swirl source through both vorticity regions')
    # A second calculation integrates the jumps of sign(q) at z=0 and
    # r^2+z^2=7/2, retaining the complete circular nodal contribution.
    plane_source = 2*b*b*(-s.integrate(r*s.exp(-2*k*r*r), (r,0,s.sqrt(turning)))
                         +s.integrate(r*s.exp(-2*k*r*r), (r,s.sqrt(turning),s.oo)))
    circle_source = 4*b*b*s.exp(-7*k)*s.integrate(r, (r,0,s.sqrt(turning)))
    zero(plane_source+circle_source-source, 'independent nodal calculation of the swirl source')
    absolute_linear = (s.integrate((7-2*v)*s.exp(-v), (v,0,turning))
                       +s.integrate((2*v-7)*s.exp(-v), (v,turning,s.oo)))
    axis_loss, plane_loss, circle_loss = 4*absolute_linear, 2*absolute_linear, 196*s.exp(-turning)
    zero(axis_loss+plane_loss+circle_loss-10*stock, 'all axis and nodal meridional diffusion losses')
    Cprime = s.simplify(source-10*nu*a*stock)

    Etheta = 2*s.pi*halfplane_gaussian(b*b*r**3, 2*k)
    transfer = 2*s.pi*halfplane_gaussian(a*b*b*r**3*(2*z*z-1), 1+2*k)
    zero(Etheta-s.pi**s.Rational(3,2)*b*b/(2*k)**s.Rational(5,2), 'physical swirl kinetic energy uses r dr dz')
    zero(transfer+2*k*a*b*b*s.pi**s.Rational(3,2)/(1+2*k)**s.Rational(7,2), 'signed kinetic transfer differs from critical stock production')
    theta_diffusion = 2*s.pi*halfplane_gaussian(b*b*r*((1-2*k*r*r)**2+4*k*k*r*r*z*z+1), 2*k)
    zero(theta_diffusion-5*k*Etheta, 'physical swirl kinetic dissipation')
    Em = 7*s.sqrt(2)*s.pi**s.Rational(3,2)*a*a/32
    Zm = 9*Em
    Emprime = 2*transfer-2*nu*Zm
    Ethetaprime = -2*transfer-2*nu*theta_diffusion
    zero(Emprime+Ethetaprime+2*nu*(Zm+theta_diffusion), 'opposite internal work cancels in the complete kinetic identity')

    chosen = {k:s.Rational(1,7), a:81*nu, b:144*nu}
    cp = s.simplify(Cprime.subs(chosen)/nu**2)
    yp = s.simplify(Yprime.subs(chosen)/nu**3)
    zero(cp-(-75006-17820*s.exp(-turning)+290304/s.E), 'complete selected meridional derivative')
    zero(yp-60480*s.pi, 'strictly positive selected swirl derivative')
    # exp(1)<3 (its factorial series), exp(-7/2)<1 give this strict
    # rational lower bound, without a floating sign test.
    cp_lower = s.Rational(7,6)*144**2-10*81*25
    require(cp_lower == 3942 and cp_lower > 0, 'positive analytic lower bound for Cprime/nu^2')
    return dict(Y=str(Y), radial_diffusion=str(radial), vertical_diffusion=str(vertical),
                inverse_radius_diffusion=str(inverse_radius), compression=str(compression),
                source=str(s.simplify(source)), Cprime=str(Cprime), Yprime=str(Yprime),
                kinetic_transfer=str(transfer), kinetic_energy=str(Em+Etheta),
                selected=dict(k='1/7', a='81 nu', b='144 nu',
                              Cprime_over_nu_squared=str(cp), Cprime_strict_lower='3942 nu^2',
                              Yprime='60480 pi nu^3', all_constant_weights='Every alpha>=0 has R_alpha(t)>R_alpha(0) on one common short interval.'))


def payment_checks():
    alpha, sr, sz, sw, rr = s.symbols('alpha sr sz sw rr', positive=True)
    c = (3*alpha*alpha-1)/(2*alpha)
    square = (s.sqrt(2*alpha)*sz-sw/(s.sqrt(2*alpha)*rr))**2
    zero(2*alpha*sr**2+2*alpha*sz**2+alpha*sw**2/rr**2-2*sw*sz/rr
         -(2*alpha*(sr**2-sw**2/(4*rr**2))+square+c*sw**2/rr**2),
         'complete source absorption leaves the Hardy defect and radial cost')
    theta = s.Rational(1,2)-1/(6*alpha**2)
    zero(c-3*alpha*theta, 'core compression threshold for this stock')
    f = s.Function('f')(rr)
    zero(s.diff(f,rr)**2-f*f/(4*rr**2)
         -(s.diff(f,rr)-f/(2*rr))**2-s.diff(f*f/(2*rr),rr),
         'Hardy remainder with its exact boundary term')
    G, E0, rho = s.symbols('G E0 rho', positive=True)
    Pout = G*E0/(4*s.pi*rho**3)
    K = 3*alpha*Pout/nu
    zero(K-3*alpha*G*E0/(4*s.pi*nu*rho**3), 'outside-core compression has an original-data payment')
    # A sharper payment uses |Gamma|<=G, ||s/r||_L2<=sqrt(Z), and E'=-2nu Z.
    energy, enstrophy, tau, gamma, Cstar = s.symbols('energy enstrophy tau gamma Cstar', positive=True)
    reserve = Cstar*energy**gamma*s.sqrt(tau)/(2*s.sqrt(nu*gamma))
    production = Cstar*energy**(gamma-s.Rational(1,2))*s.sqrt(enstrophy)
    loss = 2*nu*enstrophy*s.diff(reserve, energy)+s.diff(reserve,tau)
    remainder = Cstar*energy**gamma/s.sqrt(nu*gamma*tau)*(s.sqrt(nu*gamma*tau*enstrophy/energy)-s.Rational(1,2))**2
    zero(s.expand(loss-production-remainder), 'Bellman reserve pays exterior compression with a complete square')
    C0 = 3*alpha*G/(2*s.pi*nu*rho**2)
    initial = reserve.subs({Cstar:C0*E0**(1-gamma), energy:E0})
    zero(initial-3*alpha*G*E0*s.sqrt(tau)/(4*s.pi*nu*rho**2*s.sqrt(nu*gamma)), 'initial exterior allowance depends only on the original data and horizon')
    # Under NS similarity: C,Y,G invariant; E -> E/lambda, rho ->rho/lambda.
    lam = s.symbols('lambda', positive=True)
    zero(K.subs({E0:E0/lam, rho:rho/lam})-lam**2*K, 'conditional reserve rate has physical scaling')
    zero((E0/lam).subs(lam,E0)-1, 'unit initial energy by full NS scaling')
    return dict(c_alpha=str(c), theta_alpha=str(theta), outside_rate=str(K),
                adaptive_core='rho(t)>=rho0*(E(t)/E0)^p, 0<=p<1/2, gamma=1-2p',
                exterior_reserve='[3 alpha G0/(2 pi nu rho0^2)] E0^(2p) E(t)^(1-2p) sqrt((H-t)/(4 nu (1-2p)))',
                defect='(3 alpha/nu) integral_(r<rho) (-u_r/r) s^2 - c_alpha integral_(r<rho) s^2/r^2',
                scope='The radius policy and its constants are fixed from the original datum. Propagation of the core condition on every same-datum prefix and full continuation payment remain open.')


if __name__ == '__main__':
    result = dict(equations=equation_checks(), integrals=integral_checks(), payment=payment_checks(),
                  source_sha256={Path(__file__).name:hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},
                  limitation='Exact algebra and initial derivatives; actual local interval, Kato identity, Hardy and history estimates remain analytic, not Lean-certified.')
    print(json.dumps(result, indent=2))
