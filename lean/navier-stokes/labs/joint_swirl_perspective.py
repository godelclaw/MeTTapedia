#!/usr/bin/env python3
"""Exact checks for a joint strain/swirl perspective along actual NS histories.

Scalar parabolic construction, spatial integration and the conditional
continuation argument are analytic in README.md, not Lean certificates.
"""

import hashlib
import json
from pathlib import Path

import sympy as s

from axis_deformation_pressure import green_origin
from rotational_joint_enstrophy import r, z, grad, lap5, velocity
from rotational_curl_reserve import require, zero
from circulation_source_reserve import div3, lap3


def joint_identity():
    m, b, h, pressure, uz = [s.Function(n)(r, z)
                             for n in ('m', 'b', 'h', 'pressure', 'uz')]
    nu = s.symbols('nu', positive=True)
    v = s.Matrix([-r*m, uz])
    adv = lambda f: v.dot(grad(f))
    mr = nu*lap5(m)+m*m-b*b+s.diff(pressure, r)/r
    br = nu*lap5(b)+2*m*b
    hr = nu*lap5(h)+2*m*h
    radial_rhs = -adv(-r*m)+r*b*b-s.diff(pressure, r)+nu*(lap3(-r*m)+m/r)
    zero(-r*(mr-adv(m))-radial_rhs,
         'inward strain is the full radial NS equation divided by minus r')
    angular_rhs = -adv(r*b)+m*r*b+nu*(lap3(r*b)-b/r)
    zero(r*(br-adv(b))-angular_rhs, 'swirl quotient keeps radial transport')
    div5 = s.diff(v[0], r)+3*v[0]/r+s.diff(uz, z)
    incompressibility = {s.diff(uz, z): 2*m+r*s.diff(m, r)}
    zero(div5.subs(incompressibility)+2*m, 'lifted drift is not divergence free')
    zero(hr+div5.subs(incompressibility)*h-nu*lap5(h),
         'the one evolving envelope satisfies the conservative lifted law')

    Q = (m*m+b*b)/h
    material = 2*m*mr/h+2*b*br/h-(m*m+b*b)*hr/h**2
    squares = sum((s.diff(m, c)-m*s.diff(h, c)/h)**2
                  +(s.diff(b, c)-b*s.diff(h, c)/h)**2 for c in (r, z))
    zero(material-nu*lap5(Q)-2*m*s.diff(pressure, r)/(r*h)+2*nu*squares/h,
         'all direct quadratic reactions cancel, with both relative gradient squares')
    q, q_grad_squared, Lq = s.symbols('q q_grad_squared Lq', positive=True)
    power = q**s.Rational(3,2)
    zero(s.diff(power,q)*Lq-nu*s.diff(power,q,2)*q_grad_squared
         -(s.Rational(3,2)*s.sqrt(q)*Lq
           -s.Rational(3,4)*nu*q_grad_squared/s.sqrt(q)),
         'complete critical power chain rule')
    Gamma = r*r*h
    Lminus = lambda f: s.diff(f,r,2)-s.diff(f,r)/r+s.diff(f,z,2)
    zero(r*r*hr-2*r*r*m*h-nu*Lminus(Gamma),
         'envelope circulation has the actual swirl maximum-principle equation')

    f = s.Function('f')(r,z)
    zero(r*(lap5(f)-s.diff(f,z,2))-s.diff(r*s.diff(f,r)+2*f,r),
         'physical-volume integration retains the axis loss')
    q = s.symbols('q', positive=True)
    zero(s.Rational(3,4)*q**s.Rational(-1,2)
         -s.Rational(4,3)*s.diff(q**s.Rational(3,4),q)**2,
         'critical physical diffusion coefficient')
    fr, ft, mm, bb, hh = s.symbols('fr ft mm bb hh', real=True)
    zero(2*mm*(-fr/r)/hh+2*bb*(ft/r)/hh-2*(-mm*fr+bb*ft)/(r*hh),
         'an applied force has additional radial and angular source work')
    return dict(Q='(m^2+b^2)/h',
                law='(D_t-nu L5)Q=2m(p_r/r)/h-(2nu/h)(|grad m-m grad log h|^2+|grad b-b grad log h|^2)',
                axis_loss='4 pi nu integral_axis Q^(3/2) dz',
                full_diffusion='3nu integral sqrt(Q)/h times the two squares + (4nu/3) integral |grad Q^(3/4)|^2 + axis_loss',
                force_entry='2(-m f_r+b f_theta)/(r h)')


def envelope_and_consumer():
    a = s.symbols('a', nonnegative=True)
    kappa, ell, G, B, nu, CS = s.symbols('kappa ell G B nu CS', positive=True)
    zero(s.diff(a/(1+a)**3,a)-(1-2*a)/(1+a)**4,
         'envelope circulation maximum occurs at squared radius one half')
    zero((a/(1+a)**3).subs(a,s.Rational(1,2))-s.Rational(4,27),
         'original circulation envelope is four kappa over twenty seven')
    R = s.symbols('R', positive=True)
    mass = (s.Rational(8,3)*s.pi**2
            *s.integrate(R**4/(1+R*R)**3,(R,0,s.oo)))
    zero(mass-s.pi**3/2, 'finite mass of the polynomial envelope in five dimensions')
    # For f=Q^(3/4), interpolation gives ||f||_(10/3)^(10/3)
    # <= ||f||_2^(4/3) ||f||_6^2 <= CS R_stock^(2/3)||grad f||_2^2.
    zero(s.Rational(3,4)*s.Rational(10,3)-s.Rational(5,2),
         'physical parabolic interpolation produces Q to the five halves')
    zero(s.Rational(2,5)+s.Rational(3,5)-1, 'swirl L5 has the Serrin exponents')
    zero(s.Rational(1,2)*s.Rational(4,3)*nu*(3*B/(2*nu))-B,
         'half of the critical diffusion pays the needed gradient history')
    bound = CS*G**s.Rational(5,2)*B**s.Rational(2,3)*3*B/(2*nu)
    zero(bound-3*CS*G**s.Rational(5,2)*B**s.Rational(5,3)/(2*nu),
         'explicit conditional L5 swirl bound')
    return dict(initial_envelope='h0=kappa ell^-2 (1+|x|^2/ell^2)^-3',
                mass='M=pi^3 kappa ell^3/2', circulation_max='G=4 kappa/27',
                stochastic_action='integral_0^T E_rho |v5|^2 <= pi G H E0/M, rho=h/M',
                coercivity='u_r^2+u_theta^2 <= G Q',
                remaining_budget='integral_0^T [W_pressure-D/2] <= K(original datum,nu,H,kappa,ell) for every same-datum prefix',
                conditional_swirl_L5=str(bound),
                continuation='Chen-Fang-Zhang Theorem 1.1, d=0 and p=q=5, analytic consumer only')


def denominator_test():
    beta = s.exp(-3*(r*r+z*z))
    m = (1-2*z*z)*s.exp(-r*r-z*z)
    zero(m*m/beta-(1-2*z*z)**2*s.exp(r*r+z*z),
         'using the actual swirl as denominator gives infinite initial stock for smooth data')
    # On the equatorial plane of the pure Gaussian swirl, CI1 gives
    # m1=-R^-5 integral_0^R sigma^4 exp(-2 sigma^2) d sigma.
    sigma = s.symbols('sigma', positive=True)
    mass = s.integrate(sigma**4*s.exp(-2*sigma*sigma),(sigma,0,s.oo))
    zero(mass-3*s.sqrt(2*s.pi)/64, 'generated meridional quotient has a nonzero algebraic tail')
    require(2*5-6 == 4 and s.Rational(3,2)*4 > 3,
            'polynomial envelope makes the formal generated-parent moment integrable')
    return dict(failed_choice='h=b: m0=(1-2z^2)exp(-R^2), b0=exp(-3R^2) already gives infinite stock',
                generated_parent_tail='m1(R,0) ~ -3 sqrt(2pi)/(64 R^5)',
                jet_scope='For pure Gaussian swirl, the quadratic parent term divided by b0 has a divergent spatial coefficient; no interchange of time expansion and integral is claimed.',
                polynomial_repair='m1=O(R^-5), h0~R^-6 gives Q_parent=O(R^-4), whose three-halves moment is integrable.')


def actual_pressure_test():
    a, B, C = s.symbols('a B C', real=True)
    e = s.exp(-r*r-z*z)
    chi = z*(a+C*r**4)*e
    b = B*e
    v = velocity(chi)
    ur, uz = v
    zero(div3(v), 'the entire hidden-parent family is physically incompressible')
    m = -ur/r
    G = s.Matrix([[s.diff(ur,r),-b,s.diff(ur,z)],
                  [b+r*s.diff(b,r),ur/r,r*s.diff(b,z)],
                  [s.diff(uz,r),0,s.diff(uz,z)]])
    source_poly = s.expand(s.trace(G.applyfunc(lambda f:s.cancel(f/e))**2))
    source = source_poly*e**2
    convection = s.Matrix([v.dot(grad(ur))-r*b*b,v.dot(grad(uz))])
    zero(div3(convection)-source, 'full vector convection identifies the pressure source')
    rr_poly = (s.diff(source_poly,r,2)+s.diff(source_poly,r)/r
               -8*r*s.diff(source_poly,r)+(16*r*r-8)*source_poly)/2
    P0 = green_origin(rr_poly)
    expected = -s.Rational(12,7)*a*a+s.Rational(8,385)*a*C+s.Rational(4,5)*B*B+s.Rational(64,455)*C*C
    zero(P0-expected, 'canonical radial pressure by the existing exact heat resolvent')
    # Independently obtain the same Hessian through its degree-two source
    # and the indispensable local Newtonian contact term.
    R,t = s.symbols('R t', real=True, positive=True)
    g = -source_poly.subs({r:R*s.sqrt(1-t*t),z:R*t})
    g2 = s.expand(s.Rational(5,2)*s.integrate(s.expand(g)*(3*t*t-1)/2,(t,-1,1)))
    contact = -source_poly.subs({r:0,z:0})/3
    independent = contact+s.integrate(g2*s.exp(-2*R*R)/R,(R,0,s.oo))/5
    zero(P0-independent, 'independent angular Hessian calculation including contact term')
    h0 = (1+r*r+z*z)**-3
    Q = (m*m+b*b)/h0
    center = {r:0,z:0,a:1,B:1}
    zero(Q.subs(center)-2, 'same observed center stock for every hidden parent')
    zero(s.limit(lap5(Q),r,0).subs({z:0,a:1,B:1})-12,
         'same complete local diffusion for every hidden parent')
    for f in (m,b,h0,Q):
        for coordinate in (r,z):
            zero(s.diff(f,coordinate).subs(center), 'all local relative gradient squares vanish')
    pressure_work = s.factor(2*P0.subs({a:1,B:1}))
    zero(pressure_work.subs(C,0)+s.Rational(64,35), 'favorable pressure work without hidden correction')
    chosen = s.factor(pressure_work.subs(C,3))
    require(chosen > 0, 'actual hidden meridional parent reverses pressure work')
    nu = s.Rational(1,100)
    plus_rate, minus_rate = 12*nu+chosen, 12*nu-chosen
    zero(plus_rate-s.Rational(3389,3575), 'actual local rate for the positive orientation')
    zero(minus_rate+s.Rational(2531,3575), 'opposite actual rate after reversing the whole datum')
    require(plus_rate>0 and minus_rate<0, 'positive viscosity retains the opposite-rate test')
    return dict(family='chi=z(a+C r^4) exp(-R^2), u_r=-r chi_z, u_z=2chi+r chi_r, u_theta=B r exp(-R^2)',
                canonical_P_origin=str(P0), parameters='a=B=1; compare C=0 with C=3',
                unchanged='m=b=h=1, Q=2, all first gradients zero, L5 Q=12 at the origin',
                pressure_work_C0='-64/35', pressure_work_C3=str(chosen),
                reversed_datum='u0 and -u0 have identical full fields Q0 and h0, identical kinetic energy and pressure, but different retained orientation m/h.',
                rates_at_nu_one_over_one_hundred=dict(positive=str(plus_rate), negative=str(minus_rate)),
                failed_assertion='2mP/h <= any finite constant times the local relative-gradient dissipation, for all smooth unforced data',
                scope='Smooth finite-energy unforced initial data at every nu>0. This pointwise failure does not refute an integrated signed full-datum allowance.')


if __name__ == '__main__':
    result = dict(identity=joint_identity(), envelope=envelope_and_consumer(),
                  denominator=denominator_test(), actual_pressure=actual_pressure_test(),
                  limitation='Exact algebra and Gaussian pressure only; parabolic construction, integration, continuation and short-time persistence are analytic. Arbitrary-history pressure payment remains open.')
    sources = [Path(__file__), Path(__file__).with_name('axis_deformation_pressure.py')]
    result['source_sha256'] = {p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
    print(json.dumps(result, indent=2))
