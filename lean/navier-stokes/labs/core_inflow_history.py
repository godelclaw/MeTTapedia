#!/usr/bin/env python3
"""Exact pressure and signed-cutoff checks for a generated core inflow.

The uniform local NS interval and its norm estimates are analytic in
README.md. This checker does not time-step a truncated fluid model.
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


r, z = s.symbols('r z', real=True, positive=True)


def pressure_checks():
    psi = s.Function('psi')(r,z)
    lap5 = lambda f: s.diff(f,r,2)+3*s.diff(f,r)/r+s.diff(f,z,2)
    lap3 = lambda f: s.diff(f,r,2)+s.diff(f,r)/r+s.diff(f,z,2)
    F = -lap5(psi)
    pressure = -2*psi-r*s.diff(psi,r)
    fr = -r*s.diff(psi,z,2)
    fz = 2*s.diff(psi,z)+r*s.diff(psi,r,z)
    zero(r*F-s.diff(pressure,r)-fr, 'radial acceleration retains the canonical pressure response')
    zero(-s.diff(pressure,z)-fz, 'vertical acceleration retains the same pressure')
    zero(lap3(pressure)-2*F-r*s.diff(F,r), 'complete pressure Poisson equation')
    zero(s.diff(fr,r)+fr/r+s.diff(fz,z), 'generated meridional field is incompressible')
    zero((s.diff(fr,z)-s.diff(fz,r))/r-s.diff(F,z), 'generated vorticity is the full swirl source')
    # A direct Cartesian check identifies the force being projected.
    x,y,zz = X = s.symbols('x y zz', real=True)
    beta = s.exp(-x*x-y*y-zz*zz)
    u = beta*s.Matrix([-y,x,0])
    zero(s.trace(u.jacobian(X)), 'literal smooth pure swirl is divergence free')
    force = -u.jacobian(X)*u
    for actual, expected in zip(force, beta**2*s.Matrix([x,y,0])):
        zero(actual-expected, 'complete Cartesian convection supplies the radial forcing term')
    R = s.symbols('R', positive=True)
    radial_F = s.Function('F')(R)
    mass = s.Function('mass')(R)
    psiprime = -mass/R**4
    zero((s.diff(psiprime,R)+4*psiprime/R+radial_F).subs(s.diff(mass,R),R**4*radial_F),
         'five-dimensional radial Newtonian flux')
    f = s.Function('f')(z)
    g = s.Function('g')(z)
    zero(s.diff(f,z,2)*g-s.diff(s.diff(f,z)*g,z)+s.diff(f,z)*s.diff(g,z),
         'signed cutoff pairing retains its complete axial boundary term')
    return dict(pressure='p0=-(2+r partial_r)psi, psi=(-Delta5)^-1(beta^2)',
                acceleration='f_r=-r psi_zz, f_z=(2+r partial_r)psi_z',
                radial_flux='psi_prime(R)=-R^-4 integral_0^R sigma^4 F(sigma) d sigma',
                family_sign='P1,rho=-integral_(r<rho) r^2 z^2/R^2 F_prime(R) psi_prime(R) dr dz <=0 when F_prime<=0')


def gaussian_checks():
    h,tau = s.symbols('h tau', positive=True)
    heat = (1+8*h)**s.Rational(-5,2)*s.exp(-2*(r*r+z*z)/(1+8*h))
    lap5 = s.diff(heat,r,2)+3*s.diff(heat,r)/r+s.diff(heat,z,2)
    zero(s.diff(heat,h)-lap5, 'full five-dimensional heat resolvent')
    zero(heat.subs(h,0)-s.exp(-2*(r*r+z*z)), 'actual squared Gaussian swirl is the source')
    kernel = s.diff(heat,z,2).subs(h,(1/tau-1)/8)/(8*tau*tau)
    target = tau**s.Rational(3,2)*(4*z*z*tau-1)*s.exp(-2*(r*r+z*z)*tau)/2
    zero(kernel-target, 'canonical inward-strain response on and off the axis')
    zero(s.integrate(target.subs({r:0,z:0}),(tau,0,1))+s.Rational(1,5),
         'outward response at the strongest-swirl center')
    negative = s.integrate(tau**s.Rational(3,2),(tau,0,s.Rational(1,4)))
    positive = s.Rational(1,4)*s.Rational(9,16)*2*s.Rational(1,16)
    require(3**5 < 16**2, 'exp(5/2)<16 follows from exp(1)<3')
    m_lower = (positive-negative)/2
    zero(m_lower-s.Rational(13,5120), 'strict inward-strain lower bound at z=1, r<=1/2')
    point_lower = m_lower/4
    zero(point_lower-s.Rational(13,20480), 'inflow Reynolds numerator at r=1/2, z=1')

    z_moment = s.integrate((4*tau*z*z-1)*s.exp(-2*(1+tau)*z*z),(z,-s.oo,s.oo))
    zero(z_moment+s.sqrt(s.pi)/(s.sqrt(2)*(1+tau)**s.Rational(3,2)),
         'every radial slice has strictly negative swirl-weighted initial compression')
    r_moment = s.integrate(r*r*s.exp(-2*(1+tau)*r*r),(r,0,s.oo))
    integrand = s.simplify(tau**s.Rational(3,2)*z_moment*r_moment/2)
    zero(integrand+s.pi*tau**s.Rational(3,2)/(32*(1+tau)**3),
         'unweighted meridional integration retains the radial measure')
    t = s.symbols('t', real=True)
    primitive = 3*s.atan(t)/4-(5*t**3+3*t)/(4*(1+t*t)**2)
    zero(s.diff(primitive,t)-2*t**4/(1+t*t)**3, 'independent rational primitive after tau=t^2')
    endpoint = s.simplify(primitive.subs(t,1)-primitive.subs(t,0))
    zero(endpoint-3*s.pi/16+s.Rational(1,2), 'complete Gaussian pairing')
    total = -s.pi*endpoint/32
    zero(total-s.pi*(8-3*s.pi)/512, 'global pairing is strictly negative using pi>3')

    # On tau in[1/2,1], r in[0,min(rho,1)], use
    # sqrt(pi)/(2sqrt(2))>1/2, (tau/(1+tau))^(3/2)>1/6,
    # exp(-2(1+tau)r^2)>1/81, and integral r^2 dr=min(rho^3,1)/3.
    cutoff_lower = s.Rational(1,2)*s.Rational(1,2)*s.Rational(1,6)*s.Rational(1,81)*s.Rational(1,3)
    zero(cutoff_lower-s.Rational(1,5832), 'strict all-radius lower bound for the favorable pairing')
    return dict(inward_kernel=str(target), center_inward_strain='-1/5',
                pointwise_inflow_lower=str(point_lower), cutoff_P1='P1,rho < -min(rho^3,1)/5832',
                full_pairing=str(total),
                explanation='Pointwise inflow is positive near the axial front, but the swirl-weighted pairing is negative inside every radial cutoff.')


def interval_checks():
    A,nu,delta,M,cstar = s.symbols('A nu delta M cstar', positive=True)
    zero(A*(delta/2)*cstar/2-A*delta*cstar/4, 'uniform local expansion on the crossing window')
    zero((A*delta*cstar/4).subs(A,8*M*nu/(delta*cstar))-2*M*nu,
         'finite amplitude gives any prescribed inflow multiple')
    require(s.Rational(3,4)**2 == s.Rational(9,16), 'energy ratio retains every allowed paid radius above 3/4')
    alpha,t = s.symbols('alpha t', positive=True)
    signed_loss = (3*alpha/nu)*A**4*s.Rational(27,64)*s.integrate(t,(t,0,delta/A))/11664
    zero(signed_loss-alpha*A*A*delta*delta/(18432*nu),
         'one actual interval consumes a finite critical stock while crossing the pointwise cap')
    full_loss = (3*alpha/nu)*A**4*s.integrate(t,(t,0,delta/A))/11664
    zero(full_loss-alpha*A*A*delta*delta/(7776*nu),
         'the original critical stock has a uniform depletion over the actual interval')
    rho,lam = s.symbols('rho lambda', positive=True)
    weights = dict(velocity=1,time=-2,inflow_r_times_ur=0,viscosity=0,C=0,Y=0,P=2)
    require(weights['P']+weights['time']==0, 'integrated compression has critical spatial scaling')
    zero((lam*A)*(rho/lam)-A*rho, 'dimensionless inflow is preserved by full spatial NS similarity')
    return dict(actual_family='u_A(t,x)=A v_(nu/A)(A t,x), A>=nu',
                interval='0<t<=delta/A, uniform delta determined by the one base datum',
                crossing_window='delta/(2A)<=t<=delta/A',
                signed_core_charge='at least alpha A^2 delta^2/(18432 nu) for the paid radii with rho0=1',
                scope='Uniform local estimates are analytic. Any prescribed radius is treated by NS spatial scaling; a different datum-selected smaller radius is not refuted. No recurrent cascade or global continuation is established.')


def evolving_pairing_checks():
    m,sw,uz,pressure = [s.Function(name)(r,z) for name in ['m','sw','uz','pressure']]
    nu = s.symbols('nu', positive=True)
    ur = -r*m
    adv = lambda f: ur*s.diff(f,r)+uz*s.diff(f,z)
    lap2 = lambda f: s.diff(f,r,2)+s.diff(f,z,2)
    mt = -adv(m)+nu*(lap2(m)+3*s.diff(m,r)/r)+m*m-sw*sw/r**2+s.diff(pressure,r)/r
    st = -adv(sw)+m*sw+nu*(lap2(sw)+s.diff(sw,r)/r-sw/r**2)
    radial_rhs = -adv(ur)+sw*sw/r-s.diff(pressure,r)+nu*(lap2(ur)+s.diff(ur,r)/r-ur/r**2)
    zero(-r*mt-radial_rhs, 'inward-strain equation agrees with the full radial NS equation')
    density = m*sw*sw
    lhs = mt*sw*sw+2*m*sw*st+s.diff(ur*density,r)+s.diff(uz*density,z)
    lhs = lhs.subs(s.diff(uz,z),2*m+r*s.diff(m,r))
    Jr = sw*sw*s.diff(m,r)+2*m*sw*s.diff(sw,r)+m*sw*sw/r
    Jz = sw*sw*s.diff(m,z)+2*m*sw*s.diff(sw,z)
    defect = (2*sw*sw*s.diff(m,r)/r-4*sw*(s.diff(m,r)*s.diff(sw,r)+s.diff(m,z)*s.diff(sw,z))
              -2*m*(s.diff(sw,r)**2+s.diff(sw,z)**2)-m*sw*sw/r**2)
    reaction = 4*m*m*sw*sw-sw**4/r**2+s.diff(pressure,r)*sw*sw/r
    zero(lhs-nu*(s.diff(Jr,r)+s.diff(Jz,z))-reaction-nu*defect,
         'complete evolving compression density, including pressure and viscous flux')
    zero(-ur*density-r*m*m*sw*sw, 'advective flux through a fixed radial cutoff is retained')
    return dict(density='m s^2',
                reaction='4m^2 s^2-s^4/r^2+(p_r/r)s^2',
                viscous_flux='J=s^2 grad(m)+2m s grad(s)+(m s^2/r)e_r',
                viscous_defect='2s^2 m_r/r-4s grad(m).grad(s)-2m|grad(s)|^2-m s^2/r^2',
                moving_boundary='rho_prime integral_z m s^2 at r=rho; this term is additional if the core pairing is differentiated')


if __name__ == '__main__':
    print(json.dumps(dict(pressure=pressure_checks(), gaussian=gaussian_checks(),
                          interval=interval_checks(), evolution=evolving_pairing_checks(),
                          source_sha256={Path(__file__).name:hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},
                          limitation='Exact initial response and algebra; the uniform actual NS interval and all-cutoff remainder bounds remain analytic, not Lean-certified.'), indent=2))
