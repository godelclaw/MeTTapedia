#!/usr/bin/env python3
"""Exact pressure-tail coefficients and their original-energy Bellman payment.

Actual solution asymptotics, density comparison and the divergence of a
pressure-square diagnostic are analytic arguments in the accompanying text.
No truncated profile is substituted for the complete Navier--Stokes flow.
"""

import hashlib
import json
from pathlib import Path

import sympy as s

from integrated_swirl_pressure import gaussian_pair
from rotational_joint_enstrophy import r, z, velocity
from rotational_curl_reserve import zero


def physical_moments():
    exponential = s.exp(-r*r-z*z)
    meridional = velocity(z*exponential)
    swirl = 2*s.sqrt(2)*r*z*exponential
    axial_poly = s.cancel(meridional[1]**2/exponential**2)
    horizontal_poly = s.cancel((meridional[0]**2+swirl**2)/exponential**2)
    scale = s.pi**s.Rational(3,2)
    axial = s.simplify(gaussian_pair(axial_poly,s.Integer(2),True)/scale)
    horizontal = s.simplify(gaussian_pair(horizontal_poly,s.Integer(2),True)/(2*scale))
    zero(axial-s.sqrt(2)/8, 'complete axial kinetic tensor entry')
    zero(horizontal-11*s.sqrt(2)/64, 'each complete horizontal tensor entry')
    delta = s.simplify(axial-horizontal)
    zero(delta+3*s.sqrt(2)/64, 'nonzero actual initial pressure anisotropy')
    zero(2*horizontal+axial-15*s.sqrt(2)/32, 'full original kinetic energy')
    a,c = s.symbols('a c',nonnegative=True)
    energy,difference = 2*a+c,c-a
    zero(energy-difference-3*a, 'upper pressure anisotropy bound by kinetic energy')
    zero(energy/2+difference-s.Rational(3,2)*c, 'lower pressure anisotropy bound')
    return dict(Ezz_over_pi_three_halves=str(axial),
                Exx_over_pi_three_halves=str(horizontal),
                initial_delta_over_pi_three_halves=str(delta),
                physical_bound='-E(t)/2 <= delta(t)=Ezz(t)-Exx(t) <= E(t) <= E0',
                memory='A(t)=integral_0^t delta(s) ds; abs(A(t))<=E0*t')


def tail_geometry():
    radius_squared = r*r+z*z
    newton = 1/(4*s.pi*s.sqrt(radius_squared))
    pressure_shape = s.diff(newton,z,2)
    parent_shape = s.simplify(s.diff(pressure_shape,r)/r)
    zero(pressure_shape-(2*z*z-r*r)/(4*s.pi*radius_squared**s.Rational(5,2)),
         'axisymmetric pressure quadrupole from the energy tensor')
    zero(parent_shape-3*(r*r-4*z*z)/(4*s.pi*radius_squared**s.Rational(7,2)),
         'generated radial quotient with its actual sign')
    zero(s.diff(newton,r,2)+s.diff(newton,r)/r+s.diff(newton,z,2),
         'the Newtonian potential is harmonic away from the origin')
    zero(s.diff(pressure_shape,r,2)+s.diff(pressure_shape,r)/r+s.diff(pressure_shape,z,2),
         'the leading pressure quadrupole is harmonic outside the origin')
    zero(s.diff(-s.diff(pressure_shape,r),z)-s.diff(-s.diff(pressure_shape,z),r),
         'the leading generated velocity has zero curl')
    mu = s.symbols('mu',real=True)
    radial = s.symbols('radial',positive=True)
    F = 3*(1-5*mu*mu)/(4*s.pi)
    G = (3*mu*mu-1)/(4*s.pi)
    substitution = {r:radial*s.sqrt(1-mu*mu),z:radial*mu}
    zero(parent_shape.subs(substitution)-F/radial**5,
         'radial-quotient angular profile')
    zero(pressure_shape.subs(substitution)-G/radial**3,
         'pressure angular profile')
    # The equatorial cone |mu|<=1/4 stays away from both angular zero sets.
    zero(F-33/(64*s.pi)-15*(s.Rational(1,16)-mu*mu)/(4*s.pi),
         'positive lower bound for the parent shape on the cone')
    zero(-G-13/(64*s.pi)-3*(s.Rational(1,16)-mu*mu)/(4*s.pi),
         'nonzero pressure shape on the same cone')
    root = 1/s.sqrt(5)
    angular = s.simplify(4*s.pi*(s.integrate(F**3,(mu,0,root))
                                -s.integrate(F**3,(mu,root,1))))
    expected = 27*(75+2*s.sqrt(5))/(175*s.pi**2)
    zero(angular-expected, 'full spherical integral of the absolute cubic profile')
    exponent = s.symbols('exponent',real=True)
    cutoff,L = s.symbols('cutoff L',positive=True)
    primitive = radial**(3*exponent-12)/(3*exponent-12)
    zero(s.diff(primitive,radial)-radial**(3*exponent-13),
         'leading stock radial primitive, for exponent below four')
    C = expected*cutoff**(3*exponent-12)/(L**s.Rational(3,2)*(12-3*exponent))
    zero(C.subs(exponent,s.Rational(10,3))-expected/(2*L**s.Rational(3,2)*cutoff**2),
         'finite leading stock coefficient at the diagnostic threshold')
    return dict(pressure_shape=str(s.factor(pressure_shape)),
                parent_shape=str(parent_shape), angular_cubic_integral=str(expected),
                profile='p_lead=delta(t)*partial_zz N; u_lead=-A(t)*grad(partial_zz N); m_lead=A(t)*F',
                leading_stock_coefficient=str(C),
                scope='The profile is used outside one fixed positive radius; all actual interior and remainder terms stay in the residual.')


def density_and_tail_orders():
    exponent = s.symbols('exponent',positive=True)
    U = 1+r*r+z*z
    h = U**(-exponent)
    lap = s.diff(h,r,2)+3*s.diff(h,r)/r+s.diff(h,z,2)
    zero(lap/h-(-10*exponent/U+4*exponent*(exponent+1)*(r*r+z*z)/U**2),
         'five-dimensional density diffusion loses two powers at infinity')
    # On cones, m~R^-5, p~R^-3 and h~L R^(-2s).
    pressure_square_order = -5+3*exponent-6-2+2
    signed_work_order = -5-5-5+3*exponent+2
    zero(pressure_square_order-(3*exponent-11), 'squared pressure radial power')
    zero(signed_work_order-(3*exponent-13), 'original signed pressure radial power')
    zero(pressure_square_order.subs(exponent,s.Rational(10,3))+1,
         'actual cone produces a logarithmic diagnostic divergence')
    zero(signed_work_order.subs(exponent,s.Rational(10,3))+3,
         'signed work keeps an integrable leading tail')
    x = s.symbols('x',positive=True)
    zero(s.diff(s.log(x),x)-1/x, 'logarithmic lower-bound integral diverges')
    zero(pressure_square_order.subs(exponent,3)+2,
         'the original exponent-three density avoids this conical divergence')
    return dict(density='h0=(1+R^2)^(-s); h(t)-h0=O_T(R^(-2s-2)) on a compact smooth prefix',
                pressure_square_radial_power=str(pressure_square_order),
                signed_work_radial_power=str(signed_work_order),
                threshold='s=10/3: V_p is infinite at every sufficiently small positive time for the actual coupled Gaussian datum, while R, W and D remain finite.',
                scope='Actual asymptotics and comparison establish the lower bound; these algebraic checks alone do not certify a PDE solution. The original s=3 observer is not refuted by this tail test.')


def bellman_payment():
    q,E,tau,C = s.symbols('q E tau C',nonnegative=True)
    v = s.symbols('v',real=True)
    reachable = q+E*tau
    B = C*(reachable**3-q**3)
    nonnegative = C*E*tau*(3*q*q+3*q*E*tau+(E*tau)**2)
    zero(B-nonnegative, 'the correction is nonnegative before the original horizon')
    # q=abs(A), q'=v=sgn(A)*delta almost everywhere, tau'=-1, v<=E0.
    work = 3*C*q*q*v
    rate = s.diff(B,q)*v-s.diff(B,tau)
    zero(rate+work-3*C*reachable**2*(v-E),
         'one original-energy allowance pays every compatible continuation')
    zero(B.subs(tau,0), 'the correction expires at the prescribed horizon')
    zero(B.subs(q,0)-C*(E*tau)**3, 'initial allowance depends on original energy and horizon')
    Rdot,D,W,Wlead = s.symbols('Rdot D W Wlead',real=True)
    # Rdot+D=W and Bdot+Wlead<=0 imply the stated physical consumer.
    zero((Rdot+D-W)+(rate+Wlead)-((Rdot+rate)+D-(W-Wlead)),
         'the correction attaches to the actual stock without removing its residual')
    return dict(correction='B(t)=C*((abs(A(t))+E0*(H-t))^3-abs(A(t))^3)>=0',
                paid_work='W_lead(t)=3*C*abs(A(t))*A(t)*delta(t)',
                inequality='B_prime+W_lead<=0 almost everywhere',
                original_allowance='B(0)=C*(E0*H)^3',
                physical_consumer='(R+B)_prime+D <= W-W_lead',
                composition='A and the original E0,H are inherited at every seam; integrated payments telescope.',
                limitation='The complete pressure remainder W-W_lead and arbitrary-history continuation are not bounded here.')


if __name__ == '__main__':
    output = dict(moments=physical_moments(), geometry=tail_geometry(),
                  tail_orders=density_and_tail_orders(), payment=bellman_payment())
    names = ('integrated_swirl_pressure.py','rotational_joint_enstrophy.py',
             'circulation_source_reserve.py','rotational_curl_reserve.py')
    paths = [Path(__file__)]+[Path(__file__).with_name(name) for name in names]
    output['source_sha256'] = {p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    print(json.dumps(output,indent=2))
