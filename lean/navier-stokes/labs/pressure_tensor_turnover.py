#!/usr/bin/env python3
"""Exact unforced pressure redistribution from an isotropic energy tensor.

The stress balance is reused from pressure_stress_transport.py. Gaussian
pressure moments and concentration exponents are checked here. Actual
short-time evolution and smoothed-kernel limits remain analytic.
"""

import hashlib
import json
from pathlib import Path

import sympy as s

from integrated_swirl_pressure import r, z, d, gaussian_pair
from rotational_curl_reserve import require, zero
from circulation_source_reserve import lap3, div3


def actual_tensor_rate():
    B=s.symbols('B',real=True)
    exponential=s.exp(-r*r-z*z)
    chi=z*exponential
    ur,uz=-r*s.diff(chi,z),2*chi+r*s.diff(chi,r)
    b=B*z*exponential
    v=s.Matrix([ur,uz])
    zero(div3(v), 'complete datum is incompressible')
    gradient=s.Matrix([[s.diff(ur,r),-b,s.diff(ur,z)],
                       [b+r*s.diff(b,r),ur/r,r*s.diff(b,z)],
                       [s.diff(uz,r),0,s.diff(uz,z)]])
    matrix=gradient.applyfunc(lambda f:s.cancel(f/exponential))
    source=s.expand(s.trace(matrix*matrix))
    convection=s.Matrix([ur*s.diff(ur,r)+uz*s.diff(ur,z)-r*b*b,
                         ur*s.diff(uz,r)+uz*s.diff(uz,z)])
    zero(div3(convection)-source*exponential**2,
         'canonical pressure retains radial, axial and swirl convection')
    moments=lambda expr:gaussian_pair(s.cancel(expr/exponential**2),s.Integer(2),True)
    horizontal=moments(ur*ur+r*r*b*b)/2
    axial=moments(uz*uz)
    Zaxial=moments(s.diff(uz,r)**2+s.diff(uz,z)**2)
    Zall=gaussian_pair(s.trace(matrix.T*matrix),s.Integer(2),True)
    Zdelta=s.factor((3*Zaxial-Zall)/2)
    zero(horizontal-s.sqrt(2)*s.pi**s.Rational(3,2)*(B*B+3)/64,
         'horizontal component energy')
    zero(axial-s.sqrt(2)*s.pi**s.Rational(3,2)/8, 'axial component energy')
    zero((axial-horizontal).subs(B,s.sqrt(5)), 'isotropic original energy tensor')
    zero(Zdelta+s.sqrt(2)*s.pi**s.Rational(3,2)*(7*B*B-45)/64,
         'complete anisotropic kinetic dissipation')
    zero(moments(uz*lap3(uz))+Zaxial, 'independent viscous integration by parts')
    advective=s.cancel(uz*convection[1]/exponential**3)
    zero(gaussian_pair(advective,s.Integer(3),True), 'axial transport has zero integrated energy work')

    variance=(d-1)/(4*d)
    heat=0
    for (ir,iz),co in s.Poly(source,r,z).terms():
        require(ir%2==0 and iz%2==0, 'even complete Gaussian source')
        i,j=ir//2,iz//2
        radial=sum(s.binomial(i,k)**2*s.factorial(k)*(2*variance)**k
                   *(r*r/d**2)**(i-k) for k in range(i+1))
        axial_moment=sum(s.binomial(2*j,2*k)*s.factorial2(2*k-1)*variance**k
                         *(z/d)**(2*j-2*k) for k in range(j+1))
        heat+=co*radial*axial_moment
    heat=s.expand(heat)
    evolved=heat*d**s.Rational(-3,2)*s.exp(-2*(r*r+z*z)/d)
    zero(heat.subs(d,1)-source, 'original canonical pressure source')
    zero(8*s.diff(evolved,d)-lap3(evolved), 'entire pressure heat evolution')
    weight=s.cancel(s.diff(uz,z)/exponential)
    pair=gaussian_pair(weight*heat,1+2/d,True)/d**s.Rational(3,2)
    opposite=gaussian_pair(s.cancel(uz/exponential)*(s.diff(heat,z)-4*z*heat/d),
                          1+2/d,True)/d**s.Rational(3,2)
    zero(pair+opposite, 'pressure redistribution agrees with direct axial force work')
    y=s.symbols('y',positive=True)
    rational=s.factor(pair.subs(d,y*y-2)*2*y/s.pi**s.Rational(3,2))
    expected=-16*(B*B*y**4-3*B*B*y**2+9*y**4-54*y**2+33)/y**12
    zero(rational-expected, 'full space and heat integral has a rational integrand')
    primitive=s.integrate(rational,y)
    zero(s.diff(primitive,y)-rational, 'pressure-strain primitive')
    value=s.simplify(s.pi**s.Rational(3,2)
                     *(s.limit(primitive,y,s.oo)-primitive.subs(y,s.sqrt(3)))/8)
    zero(value-4*s.sqrt(3)*s.pi**s.Rational(3,2)*(12-B*B)/5103,
         'exact global pressure-strain integral')
    C=s.simplify(3*value.subs(B,s.sqrt(5)))
    V=s.simplify(2*Zdelta.subs(B,s.sqrt(5)))
    E=s.simplify((2*horizontal+axial).subs(B,s.sqrt(5)))
    Z=s.simplify(Zall.subs(B,s.sqrt(5)))
    zero(C-4*s.sqrt(3)*s.pi**s.Rational(3,2)/243, 'nonlinear anisotropy production')
    zero(V-5*s.sqrt(2)*s.pi**s.Rational(3,2)/16, 'viscous anisotropy production')
    zero(E-3*s.sqrt(2)*s.pi**s.Rational(3,2)/8, 'full isotropic energy')
    zero(Z-49*s.sqrt(2)*s.pi**s.Rational(3,2)/16, 'full kinetic gradient energy')
    # 32*C >= 2*V follows by squaring the two positive radical coefficients.
    require(s.Rational(128,243)**2*3>s.Rational(5,8)**2*2,
            'amplitude at least 32 viscosities gives opposite actual signs')
    return dict(pressure_strain=str(value),primitive=str(primitive),
                E_base=str(E),Z_base=str(Z),C=str(C),V=str(V),
                rates='delta_plus_prime=C*a^3-nu*V*a^2; delta_minus_prime=-C*a^3-nu*V*a^2',
                signs='a>=32nu implies delta_plus_prime>=C*a^3/2>0 and delta_minus_prime<-C*a^3',
                kinetic='E_plus_prime=E_minus_prime=-2nu*a^2*Z_base<0',
                scope='Actual canonical pressure and full integrated unforced tangent; same initial energy tensor and pressure do not identify the signed rate.')


def filtered_receiver_and_concentration():
    x,y,R,tau=s.symbols('x y R tau',real=True,positive=True)
    G=s.exp(-(x*x+y*y+z*z)/(4*tau))/(4*s.pi*tau)**s.Rational(3,2)
    difference=(s.diff(G,z,2)-s.diff(G,x,2)).subs({x:0,y:0,z:R})
    axis_heat=s.exp(-R*R/(4*tau))/(4*s.pi*tau)**s.Rational(3,2)
    zero(difference-R*R*axis_heat/(4*tau*tau),
         'fixed noncentral axial receiver sees nonzero anisotropic coarse pressure')
    zero(s.Rational(2,3)*difference-R*R*axis_heat/(6*tau*tau),
         'trace-free tensor contraction has the correct coefficient')
    lam,E,nu,C,V,Z=s.symbols('lam E nu C V Z',positive=True)
    amplitude=lam**s.Rational(3,2)/s.sqrt(E)
    zero(amplitude**2*E/lam**3-1, 'concentrated original energy is exactly one')
    zero(amplitude**3/lam**2-lam**s.Rational(5,2)/E**s.Rational(3,2),
         'complete nonlinear tensor-rate scaling')
    zero(amplitude**2/lam-lam**2/E, 'complete viscous tensor-rate scaling')
    rate=C*lam**s.Rational(5,2)/E**s.Rational(3,2)-nu*V*lam**2/E
    ratio=rate/(1+nu*Z*lam**2/E)
    zero(s.limit(ratio/s.sqrt(lam),lam,s.oo)-C/(nu*Z*s.sqrt(E)),
         'no energy-only bound by one plus viscous dissipation for the initial rate')
    zero(amplitude**3/lam**3-lam**s.Rational(3,2)/E**s.Rational(3,2),
         'first-moment nonlinear kernel-replacement remainder')
    zero(nu*amplitude**2/lam**2-nu*lam/E,
         'first-moment viscous kernel-replacement remainder')
    return dict(fixed_receiver='x_R=(0,0,R), R>0; L>0 fixed',
                response='kappa_L(R)=R^2/6 * int_(L^2)^infinity tau^(-2)G_tau(x_R) d tau >0',
                material_rate='D_t p_low,plus/minus(0,x_R)=+/-kappa_L(R)*C*lambda^(5/2)/E_base^(3/2)+O(nu*lambda^2+lambda^(3/2))',
                initial_equal='The two initial pressures agree everywhere, including after smoothing; their material rates have opposite signs for sufficiently large lambda.',
                limitation='The large rates occur across distinct smooth initial data. They do not establish large time-integrated absolute variation, infinite renewals or blowup.')


def retained_signed_payment():
    E0,t,H,C,A,delta=s.symbols('E0 t H C A delta',real=True)
    positive=s.symbols('positive',nonnegative=True)
    # Reuse the earlier admissible control |delta|<=E0. For each sign of A,
    # the original pressure-tail Bellman payment retains its full derivative.
    for sign in (-1,1):
        a=sign*positive
        stock=C*positive**3
        reserve=C*((positive+E0*(H-t))**3-positive**3)
        derivative=s.diff(reserve,t)+s.diff(reserve,positive)*sign*delta
        work=3*C*positive**2*sign*delta
        zero(derivative+work-3*C*(positive+E0*(H-t))**2*(sign*delta-E0),
             'existing accumulated-parent payment requires no bound on delta prime')
    return dict(memory='delta(t)=delta_prime(0)t+o(t); A(t)=delta_prime(0)t^2/2+o(t^2)',
                far_pressure='p_lead=delta(t)*partial_zz N',
                far_velocity='u_lead=-A(t)*grad(partial_zz N)',
                payment='The PT8 reserve still pays this generated parent using |delta|<=E0. No derivative clock or new allowance is required.',
                open='The joint short-scale pressure work in PC5 remains unpaid.')


if __name__=='__main__':
    output=dict(tensor=actual_tensor_rate(),receiver=filtered_receiver_and_concentration(),
                retained=retained_signed_payment())
    paths=[Path(__file__)]+[Path(__file__).with_name(name) for name in
        ('integrated_swirl_pressure.py','rotational_curl_reserve.py',
         'rotational_joint_enstrophy.py','circulation_source_reserve.py',
         'pressure_stress_transport.py','pressure_history_source.py')]
    output['source_sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    print(json.dumps(output,indent=2))
