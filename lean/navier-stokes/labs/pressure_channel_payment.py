#!/usr/bin/env python3
"""Pressure-channel identities, a coarse-history payment, and exact adverse work.

All sources come from the full axisymmetric velocity. Kernel bounds, actual
local evolution and spatial limiting arguments are analytic in README.md;
these exact fixtures are not Lean certificates or a regularity proof.
"""

import hashlib
import json
from pathlib import Path

import sympy as s

from rotational_curl_reserve import require, zero
from rotational_joint_enstrophy import r, z
from integrated_swirl_pressure import gaussian_pair, d
from circulation_source_reserve import lap3, div3
from axis_deformation_pressure import green_origin


def source_channels():
    ur, uz, b = [s.Function(name)(r,z) for name in ('ur','uz','b')]
    mer = s.Matrix([[s.diff(ur,r),0,s.diff(ur,z)],
                    [0,ur/r,0],[s.diff(uz,r),0,s.diff(uz,z)]])
    swirl = s.Matrix([[0,-b,0],[b+r*s.diff(b,r),0,r*s.diff(b,z)],[0,0,0]])
    zero(s.trace(mer*swirl+swirl*mer), 'both mixed Poisson-source terms vanish')
    zero(s.trace(swirl*swirl)+s.diff(r*r*b*b,r)/r,
         'complete swirl source retains the cylindrical basis derivatives')
    source_mer = s.diff(ur,r)**2+(ur/r)**2+s.diff(uz,z)**2+2*s.diff(ur,z)*s.diff(uz,r)
    zero(s.trace(mer*mer)-source_mer, 'meridional source retains its axial interaction')
    return dict(meridional=str(source_mer),swirl='-r^(-1) partial_r(r^2 b^2)',
                scope='Poisson sources split exactly; the two pressure works still use the same complete evolving velocity and observer.')


def coarse_kernel_and_payment():
    x = s.Matrix(s.symbols('x0 x1 x2',real=True))
    a = s.Matrix(s.symbols('a0 a1 a2',real=True))
    tau,L,ell,E,H,t,e,J = s.symbols('tau L ell E H t e J',positive=True)
    heat = s.exp(-x.dot(x)/(4*tau))/(4*s.pi*tau)**s.Rational(3,2)
    directional2 = sum(a[i]*a[j]*s.diff(heat,x[i],x[j]) for i in range(3) for j in range(3))
    for k in range(3):
        expected=heat*(-x[k]*x.dot(a)**2/(8*tau**3)
                       +(2*a[k]*x.dot(a)+a.dot(a)*x[k])/(4*tau**2))
        zero(s.diff(directional2,x[k])-expected,
             'contracted Gaussian third derivative retains the whole stress tensor')
    q = s.symbols('q',nonnegative=True)
    for power in (1,3):
        zero(s.diff(q**power*s.exp(-q*q),q)
             -q**(power-1)*s.exp(-q*q)*(power-2*q*q),
             'Gaussian envelope maximum has its exact critical point')
    # exp(1)>2 implies each of q^3 exp(-q^2) and (3/2)q exp(-q^2)
    # is at most one. Together they are bounded by two.
    require(s.Rational(3,4)**3<1 and s.Rational(3,4)<1,
            'safe rational bounds for both Gaussian maxima')
    C = (4*s.pi)**s.Rational(-3,2)
    zero(s.integrate(2*C/tau**3,(tau,L*L,s.oo))-C/L**4,
         'coarse pressure kernel is integrated over all heat times above L squared')
    Jbound = s.simplify((9/s.pi**2)*(8*s.pi/3)
                       *s.integrate(r**4/(ell*ell+r*r)**5,(r,0,s.oo)))
    zero(Jbound-9/(32*ell**5), 'physical energy of the smooth parent has a fixed profile bound')
    Cq = 3/(s.pi*ell**4)
    cost=6*e**s.Rational(-3,2)*(C/L**4+Cq)*(E**2+J*E**3*t*t)
    reserve=6*e**s.Rational(-3,2)*(C/L**4+Cq)*(E**2*(H-t)+J*E**3*(H**3-t**3)/3)
    zero(s.diff(reserve,t)+cost, 'one remaining reserve pays every known pressure contribution')
    zero(reserve.subs(t,H), 'the known-pressure allowance is not reissued at a later seam')
    return dict(kernel_constant=str(C),
                gradient='||grad exp(L^2 Delta)p||_infinity <= C*E(t)/L^4',
                channel_sum='sum_j ||grad exp(L^2 Delta)p_j||_infinity <= C*(E_mer+E_sw)/L^4',
                parent_profile_energy_bound=str(Jbound),
                reserve=str(reserve),
                open='int_0^T Omega*(W_high-D/2) <= K_high(original datum,nu,H)',
                limitation='The payment uses only a kinetic-energy bound. It also bounds the velocity-generated pressure of a forced flow with that bound; an additional pressure from the force is not included.')


def gaussian_channels():
    exponential=s.exp(-r*r-z*z)
    chi=z*exponential
    ur,uz=-r*s.diff(chi,z),2*chi+r*s.diff(chi,r)
    b=2*s.sqrt(2)*z*exponential
    zero(div3(s.Matrix([ur,uz])), 'actual smooth Gaussian datum is incompressible')
    zero((-ur/r)**2+b*b-(1+2*z*z)**2*exponential**2,
         'both horizontal components give an exact positive square')
    gradient=s.Matrix([[s.diff(ur,r),-b,s.diff(ur,z)],
                       [b+r*s.diff(b,r),ur/r,r*s.diff(b,z)],
                       [s.diff(uz,r),0,s.diff(uz,z)]])
    matrix=gradient.applyfunc(lambda f:s.cancel(f/exponential))
    energy=gaussian_pair(s.cancel((ur*ur+uz*uz+r*r*b*b)/exponential**2),s.Integer(2),True)
    kinetic_loss=gaussian_pair(s.trace(matrix.T*matrix),s.Integer(2),True)
    zero(energy-15*s.sqrt(2)*s.pi**s.Rational(3,2)/32, 'original complete kinetic energy')
    zero(kinetic_loss-119*s.sqrt(2)*s.pi**s.Rational(3,2)/32,
         'actual kinetic dissipation is strictly positive')
    total=s.expand(s.trace(matrix*matrix))
    swirl=s.expand(s.cancel((-2*b*b-r*s.diff(b*b,r))/exponential**2))
    sources={'meridional':s.expand(total-swirl),'swirl':swirl}
    variance=(d-1)/(4*d)
    y=s.symbols('y',positive=True)
    output={}
    for name,source in sources.items():
        zero(gaussian_pair(source,s.Integer(2),True), 'each full pressure source has zero mass')
        pairs={}
        for absolute in (False,True):
            heat=0
            for (ir,iz),co in s.Poly(source,r,z).terms():
                require(ir%2==0 and iz%2==0, 'even Gaussian source powers')
                i,j=ir//2,iz//2
                radial=sum(s.binomial(i,k)**2*s.factorial(k)*(2*variance)**k
                           *(r*r/d**2)**(i-k) for k in range(i+1))
                axial=sum(s.binomial(2*j,2*k)*s.factorial2(2*k-1)*variance**k
                          *(z/d)**(2*j-2*k) for k in range(j+1))
                heat+=(abs(co) if absolute else co)*radial*axial
            heat=s.expand(heat)
            if not absolute:
                zero(heat.subs(d,1)-source, 'pressure heat evolution retains the whole initial source')
                evolved=heat*d**s.Rational(-3,2)*s.exp(-2*(r*r+z*z)/d)
                zero(8*s.diff(evolved,d)-lap3(evolved), 'full three-dimensional pressure heat equation')
            # Before expansion each majorant term and its r derivative is
            # nonnegative for r>=0,d>=1, using even axial powers.
            weight=r**3*((1+2*z*z)**2 if absolute else 1-4*z**4)
            derivative=s.diff(heat,r)+(1 if absolute else -1)*4*r*heat/d
            integrand=gaussian_pair(weight*derivative,2*(d+1)/d)/d**s.Rational(3,2)
            rational=s.factor(integrand.subs(d,y*y)*2*y/s.pi)
            primitive=s.integrate(rational,y)
            zero(s.diff(primitive,y)-rational, 'exact rational pressure-work primitive')
            endpoint=s.simplify(s.limit(primitive,y,s.oo)-primitive.subs(y,1))
            value=s.simplify(3*s.pi**2*endpoint/4)
            pairs['absolute_bound' if absolute else 'signed_work']=str(value)
            pairs['absolute_primitive' if absolute else 'signed_primitive']=str(primitive)
        expected=(3*s.pi**2*(10336-6285*s.pi)/2097152 if name=='meridional'
                  else 3*s.pi**2*(256+213*s.pi)/262144)
        zero(s.sympify(pairs['signed_work'])-expected, 'entire spatial channel work')
        expected_abs=(3*s.pi**2*(-160+527943*s.pi)/2097152 if name=='meridional'
                      else 3*s.pi**2*(-109568+48933*s.pi)/262144)
        zero(s.sympify(pairs['absolute_bound'])-expected_abs, 'entire absolute-work majorant')
        output[name]=dict(source=str(source),**pairs)
    M,B,L=1-2*z*z,2*s.sqrt(2)*z,1+2*z*z
    relative=sum((s.diff(f,r)-2*r*f+2*f/r)**2+(s.diff(f,z)-2*z*f)**2 for f in (M,B))
    R=gaussian_pair(r**3*L**3,s.Integer(3),True)
    D1=gaussian_pair(s.expand(3*r**3*L*relative),s.Integer(3),True)
    D2=gaussian_pair(s.cancel(s.Rational(3,4)*r**3*L**3*((2/r-4*r)**2+(8*z/L-4*z)**2)),s.Integer(3),True)
    zero(R-8*s.pi**2/81, 'flat physical stock')
    zero(D1-2*s.pi**2, 'complete relative-gradient diffusion')
    zero(D2-14*s.pi**2/27, 'complete critical-power diffusion')
    zero(D1+D2-68*s.pi**2/27, 'all physical diffusion, with zero axis boundary')
    output['flat_stock']=str(R)
    output['flat_diffusion_over_nu']=str(D1+D2)
    output['kinetic_energy']=str(energy)
    output['kinetic_gradient_squared']=str(kinetic_loss)
    origin={}
    for name,source in sources.items():
        if name=='swirl':
            source=s.Rational(5,8)*source  # The isotropic fixture has B^2=5.
        radial_hessian=(s.diff(source,r,2)+s.diff(source,r)/r-8*r*s.diff(source,r)
                        +(16*r*r-8)*source)/2
        origin[name]=green_origin(radial_hessian)
    zero(origin['meridional']+s.Rational(12,7), 'isotropic fixture keeps the complete meridional pressure')
    zero(origin['swirl']-s.Rational(2,7), 'isotropic fixture keeps the complete swirl pressure')
    E_horizontal=gaussian_pair(s.cancel((ur*ur+s.Rational(5,8)*r*r*b*b)/exponential**2),s.Integer(2),True)/2
    E_axial=gaussian_pair(s.cancel(uz*uz/exponential**2),s.Integer(2),True)
    zero(E_horizontal-E_axial, 'isotropic tensor does not discard either source channel')
    output['isotropic_fixture']=dict(meridional_P=str(origin['meridional']),
        swirl_P=str(origin['swirl']),total_P=str(sum(origin.values())),
        scope='B=sqrt(5) fixture from RP14; an axis-curvature test, not a whole-domain sign claim')
    return output


def finite_observer_bounds():
    pi_lower,pi_upper=s.Integer(3),s.Rational(22,7)
    kappa=s.Rational(1,10000)
    mer_abs_upper=3*pi_upper**2*(-160+527943*pi_upper)/2097152
    sw_abs_upper=3*pi_upper**2*(-109568+48933*pi_upper)/262144
    require(0<mer_abs_upper<32 and 0<sw_abs_upper<8,
            'rational bounds on the complete absolute integrals')
    sw_lower=3*pi_lower**2*(256+213*pi_lower)/262144
    mer_negative=3*pi_lower**2*(6285*pi_lower-10336)/2097152
    total_reversed=27*pi_lower**2*(509*pi_lower-1376)/2097152
    floor_error=2*kappa*40/9
    require(sw_lower-2*kappa*8/9>s.Rational(9,100), 'swirl pressure is positive for a finite stochastic density')
    require(mer_negative-2*kappa*32/9>s.Rational(1,10), 'meridional pressure has the opposite whole-domain sign')
    # e=1, heat length L=10, parent length ell=100.
    require(pi_upper**3<36, 'pi^(3/2)<6')
    coarse_upper=s.Rational(675,4096)*6/10**4
    smooth_upper=s.Rational(81,2048000000)*10
    require(coarse_upper<s.Rational(1,10000), 'entire coarse pressure work has a small explicit bound on this datum')
    require(smooth_upper<s.Rational(1,2000000), 'subtracted smooth pressure has a small explicit bound')
    require(total_reversed-floor_error-coarse_upper-smooth_upper>s.Rational(1,64),
            'positive residual and high-pressure work survive both exact subtractions')
    require(10*(s.Rational(136,27)+480*kappa**2*s.Rational(8,81))<51,
            'complete diffusion for the finite positive floor')
    require(s.Rational(1,64)-s.Rational(51,4096)>s.Rational(1,512),
            'amplitude at least 4096 viscosities beats all actual diffusion')
    lam=s.symbols('lam',positive=True)
    zero((lam**s.Rational(3,2))**2/lam**3-1, 'concentration preserves kinetic energy')
    zero((lam**s.Rational(3,2))**4/lam**2-lam**4, 'pressure work concentration exponent')
    zero((lam**s.Rational(3,2))**3/lam-lam**s.Rational(7,2), 'physical diffusion concentration exponent')
    return dict(parameters='e=1, kappa=1/10000, h0=kappa*(1+rho^2)^(-3), L=10, ell=100',
                signs='V: W_sw>9/100 and W_mer<-1/10; reversing meridional velocity reverses both works',
                reversed='-a V: W_res(0)>a^4/64, W_high(0)>a^4/64, D(0)<51*nu*a^3',
                actual_growth='a>=4096nu implies R_prime(0)>a^4/512; continuity gives a nonzero actual smooth interval',
                concentration='Energy one: W_high~c*lambda^4/E_V^2, D~nu*(68pi^2/27)*lambda^(7/2)/E_V^(3/2), c=27pi^2*(509pi-1376)/2097152>0',
                limitation='No common lower bound on the short interval is asserted. These tests refute channel sign and instantaneous absorption, not an original-full-datum history allowance.')


if __name__=='__main__':
    output=dict(channels=source_channels(),coarse=coarse_kernel_and_payment(),
                gaussian=gaussian_channels(),finite_test=finite_observer_bounds())
    paths=[Path(__file__)]+[Path(__file__).with_name(name) for name in
        ('rotational_curl_reserve.py','rotational_joint_enstrophy.py',
         'integrated_swirl_pressure.py','circulation_source_reserve.py',
         'axis_deformation_pressure.py')]
    output['source_sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    print(json.dumps(output,indent=2))
