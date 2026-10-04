#!/usr/bin/env python3
"""Joint pressure/receiver correction: coercivity test and complete drift.

The canonical Gaussian pressure and all generated source terms are kept.
PDE realization, operator estimates and the conditional consumer are analytic
in README.md. Exact algebra here is not a Lean certificate.
"""

import hashlib
import json
from pathlib import Path

import sympy as s

from integrated_swirl_pressure import source_and_heat, gaussian_pair, r, z, d
from rotational_curl_reserve import require, zero


def gaussian_corrector():
    source, heat, energy = source_and_heat()
    y = s.symbols('y', positive=True)
    weight = r**3*(1-4*z**4)
    rate = 2*(d+1)/d
    direct = gaussian_pair(weight*(s.diff(heat,r)-4*r*heat/d), rate)/d**s.Rational(3,2)
    by_parts = -gaussian_pair((s.diff(weight,r)-4*r*weight)*heat, rate)/d**s.Rational(3,2)
    zero(direct-by_parts, 'receiver integration by parts has zero axis flux')
    rational = s.factor(direct.subs(d,y*y)*2*y*(y*y-1)/(8*s.pi))
    primitive = s.integrate(rational,y)
    zero(s.diff(primitive,y)-rational, 'whole-pressure inverse-Laplacian primitive')
    value = s.simplify(3*s.pi**2*(s.limit(primitive,y,s.oo)-primitive.subs(y,1))/4)
    expected = 3*s.pi**2*(3753*s.pi-7696)/4194304
    zero(value-expected, 'signed correction uses the complete canonical pressure')

    variance = (d-1)/(4*d)
    majorant = 0
    for (ir,iz), co in s.Poly(source,r,z).terms():
        require(ir%2==0 and iz%2==0, 'even source gives positive Gaussian majorants')
        i,j=ir//2,iz//2
        radial=sum(s.binomial(i,k)**2*s.factorial(k)*(2*variance)**k
                   *(r*r/d**2)**(i-k) for k in range(i+1))
        axial=sum(s.binomial(2*j,2*k)*s.factorial2(2*k-1)*variance**k
                  *(z/d)**(2*j-2*k) for k in range(j+1))
        majorant += abs(co)*radial*axial
    majorant=s.expand(majorant)
    positive_pair=gaussian_pair(r**3*(1+2*z*z)**2
        *(s.diff(majorant,r)+4*r*majorant/d), rate)/d**s.Rational(3,2)
    positive_rational=s.factor(positive_pair.subs(d,y*y)*2*y*(y*y-1)/(8*s.pi))
    positive_primitive=s.integrate(positive_rational,y)
    zero(s.diff(positive_primitive,y)-positive_rational, 'absolute correction majorant primitive')
    absolute=s.simplify(3*s.pi**2*(s.limit(positive_primitive,y,s.oo)
                                  -positive_primitive.subs(y,1))/4)
    zero(absolute-9*s.pi**2*(248464+130393*s.pi)/4194304,
         'complete finite absolute correction bound')
    lower=3*3**2*(3753*3-7696)/s.Integer(4194304)
    upper=9*s.Rational(22,7)**2*(248464+130393*s.Rational(22,7))/4194304
    require(lower>s.Rational(1,50) and upper<16,
            'rational sign and majorant bounds require only 3<pi<22/7')
    kappa=s.Rational(1,10000)
    require(lower-2*kappa*16/9-s.Rational(1,10000)>s.Rational(1,64),
            'positive correction survives finite circulation weight and heat cutoff')
    require(s.Rational(675,4096)*6<1,
            'coarse corrector tail is below 1/L^2 for this complete datum')
    require(8*s.Rational(22,7)**2/81<1, 'physical initial stock is below one')
    a,nu=s.symbols('a nu',positive=True)
    zero((a**3-a**4/(128*nu)).subs(a,256*nu)+(256*nu)**3,
         'negative correction dominates the stock at a finite amplitude')
    lam=s.symbols('lam',positive=True)
    amp=lam**s.Rational(3,2)
    zero(amp**2/lam**3-1, 'kinetic energy preserved by concentration')
    zero(amp**3/lam**3-lam**s.Rational(3,2), 'initial stock concentration power')
    zero(amp**4/lam**4-lam**2, 'signed elliptic correction concentration power')
    zero(amp**6/lam**6-lam**3, 'positive completion concentration power')
    return dict(C_infinity=str(value), absolute_bound=str(absolute),
                primitive=str(primitive), absolute_primitive=str(positive_primitive),
                energy=energy,
                finite_parameters='e=1, h0=10^(-4)(1+rho^2)^(-3), L=100; C_L(V)>1/64 and R(V)<1',
                failure='J(-a V)=R+C_L/(2nu)<-a^3 when a>=256nu; actual kinetic energy decreases',
                concentration='At energy one and fixed positive L: C_L(-u_lambda)~-C_infinity*lambda^2/E_V^2, R~R_V*lambda^(3/2)/E_V^(3/2)',
                limitation='This rejects the uncompleted reserve and an energy-only lower allowance. It does not reject a full-datum allowance or a cutoff chosen separately for each datum.')


def two_factor_diffusion():
    x=s.symbols('x0:3',real=True)
    t,nu=s.symbols('t nu',real=True)
    variables=(t,)+x
    u=s.Matrix([s.Function('u'+str(i))(*variables) for i in range(3)])
    a=s.Matrix([s.Function('a'+str(i))(*variables) for i in range(2)]+[0])
    q=s.Function('q')(*variables)
    grad=lambda f:s.Matrix([s.diff(f,c) for c in x])
    lap=lambda f:sum(s.diff(f,c,2) for c in x)
    material=lambda f:s.diff(f,t)+u.dot(grad(f))
    operator=lambda f:material(f)-nu*lap(f)
    dq=grad(q)
    flux=s.Matrix([sum(s.diff(a[i],x[j])*dq[i]-a[i]*s.diff(dq[i],x[j])
                       for i in range(3)) for j in range(3)])
    comm=sum(a[i]*s.diff(u[j],x[i])*dq[j] for i in range(3) for j in range(3))
    defect=sum(operator(a[i])*dq[i] for i in range(3))+a.dot(grad(operator(q)))-comm
    zero(material(a.dot(dq))-defect-2*nu*a.dot(grad(lap(q)))
         -nu*sum(s.diff(flux[j],x[j]) for j in range(3)),
         'pointwise two-factor identity retains receiver transport and its complete flux')
    return dict(pressure_primitive='q=int_0^(L^2) exp(s Delta)p ds; -Delta q=p_high',
                complete_source='S_q=Q_L[-u tensor grad p-grad p tensor u-2nu G]+[u.grad,Q_L]T',
                pairing='C_prime=-2nu W_high+E_corr',
                defect='E_corr=int [(D_t-nu Delta)a].grad q+a.grad S_q-a_i partial_i u_j partial_j q',
                factor='Both diffusing factors contribute; C/(2nu), not C/nu, cancels W_high.')


def positive_completion():
    x,y=s.symbols('x y',nonnegative=True)
    zero(x**3/s.Integer(2)-3*x*x*y+16*y**3
         -(x-4*y)**2*(x+2*y)/2, 'exact cubic remainder for half-stock coercivity')
    zero(s.diff(x**3-3*x*x*y+16*y**3,x,2).subs(x,y/2)+3*y,
         'coercivity does not imply joint convexity or payment of the mixed viscous terms')
    H,radius=s.symbols('H radius',positive=True)
    w0,w1,v0,v1,k=s.symbols('w0 w1 v0 v1 k',real=True)
    psi=(w0*w0+w1*w1)**s.Rational(3,2)/H**s.Rational(3,2)
    directions=s.Matrix([v0,v1,k])
    hessian=s.hessian(psi,(w0,w1,H)).subs({w0:radius,w1:0})
    actual=s.simplify((directions.T*hessian*directions)[0])
    completed=(3*radius*v1*v1/H**s.Rational(3,2)
        +6*radius*(v0-3*radius*k/(4*H))**2/H**s.Rational(3,2)
        +s.Rational(3,8)*radius**3*k*k/H**s.Rational(7,2))
    zero(actual-completed, 'pressure-primitive cubic has a nonnegative full joint Hessian')
    radius_coordinate=s.symbols('r_axis',positive=True)
    vr0,vr1,vz0,vz1,Hr,Hz=s.symbols('vr0 vr1 vz0 vz1 Hr Hz',real=True)
    hess_sum=actual.subs({v0:vr0,v1:vr1,k:Hr}) \
             +actual.subs({v0:vz0,v1:vz1,k:Hz}) \
             +3*radius**3/(radius_coordinate**2*H**s.Rational(3,2))
    squares=3*radius/H**s.Rational(3,2)*(
        (vr0-radius*Hr/H+radius/radius_coordinate)**2+vr1**2
        +(vz0-radius*Hz/H)**2+vz1**2
        +(vr0-radius*Hr/(2*H))**2+(vz0-radius*Hz/(2*H))**2)
    psi_radial=3*radius**2*vr0/H**s.Rational(3,2) \
               -s.Rational(3,2)*radius**3*Hr/H**s.Rational(5,2)
    zero(squares-hess_sum+3*radius**3*Hr/(radius_coordinate*H**s.Rational(5,2))
         -2*psi_radial/radius_coordinate,
         'complete circulation-weight diffusion is positive squares plus an exact radial flux')
    wr,wt,br,bt=s.symbols('wr wt br bt',real=True)
    rho=s.sqrt(wr*wr+wt*wt)
    pairing=-3*rho*(wr*br+wt*bt)/H**s.Rational(3,2)
    zero(pairing.subs({wr:-wr,wt:-wt},simultaneous=True)+pairing,
         'velocity reversal retains the joint receiver sign, also for isotropic data')
    nu,W,D,known,source,alpha,R,C,B,Ecorr,Wbeta,Dbeta=s.symbols(
        'nu W D known source alpha R C B Ecorr Wbeta Dbeta',real=True)
    base_rate=-D+alpha*R+W+known+source
    correction_rate=(-2*nu*W+Ecorr)/(2*nu)+2*(Wbeta-Dbeta)/nu**3
    zero(base_rate+correction_rate+D+2*Dbeta/nu**3-alpha*R-known-source
         -Ecorr/(2*nu)-2*Wbeta/nu**3,
         'joint corrected drift cancels exactly the named fine-pressure work')
    return dict(reserve='J_star=R+C/(2nu)+2 B/nu^3, B=int |grad_h q|^3/H^(3/2)',
                coercivity='R/2<=J_star<=3R/2+4B/nu^3',
                pressure_stock_drift='B_prime+D_beta=W_beta, D_beta>=0, W_beta=3 int abs(beta) beta.S_beta/H^(3/2)',
                physical_sources='S_beta=L beta=grad_h S_q-(partial_i u_j partial_j q)_(i=1,2); L H=-2nu H_r/r',
                diffusion='D_beta is the RP physical sum of squares with w replaced by beta; its axis boundary is zero.',
                mixed_diffusion='Mixed viscous terms remain in F_star. The full completed density has second x derivative -3y at x=y/2 for aligned fields; this alone is not an actual-flow counterexample.',
                continuation='(Omega^2 J_star)_prime+Omega^2 D_star<=Omega^2*(k_known+k_source+F_star), D_star=D+2D_beta/nu^3, F_star=E_corr/(2nu)+2W_beta/nu^3',
                open='Bound int_0^T Omega^2*(F_star-D_star/2) by one finite original-data allowance for every available same-datum prefix.',
                scope='Coercivity and the exact drift are established analytically. The correction source still contains pressure and its history; no payment or regularity claim follows from cancellation alone.')


def actual_heat_calibration():
    x,y,z,t=s.symbols('x y z t',real=True)
    nu,L=s.symbols('nu L',positive=True)
    coordinates=(x,y,z)
    velocity=s.exp(-2*nu*t)*s.Matrix([s.sin(x)*s.cos(y),-s.cos(x)*s.sin(y),0])
    pressure=s.exp(-4*nu*t)*(s.cos(2*x)+s.cos(2*y))/4
    grad=lambda f:s.Matrix([s.diff(f,c) for c in coordinates])
    lap=lambda f:sum(s.diff(f,c,2) for c in coordinates)
    zero(sum(s.diff(velocity[i],coordinates[i]) for i in range(3)),
         'periodic Taylor-Green calibration is divergence free')
    residual=s.diff(velocity,t)+s.Matrix([velocity.dot(grad(v)) for v in velocity]) \
             +grad(pressure)-nu*s.Matrix([lap(v) for v in velocity])
    require(all(s.trigsimp(v)==0 for v in residual),
            'calibration satisfies every unforced three-dimensional NS component')
    primitive=(1-s.exp(-4*L*L))*pressure/4
    zero(-lap(primitive)-(1-s.exp(-4*L*L))*pressure,
         'actual pressure heat primitive has its exact finite-scale multiplier')
    require(all(s.trigsimp(v)==0 for v in velocity.subs(x,x+s.pi)+velocity),
            'one translation reverses velocity')
    require(s.trigsimp(primitive.subs(x,x+s.pi)-primitive)==0,
            'the same translation preserves the actual pressure primitive')
    # Translation makes the signed pairing zero; the positive stock remains.
    R0,B0=s.symbols('R0 B0',positive=True)
    R=R0*s.exp(-6*nu*t)
    B=B0*s.exp(-12*nu*t)
    zero(s.diff(R+2*B/nu**3,t)+6*nu*R+24*B/nu**2,
         'positive completion decreases on a complete physical heat trajectory')
    return dict(flow='u=exp(-2nu t)*(sin x cos y,-cos x sin y,0) on the period-2pi torus',
                observer='H=1, A=0; this calibrates the correction, not the axisymmetric consumer',
                pairing='C=0 by translation symmetry; canonical pressure is nonzero',
                reserve='J_star=exp(-6nu t)R0+2exp(-12nu t)B0/nu^3',
                drift='J_star_prime=-6nu R-24B/nu^2<0')


if __name__=='__main__':
    result=dict(gaussian=gaussian_corrector(),diffusion=two_factor_diffusion(),
                completion=positive_completion(),calibration=actual_heat_calibration())
    paths=[Path(__file__)]+[Path(__file__).with_name(name) for name in
        ('integrated_swirl_pressure.py','rotational_curl_reserve.py',
         'rotational_joint_enstrophy.py','circulation_source_reserve.py',
         'pressure_channel_payment.py','regularized_parent_payment.py')]
    result['source_sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    print(json.dumps(result,indent=2))
