#!/usr/bin/env python3
"""A positive nonlinear return from initially pure swirl.

The periodic-axial inverse and physical radial moments are exact.
Slow axial localization gives smooth finite-energy whole-space data by
an analytic Fourier-multiplier estimate with explicit rational constants.
Optional quadrature checks the literal localized heat resolvent;
it is not an error certificate.
The result concerns the sign of a generated nonlinear contribution,
not growth of the complete viscous norm or singularity.
"""

import argparse
import json
import math
import sympy as s
from rotational_curl_reserve import require, zero


def radial_integral(poly,y,rate=3):
    return s.factor(sum(co*s.factorial(n)/s.Integer(rate)**(n+1)
                        for (n,),co in s.Poly(s.expand(poly),y).terms())/2)


def exact_profile():
    r=s.symbols('r',positive=True)
    y,a=s.symbols('y a',nonnegative=True)
    z,beta=s.symbols('z beta',real=True)
    P=-48+(32+a)*y-4*y*y
    Q=(P-20)**2+21
    q=r**6*s.exp(-r*r)
    h=r**4*s.exp(-r*r)*P.subs(y,r*r)
    F=r**4*s.exp(-r*r)*Q.subs(y,r*r)
    lap4=lambda g:s.diff(g,r,2)+3*s.diff(g,r)/r
    zero(a*q-lap4(q)-h,'h=(beta^2-Delta_R4)q is the literal radial inverse certificate')
    zero(Q-P-((P-s.Rational(41,2))**2+s.Rational(3,4)),
         'F-h has a uniform positive polynomial factor')
    zero(Q+P-((P-s.Rational(39,2))**2+s.Rational(163,4)),
         'F+h has a uniform positive polynomial factor')
    Pformal=s.symbols('P',real=True)
    phase=s.symbols('phase',real=True)
    qformal=(Pformal-20)**2+21
    zero(qformal+Pformal*phase-
         ((1+phase)*(qformal+Pformal)+(1-phase)*(qformal-Pformal))/2,
         'positivity for every cosine phase follows from both endpoints')
    periodic_sigma=-2*a*q*s.cos(beta*z)
    # With a=beta^2, the source mode h*cos(beta*z) is inverted by
    # q*cos(beta*z). The axial mean F has zero axial response.
    zero((-lap4(q*s.cos(beta*z))-s.diff(q*s.cos(beta*z),z,2)
          -h*s.cos(beta*z)).subs(a,beta**2),
         'full five-dimensional inverse on the nonzero axial mode')
    zero((periodic_sigma-2*s.diff(q*s.cos(beta*z),z,2)).subs(a,beta**2),
         'generated physical strain response with the sign retained')
    theta=s.symbols('theta',real=True)
    ff,hh,qq=s.symbols('F h q',real=True)
    cubic=(ff+hh*s.cos(theta))**2*(-2*a*qq*s.cos(theta))
    zero(s.integrate(s.expand_trig(cubic),(theta,-s.pi,s.pi))/(2*s.pi)+2*a*ff*hh*qq,
         'signed complete axial average, before absolute values')
    J=radial_integral(y**7*Q*P,y)
    expected=s.Rational(2240,19683)*(90*a**3-288*a**2+1485*a-5222)
    zero(J-expected,'exact physical radial source-return moment')
    bernstein=[-s.Rational(n,19683) for n in (11697280,10588480,9694720,8814400)]
    zero(J-sum(bernstein[j]*s.binomial(3,j)*a**j*(1-a)**(3-j) for j in range(4)),
         'negative Bernstein certificate for every 0<=beta^2<=1')
    require(all(c<0 for c in bernstein),'all Bernstein coefficients are strictly negative')
    zero(J.subs(a,1)+s.Rational(8814400,19683),'endpoint radial moment')
    # The real whole-space velocity is u=(-x2*b,x1*b,0), with
    # b=r^2 exp(-(r^2+z^2/L^2)/2) sqrt(Q+P cos(beta*z)).
    x1,x2=s.symbols('x1 x2',real=True)
    B=s.Function('B')(x1*x1+x2*x2,z)
    u=s.Matrix([-x2*B,x1*B,0])
    zero(s.diff(u[0],x1)+s.diff(u[1],x2),'literal Cartesian divergence-free pure swirl')
    omega=s.Matrix([-s.diff(u[1],z),s.diff(u[0],z),s.diff(u[1],x1)-s.diff(u[0],x2)])
    zero(-x2*omega[0]+x1*omega[1], 'initial angular vorticity is zero')
    coordinates=(x1,x2,z)
    nu=s.symbols('nu',positive=True)
    rhs=s.Matrix([-sum(u[j]*s.diff(u[i],coordinates[j]) for j in range(3))
                  +nu*sum(s.diff(u[i],x,2) for x in coordinates) for i in range(3)])
    curl_rhs=s.Matrix([s.diff(rhs[2],x2)-s.diff(rhs[1],z),
                       s.diff(rhs[0],z)-s.diff(rhs[2],x1),
                       s.diff(rhs[1],x1)-s.diff(rhs[0],x2)])
    zero(-x2*curl_rhs[0]+x1*curl_rhs[1]-(x1*x1+x2*x2)*s.diff(B*B,z),
         'actual convective and viscous RHS generates eta_t=partial_z(b^2); pressure curl is zero')
    chi=s.Function('chi')(r,z)
    vr=-r*s.diff(chi,z); vz=2*chi+r*s.diff(chi,r)
    zero((s.diff(vr,z)-s.diff(vz,r))/r+lap4(chi)+s.diff(chi,z,2),
         'canonical meridional reconstruction has eta=-Delta5 chi')
    zero(r*(vr*vr+vz*vz)-r**3*(s.diff(chi,r)**2+s.diff(chi,z)**2)
         -s.diff(2*r*r*chi*chi,r),
         'physical meridional energy equals lifted potential-gradient energy, up to the displayed boundary flux')
    energy_moment=radial_integral(y**6*P,y,2)
    gradient_moment=radial_integral(4*y**6*(3-y)**2,y,2)
    potential_moment=radial_integral(y**7,y,2)
    zero(energy_moment-gradient_moment-a*potential_moment,
         'nonnegative kinetic-energy return moment from the radial inverse')
    require(gradient_moment>0 and potential_moment>0,'both exact energy moments are positive')
    return {
        'profile':'y=r^2, a=beta^2 in (0,1], P=-48+(32+a)y-4y^2, Q=(P-20)^2+21',
        'radial_fields':'q=r^6 exp(-r^2), h=r^4 exp(-r^2) P, F=r^4 exp(-r^2) Q',
        'positive_source':'f_L=exp(-z^2/L^2)*(F+h*cos(beta*z)), b0=sqrt(f_L)',
        'velocity':'u0=(-x2*b0,x1*b0,0); b0=r^2 times a smooth positive factor, so the axis is regular',
        'radial_moment':str(J),'bernstein_coefficients':[str(c) for c in bernstein],
        'energy_weighted_radial_moment':str(energy_moment),
        'favorable_energy_exchange':'integral_R3 r^2*f*sigma=-(2/pi)*||partial_z(-Delta5)^(-1/2)f||_L2(R5)^2<=0',
        'unlocalized_response':'sigma=-2*beta^2*q*cos(beta*z)',
        'localized_limit':'L^-1 integral_R3 f_L^2*(2partial_zz K5 f_L) dx -> -4*pi*beta^2*J(beta^2)*sqrt(pi/3)>0',
        'actual_unforced_rate':'for any fixed nu>0, strain=-2*u_r/r is initially zero and strain_t(0)=2partial_zz K5 f_L',
        'returned_quartic_work':'N=4integral_R3 strain*b^4; N_prime(0)=4integral_R3 f_L^2*sigma_L>0 for all sufficiently large L',
        'scope':'refutes an unconditional nonpositive initial generated-feedback sign; the beta^2 depletion factor remains, and no total viscous growth or repeated renewal is established'}


def localization_certificate():
    """Exact arithmetic for the analytic localization-error estimate.

    Hardy, Plancherel and the physical weighted pairing are proved in the
    companion text; symbolic arithmetic alone does not certify those steps.
    """
    rho,eta,beta=s.symbols('rho eta beta',nonnegative=True)
    denominator=(rho*rho+eta*eta)*(rho*rho+beta*beta)
    zero(denominator-rho*rho*(eta+beta)**2-(rho*rho-eta*beta)**2,
         'multiplier difference denominator bounds rho^2*(eta+beta)^2')
    zero(rho*rho+eta*eta-2*rho*eta-(rho-eta)**2,
         'zero axial mode multiplier is bounded by abs(eta)/(2rho)')
    y=s.symbols('y',nonnegative=True)
    P=-48+33*y-4*y*y; Q=(P-20)**2+21
    X=2*radial_integral(y**7*Q**4,y,4)
    R=2*radial_integral(y**6*Q**2,y,2)
    D=2*radial_integral(y**5*P**2,y,2)
    A0=radial_integral(y**7*Q**2,y)
    J=radial_integral(y**7*Q*P,y)
    expected=(s.Rational(191912289955843275,2097152),s.Integer(3882780),
              s.Rational(6075,16),s.Rational(4395411160,59049),
              -s.Rational(8814400,19683))
    for actual,wanted,name in zip((X,R,D,A0,J),expected,('X','R','D','A0','J')):
        zero(actual-wanted,'exact localization radial moment '+name)
    roots=(302508,1971,20)
    for value,upper in zip((X,R,D),roots):
        require((upper-1)**2<value<=upper**2,'certified upper integer square root')
    rx,rr,rd=roots
    C1=4*rx*(s.Rational(rr,2)+rd)/abs(J)
    C2=36*A0/abs(J)
    L=2**24
    require(C1/L<s.Rational(1,4),'multiplier localization error is less than one quarter of the positive limit')
    require(C2/L**2<s.Rational(1,4),'axial averaging error is less than one quarter of the positive limit')
    require(1-C1/L-C2/L**2>s.Rational(1,2),'localized physical pairing is at least half the positive limit')
    # Exact full kinetic energy before optional amplitude normalization.
    a=s.symbols('a',nonnegative=True)
    Pa=P+(a-1)*y; Qa=(Pa-20)**2+21
    EF=radial_integral(y**3*Qa,y,1)
    zero(radial_integral(y**3*Pa,y,1)-12*a,'oscillatory energy coefficient')
    zero(EF.subs(a,1)-3339,'nonoscillatory energy coefficient at beta=1')
    return {'beta':1,'L':L,
            'radial_moments':{k:str(v) for k,v in zip(('X','R','D','A0','J'),expected)},
            'root_upper_bounds':list(roots),'C1':str(C1),'C2':str(C2),
            'relative_error_upper':str(C1/L+C2/L**2),
            'certified_analytic_consequence':'I_L/L >= I_infinity/2 > 0, using the stated multiplier/Hardy/physical-pairing proof',
            'energy':'||u0||_2^2=2*pi^(3/2)*L*(EF+12*beta^2*exp(-beta^2*L^2/4))',
            'EF':str(EF),'normalization':'u0/sqrt(E) has energy one and I scales by E^-3, preserving its positive sign',
            'scope':'rational identities and comparisons are exact; functional-analytic and actual-solution implications are analytic, not Lean-certified'}


def localized_quadrature():
    import numpy as np
    from scipy.special import roots_legendre
    y=s.symbols('y')
    rows=[]
    for beta in (1.,.5):
        a=s.Rational(str(beta))**2
        P=-48+(32+a)*y-4*y*y
        F=y*y*((P-20)**2+21)
        h=y*y*P
        sources=[F,h]
        tests=[s.expand(F*F+h*h/2),s.expand(2*F*h),s.expand(h*h/2)]
        J=float(radial_integral(y**7*((P-20)**2+21)*P,y))
        limit=-4*math.pi*beta**2*J*math.sqrt(math.pi/3)
        for order in (96,160,256):
            nodes,weights=roots_legendre(order)
            us=(nodes+1)/2; ws=weights/2
            radial={}
            for m,test in enumerate(tests):
                for n,source in enumerate(sources):
                    values=np.zeros_like(us)
                    for (i,),ci in s.Poly(test,y).terms():
                        for (j,),cj in s.Poly(source,y).terms():
                            for ell in range(j+1):
                                co=float(ci*cj)*math.comb(j+1,j-ell)*math.factorial(j)/math.factorial(ell)
                                co*=math.factorial(i+ell)/2
                                values+=co*(1-us)**(j-ell)*us**(2*ell)/(2+us)**(i+ell+1)
                    # values = integral r dr [test exp(-2r^2)]
                    #                      heat_t[source exp(-r^2)] / u^2,
                    # u=1/(1+4t). The time Jacobian is accounted below.
                    radial[m,n]=values
            for L in (256.,512.,1024.,4096.):
                delta=1/(L*L)
                tt=(1-us)/(4*us)
                az=1+4*delta*tt
                d=delta/az
                bz=2*delta+d
                total=np.zeros_like(us)
                for m in range(3):
                    for n in range(2):
                        xi=n*beta/az
                        pref=az**(-.5)*np.sqrt(math.pi/(2+1/az))*np.exp(-(n*beta)**2*tt/az)
                        zz=np.zeros_like(us)
                        for sign in (-1,1):
                            freq=xi+sign*m*beta
                            coeff=-2*d*(1-d/bz)-(xi-d*freq/bz)**2
                            zz+=.5*pref*np.exp(-freq*freq/(4*bz))*coeff
                        total+=radial[m,n]*zz
                answer=math.pi*float(np.dot(ws,total))
                rows.append({'beta':beta,'L':L,'order':order,'I_over_L':answer,
                             'positive_limit':limit,'relative_to_limit':answer/limit})
    return rows


def heat_kernel_certificates():
    y,u=s.symbols('y u',positive=True)
    for j in range(7):
        poly=sum(s.binomial(j+1,j-ell)*s.factorial(j)/s.factorial(ell)
                 *(1-u)**(j-ell)*u**(2+2*ell)*y**ell for ell in range(j+1))
        heat=poly*s.exp(-u*y)
        zero((-4*u*u*s.diff(heat,u)-4*y*s.diff(heat,y,2)-8*s.diff(heat,y))/s.exp(-u*y),
             'literal R4 radial heat equation for source monomial '+str(j))
        zero(heat.subs(u,1)-y**j*s.exp(-y),'radial heat initial datum '+str(j))
    t,d=s.symbols('t d',positive=True)
    z,k=s.symbols('z k',real=True)
    az=1+4*d*t
    hz=az**s.Rational(-1,2)*s.exp(-d*z*z/az-k*k*t/az)*s.cos(k*z/az)
    zero(s.diff(hz,t)-s.diff(hz,z,2),'axial Gaussian-modulated heat equation')
    zero(hz.subs(t,0)-s.exp(-d*z*z)*s.cos(k*z),'axial heat initial datum')
    B,xi,frequency=s.symbols('B xi frequency',real=True)
    paired=-2*d+4*d*d*(1/(2*B)-frequency**2/(4*B*B))+2*d*xi*frequency/B-xi*xi
    zero(paired-(-2*d*(1-d/B)-(xi-d*frequency/B)**2),
         'exact paired second derivative after Gaussian moments')
    return {'radial':'all source monomials j=0..6 satisfy the R4 heat PDE and exact initial data',
            'axial':'Gaussian-modulated axial heat PDE, initial data and second-derivative pairing checked',
            'scope':'heat and integral identification remain analytic; quadrature is numerical evidence only'}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--quadrature',action='store_true')
    args=p.parse_args()
    result={'exact':exact_profile(),'localization':localization_certificate(),
            'heat_kernels':heat_kernel_certificates()}
    if args.quadrature:
        result['localized_quadrature']=localized_quadrature()
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
