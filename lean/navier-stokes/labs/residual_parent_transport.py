#!/usr/bin/env python3
"""Generated-parent transport, separated-source payment and exact initial jets.

The symbolic certificates retain the actual coupled drift and all Ito terms.
Compact radial swirl and a smooth compact meridional parent give genuine
finite-energy initial data. Elliptic identification, local PDE evolution,
stopping and the moment expansion are analytic, not Lean certificates.
"""

import argparse
import json
import sympy as s
from rotational_curl_reserve import require, zero
from rotational_joint_enstrophy import r, z, grad, lap5, velocity
from circulation_source_reserve import div3


def residual_equations():
    chi, b = [s.Function(n)(r,z) for n in ('chi','b')]
    beta=s.Function('beta')(r)
    nu=s.symbols('nu',positive=True)
    v=velocity(chi)
    a=v[0]/r
    zero(div3(v),'physical incompressibility of the full parent')
    zero(s.diff(v[0],r)+3*v[0]/r+s.diff(v[1],z)-2*a,
         'the lifted drift retains its nonzero five-dimensional divergence')
    brate=nu*lap5(b)-v.dot(grad(b))-2*a*b
    f=beta*b*b
    production=(-4*a*f-2*nu*beta*grad(b).dot(grad(b))
        +b*b*(v[0]*s.diff(beta,r)-nu*lap5(beta))
        -2*nu*s.diff(beta,r)*s.diff(b*b,r))
    zero(2*beta*b*brate+v.dot(grad(f))-nu*lap5(f)-production,
         'full current-source stock equation, including fixed-cutoff defects')
    # k=2 partial_z N5 is locally integrable. The commutator kernel uses
    # (v(x)-v(y)).grad k + k div_5 v(y); it is not just the first term.
    N=1/(8*s.pi**2*(r*r+z*z)**s.Rational(3,2))
    k=2*s.diff(N,z)
    zero(k+3*z/(4*s.pi**2*(r*r+z*z)**s.Rational(5,2)),
         'literal strain-response kernel')
    zero(2*s.diff(N,z,2)-(-3+15*z*z/(r*r+z*z))/(4*s.pi**2*(r*r+z*z)**s.Rational(5,2)),
         'separated current-source kernel; contact term remains in the near part')
    J,V,q,qz,Lq,qzz,C,sigma=s.symbols('J V q qz Lq qzz C sigma',real=True)
    acceleration=q*q+nu*(Lq+qzz)+C+sigma
    zero(J*q*q+J*(nu*(Lq+qzz)+C+sigma)-J*acceleration,
         'residual acceleration retains q_core squared and the actual commutator')
    ell=s.symbols('ell',positive=True)
    Q=J*J+ell*ell*V*V
    E=Q*Q
    L=lambda p:V*s.diff(p,J)+J*acceleration*s.diff(p,V)+nu*J*J*qz*qz*s.diff(p,V,2)
    expected=4*J*V*Q*(1+ell*ell*acceleration)+4*nu*ell*ell*J*J*qz*qz*(J*J+3*ell*ell*V*V)
    zero(L(E)-expected,'complete residual quartic generator')
    return {'source_stock':'f=(1-zeta_rho)*b^2, nonnegative; (1-zeta_rho)*S=partial_z f',
        'residual':'(partial_t+v.grad-nu*L5)q_core=[v.grad,T]eta_core+sigma; T=2*partial_z*K5; sigma=2*partial_zz*K5*f',
        'commutator_kernel':'(v(x)-v(y)).grad k(x-y)+2*a(y)*k(x-y), k=2*partial_z N5',
        'axis_acceleration':'q_core^2+nu*(L5 q_core+partial_zz q_core)|axis+C_axis+sigma_axis',
        'source_stock_defect':str(production),
        'scope':'actual source-history components under the full drift; no independent NS evolution for the residual'}


def separated_source_payment():
    E0,delta,ell,H,t=s.symbols('E0 delta ell H t',positive=True)
    K=3*E0/(s.pi*delta**5)
    # R5 radial volume is pi times the physical integral of r^2 b^2.
    zero(2*s.pi**2-s.pi*(2*s.pi),'conversion of lifted b^2 mass to physical swirl energy')
    zero(3/(s.pi**2*delta**5)*(s.pi*E0)-K,
         'separated source acceleration is paid by original kinetic energy')
    J,V=s.symbols('J V',real=True)
    Q=J*J+ell*ell*V*V
    E=Q*Q
    zero(Q-2*ell*J*V-(J-ell*V)**2,'positive mixed moment comparison')
    zero(Q+2*ell*J*V-(J+ell*V)**2,'negative mixed moment comparison')
    c=2/ell+2*ell*K
    zero(s.diff(s.exp(c*(H-t)),t)+c*s.exp(c*(H-t)),
         'one original-horizon factor pays separated source and the kinematic term')
    zero(c.subs(ell,1/s.sqrt(K))-4*s.sqrt(K),'balanced finite source payment')
    zero(c-4*s.sqrt(K)-2*(1-s.sqrt(K)*ell)**2/ell,
         'the selected scale minimizes this comparison rate')
    qz,nu,G=s.symbols('qz nu G',real=True)
    remaining=4*ell*ell*J*V*Q*G+4*nu*ell*ell*J*J*qz*qz*(J*J+3*ell*ell*V*V)
    zero(E.subs({J:1,V:0})-1,'zero initial residual strain gives unit initial metric')
    return {'bound':'|sigma_far|<=K_delta=3*||u0||_2^2/(pi*delta^5)',
        'near_part':'includes the principal value and the local -2f/5 contact term',
        'clock':'exp(c*(H-t)), c=2/ell+2*ell*K_delta',
        'balanced_choice':'ell=1/sqrt(K_delta), c=4*sqrt(K_delta) when E0>0',
        'initial_full_multiplier':'exp(8*M_H+4*H*sqrt(K_delta))',
        'remaining_acceleration':'G=q_core^2+nu*(L5 q_core+q_core_zz)|axis+[v.grad,T]eta_core|axis+sigma_near',
        'signed_remaining_cost':str(remaining),
        'scope':'funds only the separated direct source and kinematic contribution; near source, transport, full diffusion and noise remain'}


def angular_average(polynomial,x):
    """Normalized S4 average of a polynomial in its axial coordinate."""
    return s.factor(sum(co*(s.Rational(3,(k+1)*(k+3)) if k%2==0 else 0)
        for (k,),co in s.Poly(s.expand(polynomial),x).terms()))


def compact_parent_jets():
    x=s.symbols('x',real=True)
    radial=s.symbols('radial',positive=True)
    C=s.symbols('C',real=True)
    chi=C*z*r**4
    v=velocity(chi)
    a=v[0]/r
    y=s.symbols('y',nonnegative=True)
    F=s.Function('F')(y)
    f=F.subs(y,r*r+z*z)
    fp=s.diff(F,y).subs(y,r*r+z*z)
    fpp=s.diff(F,y,2).subs(y,r*r+z*z)
    adv=v.dot(grad(f))
    ft=-adv-4*a*f
    predicted_ft=2*C*r**4*(r*r-6*z*z)*fp+4*C*r**4*f
    zero(ft-predicted_ft,'actual nonviscous swirl-square evolution on the source support')
    source=s.diff(f,z)
    adv_source=v.dot(grad(source))
    predicted_adv=12*C*z*r**4*fp+4*C*z*r**4*(-r*r+6*z*z)*fpp
    zero(adv_source-predicted_adv,'transport of the actual generated eta source')
    zero(v[0]+C*r**5,'hidden parent radial velocity')
    zero(v[1]-6*C*z*r**4,'hidden parent axial velocity')
    zero(v[1].subs(r,0),'complete initial axis velocity vanishes for both parent phases')
    q=s.diff(v[1],z)
    zero(s.limit(s.diff(q,r,2)+s.diff(q,r)/r+s.diff(q,z,2),r,0),
         'initial axis diffusion trace also vanishes')
    # Multipole coefficients of N5 along an exterior axis observation.
    # The angular densities have degrees at most six and seven. Orthogonality
    # makes all higher coefficients vanish; the exterior PDE identification
    # for smooth radial profiles is an analytic integration argument.
    h=s.symbols('h',real=True)
    expansion=sum(s.gegenbauer(l,s.Rational(3,2),x)*h**l for l in range(8))
    zero(s.series((1-2*x*h+h*h)**s.Rational(-3,2),h,0,8).removeO()-expansion,
         'Newtonian multipole normalization through every retained angular degree')
    for l in range(8):
        for degree in range(l):
            zero(angular_average(s.gegenbauer(l,s.Rational(3,2),x)*x**degree,x),
                 'angular orthogonality to lower-degree source components')
    # The IBP rules are integral R^k F'(R^2)=-((k-1)/2) integral R^(k-2)F
    # and the analogous second-derivative rule. All boundary terms vanish.
    k=s.symbols('k',positive=True)
    zero(s.diff(radial**(k-1)/2,radial)-(k-1)*radial**(k-2)/2,
         'first radial moment integration-by-parts coefficient')
    zero((k-1)*(k-3)/4-((k-1)/2)*((k-3)/2),
         'second radial moment integration-by-parts coefficient')
    rows=[]
    for l in range(0,8,2):
        G=s.gegenbauer(l,s.Rational(3,2),x)
        ft_moment=(-(l+9)*angular_average(G*(1-x*x)**2*(1-7*x*x),x)
                   +4*angular_average(G*(1-x*x)**2,x))
        j=l+1
        Gj=s.gegenbauer(j,s.Rational(3,2),x)
        adv_moment=(-6*(j+8)*angular_average(Gj*x*(1-x*x)**2,x)
             +(j+10)*(j+8)*angular_average(Gj*x*(1-x*x)**2*(-1+7*x*x),x))
        sigma_rate=s.factor(2*(l+3)*(l+4)*ft_moment)
        transport=s.factor(-2*(j+3)*adv_moment)
        rows.append([l,sigma_rate,transport,s.factor(sigma_rate-transport)])
    expected=[s.Rational(3456,35),s.Rational(4992,7),-s.Rational(21760,11),s.Rational(161280,143)]
    for row,target in zip(rows,expected):
        zero(row[3]-target,'complete residual second strain derivative coefficient')
    require(4*expected[1]+expected[2]>0,
            'at observation z>=2 the positive M6 term dominates the negative M8 term')
    # At t=0 the radial source has exterior potential M0/(8 pi^2 z^3).
    M,D=s.symbols('M D',positive=True)
    exterior=M/(8*s.pi**2*z**3)
    sigma=2*s.diff(exterior,z,2)
    zero(sigma-3*M/(s.pi**2*z**5),'strictly positive initial source response outside its support')
    zero(s.diff(sigma,z,2)-90*M/(s.pi**2*z**7),'axial sampling diffusion of the source response')
    nu=s.symbols('nu',positive=True)
    viscous=-4*nu*s.diff(D/(8*s.pi**2*z**3),z,2)
    zero(viscous+6*nu*D/(s.pi**2*z**5),'source-gradient dissipation retains its full viscous cost')
    # Meridional reversal preserves the entire pressure source, not just its trace at the axis.
    cm,bm=s.Function('cm')(r,z),s.Function('bm')(r,z)
    vm=velocity(cm)
    Gm=s.Matrix([[s.diff(vm[0],r),0,s.diff(vm[0],z)],
                 [0,vm[0]/r,0],[s.diff(vm[1],r),0,s.diff(vm[1],z)]])
    Gs=s.Matrix([[0,-bm,0],[bm+r*s.diff(bm,r),0,r*s.diff(bm,z)],[0,0,0]])
    zero(s.trace((Gm+Gs)**2)-s.trace((-Gm+Gs)**2),
         'opposite hidden parent phases have the same canonical pressure source')
    return {'datum':'b0=B(R^2), B smooth supported in R<1; chi0=C*z*r^4*kappa(R^2), kappa=1 for R<=3 and zero for R>=4',
        'cutoff':'rho=5, so the first two residual source jets are wholly in the core',
        'moments':'M_j=integral_R5 |y|^j b0(y)^2 dy; D=integral_R5 |grad b0|^2 dy',
        'initial_core_strain_rate':'sigma(z)=3*M0/(pi^2*z^5)>0 for z>1',
        'rows_l_sigma_rate_transport_core_rate':rows,
        'core_second_rate':'C/(8*pi^2)*(3456*M4/(35*z^5)+4992*M6/(7*z^7)-21760*M8/(11*z^9)+161280*M10/(143*z^11))-6*nu*D/(pi^2*z^5)',
        'positive_parent_coefficient':'for z>=2, H(z)>=432*M4/(35*pi^2*z^5)>0 using M8<=M6',
        'same_for_opposite_C':'b0, sigma, initial full axis velocity and diffusion, canonical pressure, total energy, ||eta0||_2 and the prior scalar M_H',
        'scope':'actual compatible initial source-history jets; sign reversal changes the next residual deformation coefficient, not its already positive quadratic burst'}


def stochastic_moment_jet():
    t,z,J,nu=s.symbols('t z J nu',real=True)
    qc,U=s.Function('qc')(t,z),s.Function('U')(t,z)
    sigma,kappa=s.Function('sigma')(z),s.Function('kappa')(z)
    L=lambda f:s.diff(f,t)+U*s.diff(f,z)+nu*s.diff(f,z,2)+J*qc*s.diff(f,J)
    def initial(expr):
        sub={qc:0,U:0,J:1}
        for i,d in enumerate(sorted(expr.atoms(s.Derivative),key=str)):
            nt=d.variables.count(t); nz=d.variables.count(z)
            if nt==0: sub[d]=0
            elif d.expr==qc and nt in (1,2):
                sub[d]=s.diff(sigma if nt==1 else kappa,z,nz)
            else: sub[d]=s.Symbol('free_jet_'+str(i),real=True)
        return s.simplify(s.expand(expr).xreplace(sub))
    p=J**4
    zero(initial(L(p)),'zero initial residual deformation drift')
    zero(initial(L(L(p)))-4*sigma,'initial second moment derivative')
    zero(initial(L(L(L(p))))-4*kappa-8*nu*s.diff(sigma,z,2),
         'complete third weak derivative, with both time-ordered diffusion terms')
    return {'second':'4*sigma(z)',
        'third':'4*(C*H(z)+nu*(-6*D/(pi^2*z^5)+180*M0/(pi^2*z^7)))',
        'opposite_sign_condition':'choose |C|*H(z)>nu*abs(-6*D/(pi^2*z^5)+180*M0/(pi^2*z^7))',
        'scope':'localized moment expansion for each fixed smooth datum and nu>0; no uniform long-time or infinite-renewal conclusion'}


def forecast_weight_defect():
    t,z,H,nu,Lambda=s.symbols('t z H nu Lambda',real=True)
    q,U=s.Function('q')(t,z),s.Function('U')(t,z)
    A=lambda f:s.diff(f,t)+U*s.diff(f,z)+nu*s.diff(f,z,2)
    h=A(q)
    tau=H-t
    psi=4*tau*q+2*tau*tau*h+Lambda*tau**3
    expected=2*tau*tau*A(h)-3*Lambda*tau*tau+nu*(4*tau*s.diff(q,z)+2*tau*tau*s.diff(h,z))**2
    zero(A(psi)+nu*s.diff(psi,z)**2+4*q-expected,
         'complete logarithmic supersolution defect of the source forecast')
    C,P,B,sz=s.symbols('C P B sz',real=True)
    initial=2*H*H*(C*P+nu*B)-3*Lambda*H*H+4*nu*H**4*sz*sz
    lower=s.Rational(2,3)*(C*P+nu*B)+s.Rational(4,3)*nu*H*H*sz*sz
    zero(initial-3*H*H*(lower-Lambda),
         'necessary cubic prefunding at the actual compact-parent initial state')
    return {'candidate':'psi=4*(H-t)*q_core+2*(H-t)^2*h+Lambda*(H-t)^3, h=(partial_t+U*partial_z+nu*partial_zz)q_core',
        'complete_defect':'2*(H-t)^2*A(h)-3*Lambda*(H-t)^2+nu*(4*(H-t)*q_core_z+2*(H-t)^2*h_z)^2',
        'necessary_initial_Lambda':'(2/3)*(C*H_response(z)+nu*B_visc(z))+(4/3)*nu*H^2*sigma_z(z)^2',
        'failure':'Lambda=0 fails for the positive compact-parent phase large enough; the obstacle is inactive at the tested point because psi(0)=2*H^2*sigma>0',
        'scope':'refutes this two-term forecast supersolution; a funded dynamic correction must still control the full A(h) and gradient term'}


def independent_quadrature():
    """Direct Newtonian integrals for an actual smooth compact radial bump.

This is numerical supporting evidence, independent of the finite multipole
evaluation above. Neither quadrature tolerance nor resolution is a proof.
"""
    import numpy as np
    from numpy.polynomial.legendre import leggauss
    results=[]
    for n in (48,80,128):
        x,w=leggauss(n)
        R=(x+1)/2
        wr=w/2
        rr=R[:,None]
        xx=x[None,:]
        f=np.exp(-2/(1-R**2))
        fp=-2*f/(1-R**2)**2
        fpp=(4/(1-R**2)**4-4/(1-R**2)**3)*f
        M=lambda j:8*np.pi**2/3*np.dot(wr,R**(j+4)*f)
        ft=(2*rr**6*(1-xx**2)**2*(1-7*xx**2)*fp[:,None]
            +4*rr**4*(1-xx**2)**2*f[:,None])
        advS=(12*rr**5*xx*(1-xx**2)**2*fp[:,None]
            +4*rr**7*xx*(1-xx**2)**2*(-1+7*xx**2)*fpp[:,None])
        weight=2*np.pi**2*wr[:,None]*rr**4*w[None,:]*(1-xx**2)
        for Z in (2.,3.):
            distance2=Z*Z+rr*rr-2*Z*rr*xx
            dz=Z-rr*xx
            hessian=(-3+15*dz*dz/distance2)/(4*np.pi**2*distance2**2.5)
            kernel=-3*dz/(4*np.pi**2*distance2**2.5)
            source_rate=float(np.sum(weight*hessian*ft))
            transport=float(np.sum(weight*kernel*advS))
            formula=(3456*M(4)/(35*Z**5)+4992*M(6)/(7*Z**7)
                -21760*M(8)/(11*Z**9)+161280*M(10)/(143*Z**11))/(8*np.pi**2)
            error=abs(source_rate-transport-formula)/formula
            require(error<(1e-7 if n==48 else 1e-11),
                    'direct kernel quadrature agrees with the independent moment formula')
            results.append({'order':n,'z':Z,'source_rate':source_rate,
                'transport':transport,'residual_rate':source_rate-transport,
                'moment_formula':float(formula),'relative_error':float(error)})
    return {'profile':'b0=exp(-1/(1-R^2)) for R<1 and zero outside',
            'scope':'numerical initial-jet cross-check only','rows':results}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quadrature',action='store_true',help='also run an independent numerical kernel check (requires numpy)')
    args=parser.parse_args()
    result={'residual':residual_equations(),
        'separated_source':separated_source_payment(),
        'compact_parents':compact_parent_jets(),
        'moment':stochastic_moment_jet(),
        'forecast':forecast_weight_defect()}
    if args.quadrature:
        result['quadrature']=independent_quadrature()
    print(json.dumps(result,indent=2,default=str))
