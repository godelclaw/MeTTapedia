#!/usr/bin/env python3
"""Heat-history source payment with the full parent transport retained.

Exact local identities and kernel constants are checked symbolically.
The PDE duality, semigroup representation, spatial integral comparisons
and history bounds are analytic. A bounded receiver curvature is an
explicit hypothesis, not a bound proved from the initial fluid.
"""

import argparse
import json
import sympy as s
from rotational_curl_reserve import require, zero
from rotational_joint_enstrophy import r, z, grad, lap5, velocity


def source_reserve():
    C, nu, H, L, t, E, d = s.symbols('C nu H L t E d', positive=True)
    R = C*(H-t+L**2/(2*nu))*E
    rate = s.diff(R, t)-2*nu*d*s.diff(R, E)
    cost = C*(E+L**2*d)
    zero(rate+cost+2*C*nu*(H-t)*d,
         'one actual kinetic-energy reserve pays every source-history seam')
    work=s.symbols('work',real=True)
    forced_rate=s.diff(R,t)+(-2*nu*d+2*work)*s.diff(R,E)
    zero(forced_rate+cost+2*C*nu*(H-t)*d-2*C*(H-t+L**2/(2*nu))*work,
         'external energy work retains its exact weighted payment defect')
    zero((C*(H+L**2/(2*nu))*E).subs({C:s.pi, L:2*s.sqrt(nu*H)})-3*s.pi*E*H,
         'the diffusion-length logarithmic source allowance')
    zero(2*s.pi**2*r**3-s.pi*r**2*(2*s.pi*r),
         'physical and lifted measures differ by pi*r^2')
    x, y = s.symbols('x y', real=True)
    rad = s.sqrt(x*x+y*y)
    ur, uz, b = [s.Function(n)(rad,z) for n in ('ur','uz','b')]
    u = s.Matrix([ur*x/rad-b*y, ur*y/rad+b*x, uz])
    G = u.jacobian([x,y,z]).subs({x:r,y:0})
    zero(G[:,1]-s.Matrix([-s.Function('b')(r,z),s.Function('ur')(r,z)/r,0]),
         'the angular derivative of the moving physical frame contains b^2')
    squared = sum(entry**2 for entry in G)
    zero(squared-s.Function('b')(r,z)**2-
         sum(G[i,j]**2 for i in range(3) for j in range(3) if (i,j)!=(0,1)),
         'the remainder in |grad u|^2-b^2 is a sum of physical squares')
    return {
        'stock':'B_L=integral_R5 beta*b^2*(1+log(1+L^2/r^2)) <= pi*(E+L^2*d)',
        'hypotheses':'0<=beta<=1, smooth axisymmetric whole-space unforced flow, regular axis, finite energy and dissipation',
        'reserve':'R_L=pi*(H-t+L^2/(2*nu))*E(t)>=0 on [0,H]',
        'rate':'R_L_prime+pi*(E+L^2*d)=-2*pi*nu*(H-t)*d<=0',
        'allowance':'integral_0^H B_L <= pi*(H+L^2/(2*nu))*E0',
        'diffusion_length':'L^2=4*nu*H gives 3*pi*E0*H',
        'forcing_defect':'2*pi*(H-t+L^2/(2*nu))*<u,force>; a forced residual equation also retains its additional vorticity source',
        'scope':'source stock is paid over the entire horizon; receiver derivatives are not bounded here'}


def receiver_identities():
    chi, A, eta, f, rho, w = [s.Function(n)(r,z) for n in ('chi','A','eta','f','rho','w')]
    nu = s.symbols('nu', positive=True)
    v = velocity(chi)
    div5 = lambda v: s.diff(v[0],r)+3*v[0]/r+s.diff(v[1],z)
    lapminus = lambda p:s.diff(p,r,2)-s.diff(p,r)/r+s.diff(p,z,2)
    zero(lap5(A/r**2)-lapminus(A)/r**2, 'physical adjoint diffusion')
    zero(div5(v*A/r**2)-v.dot(grad(A))/r**2,
         'r^2 renormalization cancels the full lifted transport divergence')
    flux = s.Matrix([r*(A*s.diff(eta,r)-eta*s.diff(A,r))+2*A*eta,
                     r*(A*s.diff(eta,z)-eta*s.diff(A,z))])
    zero(r*(A*lap5(eta)-eta*lapminus(A))-s.diff(flux[0],r)-s.diff(flux[1],z),
         'physical Green identity retains the axis flux')
    etat = nu*lap5(eta)-v.dot(grad(eta))+s.diff(f,z)
    rhot = -nu*lap5(rho)-w
    divergence = nu*div5(rho*grad(eta)-eta*grad(rho))-div5(v*eta*rho)+s.diff(f*rho,z)
    zero(etat*rho+eta*rhot+eta*w+f*s.diff(rho,z)-eta*div5(v*rho)-divergence,
         'exact space-time duality with the actual unforced parent transport')
    zero(r**2*(-f*s.diff(A/r**2,z)+eta*div5(v*A/r**2))
         -(-f*s.diff(A,z)+eta*v.dot(grad(A))), 'physical measure form of both signed costs')
    h=s.symbols('h',real=True)
    P=r*r/(2*(r*r+h*h)**s.Rational(3,2))
    zero(s.integrate(P,(h,-s.oo,s.oo))-1, 'normalized instantaneous axial receiver kernel')
    zero(-2*r*r/(8*s.pi**2*(r*r+h*h)**s.Rational(3,2))+P/(2*s.pi**2),
         'instantaneous renormalized receiver and its nonzero axis trace')
    return {
        'observable':'I=integral_0^H integral_R m(t,z)*q_core(t,0,z) dz dt',
        'heat_receiver':'rho(s)=integral_s^H exp(nu*(t-s)*Delta5)*T_star(delta_R4*m(t)) dt, T_star=-2*partial_z*K5',
        'exact_duality':'I=-integral f*rho_z + integral eta_core*div5(v*rho)',
        'physical_form':'A=r^2*rho; I=pi*integral_R3_time (-f*A_z+eta_core*v.grad A)',
        'instantaneous_trace':'r^2*T_star(delta_R4*m)=-P_r(m_z)/(2*pi^2) -> -m_z/(2*pi^2)',
        'history_trace':'bounded first receiver derivative gives A=O(r^2*(1+|log r|)); Green axis flux tends to zero',
        'scope':'v is the full coupled drift. Dropping the transport term changes the equation; instantaneous and time-integrated receiver traces differ'}


def heat_history_kernel():
    nu,h,u,x=s.symbols('nu h u x',positive=True)
    heat4=(4*s.pi*u)**(-2)*s.exp(-r*r/(4*u))
    zero(s.diff(heat4,u)-(s.diff(heat4,r,2)+3*s.diff(heat4,r)/r),
         'literal four-transverse-dimensional heat kernel')
    # The lower limit nu*(t-s) is crucial: K5 integrates the heat kernel
    # from zero to infinity before the additional history propagation.
    tail=(1-s.exp(-r*r/(4*u)))/(2*s.pi**2*r*r)
    zero(s.diff(tail,u)+2*heat4, 'integral_u^infinity of twice the heat kernel')
    kernel=(s.expint(1,x)+(1-s.exp(-x))/x)/(8*s.pi**2*nu)
    K=kernel.subs(x,r*r/(4*nu*h))
    zero(s.diff(K,h)-tail.subs(u,nu*h), 'time-integrated heat resolvent, including all constants')
    zero(s.diff(s.log(1+1/x),x)+1/(x*(1+x)),
         'logarithmic majorant from exp(-x)<=1/(1+x)')
    zero(s.diff((1-s.exp(-x)),x)-s.exp(-x), 'the other kernel term is bounded by one')
    E0,M2,H=s.symbols('E0 M2 H',positive=True)
    zero(M2/(8*s.pi**2*nu)*(3*s.pi*E0*H)-3*M2*E0*H/(8*s.pi*nu),
         'full heat-history source payment at diffusion length')
    return {
        'exact_kernel':'A_nu(h,r)=[E1(x)+(1-exp(-x))/x]/(8*pi^2*nu), x=r^2/(4*nu*h)',
        'majorant':'A_nu(h,r)<= [1+log(1+4*nu*h/r^2)]/(8*pi^2*nu)',
        'receiver_hypothesis':'M2=sup_(t,z) |partial_zz m(t,z)| < infinity',
        'heat_source_payment':'abs(integral f*rho_z)<=3*M2*E0*H/(8*pi*nu)',
        'scope':'prescribed smooth receiver, or conditional on M2 for an evolving receiver; neither the full transport cost nor datum-controlled M2 is supplied'}


def parent_time_ordering():
    t,a,H,nu=s.symbols('t a H nu',positive=True)
    source,source_rate,transport,diffusion,receiver_diffusion=s.symbols(
        'source source_rate transport diffusion receiver_diffusion',real=True)
    # These symbols denote the paired T S0, T S_t0, T(v0.grad S0),
    # nu*Delta5*T S0 and nu*<m0_zz,T S0>, respectively.
    heat=s.integrate(source+a*source_rate+(t-a)*diffusion,(a,0,t))
    correction=-s.integrate(a*transport,(a,0,t))
    q=heat+correction
    zero(q-t*source-t*t/2*(source_rate+diffusion-transport),
         'Duhamel expansion recovers both actual source evolution and parent transport')
    I=s.integrate(q+t*t*receiver_diffusion,(t,0,H))
    zero(I-H*H*source/2-H**3*(source_rate+diffusion-transport+2*receiver_diffusion)/6,
         'history pairing reproduces the two time-ordered sampling diffusion terms')
    # Compatibility with the previously checked compact-parent multipoles.
    rows=[(0,s.Rational(1152,35),-s.Rational(2304,35),s.Rational(3456,35)),
          (2,384,-s.Rational(2304,7),s.Rational(4992,7)),
          (4,-s.Rational(11008,11),s.Rational(10752,11),-s.Rational(21760,11)),
          (6,s.Rational(80640,143),-s.Rational(80640,143),s.Rational(161280,143))]
    for ell,sr,tr,expected in rows:
        zero(sr-tr-expected,'retained compact-parent history coefficient '+str(ell))
    return {'coefficient':'I=H^2*<m0,sigma>/2+H^3*<m0,kappa+2*nu*sigma_zz>/6+O(H^4)',
        'compact_parents':'kappa=sigma_t-T(v0.grad S0) outside the source support; heat diffusion of sigma is zero there',
        'moment':'for the actual J_core^4 weighted density m, E[J_core(H)^4]=1+4*I',
        'scope':'the earlier opposite-parent third derivative survives in the exact transport remainder; no long-time Taylor control follows'}


def transport_payment():
    nu,H,M1,M2,E0,Y=s.symbols('nu H M1 M2 E0 Y',positive=True)
    x=s.symbols('x',positive=True)
    F=s.expint(1,x)+(1-s.exp(-x))/x
    K=F.subs(x,r*r/(4*nu*H))/(8*s.pi**2*nu)
    # Differentiate the positive kernel before taking absolute values.
    # |partial_r(r^2 rho)| <= M1*(2r K-r^2 K_r).
    zero(s.diff(F,x)+(1-s.exp(-x))/x**2,'radial kernel derivative cancellation')
    ar=(2*r*K-r*r*s.diff(K,r)).subs(r,2*s.sqrt(nu*H*x))
    ar_formula=s.sqrt(H/nu)/(2*s.pi**2)*(s.sqrt(x)*s.expint(1,x)+2*(1-s.exp(-x))/s.sqrt(x))
    zero(ar-ar_formula,'complete upper bound for the radial receiver derivative')
    az_over_r=(r*K).subs(r,2*s.sqrt(nu*H*x))
    zero(az_over_r-s.sqrt(H/nu)/(4*s.pi**2)*
         (s.sqrt(x)*s.expint(1,x)+(1-s.exp(-x))/s.sqrt(x)),
         'complete upper bound for the axial receiver derivative divided by radius')
    zero((r*r*K).subs(r,2*s.sqrt(nu*H*x))-H*x*F/(2*s.pi**2),
         'bounded axial derivative without the inverse radius')
    # Bounds: sqrt(x) E1(x)<=2, (1-exp(-x))/sqrt(x)<=1,
    # x*E1(x)<=exp(-x). They follow by positive one-variable integrals.
    Br=2*M1*s.sqrt(H/nu)/s.pi**2
    Bz=3*M2*s.sqrt(H/nu)/(4*s.pi**2)
    Cz=M2*H/(2*s.pi**2)
    omega,g,vr,vz,Ar,Az=s.symbols('omega g vr vz Ar Az',real=True)
    zero((omega/r-g)*(vr*Ar+vz*Az)-
         (omega*(vr/r*Ar+vz*Az/r)-g*(vr*Ar+vz*Az)),
         'eta_core=omega_theta/r-g keeps both actual and paid parent histories')
    # Pointwise |curl_theta|^2 <= 2|grad u|^2 is sufficient; the sharper
    # integrated curl/gradient identity is not needed for this constant.
    urz,uzr=s.symbols('urz uzr',real=True)
    zero(2*(urz**2+uzr**2)-(urz-uzr)**2-(urz+uzr)**2,
         'physical vorticity comparison by a square')
    transport=s.pi*s.sqrt(2)*(Br*E0/(2*nu)+Bz*E0*s.sqrt(H/(2*nu)))
    transport+=s.pi*(Br+Cz)*Y*s.sqrt(E0)*H
    return {
        'receiver_hypotheses':'M1=sup|m_z|, M2=sup|m_zz|; both bounds must be prescribed for a funded estimate',
        'derivative_bounds':{'sup_abs_A_r':str(Br),'sup_abs_A_z_over_r':str(Bz),'sup_abs_A_z':str(Cz)},
        'physical_pointwise_payment':'integral_R3 |eta_core*v.grad A| <= sqrt(2)*Br*d+sqrt(2)*Bz*sqrt(E*d)+(Br+Cz)*Y*sqrt(E)',
        'transport_allowance':str(transport),
        'parent_hypothesis':'sup_t ||g(t)||_L2(R3)<=Y, supplied by the previous fixed-cutoff source-history estimate',
        'whole_pairing':'|I|<=3*M2*E0*H/(8*pi*nu)+transport_allowance',
        'scope':'full mutually interacting transport is included for this smooth averaged observable; a datum-uniform actual receiver bound and the singular point-observation limit remain open'}


def actual_receiver_defects():
    t,nu=s.symbols('t nu',positive=True)
    m,U,qc,qp,ell=[s.Function(n)(t,z) for n in ('m','U','qc','qp','ell')]
    relation={s.diff(U,z,j):s.diff(qc+qp,z,j-1) for j in range(1,4)}
    rhs=nu*s.diff(m,z,2)-s.diff(U*m,z)+4*qc*m
    n,p=s.diff(m,z),s.diff(m,z,2)
    expected_n=nu*s.diff(n,z,2)-U*s.diff(n,z)+2*(qc-qp)*n+(3*s.diff(qc,z)-s.diff(qp,z))*m
    expected_p=nu*s.diff(p,z,2)-U*s.diff(p,z)+(qc-3*qp)*p+(5*s.diff(qc,z)-3*s.diff(qp,z))*n+(3*s.diff(qc,z,2)-s.diff(qp,z,2))*m
    zero((s.diff(rhs,z)-expected_n).xreplace(relation),'actual first receiver derivative equation')
    zero((s.diff(rhs,z,2)-expected_p).xreplace(relation),'actual second receiver derivative equation')
    density=s.exp(ell)
    ellz=s.diff(ell,z)
    ellzz=s.diff(ell,z,2)
    ell_rate=nu*(ellzz+ellz**2)-U*ellz-s.diff(U,z)+4*qc
    fisher_rate=density*(ell_rate*ellz**2+2*ellz*s.diff(ell_rate,z))
    A=3*qc-qp
    flux=nu*density*(ellz**3+2*ellz*ellzz)-U*density*ellz**2+2*A*density*ellz
    expected=-2*nu*density*ellzz**2-4*qc*density*ellz**2-2*A*density*ellzz
    zero((fisher_rate-expected-s.diff(flux,z)).xreplace(relation),
         'signed Fisher-information defect keeps diffusion and eliminates parent derivatives by integration by parts')
    completed=-2*nu*density*(ellzz+A/(2*nu))**2+density*A**2/(2*nu)-4*qc*density*ellz**2
    zero(expected-completed,'the remaining Fisher source has no assumed favorable sign')
    L=s.symbols('L',positive=True)
    joint_rate=4*qc*density+L**2*expected
    core=density*(4*qc*(1-L**2*ellz**2)-6*L**2*qc*ellzz-nu*L**2*ellzz**2)
    zero(core+L**2*qp**2*density/nu-joint_rate-
         nu*L**2*density*(ellzz-qp/nu)**2,
         'paid parents leave a signed generated-strain cost in mass plus Fisher information')
    return {
        'first':'n_t=nu*n_zz-U*n_z+2*(q_core-q_paid)*n+(3*q_core_z-q_paid_z)*m',
        'second':'p_t=nu*p_zz-U*p_z+(q_core-3*q_paid)*p+(5*q_core_z-3*q_paid_z)*n+(3*q_core_zz-q_paid_zz)*m',
        'fisher':'F=integral m*(partial_z log m)^2; F_prime=-2nu*integral m*(partial_zz log m)^2-4*integral q_core*m*(partial_z log m)^2-2*integral (3q_core-q_paid)*m*partial_zz log m',
        'joint_quantity':'S=integral m+L^2*F>=integral m; S_prime<=core_cost+kappa*S',
        'core_cost':'integral m*[4q_core*(1-L^2*ell_z^2)-6L^2*q_core*ell_zz-nu*L^2*ell_zz^2]',
        'parent_clock':'kappa=L^2*||q_paid||_infinity^2/nu; integral kappa<=4*C_BS^2*L^2*Y^2*sqrt(H/(2nu))/nu',
        'funding_obligation':'bound the integral of exp(K_H-integral_0^t kappa)*core_cost from original data; initial joint allowance is exp(K_H)*(1+L^2*F(0))',
        'hypotheses':'actual receiver PDE, U_z=q_core+q_paid; Fisher identity additionally requires positive m, finite integrals and vanishing boundary flux',
        'scope':'no original-datum bound on receiver curvature or this Fisher defect is established; scalar accumulated parent strain does not alone pay its differentiated equation'}


def quadrature():
    import numpy as np
    from scipy.integrate import quad
    from scipy.special import exp1
    rows=[]
    # Directly integrate the original positive double kernel in scaled
    # variables. Interchange the two nonnegative integrals, not a fit to
    # the closed expression: int_0^infty min(1,v) v^-2 exp(-x/v) dv.
    for x in (1e-4,1e-2,.1,1.,10.,100.):
        first=quad(lambda v:np.exp(-x/v)/v,0,1,epsabs=1e-12,epsrel=1e-12)[0]
        second=quad(lambda v:np.exp(-x/v)/v**2,1,np.inf,epsabs=1e-12,epsrel=1e-12)[0]
        direct=first+second
        exact=exp1(x)-np.expm1(-x)/x
        error=abs(direct-exact)/exact
        bound=1+np.log1p(1/x)
        require(error<1e-10,'independent time-history kernel quadrature')
        require(direct<=bound*(1+1e-12),'logarithmic kernel comparison')
        require(np.sqrt(x)*exp1(x)<=2,'radial derivative comparison')
        require(-np.expm1(-x)/np.sqrt(x)<=1,'radial and axial derivative comparison')
        require(x*exp1(x)<=np.exp(-x)*(1+1e-12),'axial derivative comparison')
        rows.append({'x':x,'relative_error':error,'bound_ratio':direct/bound})
    return rows


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--quadrature',action='store_true')
    args=p.parse_args()
    result={'source_reserve':source_reserve(),'duality':receiver_identities(),
            'heat_kernel':heat_history_kernel(),'parent_history':parent_time_ordering(),
            'transport_payment':transport_payment(),'receiver_defects':actual_receiver_defects()}
    if args.quadrature:
        result['quadrature']=quadrature()
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
