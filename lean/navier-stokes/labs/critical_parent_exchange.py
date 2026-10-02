#!/usr/bin/env python3
"""Critical joint parent energy, complete exchange, and an initial-reserve test.

Checks the local compatibility, convex diffusion, rational profile moments
and viscous time scaling. Fractional-operator identities, localization and
actual NS interval arguments are analytic, not Lean-certified here.
"""

import argparse
import json
import sympy as s
from rotational_curl_reserve import require, zero
from rotational_joint_enstrophy import r, z, grad, lap5, velocity


def joint_exchange():
    chi = s.Function('chi')(r,z)
    v = velocity(chi)
    div5 = lambda a: s.diff(a[0],r)+3*a[0]/r+s.diff(a[1],z)
    zero(div5(v*chi), 'actual meridional transport preserves the kinetic pairing')
    b,h,p = s.symbols('b h p',positive=True)
    X = b*b+h*h
    phi = X**(p/2)
    W = X**(p/2-1)
    x = s.Matrix([b,h])
    expected = p*W*s.eye(2)+p*(p-2)*X**(p/2-2)*(x*x.T)
    zero(s.hessian(phi,[b,h])-expected, 'full convex diffusion matrix')
    q,comm,transport = s.symbols('q comm transport',real=True)
    # comm denotes <b^2,[R_z,W]h>; transport includes the kinetic
    # correction <W h,[L,v.grad]eta>+(1/2)<q W,h^2>.
    raw = q*(p*b*b*W-phi)-p*(q*b*b*W/2+comm)
    raw -= p*(transport-q*W*h*h/2)
    zero(raw-((p-2)*q*phi/2-p*comm-p*transport),
         'complete source/transport exchange at the evolving nonlinear weight')
    pp=s.Rational(5,2)
    zero(s.Rational(25,16)/pp*2-s.Rational(5,4),
         'conditional critical-clock constant with half the joint diffusion')
    lam=s.symbols('lambda',positive=True)
    zero((lam**4)**(pp/2)*lam**(-5)-1,
         'joint moment has the actual NS spatial scaling')
    return {
        'actual_variables':'L=(-Delta5)^(-1/2), h=L eta, chi=L h, R_z=partial_z L, q=2R_z h',
        'physical_energy':'integral_R5 (b^2+h^2)=pi ||u||_L2(R3)^2',
        'parent_equation':'h_t+v.grad h-nu Delta5 h=L partial_z(b^2)-C, C=[L,v.grad]eta',
        'reserve':'R_p=integral_R5 (b^2+h^2)^(p/2), p=5/2',
        'nonlinear_defect':'Q_p=((p-2)/2)integral q Phi-p<b^2,[R_z,W]h>-p T_W',
        'transport_defect':'T_W=<W h,C>+(1/2)integral q W h^2; T_1=0 by div5(v chi)=0',
        'weight':'Phi=(b^2+h^2)^(p/2), W=(b^2+h^2)^((p-2)/2)',
        'diffusion':'D_p=integral p W(|grad b|^2+|grad h|^2)+p(p-2)(b^2+h^2)^((p-4)/2)|b grad b+h grad h|^2; D_(5/2)>=(5/2)Dcrit',
        'balance':'R_p_prime+nu D_p=Q_p; at p=2, Q_2=0 recovers literal kinetic-energy dissipation',
        'conditional_clock':'if integral Q_(5/2)<=(nu/2)integral D_(5/2)+K, then integral S^2 <=(5 C5/(4nu))*(R_(5/2)(0)+K)^(12/5)',
        'scope':'actual axisymmetric evolution without reflection or ordering assumptions; the signed Q allowance remains open'}


def positive_critical_return():
    y=s.symbols('y',nonnegative=True)
    poly=-120+49*y-4*y*y
    Q=(poly-30)**2+31
    zero(Q-poly-(poly-s.Rational(61,2))**2-s.Rational(3,4),
         'Q dominates the positive profile polynomial')
    zero(Q+poly-(poly-s.Rational(59,2))**2-s.Rational(243,4),
         'Q dominates its negative as well')
    qrad=r**10*s.exp(-r*r)
    h=r**8*s.exp(-r*r)*poly.subs(y,r*r)
    zero(qrad-lap5(qrad)-h, 'exact radial inverse at unit axial frequency')
    terms=s.Poly(s.expand(poly*Q),y).terms()
    moment=lambda rows:sum(c*s.factorial(k+11)/(2*s.Rational(9,4)**(k+12))
                           for (k,),c in rows)
    J=moment(terms)
    A=moment([((k,),abs(c)) for (k,),c in terms])
    zero(J+s.Rational(1500298173892001792000,205891132094649),
         'exact critical-return radial moment')
    eps=s.Rational(1,31**3)
    require((1-eps)**7>s.Rational(1,16), 'fractional third derivative majorant is below two')
    alpha=s.Rational(5,4)
    zero(abs(alpha*(alpha-1)*(alpha-2))/6-s.Rational(5,128),
         'fractional-power Taylor remainder coefficient')
    phase=s.symbols('phase',real=True)
    zero(s.integrate(s.cos(phase)**4,(phase,0,2*s.pi))/(2*s.pi)-s.Rational(3,8),
         'phase factor in the cubic Taylor remainder')
    margin=-s.Rational(5,8)*J-s.Rational(15,512)*eps**2*A
    require(margin>0, 'the complete periodic return is strictly positive')
    zero(margin-s.Rational(832198796201609419506581504000,182729137619258227902969),
         'exact lower phase margin')
    return {
        'profiles':'qrad=r^10 exp(-r^2), h=r^8 exp(-r^2)p, F=r^8 exp(-r^2)Q^4',
        'polynomials':'p=-120+49y-4y^2, Q=(p-30)^2+31, y=r^2',
        'relative_oscillation':'|h|/F<=31^-3',
        'radial_moment':str(J),'absolute_moment_bound':str(A),'phase_margin':str(margin),
        'whole_space':'f_L=exp(-z^2/L^2)(F+h cos z), b0=sqrt(f_L), u0=(-x2 b0,x1 b0,0)',
        'localization':'A5=-partial_zz(-Delta5)^-1; ||A5 f_L-exp(-z^2/L^2)qrad cos z||_2/sqrt(L)->0 by strong multiplier continuity and dominated convergence',
        'positive_return':'I_L=integral b0^(5/2) q_t(0)>0 for all sufficiently large finite L; lim I_L/L>=4pi^2 sqrt(4pi/9)*phase_margin>0',
        'scope':'the rational phase bound is exact; the localization and existence of a sufficiently large finite L are analytic, not an explicit numerical localization certificate'}


def actual_interval():
    I,D,k=s.symbols('I D k',positive=True)
    coefficient=s.Rational(3,4)*I*k*k-s.Rational(15,4)*D*k
    zero(coefficient.subs(k,10*D/I)-s.Rational(75,2)*D*D/I,
         'complete positive-viscosity critical-moment increment')
    tau=s.symbols('tau',positive=True)
    lower=-s.Rational(15,4)*(I*tau/(20*D))*D*tau+s.Rational(3,8)*I*tau*tau
    zero(lower-s.Rational(3,16)*I*tau*tau,
         'fixed rescaled interval supplies a finite fraction of critical initial scale')
    return {
        'scaling':'fix the finite profile and nu>0; u_A(t)=A v_(nu/A)(A t), epsilon=nu/A',
        'uniform_jet':'M_epsilon_prime(0)=-(15epsilon/4)D0; M_epsilon_second(0)=(3/2)I+O(epsilon^2)',
        'time':'tau=k epsilon for v_epsilon, t=k nu/A^2 for u_A, k=10D0/I',
        'increment':'M_epsilon(k epsilon)-M0=epsilon^2*(75D0^2/(2I))+o(epsilon^2)>0',
        'remainder':'uniform C2 dependence of the smooth solution into L^(5/2); no O(epsilon^3) claim or long Taylor window is needed',
        'fixed_interval':'choose tau_*,epsilon_* with M_epsilon_second>=3I/4 on [0,tau_*]; if epsilon<=min(epsilon_*,I tau_*/(20D0)), the physical increment at tau_*/A is >=(3I tau_*^2/16) A^(5/2)',
        'necessary_allowance':'any dominating nonincreasing history reserve needs an initial excess >=c_* A^(5/2) on this amplified family, c_*>0 fixed by the unamplified profile; this does not refute a finite allowance proportional to M0',
        'no_go':'no nonincreasing state reserve R>=M which equals M on every initially pure swirl can cover this family; in particular the joint critical R_(5/2) fails that monotonicity',
        'surviving_target':'a nonzero initial allowance for future parent generation, or a signed full-datum history budget; this is a finite burst, not indefinite renewal'}


def quadrature():
    import numpy as np
    from scipy.special import roots_genlaguerre
    rows=[]
    phase=2*np.pi*(np.arange(512)+.5)/512
    c=np.cos(phase)
    for order in (32,64,96):
        x,w=roots_genlaguerre(order,11)
        y=x/(9/4)
        p=-120+49*y-4*y*y
        Q=(p-30)**2+31
        ratio=p/Q**4
        avg=np.mean(c[None,:]*np.expm1(1.25*np.log1p(ratio[:,None]*c[None,:])),axis=1)
        value=float(np.sum(w*Q**5*avg)/(2*(9/4)**12))
        require(value<0,'quadrature supports the strict negative phase pairing')
        rows.append({'radial_order':order,'phase_samples':512,'phase_radial_pairing':value})
    return {'rows':rows,'scope':'supporting floating-point periodic quadrature only; not a localization or actual-time certificate'}


if __name__ == '__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--quadrature',action='store_true')
    args=parser.parse_args()
    result={'joint_exchange':joint_exchange(),
            'critical_return':positive_critical_return(),
            'actual_interval':actual_interval()}
    if args.quadrature:
        result['quadrature']=quadrature()
    print(json.dumps(result,indent=2))
