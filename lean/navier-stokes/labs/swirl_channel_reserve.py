#!/usr/bin/env python3
"""Swirl-channel payment, separated-source obstruction, and a critical moment.

Checks exact balance identities, scaling, Gaussian constants and the
viscous rebound coefficient. Translation limits, PDE evolution, Sobolev
interpolation and continuation are analytic, not kernel-certified here.
"""

import json
import sympy as s
from rotational_curl_reserve import require, zero
from rotational_joint_enstrophy import r, z, grad, lap5, velocity


def channel_balance():
    b, chi = s.Function('b')(r,z), s.Function('chi')(r,z)
    v = velocity(chi)
    q = -2*v[0]/r
    nu = s.symbols('nu',positive=True)
    div5 = lambda x: s.diff(x[0],r)+3*x[0]/r+s.diff(x[1],z)
    bt = nu*lap5(b)-v.dot(grad(b))+q*b
    zero(2*b*bt-nu*lap5(b*b)+div5(v*b*b)-q*b*b
         +2*nu*grad(b).dot(grad(b)),
         'actual swirl-channel kinetic balance, including signed transfer')
    Z,S,D2,D3 = s.symbols('Z S D2 D3',positive=True)
    P2,P3 = s.symbols('P2 P3',real=True)
    R = (Z*S)**s.Rational(6,5)
    rate = s.diff(R,Z)*(P2-2*nu*D2)+s.diff(R,S)*(2*P3-6*nu*D3)
    expected = s.Rational(6,5)*(Z*S)**s.Rational(1,5)*(
        S*P2+2*Z*P3-2*nu*S*D2-6*nu*Z*D3)
    zero(rate-expected, 'separate-channel reserve retains both source weights')
    return {'variables':'Z=integral_R5 b^2=pi E_theta, S=integral_R5 |b|^3',
            'channel_rate':'Z_prime=P2-2nu D2, P2=integral q b^2, D2=integral |grad b|^2',
            'cubic_rate':'S_prime=2P3-6nu D3',
            'reserve':'R_theta=(Z S/pi)^(6/5)',
            'unscaled_rate':'d_t (Z S)^(6/5)=(6/5)(Z S)^(1/5)[S P2+2Z P3-2nu S D2-6nu Z D3]',
            'pure_swirl_initial_transfer':'P2_prime(0)=-2||R_z(b0^2)||_L2(R5)^2<=0; R_z=partial_z(-Delta5)^(-1/2)'}


def separated_source():
    lam = s.symbols('lambda',positive=True)
    Zg = s.pi**s.Rational(5,2)
    Sg = (2*s.pi/3)**s.Rational(5,2)
    Tg = -s.Rational(2,5)*(s.pi/2)**s.Rational(5,2)
    Ig = -s.Rational(2,5)*(2*s.pi/5)**s.Rational(5,2)
    x = s.symbols('x',real=True)
    for power,expected in ((2,Zg),(3,Sg),(4,-5*Tg/2),(5,-5*Ig/2)):
        integral = s.integrate(s.exp(-s.Rational(power,2)*x*x),
                               (x,-s.oo,s.oo))**5
        zero(integral-expected, 'five-dimensional Gaussian moment '+str(power))
    zero(lam**4*lam**(-5)-lam**(-1), 'remote Gaussian kinetic scaling')
    zero(lam**6*lam**(-5)-lam, 'remote Gaussian cubic stock scaling')
    zero(lam**4*lam**4*lam**(-5)-lam**3, 'remote quadratic pressure-return scaling')
    zero(lam**6*lam**4*lam**(-5)-lam**5, 'remote cubic pressure-return scaling')
    Z,S,I = s.symbols('Z S I',positive=True)
    T = s.symbols('T',real=True)
    J = (S+lam*Sg)*(T+lam**3*Tg)+2*(Z+Zg/lam)*(I+lam**5*Ig)
    zero(s.limit(lam*J,lam,0,dir='+')-2*Zg*I,
         'weak distant source overturns the global product despite signed kinetic transfer')
    # A finite-parameter lower bound: for 0<lambda<=1, all omitted
    # terms in this expression are nonnegative.
    ta,ia,zg,sg,tg = s.symbols('ta ia zg sg tg',nonnegative=True)
    j = (S+lam*sg)*(-ta-lam**3*tg)+2*(Z+zg/lam)*(I-lam**5*ia)
    C = (S+sg)*(ta+tg)+2*(Z+zg)*ia
    remainder = ((1-lam)*sg*ta+(1-lam**3)*S*tg+(1-lam**4)*sg*tg
                 +2*Z*I+2*ia*((1-lam**5)*Z+(1-lam**4)*zg))
    zero(j-(2*zg*I/lam-C)-remainder, 'explicit lower bound before choosing finite separation')
    zero((2*zg*I/lam-C).subs(lam,zg*I/(C+2*zg*I))-C-4*zg*I,
         'one finite scale has a strictly positive lower margin')
    return {'base':'fixed nonnegative Schwartz pure swirl with I=integral b_*^3 sigma_*>0 from swirl_cubic_clock.py',
            'remote':'g_lambda,R(X)=lambda^2 exp(-lambda^2 |X-R e_z|^2/2), b0=b_*+g_lambda,R',
            'Gaussian_constants':{'Z':str(Zg),'S':str(Sg),'T2':str(Tg),'I3':str(Ig)},
            'ordered_limits':'first R->infinity at each fixed lambda>0, then lambda->0',
            'separated_second_coefficient':str(J),
            'positive_leading_coefficient':'lambda J_lambda -> 2 Zg I>0',
            'finite_choice':'C=(S+Sg)(|T|+|Tg|)+2(Z+Zg)|Ig|; choose lambda=Zg I/(C+2Zg I), then sufficiently large finite R',
            'analytic_input':'L2 bounded translation-invariant Riesz multiplier and Schwartz translation decoupling; the full composite NS datum is used'}


def viscous_rebound():
    Z,S,D2,D3,I,eps = s.symbols('Z S D2 D3 I epsilon',positive=True)
    T = s.symbols('T',real=True)
    k = s.symbols('k',positive=True)
    Zt = Z+eps**2*(T*k*k/2-2*D2*k)
    St = S+eps**2*(I*k*k-6*D3*k)
    J = S*T+2*Z*I
    loss = 2*S*D2+6*Z*D3
    coefficient = s.expand(Zt*St).coeff(eps,2)
    zero(coefficient-J*k*k/2+loss*k, 'complete two-channel viscous product expansion')
    zero(s.factor(coefficient.subs(k,4*loss/J)-4*loss**2/J),
         'strict positive rebound when the composite initial coefficient J is positive')
    return {'condition':'J=S0*T2+2Z0*I3>0, supplied by the separated-source construction',
            'loss':'L=2 S0 D2,0+6 Z0 D3,0',
            'time':'u_A(t)=A v_(nu/A)(A t), k=4L/J, t=k nu/A^2',
            'positive_coefficient':'Z S-Z0 S0=(nu/A)^2*(4L^2/J)+O((nu/A)^3) for v_(nu/A)',
            'scope':'actual short unforced histories at every fixed nu>0, for sufficiently large A; no separate evolutions are glued',
            'refuted':'monotonicity of the global product (E_theta S)^(6/5), even from pure swirl',
            'not_refuted':'an original-datum allowance, a spatially compatible correction, or regularity'}


def critical_moment():
    # Positive b suffices for the symbolic chain rule; |b|^(5/2) is C2
    # and gives the same integrated identity for sign-changing smooth b.
    b, nu = s.symbols('b nu',positive=True)
    br,bz,brr,bzz,vr,vz,q = s.symbols('br bz brr bzz vr vz q',real=True)
    p = s.Rational(5,2)
    bt = nu*(brr+3*br/r+bzz)-vr*br-vz*bz+q*b
    phi = b**p
    phib = s.diff(phi,b); phibb = s.diff(phi,b,2)
    lap_phi = phib*(brr+3*br/r+bzz)+phibb*(br*br+bz*bz)
    div_v_phi = -q*phi+phib*(vr*br+vz*bz)
    zero(phib*bt-nu*lap_phi+div_v_phi-(p-1)*q*phi
         +nu*p*(p-1)*b**(p-2)*(br*br+bz*bz),
         'complete critical moment balance')
    zero(s.Rational(1,3)-s.Rational(7,12)/p-s.Rational(5,12)/s.Rational(25,6),
         'critical moment interpolation for the cubic continuation clock')
    zero(s.Rational(7,4)/p-s.Rational(7,10), 'moment exponent in the cubic stock bound')
    zero(s.Rational(5,4)/p-s.Rational(1,2), 'diffusion exponent in the cubic stock bound')
    coefficient = (p*p/4)*s.Rational(8,15)
    zero(coefficient-s.Rational(5,6), 'conditional clock allowance coefficient')
    lam = s.symbols('lambda',positive=True)
    zero((lam**2)**p*lam**(-5)-1, 'critical moment is invariant under NS scaling')
    zero((lam**2)**(p-2)*(lam**3)**2*lam**(-5)-lam**2,
         'critical moment diffusion has the inverse physical time scaling')
    return {'actual_moment':'M=integral_R5 |b|^(5/2), additive across disjoint regions',
            'actual_diffusion':'Dcrit=integral_R5 |b|^(1/2)|grad b|^2',
            'actual_parent_cost':'Pcrit=integral_R5 q|b|^(5/2)',
            'balance':'M_prime=(3/2)Pcrit-(15nu/4)Dcrit',
            'clock_bound':'S^2 <= (25/16) C5 M^(7/5) Dcrit',
            'candidate_budget':'(3/2) integral_0^T Pcrit <= (15nu/8) integral_0^T Dcrit+K(u0,nu,H)',
            'conditional_payment':'M(T)+(15nu/8)integral_0^T Dcrit <= M0+K=N',
            'conditional_continuation_clock':'integral_0^T S^2 <= (5 C5/(6nu))*N^(12/5)',
            'concentrated_mixture':'for b0=g+lambda^2*g(lambda X), lambda>=1, M0<=2^(5/2)*integral g^(5/2), independently of lambda',
            'scope':'analytic sufficient axisymmetric budget; neither its signed payment nor monotonicity is asserted'}


def many_burst_entropy():
    N,lam = s.symbols('N lambda',positive=True)
    j = s.symbols('j',integer=True,positive=True)
    lamN = N*N
    mass_ratio = N*lamN**(-3)
    zero(mass_ratio-N**(-5), 'total narrow-packet source mass')
    zero(N*lamN**s.Rational(-1,2)-1,
         'triangle inequality gives a uniform physical kinetic square')
    entropy_bound = lamN**(-3)*(5*N*s.log(lamN)+N**3/2)
    zero(s.expand_log(entropy_bound,force=True)-(10*s.log(N)/N**5+1/(2*N**3)),
         'all remote means are retained in the Gaussian relative entropy')
    zero(s.diff(10*s.log(N)/N**5,N)-10*(1-5*s.log(N))/N**6,
         'uniform logarithmic entropy bound two over e')
    nu,H = s.symbols('nu H',positive=True)
    Mbase = (2*s.pi)**s.Rational(5,2)
    Ebound = 4*s.pi**s.Rational(3,2)
    Gbound = 16/s.E
    reserve_bound = 2/s.E+s.Rational(1,2)+s.pi*Gbound*H*Ebound/(2*nu*Mbase)
    zero(reserve_bound-(2/s.E+s.Rational(1,2)+4*s.sqrt(2)*H/(s.E*nu)),
         'entire source entropy allowance is uniform in the packet count')
    zero((N*lam)**2*lam**(-2)-N*N,
         'actual cubic and physical swirl clocks retain the square of multiplicity')
    zero((lam**2)**s.Rational(5,2)*lam**(-5)-1,
         'each narrow packet contributes one critical moment unit')
    zero(4*s.pi**2*s.integrate(r**3,(r,1,2))-15*s.pi**2,
         'five-dimensional volume of one retained annulus')
    zero(4*s.pi*s.integrate(r**5,(r,1,2))-42*s.pi,
         'physical fourth-power swirl weight on one retained annulus')
    return {'data':'b0,N(X)=g(X)+sum_(j=1)^N lambda^2 g(lambda*(X-j e_z)), g=exp(-|X|^2/2), lambda=N^2',
            'physical_velocity':'u0,N=(-x2*b0,N,x1*b0,N,0); every datum is a finite Schwartz pure swirl',
            'uniform_energy':'E0,N<=4*pi^(3/2)',
            'uniform_circulation':'G0,N<=16/e, using the Gaussian lattice-sum bound',
            'source_mass':'M1,N=(2pi)^(5/2)*(1+N^-5)',
            'uniform_initial_entropy':'KL(rho0,N||N(0,I5))<=2/e+1/2, including all translated means',
            'uniform_entropy_reserve':str(reserve_bound),
            'actual_rescaling':'v_N(tau,y)=lambda^-1 u_N(tau/lambda^2,y/lambda), with viscosity unchanged',
            'uniform_local_input':'v_N(0)=lambda^-1 u_base(y/lambda)+sum_j u_base(y-lambda*j*e_z); Gaussian separation bounds every C_b^m norm independently of N',
            'analytic_interval':'uniform C_b^1 local evolution stays close on a fixed interval 0<=tau<=tau0(nu), retaining positive swirl on N disjoint annuli',
            'unbounded_physical_clock':'integral_0^(tau0/lambda^2) ||u_theta,N||_4^8 >= c(nu)*N^2',
            'unbounded_source_clock':'integral_0^(tau0/lambda^2) S_N^2 >= c_prime(nu)*N^2',
            'critical_initial_stock':'integral |b0,N|^(5/2)>=N*integral g^(5/2)',
            'refuted':'a finite uniform bound on either displayed clock based only on the displayed common upper bounds, at fixed viscosity and horizon',
            'not_refuted':'a budget depending on the full datum or critical moment; no single datum is asserted to blow up'}


def funded_parent_factor():
    M,w,a,nu,D = s.symbols('M w a nu D',nonnegative=True)
    Pc,Ppaid = s.symbols('Pc Ppaid',real=True)
    rate = -s.Rational(3,2)*a*w*M+w*(s.Rational(3,2)*(Pc+Ppaid)-s.Rational(15,4)*nu*D)
    defect = w*(s.Rational(3,2)*Pc-s.Rational(15,8)*nu*D)
    zero(rate+s.Rational(15,8)*nu*w*D-defect
         -s.Rational(3,2)*w*(Ppaid-a*M),
         'complete paid-parent integrating factor leaves only the signed core cost')
    exponent = s.Rational(3,2)*(s.Rational(7,5)+1)
    zero(exponent-s.Rational(18,5), 'full moment/diffusion factor in the continuation clock')
    zero(2*exponent-s.Rational(36,5), 'existing radial parent allowance has q=-2a')
    return {'split':'q=q_paid+q_core throughout space, with integral_0^T ||q_paid||_infinity<=A_H=2M_H for every available prefix T<=H',
            'factor':'w(t)=exp(-(3/2)integral_0^t ||q_paid||_infinity), exp(-3A_H/2)<=w<=1',
            'remaining_budget':'integral_0^T w[(3/2)Pcrit_core-(15nu/8)Dcrit]<=K(u0,nu,H,rho)',
            'conditional_clock':'integral_0^T S^2 <= (5C5/(6nu))*exp(36M_H/5)*(M0+K)^(12/5)',
            'paid_history':'all initial meridional vorticity and all source histories created outside the original radial cutoff, retaining their later motion',
            'unpaid_history':'parents generated near the axis, with the full interacting drift, pressure reconstruction and later transport',
            'scope':'uses the earlier analytic full-space paid-parent bound; no reset at seams and no payment of the remaining signed core cost is asserted'}


if __name__ == '__main__':
    print(json.dumps({'channel':channel_balance(),'separation':separated_source(),
                      'viscous_rebound':viscous_rebound(),'critical_moment':critical_moment(),
                      'many_burst_entropy':many_burst_entropy(),
                      'funded_parent_factor':funded_parent_factor()},indent=2))
