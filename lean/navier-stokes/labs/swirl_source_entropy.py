#!/usr/bin/env python3
"""An actual-flow circulation envelope with a funded stochastic action.

The differential identities, measure conversion and reserve algebra are
exact. Parabolic construction, maximum principles, entropy integration,
Girsanov identification and moment bounds remain analytic.
No deformation-moment or general regularity estimate is asserted.
"""

import json
import sympy as s
from rotational_curl_reserve import zero
from rotational_joint_enstrophy import r, z, grad, lap5, velocity


def physical_density():
    chi, b=s.Function('chi')(r,z),s.Function('b')(r,z)
    v=velocity(chi)
    div5=lambda x:s.diff(x[0],r)+3*x[0]/r+s.diff(x[1],z)
    q=-2*v[0]/r
    nu=s.symbols('nu',positive=True)
    zero(div5(v)+q,'incompressibility fixes the divergence of the five-dimensional drift')
    physical_rhs=nu*lap5(b)-v.dot(grad(b))+q*b
    zero(physical_rhs-(nu*lap5(b)-div5(v*b)),
         'actual swirl amplitude is a five-dimensional Fokker-Planck density when nonnegative')
    Gamma=r*r*b
    circulation_rhs=nu*(s.diff(Gamma,r,2)-s.diff(Gamma,r)/r+s.diff(Gamma,z,2))-v.dot(grad(Gamma))
    zero(r*r*physical_rhs-circulation_rhs,
         'the same actual-flow positive envelope has the circulation maximum principle')
    zero(3*b*b*physical_rhs-(nu*lap5(b**3)-div5(v*b**3)+2*q*b**3
         -6*nu*b*grad(b).dot(grad(b))),
         'cubic source stock retains signed parent work and the full diffusion payment')
    zero(2*s.pi**2*r**3*b*v.dot(v)-s.pi*(r*r*b)*v.dot(v)*2*s.pi*r,
         'lifted action equals physical kinetic action weighted by circulation')
    return {'drift':'v5=(u_r*x_h/r,u_z) on R4 x R, |v5|^2=u_r^2+u_z^2, div5(v5)=2u_r/r=-q',
            'density':'b_t=nu*Delta5 b-div5(v5*b)',
            'envelope':'B solves the same linear equation along the actual NS drift, B0=|b0|; |b|<=B and 0<=r^2 B<=G0=||r^2 b0||_infinity',
            'mass':'M=integral_R5 B=integral_R5 |b0|>0, rho=B/M',
            'pointwise_in_time_action':'integral_R5 rho*|v5|^2=(pi/M)*integral_R3 (r^2 B)*|v_mer|^2 <= C*E(t), C=pi*G0/M',
            'cubic_stock_balance':'d_t integral_R5 b^3 +6nu*integral_R5 b*|grad b|^2 =2*integral_R5 q*b^3 for nonnegative b',
            'scope':'axisymmetric actual unforced whole-space flow, regular axis, finite initial envelope mass and circulation maximum; not an arbitrary chosen fluid force'}


def entropy_identity():
    phi,g,chi=[s.Function(n)(r,z) for n in ('phi','g','chi')]
    rho=s.exp(phi+g)
    nu=s.symbols('nu',positive=True)
    v=velocity(chi)
    div5=lambda x:s.diff(x[0],r)+3*x[0]/r+s.diff(x[1],z)
    J=nu*grad(rho)-rho*v
    rho_t=div5(J)
    # gamma=exp(g) solves the actual five-dimensional heat equation.
    gamma_log_rate=nu*(lap5(g)+grad(g).dot(grad(g)))
    entropy_rate=(phi+1)*rho_t-rho*gamma_log_rate
    flux=(phi+1)*J-nu*rho*grad(g)
    zero(entropy_rate-div5(flux)+nu*rho*grad(phi).dot(grad(phi))-rho*v.dot(grad(phi)),
         'complete relative entropy rate with heat reference and all transport fluxes')
    p=grad(phi)
    raw=-nu*rho*p.dot(p)+rho*v.dot(p)
    bound=-nu*rho*p.dot(p)/2+rho*v.dot(v)/(2*nu)
    zero(bound-raw-rho*(v-nu*p).dot(v-nu*p)/(2*nu),
         'nonnegative square leaves half the full Fisher dissipation')
    t,L=s.symbols('t L',positive=True)
    variance=L*L+2*nu*t
    gaussian=(2*s.pi*variance)**s.Rational(-5,2)*s.exp(-(r*r+z*z)/(2*variance))
    zero(s.diff(gaussian,t)-nu*lap5(gaussian),'normalized five-dimensional heat reference')
    return {'relative_entropy':'K=integral rho*log(rho/gamma_L), gamma_L=N(0,(L^2+2nu*t)I5)',
            'relative_fisher':'I=integral rho*|grad log(rho/gamma_L)|^2',
            'exact_rate':'K_prime=-nu*I+integral rho*v5.grad log(rho/gamma_L)',
            'square':'Q=(1/(2nu))*integral rho*|v5-nu*grad log(rho/gamma_L)|^2>=0',
            'rate_with_square':'K_prime=-(nu/2)*I+W/(2nu)-Q, W=integral rho*|v5|^2'}


def reserves():
    C,nu,H,t,E,d,K,I,W,Q=s.symbols('C nu H t E d K I W Q',positive=True)
    RA=C*(H-t)*E
    R=K+RA/(2*nu)
    rate=s.diff(R,t)-2*nu*d*s.diff(R,E)+(-nu*I/2+W/(2*nu)-Q)*s.diff(R,K)
    zero(rate+nu*I/2+Q+(C*E-W)/(2*nu)+C*(H-t)*d,
         'nonnegative entropy-plus-energy reserve pays the entire compatible Fisher history')
    zero(s.diff(RA,t)-2*nu*d*s.diff(RA,E)+C*E+2*nu*C*(H-t)*d,
         'same horizon reserve pays drift action on every subinterval')
    # Noise sqrt(2nu) gives action coefficient 1/(4nu), not 1/(2nu).
    noise=s.sqrt(2*nu)
    zero(s.Rational(1,2)/noise**2-1/(4*nu),'Girsanov entropy normalization')
    return {'action_reserve':'R_A=C*(H-t)*E(t)>=0, R_A_prime+W<=0',
            'entropy_reserve':'R=K+C*(H-t)*E(t)/(2nu)>=0',
            'exact_ledger':'R_prime+(nu/2)*I+Q+(C*E-W)/(2nu)+C*(H-t)*d=0',
            'initial_allowance':'R(0)=KL(rho0||gamma_L(0))+pi*G0*H*E0/(2nu*M)',
            'whole_history':'R(T)+(nu/2)*integral_0^T I<=R(0) for every smooth prefix T<=H',
            'path_entropy':'KL(P_[0,T]||Brownian_rho0,nu)=integral_0^T W/(4nu)<=pi*G0*H*E0/(4nu*M)',
            'scope':'funded actual-source-envelope action and relative Fisher information; no optimal Schrodinger bridge or fourth deformation moment bound is claimed'}


def concentration_gap():
    lam=s.symbols('lam',positive=True)
    x=s.symbols('x',nonnegative=True)
    g=s.exp(-x/2)
    spike=lam**2*s.exp(-lam**2*x/2)
    # Both gradients are negative multiples of the same radial vector.
    A,B,a,c=s.symbols('A B a c',nonnegative=True)
    zero((A+B)*(a+c)**2-B*c*c-
         (A*a*a+B*a*a+2*(A+B)*a*c+A*c*c),
         'adding the positive Gaussian background cannot reduce the cubic diffusion source')
    zero(lam**2*(lam**3)**2*lam**(-5)-lam**3,
         'five-dimensional instantaneous cubic-variance scaling')
    zero(lam**3*lam**(-2)-lam,
         'physical NS time scaling leaves an unbounded integrated cubic variance')
    weight=1/(1+lam**3)
    KLspike=s.Rational(5,2)*(lam**(-2)-1+2*s.log(lam))
    zero(weight-lam**(-3)/(1+lam**(-3)),'normalized concentrated source mass')
    zero(5*s.log(lam)-(lam**2-1)*5/(2*lam**2)-KLspike,
         'Gaussian entropy formula from its exact second moment')
    zero(s.diff(s.log(lam)/lam**3,lam)-(1-3*s.log(lam))/lam**4,
         'uniform mixture-entropy upper bound is 5/(3e) for lambda>=1')
    zero(s.diff(x*g,x)-g*(1-x/2),'circulation maximum occurs at squared radius two')
    zero((x*g).subs(x,2)-2/s.E,'each Gaussian circulation maximum is two over e')
    Mbase=(2*s.pi)**s.Rational(5,2)
    Ebase=s.pi**s.Rational(3,2)
    nu,H=s.symbols('nu H',positive=True)
    Cmax=s.pi*(4/s.E)/Mbase
    Rmax=5/(3*s.E)+Cmax*H*(4*Ebase)/(2*nu)
    zero(Rmax-(5/(3*s.E)+s.sqrt(2)*H/(s.E*nu)),
         'all initial entropy reserves in the Gaussian mixture family have one finite upper bound')
    zero(s.diff(g,x)+g/2,'base gradient direction')
    zero(s.diff(spike,x)+lam**2*spike/2,'spike gradient direction')
    return {'data':'b0_lambda(X)=exp(-|X|^2/2)+lambda^2*exp(-lambda^2*|X|^2/2), lambda>=1',
            'physical_velocity':'u0_lambda(x)=u_base(x)+lambda*u_base(lambda*x), u_base=(-x2*g,x1*g,0)',
            'mass':'M_lambda=(2pi)^(5/2)*(1+lambda^-3), bounded below by (2pi)^(5/2)',
            'energy_bound':'E0_lambda<=4*pi^(3/2)',
            'circulation_bound':'G0_lambda<=4/e',
            'normalized_mixture':'rho0_lambda=(1-w)*N(0,I5)+w*N(0,lambda^-2 I5), w=1/(1+lambda^3)',
            'entropy_bound':'KL(rho0_lambda||N(0,I5))<=w*(5/2)*(lambda^-2-1+2log(lambda))<=5/(3e)',
            'uniform_initial_reserve':str(s.simplify(Rmax)),
            'instantaneous_variance_lower':'integral_R5 b0_lambda*|grad b0_lambda|^2 >= lambda^3*integral_R5 g*|grad g|^2',
            'rescaled_actual_initial_velocity':'lambda^-1*u0_lambda(y/lambda)=u_base(y)+lambda^-1*u_base(y/lambda) -> u_base in C_b^1',
            'analytic_interval_consequence':'a common C_b^1 mild-solution interval gives integral_0^(tau/lambda^2) integral_R5 b_lambda*|grad b_lambda|^2 >= c*lambda for all sufficiently large lambda',
            'scope':'refutes uniform payment of the raw nonnegative third-moment covariance source by this bounded entropy/action reserve; full-datum history payment and signed cancellations remain open'}


if __name__=='__main__':
    print(json.dumps({'physical_density':physical_density(),'entropy_identity':entropy_identity(),
                      'reserves':reserves(),'concentration_gap':concentration_gap()},indent=2))
