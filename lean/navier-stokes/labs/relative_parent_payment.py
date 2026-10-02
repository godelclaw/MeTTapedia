#!/usr/bin/env python3
"""Relative critical parent balance and payments for its supplied source terms.

Checks algebra, harmonic-analysis exponents, heat integration constants,
and a compatible two-field kinetic cross pairing. The PDE estimates and
history payment are analytic; no arbitrary-history regularity is claimed.
"""

import json
import sympy as s
from rotational_curl_reserve import require, zero
from rotational_joint_enstrophy import r, z, grad, lap5, velocity


def relative_balance():
    b,a,p=s.symbols('b a p',positive=True)
    q0,qr,comm,tr,forcing=s.symbols('q0 qr comm tr forcing',real=True)
    X=b*b+a*a
    phi=X**(p/2)
    w=X**(p/2-1)
    q=q0+qr
    raw=q*(p*w*b*b-phi)-p*(qr*w*b*b/2+comm)
    raw-=p*(tr-q*w*a*a/2)
    raw+=p*forcing
    paid=q0*w*((p-1)*b*b+(p/2-1)*a*a)
    renewal=(p/2-1)*qr*phi-p*comm-p*tr
    zero(raw-paid-renewal-p*forcing, 'full relative critical exchange')
    zero((p-1)*phi-paid/q0-p*w*a*a/2,
         'the paid-parent coefficient is at most (p-1) times the joint moment')
    vec=s.Matrix([b,a])
    zero(s.hessian(phi,[b,a])-
         (p*w*s.eye(2)+p*(p-2)*X**(p/2-2)*(vec*vec.T)),
         'complete evolving convex diffusion')
    return {
        'variables':'h=eta_core-eta1, a=L h, L=(-Delta5)^(-1/2), qR=2 R_z a, q=q0+qR',
        'amplitude':'Phi=(b^2+a^2)^(p/2), w=(b^2+a^2)^((p-2)/2), p=5/2',
        'parent_equation':'D_v a=R_z(b^2)-[L,v.grad]h+f',
        'supplied_terms':'f=-R_z(zeta b^2)-R_z(beta B^2)-L(v.grad eta1)',
        'transport':'T_w=<w a,[L,v.grad]h>+(1/2)integral q w a^2',
        'renewal':'Q_R=((p-2)/2)integral qR Phi-p<b^2,[R_z,w]a>-p T_w',
        'balance':'R_p_prime+nu D_p=Q_R+integral q0 w[(p-1)b^2+(p/2-1)a^2]+p<w a,f>',
        'scope':'the complete nonlinear Q_R is unpaid; the supplied f terms have initial-data L1_t Lp_x bounds',
    }


def payment_exponents():
    p=s.Rational(5,2)
    zero(1/s.Rational(5,3)-1/p-s.Rational(1,5),
         'Riesz potential maps L5/3 into L5/2 in dimension five')
    zero(1/s.Rational(5,3)-s.Rational(1,2)-s.Rational(1,10),
         'physical velocity energy pairs with the weighted prepared gradient')
    zero(1+ s.Rational(1,5)-s.Rational(9,10)-s.Rational(3,10),
         'early heat Young exponents')
    zero(1+ s.Rational(1,5)-s.Rational(7,10)-s.Rational(1,2),
         'late heat Young exponents')
    early,late,x=s.symbols('early late x',positive=True)
    split=late/early
    integral=s.integrate(early/s.sqrt(x),(x,0,split))
    integral+=s.integrate(late/x**s.Rational(3,2),(x,split,s.oo))
    zero(integral-4*s.sqrt(early*late), 'complete prepared square-source clock')
    zero(20*9*2+2*20*27-180*8,
         'weighted heat commutation and source product constants')
    zero(s.Rational(180,2)-90, 'integrated prepared transport constant')
    zero(s.Rational(2,5)*3-s.Rational(6,5), 'off-axis circulation exponent')
    zero(s.Rational(2,5)*6-s.Rational(12,5), 'off-axis radial cutoff exponent')
    y=s.symbols('y',nonnegative=True)
    gap=s.Rational(3,2)*y**5-s.Rational(5,2)*y**3+1
    factor=(y-1)**2*(3*y**3+6*y**2+4*y+2)/2
    zero(gap-factor, 'normalized Young payment is nonnegative for every receiver size')
    zero(s.Rational(25,16)*2/p-s.Rational(5,4),
         'conditional clock after half of joint diffusion')
    zero((p-1)*s.Rational(12,5)-s.Rational(18,5),
         'combined history-weight exponent')


def kinetic_cross_pairing():
    chi=s.exp(-(r*r+z*z)/2)
    chi0=z*chi
    eta=-lap5(chi)
    vr,v0=velocity(chi),velocity(chi0)
    div5=lambda v:s.diff(v[0],r)+3*v[0]/r+s.diff(v[1],z)
    zero(div5(vr*chi), 'the residual velocity has its own kinetic cancellation')
    f=s.expand(s.simplify(chi*v0.dot(grad(eta))/chi**3))
    zero(f-(r*r+z*z-7)*(-r*r+2*z*z), 'complete compatible cross integrand')
    value=0
    rate=s.Rational(3,2)
    for (i,j),c in s.Poly(f,r,z).terms():
        if j%2:
            continue
        radial=s.gamma(s.Rational(i+4,2))/(2*rate**s.Rational(i+4,2))
        axial=s.gamma(s.Rational(j+1,2))/rate**s.Rational(j+1,2)
        value+=2*s.pi**2*c*radial*axial
    value=s.simplify(value)
    zero(value-s.Rational(28,9)*(2*s.pi/3)**s.Rational(5,2),
         'nonzero exact cross pairing of two reconstructed meridional fields')
    require(value.is_positive, 'the omitted cross pairing would have a genuine sign')
    return {'pairing':str(value),
            'scope':'a kinematically compatible two-field algebra test, not a claim that this pair is realized by the prescribed source-history split'}


def certificate():
    return {
        'source_clock':'Sigma_B=(4 C_R A_e A_l sqrt(C5)/nu) F G',
        'heat_constants':'A_e=(4pi)^(-1/4)(10/9)^(-9/4), A_l=(4pi)^(-3/4)(10/7)^(-7/4)',
        'outside_clock':'Sigma_out=C_R H pi^(2/5) E0^(2/5) Gamma0^(6/5) rho^(-12/5)',
        'transport_clock':'Sigma_adv=90 C_I sqrt(pi E0) C_beta A3 H^2 (C3+8nu H B4)',
        'initial_norms':'C_beta=max_|alpha|<=3 ||D^alpha beta||_infinity; A3=max_|alpha|<=3 ||D^alpha b0||_infinity; B4=max_|alpha|<=4 ||D^alpha b0||_10; C3=max_i<=4,|alpha|<=3 ||y_i D^alpha b0||_10',
        'physical_input':'||v/r||_L2(R5)<=sqrt(pi E0) from actual unforced kinetic energy; no future velocity-gradient bound',
        'majorant':'||f(t)||_(5/2)<=g(t), integral_0^H g<=Sigma=Sigma_B+Sigma_out+Sigma_adv; g uses only original data and heat history',
        'young_payment':'p g R^((p-1)/p)<=(p-1)(g/Sigma)R+g Sigma^(p-1); integral g Sigma^(p-1)<=Sigma^p',
        'weight':'Omega=exp[-(3/2) integral(a0+g/Sigma)], a0=||q_paid||_infinity+||q1||_infinity; omit g/Sigma if Sigma=0',
        'remaining_target':'integral_0^T Omega[Q_R-(nu/2)D_p]<=K_joint(original datum,nu,H,rho)',
        'conditional_clock':'integral_0^T S^2 <=(5 C5/(4nu))*exp[(18/5)(2 M_H+A_cal+1)]*(M0+Sigma^(5/2)+K_joint)^(12/5)',
        'scope':'prepared source, off-axis source, and full actual transport of the prepared parent are paid; residual nonlinear exchange and transport remain OPEN',
    }


if __name__=='__main__':
    balance=relative_balance()
    payment_exponents()
    print(json.dumps({'balance':balance,'kinetic_cross':kinetic_cross_pairing(),
                      'payment':certificate()},indent=2))
