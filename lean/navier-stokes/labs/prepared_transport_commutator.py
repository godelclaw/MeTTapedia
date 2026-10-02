#!/usr/bin/env python3
"""Homogeneous prepared-transport payment and the complete residual parent.

Exact checks cover kernel derivatives, cancellation, exponents and critical
balance algebra. Singular-integral bounds, potential reconstruction and
actual PDE history estimates are analytic, not Lean-certified here.
"""

import json
import sympy as s
from rotational_curl_reserve import zero
from rotational_joint_enstrophy import r, z, velocity


def kernel_checks():
    zz=s.symbols('z0:5',real=True)
    radius2=sum(t*t for t in zz)
    kernel=radius2**(-2)
    for j,k in [(0,0),(0,1)]:
        kj=-4*zz[j]/radius2**3
        kjk=-4*int(j==k)/radius2**3+24*zz[j]*zz[k]/radius2**4
        zero(s.diff(kernel,zz[j])-kj, 'first derivative of the five-dimensional I1 kernel')
        zero(s.diff(kernel,zz[j],zz[k])-kjk, 'second derivative of the I1 kernel')
        for ell in (0,1,2):
            local=zz[ell]*kjk
            zero(local.xreplace({x:-x for x in zz})+local,
                 'the local homogeneous degree-minus-five kernel is odd')
            lam=s.symbols('lambda',positive=True)
            zero(local.xreplace({x:lam*x for x in zz})-lam**(-5)*local,
                 'the local angular kernel has the Calderon-Zygmund homogeneity')
            # Fourier transform of z_ell partial_j partial_k I1, with
            # derivative symbol i xi_j. It is a bounded degree-zero symbol.
            multiplier=s.I*s.diff(-zz[j]*zz[k]/s.sqrt(radius2),zz[ell])
            riesz=lambda i:s.I*zz[i]/s.sqrt(radius2)
            predicted=(-int(ell==j)*riesz(k)-int(ell==k)*riesz(j)
                       -riesz(j)*riesz(k)*riesz(ell))
            zero(multiplier-predicted, 'odd local kernel has a bounded Riesz multiplier')
    x,y=s.symbols('x y',real=True)
    K=s.Function('K')
    F=s.Function('F')
    h=K(x-y)*(F(y)-F(x))
    expected=s.diff(K(x-y),y,2)*(F(y)-F(x))
    expected+=2*s.diff(K(x-y),y)*s.diff(F(y),y)+K(x-y)*s.diff(F(y),y,2)
    zero(s.diff(h,y,2)-expected, 'complete twice-integrated kernel product rule')
    rr=s.symbols('radius',positive=True)
    zero(s.integrate(rr**4*rr**(-6)*rr**2,(rr,0,2))-2,
         'the local quadratic Taylor remainder is integrable')
    zero(s.integrate(rr**4*rr**(-6),(rr,1,s.oo))-1,
         'the distant second-derivative kernel is integrable')
    p=s.Rational(5,2)
    zero(1/s.Rational(5,3)-1/p-s.Rational(1,5),
         'the homogeneous low-frequency potential uses strong HLS')
    zero(1/s.Rational(5,3)-1/p-1/s.Integer(5),
         'the Hessian coefficient multiplies L5/2 into L5/3')
    zero(1/s.Rational(5,2)-s.Rational(1,5)-s.Rational(1,5),
         'order-one prepared potential reconstruction into L5')
    zero(1/s.Rational(5,3)-s.Rational(1,5)-s.Rational(2,5),
         'weighted order-two prepared reconstruction into L5')
    zero(27*2+2*81-27*8, 'initial weighted heat seminorm coefficient')


def complete_residual_balance():
    b,a,p=s.symbols('b a p',positive=True)
    qr,q1,cpre,tself,comm,force=s.symbols('qR q1 c_pre T_self comm force',real=True)
    X=b*b+a*a
    phi=X**(p/2)
    w=X**(p/2-1)
    raw=(qr+q1)*(p*w*b*b-phi)-p*(qr*w*b*b/2+comm)
    # The total transport is its residual self part plus prepared transport.
    raw-=p*(tself-qr*w*a*a/2+cpre)
    raw+=p*force
    qself=(p/2-1)*qr*phi-p*comm-p*tself
    paid=q1*w*((p-1)*b*b-a*a)
    zero(raw-qself-paid+p*cpre-p*force,
         'complete residual balance combines the prepared divergence before absolute values')
    zero((p-1)*phi-paid/q1-p*w*a*a,
         'upper prepared coefficient bound')
    zero(paid/q1+phi-p*w*b*b,
         'lower prepared coefficient bound')
    chi=s.Function('chi')(r,z)
    va=velocity(chi)
    div5=lambda v:s.diff(v[0],r)+3*v[0]/r+s.diff(v[1],z)
    zero(div5(va*chi), 'recombined residual retains its exact kinetic compatibility')
    pp=s.Rational(5,2)
    zero(s.Rational(12,5)*pp-6, 'prepared commutator contribution to continuation exponent')
    zero(s.Rational(12,5)*(pp-1)-s.Rational(18,5),
         'prepared strain and supplied-source contribution to continuation exponent')
    zero(s.Rational(25,16)*2/pp-s.Rational(5,4),
         'critical-clock coefficient with half the joint diffusion')
    return {
        'state':'h=eta-eta1 (ALL unprepared parents), a=L h, v=v_a+v1, q=q_a+q1',
        'initial':'a(0)=L eta0, so R_p(0) contains both initial swirl and meridional data',
        'supply':'f=-R_z(B^2)-L(v.grad eta1), beta=1; no outside-source subtraction',
        'self_transport':'T_w^a=<w a,[L,v_a.grad]h>+(1/2)integral q_a w a^2; T_1^a=0',
        'self_exchange':'Q_self=((p-2)/2)integral q_a Phi-p<b^2,[R_z,w]a>-p T_w^a',
        'identity':'R_p_prime+nu D_p=Q_self+integral q1 w[(p-1)b^2-a^2]-p<w a,[L,v1.grad]h>+p<w a,f>',
        'scope':'quadratic self cancellation is restored; critical spatial-weighted Q_self remains OPEN',
    }


def certificate():
    return {
        'operator':'||[L,V.grad]L^(-1)a||_(5/2)<=C_op N(V)||a||_(5/2)',
        'coefficient':'N(V)=||V||_infinity+||grad V||_infinity+||D2 V||_infinity+||D2 V||_5',
        'kernel':'[L,F]partial_j partial_k has K_jk(F(y)-F(x))-K_j F_k-K_k F_j+K F_jk',
        'low_frequency':'K*(F_jk g) uses ||F_jk||_5 ||g||_(5/2) and I1:L5/3->L5/2',
        'prepared':'J=int_0^t heat(nu(t-s))[beta B(s)^2]ds, chi1=partial_z(-Delta5)^(-1)J, v1=(-y_h partial_z chi1,2chi1+y_h.grad_h chi1)',
        'initial_bound':'integral_0^H c1(t)dt<=C1=C_* C_beta,4 H^2(1+8nu H) N0^2',
        'N0':'sum of ||D^alpha b0||_q and ||y_i D^alpha b0||_q for |alpha|<=4, i<=4, q in {1,infinity,5/3,5/2}',
        'complete_parent':'use beta=1 for the recombined residual; Sigma=Sigma_B+Sigma_adv from the preceding payment, no Sigma_out',
        'weight':'Omega=exp[-integral ((p-1)(||q1||_infinity+g/Sigma)+p c1)], p=5/2; omit g/Sigma if Sigma=0',
        'logarithmic_allowance':'integral exponent<=(3/2)(A_cal+1)+(5/2)C1',
        'remaining_target':'integral_0^T Omega[Q_self-(nu/2)D_p]<=K_full(u0,nu,H)',
        'conditional_clock':'integral_0^T S^2 <=(5 C5/(4nu))*exp[(18/5)(A_cal+1)+6C1]*(R_p(0)+Sigma^(5/2)+K_full)^(12/5)',
        'status':'analytic estimates and exact scalar checks; no arbitrary-data regularity proof or new Lean theorem',
    }


if __name__=='__main__':
    kernel_checks()
    print(json.dumps({'balance':complete_residual_balance(),'payment':certificate()},indent=2))
