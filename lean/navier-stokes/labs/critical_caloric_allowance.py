#!/usr/bin/env python3
"""Critical initial funding for the complete first caloric parent history.

Checks exponents, time integrals, constants, and the exact decomposition.
Heat/Riesz bounds and the actual-flow Duhamel passage remain analytic.
"""

import json
import sympy as s
from rotational_curl_reserve import require, zero


def critical_bound():
    p=s.Rational(5,2)
    dimension=s.Integer(5)
    r_early=s.Rational(5,3)
    r_late=s.Rational(5,4)
    zero(1+1/p-1/(p/2)-1/r_early, 'early heat convolution exponents')
    zero(1+1/(2*p)-1/p-1/r_late, 'late heat convolution exponents')
    zero(dimension*(1-1/r_early)/2-1, 'early smoothing has one inverse time power')
    zero(dimension*(1-1/r_late)/2-s.Rational(1,2), 'late smoothing has half an inverse time power')
    t,nu=s.symbols('t nu',positive=True)
    a=s.symbols('a',real=True)
    zero(s.integrate(1/(t-a),(a,0,t/2))-s.log(2), 'early time integral')
    zero(s.integrate(1/a,(a,t/2,t))-s.log(2), 'late time integral')
    zero(s.Rational(25,16)/(p*(p-1))-s.Rational(5,12),
         'heat entropy and Sobolev integrated receiver constant')
    zero(1+2/p-s.Rational(9,5), 'critical initial funding exponent')
    zero(s.Rational(3,2)*s.Rational(5,12)-s.Rational(5,8),
         'physical production prefactor')
    A=(4*s.pi)**(-1)*(s.Rational(5,3))**(-s.Rational(3,2))
    B=(4*s.pi)**(-s.Rational(1,2))*(s.Rational(5,4))**(-2)
    CR,C5,M=s.symbols('C_R C_5 M_0',positive=True)
    Cq=2*CR*s.log(2)*(A+B**2)
    allowance=5*C5*Cq*M**s.Rational(9,5)/(8*nu**2)
    require(allowance.is_positive, 'the critical allowance is positive for nonzero data')
    return {
        'variables':'p=5/2, M0=integral_R5 |b0|^p, B(t)=exp(nu*t*Delta5)b0',
        'cutoff':'any fixed measurable 0<=beta<=1; for the physical history split beta is the original smooth radial core cutoff',
        'parent':'q1(t)=-2 A5 integral_0^t exp(nu*(t-s)*Delta5)[beta B(s)^2] ds, A5=-partial_zz(-Delta5)^-1',
        'riesz_constant':'C_R is the universal L^(5/2) operator norm bound for A5',
        'heat_constants':{'early':str(A),'late':str(B)},
        'Cq':str(Cq),
        'parent_bound':'sup_t ||q1(t)||_(5/2) <= (Cq/nu) M0^(4/5)',
        'receiver_bound':'integral_0^infinity ||B(t)||_(25/6)^(5/2) dt <= (5 C5/(12nu)) M0',
        'prepared_allowance':'(3/2) integral_0^infinity integral |q1| |B|^(5/2) <= (5 C5 Cq/(8nu^2)) M0^(9/5)',
        'scope':'the two heat time ranges remove both endpoint singularities; this is a complete time interval, not a Taylor window',
    }


def physical_split():
    q1,qr,F,F0=s.symbols('q1 qr F F0',real=True)
    zero((q1+qr)*F-(q1*F0+q1*(F-F0)+qr*F),
         'complete source/receiver splitting keeps both defects')
    C5,Cq,nu,M=s.symbols('C5 Cq nu M0',positive=True)
    coefficient=s.Rational(3,2)*s.Rational(25,16)*C5*Cq/nu
    threshold=2*nu**2/(5*C5*Cq)
    zero(coefficient*threshold-s.Rational(15,16)*nu,
         'a small initial caloric parent can instead be absorbed with the ACTUAL receiver')
    return {
        'actual_core_equation':'(partial_t+v.grad-nu*Delta5)eta_core=partial_z(beta b^2), eta_core(0)=0',
        'remainder_parent':'qR=2partial_z(-Delta5)^-1 integral_0^t heat(t-s)[partial_z(beta*(b^2-B^2))-v.grad eta_core] ds',
        'exact_identity':'Pcrit_core = <q1,|B|^p> + <q1,|b|^p-|B|^p> + <qR,|b|^p>',
        'remaining_target':'integral_0^T w[(3/2)(receiver_mismatch+remainder_work)-(15nu/8)Dcrit] <= K_rem(u0,nu,H,rho)',
        'consequence':'the original core budget holds with K=K_cal+K_rem, where K_cal=(5 C5 Cq/(8nu^2))*M0^(9/5)',
        'small_caloric_parent':'if M0^(4/5)<=2nu^2/(5C5Cq), then (3/2)|<q1,|b|^p>| <=(15nu/16)Dcrit; the qR history is still unpaid',
        'retained':'full actual meridional transport, pressure reconstruction, source deformation, receiver deformation, original cutoff, and one original integrating factor',
        'not_claimed':'the actual evolution is heat flow; transport is controlled; this is a global regularity proof; or auxiliary controls are physical forces',
    }


if __name__=='__main__':
    print(json.dumps({'critical_allowance':critical_bound(),
                      'actual_history_split':physical_split()},indent=2))
