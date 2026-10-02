#!/usr/bin/env python3
"""Physical source references for the actual axis deformation receiver.

Exact differential identities and an actual unforced initial-jet test.
The Gaussian heat evolution is a calibration, not an NS trajectory.
The moment lift, comparison and short-time implication remain analytic.
"""

import json
import sympy as s
from rotational_curl_reserve import zero


def identities():
    t, r, nu = s.symbols('t r nu', positive=True)
    z = s.symbols('z', real=True)
    b, q, U, lateral = [s.Function(n)(t,z) for n in ('b','q','U','lateral')]
    # b is the actual axis swirl amplitude. Lateral = nu*Delta_R4 b|axis.
    bt = nu*s.diff(b,z,2)-U*s.diff(b,z)+q*b+lateral
    axis_operator = lambda h: nu*s.diff(h,z,2)-U*s.diff(h,z)+3*q*h
    h=b**3
    defect=3*b*b*lateral-6*nu*b*s.diff(b,z)**2
    zero(3*b*b*bt-axis_operator(h)-defect,
         'physical cube and fourth-moment density have the same axial strain coefficient')
    full=s.Function('full_b')(r,z)
    lap5=lambda f:s.diff(f,r,2)+3*s.diff(f,r)/r+s.diff(f,z,2)
    zero(lap5(full**3)-3*full**2*lap5(full)
         -6*full*(s.diff(full,r)**2+s.diff(full,z)**2),
         'the complete third-moment lift retains both diffusion covariance terms')
    # Full-strain receiver m_t=nu*m_zz-(U*m)_z+4q*m, U_z=q.
    m, href, e = [s.Function(n)(t,z) for n in ('m','href','e')]
    ratio=m/href
    ratio_t=(axis_operator(m)*href-m*(axis_operator(href)+e*href))/href**2
    ratio_rhs=nu*s.diff(ratio,z,2)+(2*nu*s.diff(href,z)/href-U)*s.diff(ratio,z)-e*ratio
    zero(ratio_t-ratio_rhs,'exact ratio equation, including the reference defect')
    return {
        'actual_axis':'b_t+U*b_z=nu*b_zz+q*b+L, U_z=q=-2*u_r/r|axis, L=nu*Delta_R4 b|axis',
        'receiver':'m_t=nu*m_zz-(U*m)_z+4q*m = nu*m_zz-U*m_z+3q*m',
        'cube_defect':'(b^3)_t-[nu*(b^3)_zz-U*(b^3)_z+3q*b^3] = 3*b^2*L-6nu*b*b_z^2',
        'relative_defect_positive_b':'e=3L/b-6nu*(b_z/b)^2',
        'ratio_equation':'(m/h)_t=nu*(m/h)_zz+(2nu*(log h)_z-U)*(m/h)_z-e*(m/h)',
        'full_moment_lift':'H_t+v.grad H=nu*Delta5 H+3q*H, H(0)=b0^3',
        'covariance':'(H-b^3)_t+v.grad(H-b^3)=nu*Delta5(H-b^3)+3q*(H-b^3)+6nu*b*|grad b|^2',
        'axis_lift_defect':'H_axis_t-[nu*H_axis_zz-U*H_axis_z+3q*H_axis]=nu*Delta_R4 H|axis',
        'scope':'full strain q is used. A source cube is neither a supersolution nor a bound on the receiver; the moment lift and its lateral trace also need control'}


def actual_initial_test():
    r,nu=s.symbols('r nu',positive=True)
    z=s.symbols('z',real=True)
    b=s.exp(-(r*r+z*z)/2)
    lap5=lambda f:s.diff(f,r,2)+3*s.diff(f,r)/r+s.diff(f,z,2)
    axis=lambda f:s.limit(f,r,0,dir='+')
    bt=nu*lap5(b)  # Actual NS initial b rate: pure swirl has U=q=0.
    h=axis(b**3)
    cube_rate=axis(3*b*b*bt)
    receiver_rate=nu*s.diff(h,z,2)
    lift_rate=axis(nu*lap5(b**3))
    zero(receiver_rate-cube_rate-6*nu*(z*z+2)*h,
         'actual smooth finite-energy pure swirl violates the cube supersolution already at its initial jet')
    zero(lift_rate-cube_rate-6*nu*z*z*h,
         'axis cube discrepancy due to retained stochastic covariance')
    zero(receiver_rate-lift_rate-12*nu*h,
         'separate nonzero transverse diffusion defect of the full moment lift')
    norm=s.sqrt(3/(2*s.pi))
    zero(s.integrate(norm*h,(z,-s.oo,s.oo))-1,'initial receiver normalization')
    rates=[s.integrate(norm*f,(z,-s.oo,s.oo)) for f in (receiver_rate,cube_rate,lift_rate)]
    for rate,target,name in zip(rates,(0,-14*nu,-12*nu),('receiver','cube','lift')):
        zero(rate-target,'initial integrated rate '+name)
    return {'actual_datum':'u0=(-x2*b0,x1*b0,0), b0=exp(-(r^2+z^2)/2); smooth Schwartz finite-energy divergence-free',
            'hypotheses':'any fixed nu>0, actual local unforced NS evolution, initial meridional velocity zero',
            'pointwise_gap_rate':'[m-sqrt(3/(2pi))*b_axis^3]_t(0,z)=sqrt(3/(2pi))*6nu*(z^2+2)*exp(-3z^2/2)>0',
            'normalized_initial_mass_rates':[str(v) for v in rates],
            'scope':'the proposed zero-defect comparison fails on a short actual interval; neither receiver moment blowup nor failure of a finite correction is implied'}


def heat_calibration():
    t,r,nu=s.symbols('t r nu',positive=True)
    z=s.symbols('z',real=True)
    lap5=lambda f:s.diff(f,r,2)+3*s.diff(f,r)/r+s.diff(f,z,2)
    k1=1+2*nu*t; k3=1+6*nu*t
    b=k1**s.Rational(-5,2)*s.exp(-(r*r+z*z)/(2*k1))
    H=k3**s.Rational(-5,2)*s.exp(-3*(r*r+z*z)/(2*k3))
    zero(s.diff(b,t)-nu*lap5(b),'literal five-dimensional heat reference for b0')
    zero(s.diff(H,t)-nu*lap5(H),'literal five-dimensional heat reference for b0^3')
    norm=s.sqrt(3/(2*s.pi))
    m=norm*k3**s.Rational(-1,2)*s.exp(-3*z*z/(2*k3))
    zero(s.diff(m,t)-nu*s.diff(m,z,2),'literal one-dimensional heat receiver')
    zero(m-norm*k3**2*H.subs(r,0),'complete covariance and transverse dilution correction')
    zero(s.diff(s.log(k3**2),t)-12*nu/k3,'finite logarithmic transverse correction rate')
    zero(m.subs(t,0)-norm*s.exp(-3*z*z/2),'matching initial receiver')
    return {'identity':'m_heat(t,z)=sqrt(3/(2pi))*(1+6nu*t)^2*H_heat(t,0,z)',
            'transverse_factor':'(1+6nu*t)^2; logarithmic rate 12nu/(1+6nu*t)',
            'moment_correction':'H_heat=heat5(b0^3), not [heat5(b0)]^3',
            'scope':'an exact diffusion calibration only; the Gaussian swirl is not asserted to follow this heat evolution under full NS'}


if __name__=='__main__':
    print(json.dumps({'identities':identities(),'actual_initial_test':actual_initial_test(),
                      'heat_calibration':heat_calibration()},indent=2))
