#!/usr/bin/env python3
"""Heat-referenced receiver cost with finite Gaussian startup allowance.

Exact algebra for the actual axis receiver equation. The proposed signed
core cost remains unpaid; the max comparison and stochastic limiting
argument are analytic, not Lean certificates. Affine drift is used only
to calibrate the receiver calculation, not as a finite-energy fluid.
"""

import json
import sympy as s
from rotational_curl_reserve import zero


def check():
    z=s.symbols('z',real=True)
    nu,k,V,eps=s.symbols('nu k V eps',positive=True)
    c,p=s.symbols('c p',real=True)
    ell=s.Function('ell')(z)
    m=s.exp(ell)
    g,h=s.diff(ell,z),s.diff(ell,z,2)
    delta=h+1/k
    # k'=2nu. The exact Fisher identity is checked from the receiver
    # PDE in source_receiver_duality.py; no parent derivative is dropped.
    raw=m*(4*c+2*nu*g*g+k*(-2*nu*h*h-4*c*g*g-2*(3*c-p)*h))
    S=m*(1+k*g*g)
    shifted=(2*nu/k)*(2*m-S)+m*(10*c-4*k*c*g*g-6*k*c*delta
                               -2*p+2*k*p*delta-2*nu*k*delta*delta)
    zero(raw-shifted-4*nu*s.diff(m*g,z),
         'complete growing-length rate and heat reference, retaining the exact flux')
    core=m*(10*c-4*k*c*g*g-6*k*c*delta-nu*k*delta*delta)
    zero(core+m*(-2*p+k*p*p/nu)-(shifted-(2*nu/k)*(2*m-S))
         -nu*k*m*(delta-p/nu)**2,
         'only the paid-parent square is spent; a full diffusion square remains')
    t=s.symbols('t',nonnegative=True)
    width=eps*eps+2*nu*t
    gaussian=s.exp(-z*z/(2*width))/s.sqrt(2*s.pi*width)
    zero(s.diff(gaussian,t)-nu*s.diff(gaussian,z,2),'regularized heat calibration')
    zero(s.diff(s.log(gaussian),z,2)+1/width,'heat curvature defect is exactly zero')
    mass=s.integrate(gaussian,(z,-s.oo,s.oo))
    fisher=s.integrate(gaussian*s.diff(s.log(gaussian),z)**2,(z,-s.oo,s.oo))
    zero(mass-1,'normalized physical receiver mass')
    zero(mass+width*fisher-2,'mass plus growing-length Fisher has constant value two')
    # At t=0 this identity is exact for every positive eps, including
    # arbitrarily narrow normalized Gaussian receivers.
    zero((mass+width*fisher).subs(t,0)-2,'width-independent initial allowance')
    SV=1+k/V
    rate=2*nu*s.diff(SV,k)+(2*p*V+2*nu)*s.diff(SV,V)
    dV=-1/V+1/k
    predicted=(2*nu/k)*(2-SV)-2*p+2*k*p*dV-2*nu*k*dV*dV
    zero(rate-predicted,'both signs of affine parent drift with variance V_prime=2pV+2nu')
    return {
        'actual_equation':'m_t=nu*m_zz-(U*m)_z+4c*m, U_z=c+p, c=q_core, p=q_paid',
        'quantities':'M=integral m, F=integral m*(log m)_z^2, k=eps^2+2nu*t, delta=(log m)_zz+1/k, S=M+kF, B=max(S,2M)',
        'initial':'normalized Gaussian variance eps^2 gives M(0)=1, F(0)=eps^-2, B(0)=2',
        'signed_core':'C_k=integral m*[10c-4kc*(log m)_z^2-6kc*delta-nu*k*delta^2]',
        'remaining_cost':'D_k=max(C_k,8*integral c*m)',
        'paid_parent_clock':'kappa=2||p||_infinity+(k/nu)*||p||_infinity^2',
        'analytic_comparison':'B_prime<=D_k+kappa*B almost everywhere',
        'uniform_clock':'for 0<eps<=eps_max, integral kappa<=K_star=4M_H+(eps_max^2/nu+2H)*P2_H',
        'conditional_allowance':'if integral exp(K_star-integral_0^t kappa)*D_k<=A uniformly in center, eps and available prefix, then E[J_core(T)^4]<=2exp(K_star)+A also in the point-started limit',
        'heat_test':'regularized heat Gaussian: B=2, delta=0, D_k=0',
        'no_core_test':'c=0 implies C_k<=0, D_k=0; actual old-parent transport is paid by the clock',
        'scope':'symbolic rates and Gaussian/affine calibrations only; the signed core bound is open, and an axis moment does not by itself construct the interior compression weight or solve general 3D NS'}


if __name__=='__main__':
    print(json.dumps(check(),indent=2))
