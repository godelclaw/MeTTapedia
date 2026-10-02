#!/usr/bin/env python3
"""Signed generated-parent histories and loss of axial swirl ordering.

Exact local differential identities, Green-kernel derivatives and constants
are checked here. Positivity of the actual drift propagator, continuation,
and the smooth local NS interval argument are analytic. Optional quadrature
checks the initial pressure response, not a subsequent fluid simulation.
"""

import argparse
import json
import sympy as s
from rotational_curl_reserve import require, zero
from rotational_joint_enstrophy import r, z, grad, lap5, velocity


def actual_history_identities():
    chi, b, eta, f, psi, h = [s.Function(n)(r,z)
                            for n in ('chi','b','eta','f','psi','h')]
    nu = s.symbols('nu',positive=True)
    v = velocity(chi)
    q = -2*v[0]/r
    div5 = lambda a: s.diff(a[0],r)+3*a[0]/r+s.diff(a[1],z)
    zero(div5(v)+q, 'full lifted drift divergence')
    eta_t = nu*lap5(eta)-v.dot(grad(eta))+s.diff(f,z)
    psi_t = -nu*lap5(psi)-div5(v*psi)-h
    flux = nu*(psi*grad(eta)-eta*grad(psi))-v*eta*psi
    zero(eta_t*psi+eta*psi_t+eta*h+f*s.diff(psi,z)
         -div5(flux)-s.diff(f*psi,z),
         'complete actual-drift adjoint duality with every transport term')
    b_t = nu*lap5(b)-v.dot(grad(b))+q*b
    n = s.diff(b,z)
    n_t = (nu*lap5(n)-v.dot(grad(n))-r*s.diff(q,r)*n/2
           +s.diff(q,z)*(b+r*s.diff(b,r)/2))
    zero(s.diff(b_t,z)-n_t, 'exact axial-order evolution defect')
    zero(s.diff(v[0],z)+r*s.diff(q,z)/2,
         'radial transport changes under the axial derivative')
    zero(s.diff(v[1],z)-q-r*s.diff(q,r)/2,
         'incompressibility retains the axial stretching term')
    B = s.symbols('B',positive=True)
    zero(s.diff(B**s.Rational(5,2),B)
         -s.Rational(5,4)*s.sqrt(B)*s.diff(B*B,B),
         'source and receiver derivatives have the same instantaneous sign')
    # On the open flat core b0=B(r), v0=0. Its first time derivative is
    # nu Delta5 B, still independent of z. phi denotes chi_t at time zero.
    radial_b = s.Function('B')(r)
    phi = s.Function('phi')(r,z)
    b_tt = (nu**2*lap5(lap5(radial_b))
            -velocity(phi).dot(grad(radial_b))+2*s.diff(phi,z)*radial_b)
    zero(s.diff(b_tt,z)-2*s.diff(phi,z,2)*(radial_b+r*s.diff(radial_b,r)/2),
         'complete initial second axial-slope derivative, including viscosity')
    delta = s.symbols('delta',positive=True)
    axis_b = delta*s.exp(-r*r/2)
    zero(s.limit(axis_b+r*s.diff(axis_b,r)/2,r,0)-delta,
         'regular axis value of the retained axial vorticity factor')
    return {
        'actual_parent':'eta_core_t=nu Delta5 eta_core-v.grad eta_core+partial_z(beta b^2), eta_core(0)=0',
        'adjoint':'-psi_t=nu Delta5 psi+div5(v psi)+h, including div5(v)=-q',
        'duality':'integral eta_core h=-integral beta b^2 psi_z when eta_core(0)=psi(T)=0 and boundary fluxes vanish',
        'axial_order_defect':'n_t+v.grad n-nu Delta5 n=-(r/2)q_r n+q_z(b+(r/2)b_r), n=b_z',
        'receiver_identity':'partial_z |b|^(5/2)=(5/4)|b|^(1/2)*partial_z(b^2)',
        'scope':'actual axisymmetric unforced equations; no prescribed independent parent or frozen receiver'}


def signed_pairing():
    Cpp,Cpm,Cmp,Cmm = s.symbols('Cpp Cpm Cmp Cmm',nonnegative=True)
    pairing = -4*(Cpp-Cpm-Cmp+Cmm)
    zero(pairing-4*(Cpm+Cmp-Cpp-Cmm),
         'all four signed source-receiver histories are retained')
    zero(4*(Cpm+Cmp)-pairing-4*(Cpp+Cmm),
         'only opposite-sign derivative histories enter the upper bound')
    C5,nu,M0,MH = s.symbols('C5 nu M0 MH',positive=True)
    coefficient = s.Rational(25,16)*s.Rational(4,15)
    zero(coefficient-s.Rational(5,12),
         'ordered histories leave the entire critical diffusion available')
    zero(s.Rational(3,2)*2*(s.Rational(7,5)+1)-s.Rational(36,5),
         'paid-parent factor in the ordered-history continuation allowance')
    return {
        'domain':'D=R4 times (0,infinity); b and v_r even in z, v_z and eta odd; beta(r) in [0,1]',
        'operators':'U_v(t,s) is the positive Dirichlet propagator of nu Delta5-v.grad on D; K_D is the positive Dirichlet inverse of -Delta5',
        'sources':'j=partial_z(beta b^2), d=partial_z |b|^(5/2), with positive and negative parts',
        'terms':'C_ab(t)=integral_0^t <d_a(t),K_D U_v(t,s) j_b(s)>_D ds >=0',
        'identity':'Pcrit_core(t)=4(C_plus_minus+C_minus_plus-C_plus_plus-C_minus_minus)',
        'ordered_case':'partial_z b^2<=0 on D throughout the prefix implies eta_core<=0 and Pcrit_core<=0',
        'conditional_clock':str(s.Rational(5,12)*C5/nu*s.exp(s.Rational(36,5)*MH)*M0**s.Rational(12,5)),
        'scope':'ordering is a history hypothesis, not a property proved from initial ordering; arbitrary histories remain open'}


def green_and_order_loss():
    R,w = s.symbols('R w',positive=True)
    G = (R*R+w*w)**(-s.Rational(3,2))
    G2 = 3*(4*w*w-R*R)/(R*R+w*w)**s.Rational(7,2)
    G3 = 15*w*(3*R*R-4*w*w)/(R*R+w*w)**s.Rational(9,2)
    zero(s.diff(G,w,2)-G2, 'axis Green-kernel second derivative')
    zero(s.diff(G2,w)-G3, 'strict kernel monotonicity in the annular construction')
    zero(3*s.Integer(4)**2-4*s.Rational(5,2)**2-23,
         'positive numerator margin for R in [4,5], w in [1/2,5/2]')
    radial = s.symbols('radial',positive=True)
    fundamental = radial**(-3)/(8*s.pi**2)
    zero(-s.diff(fundamental,radial)*(8*s.pi**2/3)*radial**4-1,
         'ordinary five-dimensional inverse-Laplacian normalization')
    zero(2*(2*s.pi**2)/(8*s.pi**2)-s.Rational(1,2),
         'axis radial integral prefactor for sigma_z')
    A = s.symbols('A',positive=True)
    D = s.symbols('D',nonnegative=True)
    delta = A/(2*(A+D))
    zero(A-delta**2*D-s.Rational(15,16)*A
         -A*(A-D)**2/(16*(A+D)**2),
         'a finite weak axis background preserves a strict positive response')
    return {
        'datum':'b0=(a(r)+delta exp(-r^2/2))*h(z); u0=(-x2 b0,x1 b0,0)',
        'radial_profile':'a>=0 smooth, nonzero, supported in 4<r<5',
        'axial_profile':'h even smooth, equals 1 for |z|<=1, equals 0 for |z|>=2, h_prime<0 on (1,2)',
        'evaluation':'r=0,z=1/2, sigma=q_t(0)=2 partial_zz K5(b0^2)',
        'response_formula':'sigma_z=(1/2)integral r^3 B(r)^2 integral_1^2 (h^2)_prime(s)[G2(r,s-1/2)-G2(r,s+1/2)] ds dr',
        'strict_sign':'the bracket is negative on the annular support, so the annulus and its Gaussian cross term give strictly positive sigma_z',
        'finite_delta':'A=sigma_z[a^2 h^2]>0, D=abs(sigma_z[exp(-r^2)h^2]); delta=A/(2(A+D)); sigma_z[full datum]>=15A/16>0',
        'actual_jet':'b_z(0)=partial_t b_z(0)=0; partial_tt b_z(0,0,1/2)=delta*sigma_z>0',
        'viscosity':'valid at every fixed nu>0; local axial flatness makes the viscous initial jet terms zero',
        'net_work':'for the full generated parent, Pcrit_prime(0)=-4<partial_z F0,K_D partial_z b0^2>_D<0; Pcrit(t)<0 and M decreases on a short interval despite loss of ordering',
        'refuted':'propagation of initial axial monotonicity for arbitrary smooth axisymmetric pure-swirl data',
        'not_refuted':'the conditional history sign theorem, a quantitative defect allowance, or regularity'}


def quadrature():
    import numpy as np
    from scipy.special import expit
    rows = []
    for order in (64,96,128):
        nodes,weights = np.polynomial.legendre.leggauss(order)
        axial = (nodes+3)/2
        aw = weights/2
        h = expit(1/(axial-1)-1/(2-axial))
        hp = -h*(1-h)*(1/(axial-1)**2+1/(2-axial)**2)
        source = 2*h*hp
        def response(kind):
            left,right = (0.,12.) if kind=='background' else (4.,5.)
            radial = left+(nodes+1)*(right-left)/2
            rw = weights*(right-left)/2
            ann = np.exp(4-1/((radial-4)*(5-radial))) if kind!='background' else np.zeros_like(radial)
            gaussian = np.exp(-radial**2/2)
            factor = {'annulus':ann**2,'cross':ann*gaussian,'background':gaussian**2}[kind]
            rr = radial[:,None]
            def g2(w):
                return 3*(4*w*w-rr*rr)/(rr*rr+w*w)**3.5
            kernel = g2(axial[None,:]-.5)-g2(axial[None,:]+.5)
            return float(.5*np.sum(rw*radial**3*factor*(kernel@(aw*source))))
        A,X,G = (response(k) for k in ('annulus','cross','background'))
        delta = A/(2*(A+abs(G)))
        full = A+2*delta*X+delta**2*G
        require(A>0 and X>0 and full>0, 'quadrature supports the proved kernel sign')
        rows.append({'order':order,'annular_sigma_z':A,'cross_sigma_z':X,
                     'background_sigma_z':G,'delta':delta,'full_sigma_z':full,
                     'actual_b_z_second_derivative':delta*full})
    return {'rows':rows,'scope':'floating-point initial pressure check; no certified quadrature error and no PDE time integration'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--quadrature',action='store_true')
    args = parser.parse_args()
    result = {'actual_history':actual_history_identities(),
              'signed_pairing':signed_pairing(),
              'order_loss':green_and_order_loss()}
    if args.quadrature:
        result['quadrature'] = quadrature()
    print(json.dumps(result,indent=2))
