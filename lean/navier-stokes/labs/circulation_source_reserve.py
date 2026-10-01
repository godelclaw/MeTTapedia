#!/usr/bin/env python3
"""Circulation pays repeated source production away from a fixed axis tube.

Exact differential, Fourier-symbol and Gaussian checks. Spatial/time
integration and the pressure-response norm estimates are analytic.
No bound for the complete signed stretching or near-axis renewal is asserted.
"""

import json
import sympy as s
from rotational_curl_reserve import zero, require
from rotational_joint_enstrophy import (
    r, z, grad, lap5, velocity, gaussian_coefficient,
)


def div3(v):
    return s.diff(r*v[0], r)/r+s.diff(v[1], z)


def lap3(f):
    return s.diff(f, r, 2)+s.diff(f, r)/r+s.diff(f, z, 2)


def entropy_identities():
    nu = s.symbols('nu', positive=True)
    chi, b, Gamma, w = [s.Function(n)(r,z) for n in ('chi','b','Gamma','w')]
    v = velocity(chi)
    a = v[0]/r
    zero(div3(v), 'actual meridional velocity is physically divergence free')
    b_rate = nu*lap5(b)-v.dot(grad(b))-2*a*b
    Gamma_rate = nu*(lap3(Gamma)-2*s.diff(Gamma,r)/r)-v.dot(grad(Gamma))
    zero(r*r*b_rate-Gamma_rate.subs(Gamma,r*r*b).doit(),
         'same circulation equation follows from actual coupled swirl')
    h = Gamma**4
    flux = v*h-nu*grad(h)+s.Matrix([2*nu*h/r,0])
    diss = Gamma**2*grad(Gamma).dot(grad(Gamma))
    zero(4*Gamma**3*Gamma_rate+div3(flux)+12*nu*diss,
         'quartic circulation balance includes the radial boundary flux')
    weighted_flux = w*flux+nu*h*grad(w)
    defect = v.dot(grad(w))+nu*lap5(w)
    zero(4*w*Gamma**3*Gamma_rate+div3(weighted_flux)+12*nu*w*diss-h*defect,
         'complete static spatial-weight defect')
    beta = s.symbols('beta', real=True)
    power = r**(-beta)
    zero(v.dot(grad(power))+nu*lap5(power)
         -power*(-beta*a+nu*beta*(beta-2)/r**2),
         'radial weight restores signed compression and diffusion potential')
    b_flux = v*b**4-nu*grad(b**4)
    div5 = lambda f: s.diff(r**3*f[0],r)/r**3+s.diff(f[1],z)
    zero(4*b**3*b_rate+div5(b_flux)+6*a*b**4
         +12*nu*b*b*grad(b).dot(grad(b)),
         'full source-scale quartic balance under mutual amplification')
    source = s.diff(b*b,z)
    zero(12*nu*b*b*grad(b).dot(grad(b))-3*nu*source**2
         -12*nu*b*b*s.diff(b,r)**2,
         'axial source squared is paid exactly by quartic diffusion')
    zero((4*Gamma**2*s.diff(Gamma,z)**2/r**6).subs(Gamma,r*r*b).doit()
         -r*r*source**2, 'physical source cost has the exact inverse sixth radial weight')
    return {'circulation':'Gamma=r*u_theta=r^2*b',
            'quartic_balance':'C4_prime=-12*nu*D_Gamma',
            'source_scale_balance':'B_prime+3*nu*||S||_5^2+12*nu*<b^2*b_r^2>_5=-6*<a*b^4>_5',
            'radial_weight_defect':'r^(-beta)*[-beta*a+nu*beta*(beta-2)/r^2]',
            'scope':'exact physical differential identities; integration requires stated moments and boundary limits'}


def source_and_response():
    E, D, nu, rho = s.symbols('E D nu rho', positive=True)
    rho_prime = s.symbols('rho_prime', real=True)
    reserve = E/(3*nu*rho**6)
    rate = s.diff(reserve,E)*(-12*nu*D)+s.diff(reserve,rho)*rho_prime
    zero(rate+4*D/rho**6+6*rho_prime*reserve/rho,
         'moving tube retains its exact radius cost')
    k = s.symbols('k0:5', real=True)
    k2 = sum(x*x for x in k)
    zero(sum((x*y)**2 for x in k for y in k)-k2*k2,
         'full five-dimensional Hessian of inverse Laplacian has unit L2 multiplier')
    horizontal, axial = sum(x*x for x in k[:4]), k[4]**2
    zero(k2*k2-4*horizontal*axial-(horizontal-axial)**2,
         'horizontal inverse-gradient of a z source has L2 operator norm at most one half')
    return {'fixed_tube':'R_rho=C4/(3*nu*rho^6); R_rho_prime+||S_rho||_5^2<=0',
            'global_weighted':'R=C4/(3*nu); R_prime+<r^6*S^2>_5<=0',
            'response':'||Hess_5*(-L5)^-1*S_rho||_5^2=||S_rho||_5^2',
            'current_forecast':'||J_rho/r^3||_5^2<=C4(0)/(4*rho^6)',
            'moving_tube':'R_prime+||S_rho||_5^2<=-6*(rho_prime/rho)*R',
            'scope':'source cutoff is radial, between zero and one, and zero for r<rho; Fourier-to-norm and interval arguments analytic'}


def compression_potential():
    nu = s.symbols('nu', positive=True)
    chi, b, W, Wt, psi, psit = [s.Function(n)(r,z)
                               for n in ('chi','b','W','Wt','psi','psit')]
    v = velocity(chi)
    a = v[0]/r
    b_rate = nu*lap5(b)-v.dot(grad(b))-2*a*b
    h, diss = b**4, b*b*grad(b).dot(grad(b))
    flux = W*(v*h-nu*grad(h))+nu*h*grad(W)
    div5 = lambda f: s.diff(r**3*f[0],r)/r**3+s.diff(f[1],z)
    defect = Wt+v.dot(grad(W))+nu*lap5(W)-6*a*W
    zero(Wt*h+4*W*b**3*b_rate+div5(flux)-h*defect+12*nu*W*diss,
         'actual weighted quartic evolution identifies the compression potential')
    log_defect = psit+v.dot(grad(psi))+nu*lap5(psi)+nu*grad(psi).dot(grad(psi))-6*a
    zero(defect.subs({W:s.exp(psi),Wt:s.exp(psi)*psit}).doit()-s.exp(psi)*log_defect,
         'exact logarithmic HJB form of the physical weight inequality')
    p, q = s.Matrix(s.symbols('p0:5', real=True)), s.Matrix(s.symbols('q0:5', real=True))
    zero(nu*p.dot(p)-(q.dot(p)-q.dot(q)/(4*nu))-(q-2*nu*p).dot(q-2*nu*p)/(4*nu),
         'auxiliary drift Hamiltonian with its full quadratic sampling cost')
    return {'weight_condition':'W>=1 and W_t+v.grad(W)+nu*L5(W)-6*a*W<=0',
            'source_payment':'R=<W*b^4>_5/(3*nu); R_prime+||S||_5^2<=0',
            'log_condition':'psi>=0 and psi_t+v.grad(psi)+nu*L5(psi)+nu*|grad(psi)|^2-6*a<=0',
            'sampling_drift':'v+q; the physical v and a stay fixed',
            'missing_bound':'an initial-datum bound for <W(0)*b(0)^4>_5 uniform over all smooth prefixes',
            'scope':'conditional physical source criterion, not construction of a globally funded weight or control of full stretching'}


def gaussian_test():
    b = s.exp(-r*r-2*z*z)
    chi = z*(1-3*r*r+4*z*z)*b/2
    Gamma = r*r*b
    source = s.diff(b*b,z)
    nu = s.Rational(1,1000)
    B = gaussian_coefficient(b**4,4)
    Db = gaussian_coefficient(b*b*grad(b).dot(grad(b)),4)
    C4 = gaussian_coefficient(Gamma**4,4,1)
    Dg = gaussian_coefficient(Gamma**2*grad(Gamma).dot(grad(Gamma)),4,1)
    S2 = gaussian_coefficient(source**2,4)
    for value, expected, label in [(B,s.Rational(1,32),'B'),(Db,s.Rational(3,32),'D_b'),
                                  (C4,s.Rational(3,256),'C4'),(Dg,s.Rational(3,128),'D_Gamma'),
                                  (S2,s.Rational(1,8),'source norm')]:
        zero(value-expected, 'exact Gaussian '+label)
    zero(gaussian_coefficient(4*Gamma**3*(lap3(Gamma)-2*s.diff(Gamma,r)/r),4,1)
         +12*Dg, 'literal physical viscous circulation rate')
    zero(gaussian_coefficient(r**6*source**2,4)
         -4*gaussian_coefficient(Gamma**2*s.diff(Gamma,z)**2,4,1),
         'same weighted source cost in the physical and lifted measures')
    rates = []
    for phase in (1,-1):
        v = velocity(phase*chi)
        a = v[0]/r
        Nb = -v.dot(grad(b))-2*a*b
        A = gaussian_coefficient(a*b**4,5)
        zero(A+phase*s.Rational(2,625), 'signed compression on the earlier phase pair')
        zero(gaussian_coefficient(4*b**3*Nb,5)+6*A, 'literal nonlinear quartic rate')
        zero(gaussian_coefficient(4*b**3*lap5(b),4)+12*Db, 'literal viscous quartic rate')
        zero(gaussian_coefficient(-4*Gamma**3*v.dot(grad(Gamma)),5,1),
             'no hidden circulation production by the interacting parents')
        # K_j=2*pi*sqrt(pi/(2*j)), so K5/K4=sqrt(4/5).
        B_rate = -12*nu*Db-6*A*s.sqrt(s.Rational(4,5))
        require(phase*B_rate>0, 'source-scale stock grows in one actual viscous phase and falls in the other')
        rates.append({'phase':phase,'B_prime_over_K4':str(B_rate),'C4_prime_over_K4':str(-12*nu*Dg)})
    zero(S2/Dg-s.Rational(16,3), 'concentrated source-to-circulation-dissipation ratio')
    return {'B_over_K4':str(B),'C4_over_K4':str(C4),'source_square_over_K4':str(S2),
            'positive_viscosity':str(nu),'phases':rates,
            'concentration_ratio':'||S_lambda||_5^2/D_Gamma_lambda=(16/3)*lambda^6',
            'scope':'smooth Schwartz unforced initial data; continuity gives a short interval, not indefinite renewal'}


def forcing_and_angular_defect():
    theta, nu = s.symbols('theta nu', real=True)
    ur, ut, uz, pressure, ft = [s.Function(n)(r,theta,z) for n in ('ur','ut','uz','p','ft')]
    lap = lambda q: s.diff(q,r,2)+s.diff(q,r)/r+s.diff(q,theta,2)/r**2+s.diff(q,z,2)
    adv = lambda q: ur*s.diff(q,r)+ut*s.diff(q,theta)/r+uz*s.diff(q,z)
    ut_rate = nu*(lap(ut)-ut/r**2+2*s.diff(ur,theta)/r**2)-adv(ut)-ur*ut/r-s.diff(pressure,theta)/r+ft
    Gamma = r*ut
    extra = 2*nu*s.diff(ur,theta)/r-s.diff(pressure,theta)+r*ft
    zero(r*ut_rate+adv(Gamma)-nu*(lap(Gamma)-2*s.diff(Gamma,r)/r)-extra,
         'full three-dimensional circulation equation retains angular pressure, vector diffusion and forcing')
    return {'circulation_extra':'2*nu*partial_theta(u_r)/r-partial_theta(p)+r*f_theta',
            'quartic_extra':'4*integral Gamma^3*circulation_extra dx',
            'meridional_force':'curl(f)_theta/r is a separate eta source, even if f_theta=0',
            'scope':'axisymmetry and zero forcing are actual hypotheses; no claim about all forced constructions'}


def scaling_test():
    lam = s.symbols('lam', positive=True)
    b = s.exp(-r*r-2*z*z)
    at_scaled = lambda f: f.subs({r:lam*r,z:lam*z},simultaneous=True)
    scaled_b = lam**2*at_scaled(b)
    zero(r*r*scaled_b-at_scaled(r*r*b), 'circulation has physical scaling degree zero')
    zero(s.diff(scaled_b**2,z)-lam**5*at_scaled(s.diff(b*b,z)),
         'actual source has physical scaling degree five')
    # Radial/axial variable substitution: r dr dz scales with degree -3,
    # and r^3 dr dz with degree -5.
    circulation_stock_degree = 0-3
    circulation_diss_degree = 2-3
    source_square_degree = 10-5
    weighted_source_degree = source_square_degree-6
    require(weighted_source_degree-2 == circulation_stock_degree,
            'time-integrated weighted cost matches its original resource')
    require(source_square_degree-circulation_diss_degree == 6,
            'unweighted conversion loses exactly six radial powers')
    return {'C4_degree':circulation_stock_degree,'D_Gamma_degree':circulation_diss_degree,
            'source_square_degree':source_square_degree,
            'integrated_weighted_source_degree':weighted_source_degree-2,
            'failed_fixed_coefficient':'C*C4/(3*nu) cannot pay the full source norm for all data: take lambda^6>3*C/4',
            'scope':'one coefficient uniform over concentrated data is refuted; a full-datum coefficient remains possible'}


if __name__ == '__main__':
    print(json.dumps({'identities':entropy_identities(),'source_response':source_and_response(),
                      'compression_potential':compression_potential(),
                      'physical_tests':gaussian_test(),'scope_defects':forcing_and_angular_defect(),
                      'scaling':scaling_test()},indent=2))
