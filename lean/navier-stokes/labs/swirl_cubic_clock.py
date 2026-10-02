#!/usr/bin/env python3
"""A critical cubic-source clock, its full reserve, and viscous rebound.

Checks exact algebra, radial moments, localization constants and scaling.
Sobolev interpolation, local NS evolution, localization and continuation
remain analytic. No arbitrary-history budget is asserted.
"""

import argparse
import json
import math
import sympy as s
from rotational_curl_reserve import require, zero
from rotational_joint_enstrophy import r, z, grad, lap5, velocity


def moment(poly, y, rate):
    return s.factor(sum(c*s.factorial(n)/rate**(n+1)
                        for (n,), c in s.Poly(s.expand(poly), y).terms())/2)


def ceil_root(value):
    n = math.isqrt(int(s.ceiling(value)))
    return n if n*n >= value else n+1


def stock_and_consumer():
    b, chi = s.Function('b')(r,z), s.Function('chi')(r,z)
    v = velocity(chi)
    q = -2*v[0]/r
    nu = s.symbols('nu', positive=True)
    div5 = lambda x: s.diff(x[0],r)+3*x[0]/r+s.diff(x[1],z)
    bt = nu*lap5(b)-v.dot(grad(b))+q*b
    zero(3*b*b*bt-nu*lap5(b**3)+div5(v*b**3)
         -2*q*b**3+6*nu*b*grad(b).dot(grad(b)),
         'full stock balance on the positive branch; C2 absolute cube gives the signed case')
    a, G = s.symbols('a G', nonnegative=True)
    zero(G*r*r*a**3-(r*a)**4-r*r*a**3*(G-r*r*a),
         'circulation converts lifted cubic stock to the physical swirl fourth power')
    zero(G*a*a-r*r*a**3-a*a*(G-r*r*a),
         'angular physical gradient energy pays the first power of the stock')
    zero(2*s.pi**2*r**3*a**3-s.pi*(r*r*a**3)*2*s.pi*r,
         'exact R5 versus physical R3 measure conversion')
    # The angular column of the actual cylindrical velocity gradient is
    # (-b,u_r/r,0), so its square contains b^2 with coefficient one.
    zero(s.Matrix([-b,v[0]/r,0]).dot(s.Matrix([-b,v[0]/r,0]))
         -b*b-(v[0]/r)**2, 'physical angular gradient pays b^2')
    zero(s.Rational(2,8)+s.Rational(3,4)-1, 'swirl Serrin exponents')
    return {'actual_stock':'S=integral_R5 |b|^3, b=u_theta/r; not the larger passive envelope',
            'stock_rate':'S_prime=2P-6nu D, P=integral_R5 q|b|^3, D=integral_R5 |b||grad b|^2',
            'swirl_bound':'||u_theta||_L4(R3)^4 <= G0*S/pi',
            'critical_consumer':'integral_0^T ||u_theta||_4^8 <= (G0/pi)^2 integral_0^T S^2',
            'already_paid':'integral_0^T S <= pi*G0*E0/(2nu)',
            'external_continuation':'Peng Wang, EJDE 2015/250, Theorem 1.1, exponents (8,4); analytic, not imported as a Lean theorem'}


def critical_reserve():
    E,S,D,d,nu = s.symbols('E S D d nu', positive=True)
    P = s.symbols('P', real=True)
    R = (E*S)**s.Rational(6,5)
    rate = s.diff(R,E)*(-2*nu*d)+s.diff(R,S)*(2*P-6*nu*D)
    parent = s.Rational(12,5)*E**s.Rational(6,5)*S**s.Rational(1,5)*P
    kinetic = s.Rational(12,5)*nu*E**s.Rational(1,5)*S**s.Rational(6,5)*d
    diffusion = s.Rational(36,5)*nu*E**s.Rational(6,5)*S**s.Rational(1,5)*D
    zero(rate-parent+kinetic+diffusion, 'full joint kinetic-cubic reserve derivative')
    zero(s.Rational(1,3)-s.Rational(4,9)/2-s.Rational(5,9)/5,
         'L3 interpolation between L2 and L5 in five dimensions')
    zero((s.Rational(2,3)*s.Rational(9,5))-s.Rational(6,5),
         'interpolation converts S^(9/5) to E^(6/5) D')
    lam = s.symbols('lambda', positive=True)
    zero((lam**(-1)*lam)**s.Rational(6,5)-1, 'joint reserve is invariant under NS spatial scaling')
    zero(lam**2*lam**(-2)-1, 'integrated S squared has the same critical scaling')
    C5 = s.symbols('C5', positive=True)
    c = s.Rational(9,4)*C5*s.pi**s.Rational(6,5)
    clock = s.factor(s.Rational(18,5)/c)
    return {'reserve':'R=(E*S)^(6/5), E=||u||_L2(R3)^2',
            'Sobolev_convention':'||f||_L(10/3)(R5)^2 <= C5*||grad f||_2^2',
            'interpolation':'S^(9/5) <= (9/4)*C5*(pi E)^(6/5)*D',
            'defect':'Q=(12/5)*E^(6/5)*S^(1/5)*P-(12nu/5)*E^(1/5)*S^(6/5)*d-(18nu/5)*E^(6/5)*S^(1/5)*D',
            'exact_ledger':'R_prime+(18nu/5)*E^(6/5)*S^(1/5)*D=Q',
            'critical_clock_coefficient':str(clock)+' * nu',
            'sufficient_payment':'integral_0^T Q <= K(u0,nu,H) uniformly over available prefixes implies a finite critical clock and axisymmetric continuation',
            'open':'no arbitrary-data upper allowance for the signed Q history is established'}


def positive_return():
    y, a = s.symbols('y a', nonnegative=True)
    p = -48+(32+a)*y-4*y*y
    Q = (p-20)**2+21
    qr = r**6*s.exp(-r*r)
    h = r**4*s.exp(-r*r)*p.subs(y,r*r)
    zero(a*qr-s.diff(qr,r,2)-3*s.diff(qr,r)/r-h,
         'exact inverse on each nonzero axial mode')
    p0 = s.symbols('p', real=True)
    Q0 = (p0-20)**2+21
    zero(Q0-p0-((p0-s.Rational(41,2))**2+s.Rational(3,4)), 'Q>|p| positive branch')
    zero(Q0+p0-((p0-s.Rational(39,2))**2+s.Rational(163,4)), 'Q>|p| negative branch')
    J = moment(y**7*Q*p,y,s.Rational(5,2))
    bern = [-s.Rational(n,244140625) for n in
            (443468906496,378671333376,331214585856,282519207936)]
    zero(J-sum(bern[k]*s.binomial(3,k)*a**k*(1-a)**(3-k) for k in range(4)),
         'negative return moment for every squared axial frequency in [0,1]')
    require(all(x<0 for x in bern), 'negative Bernstein coefficients')
    base = moment(y**7,y,s.Rational(5,2))
    Z = s.symbols('Z', real=True)
    chi = s.exp(-Z*Z)
    zero(chi**s.Rational(3,2)*chi-s.exp(-s.Rational(5,2)*Z*Z),
         'localized stock-strain pairing retains both Gaussian factors')
    margin = s.factor(-3*J.subs(a,1)/2-base/4)
    zero(margin-s.Rational(423678011904,244140625), 'positive exact Taylor margin')
    require(margin>0, 'cubic stock has positive internally generated feedback')
    x = s.symbols('x', real=True)
    zero(s.diff((1+x)**s.Rational(3,2),x,3)+s.Rational(3,8)/(1+x)**s.Rational(3,2),
         'third derivative controls the complete fractional-power remainder')
    require(s.Rational(21,20)**3<4, 'Taylor error factor (21/20)^(3/2) is below two')
    # Literal finite-energy localization at beta=1. Bounds use only exact
    # moments and upward-rounded square roots; no quadrature is a certificate.
    p = p.subs(a,1); Q = Q.subs(a,1)
    nF = moment(y**7*Q**6,y,s.Integer(3))
    nR = moment(y**6*Q**4,y,s.Integer(2))
    nH = moment(y**5*p**2,y,s.Integer(2))
    supj = moment(y**7*Q**3,y,s.Rational(5,2))
    roots = [ceil_root(v) for v in (nF,nR,nH)]
    require(all(s.Integer(n)**2>=v for n,v in zip(roots,(nF,nR,nH))),
            'all radial norms rounded upward')
    Cmult = 12*roots[0]*(s.Rational(roots[1],2)+roots[2])
    Cavg = 192*supj
    length = 1
    while (Cmult+Cavg)/length >= margin/2:
        length *= 2
    require((Cmult+Cavg)/length<margin/2, 'explicit localized positive-return certificate')
    return {'radial_profile':'p=-48+(32+a)y-4y^2, Q=(p-20)^2+21, F=r^4 exp(-r^2) Q^2, h=r^4 exp(-r^2) p',
            'source':'f_L=exp(-z^2/L^2)*(F+h*cos(beta*z)), b0=sqrt(f_L), a=beta^2',
            'physical_velocity':'u0=(-x2*b0,x1*b0,0), smooth Schwartz pure swirl',
            'ratio_bound':'|h|/F<=1/21',
            'radial_J':str(J), 'Bernstein_coefficients':list(map(str,bern)),
            'positive_average_margin_at_beta_one':str(margin),
            'localization_norm_roots':roots, 'multiplier_error_constant':str(Cmult),
            'averaging_error_constant':str(Cavg), 'explicit_length_at_beta_one':length,
            'localized_lower_bound':'I_L/(2pi^2 L)>=margin/2>0, I_L=integral_R5 b0^3*sigma_L',
            'actual_initial_rate':'q(0)=0, q_t(0)=sigma_L=2 partial_zz (-Delta5)^-1 b0^2, P_prime(0)=I_L',
            'scope':'positive signed replenishment; diffusion is included separately in the rebound calculation'}


def viscous_rebound():
    E,S,D,d,I,eps = s.symbols('E S D d I epsilon', positive=True)
    k = s.symbols('k', positive=True)
    E_t = E-2*k*eps**2*d
    S_t = S+eps**2*(I*k*k-6*D*k)
    coefficient = s.expand(E_t*S_t).coeff(eps,2)
    loss = 6*E*D+2*d*S
    zero(coefficient-(E*I*k*k-loss*k), 'complete kinetic-cubic product change')
    zero(coefficient.subs(k,2*loss/(E*I))-2*loss**2/(E*I),
         'strictly positive second-order change after both physical viscous losses')
    return {'amplitude_family':'u_A(t,x)=A*v_epsilon(A*t,x), epsilon=nu/A, v_epsilon(0)=fixed localized pure swirl',
            'uniform_short_time_expansion':'at tau=k epsilon, E=E0-2k epsilon^2 d0+O(epsilon^3); S=S0+epsilon^2(I k^2-6D0 k)+O(epsilon^3)',
            'choice':'k=2*(6E0 D0+2d0 S0)/(E0 I)',
            'positive_product_coefficient':'2*(6E0 D0+2d0 S0)^2/(E0 I)>0',
            'actual_interval':'t=k nu/A^2, for all sufficiently large A at every fixed nu>0',
            'conclusion':'(E(t) S(t))^(6/5) exceeds its initial value; the complete viscous joint reserve is not monotone even from pure swirl',
            'not_refuted':'a finite allowance depending on the full original datum or global regularity',
            'analytic_obligation':'uniform local Sobolev estimates for viscosities epsilon in [0,1] justify the remainder; not a symbolic proof of PDE existence'}


def average_quadrature():
    """Independent radial/phase integration; not an error certificate."""
    import numpy as np
    from scipy.special import roots_genlaguerre
    c = np.cos(2*np.pi*(np.arange(256)+.5)/256)
    rows = []
    for beta in (1., .5, .25):
        for order in (32,64,128):
            x,w = roots_genlaguerre(order,7)
            y = x/2.5
            p = -48+(32+beta*beta)*y-4*y*y
            Q = (p-20)**2+21
            delta = (p/Q**2)[:,None]*c[None,:]
            # Pair opposite phases and use expm1 to retain small differences.
            odd = (np.expm1(1.5*np.log1p(delta))
                   - np.expm1(1.5*np.log1p(-delta)))/2
            phase = np.mean(c[None,:]*odd,axis=1)
            value = -beta*beta*np.dot(w,Q**3*phase)/2.5**8
            require(np.isfinite(value) and value>0, 'positive numerical phase average')
            rows.append({'beta':beta,'radial_order':order,
                         'radial_phase_average':float(value)})
    return rows


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quadrature',action='store_true')
    args = parser.parse_args()
    result = {'consumer':stock_and_consumer(), 'reserve':critical_reserve(),
              'positive_return':positive_return(), 'viscous_rebound':viscous_rebound()}
    if args.quadrature:
        result['numerical_phase_averages'] = average_quadrature()
    print(json.dumps(result,indent=2))
