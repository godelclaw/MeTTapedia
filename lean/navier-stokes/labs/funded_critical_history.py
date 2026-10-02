#!/usr/bin/env python3
"""Scaling and bookkeeping for a funded critical-history obstruction.

The base positive burst is supplied by critical_parent_exchange.py.
Translation separation, actual NS stability, and limiting PDE arguments
are analytic in README.md; this checker does not certify those arguments.
"""

import json
import sympy as s
from rotational_curl_reserve import require, zero


def scalings():
    lam = s.symbols('lambda', positive=True)
    p = s.Rational(5, 2)
    zero(lam**(2*p-5)-1, 'critical moment is invariant under NS scaling')
    zero(lam**(1+6-5-2)-1,
         'time-integrated critical diffusion is invariant under NS scaling')
    zero(lam**(2+2*p-5-2)-1,
         'time-integrated signed critical production is invariant')
    zero(lam**(2-3)-1/lam, 'physical kinetic energy scaling')
    zero(lam**(2-5)-lam**(-3), 'lifted source mass scaling')
    return {
        'NS_scaling': 'u_lambda(t,x)=lambda u(lambda^2 t,lambda x); viscosity unchanged',
        'critical': 'M=int_R5 |b|^(5/2), int Dcrit dt, and int Pcrit dt are invariant',
        'kinetic': 'E_lambda=lambda^-1 E',
        'circulation': 'Gamma_lambda(x)=Gamma(lambda x); int_R3 |Gamma_lambda|^p=lambda^-3 C_p for every finite p>0',
        'source_mass': 'M1_lambda=lambda^-3 M1',
        'max_circulation': 'G_lambda=G',
    }


def packing_and_entropy():
    # For separation >=4L, the n-th non-nearest Gaussian is at distance
    # >=(n-1/2)*4L. Its bound exp(-2n) follows from this polynomial.
    n = s.symbols('n', integer=True, positive=True)
    zero((n-s.Rational(1,2))**2-n/4-(n-1)*(n-s.Rational(1,4)),
         'Gaussian lattice exponent comparison')
    # exp(2)>=1+2+2=5, so the lattice sum is <=3/2.
    zero(1+2/s.Integer(4)-s.Rational(3,2), 'uniform Gaussian lattice bound')
    N, lam, mass, background_mass, K, shift2 = s.symbols(
        'N lambda mass background_mass K shift2', positive=True)
    weight = N*mass/(background_mass*lam**3+N*mass)
    bound = weight*(K+shift2/2+5*s.log(lam))
    zero(s.limit(bound,lam,s.oo),
         'source relative entropy can vanish after concentrating each finite packet family')
    return {
        'order_of_choices': 'fix N; choose finite translation separation by actual-flow stability; then choose finite lambda sufficiently large',
        'circulation_sup': 'Gaussian packing bounds G_N uniformly in N and separation; choose a fixed Gaussian background with strictly larger G',
        'mixture_weight': str(weight),
        'KL_upper_bound': str(bound),
        'KL_limit': 'zero as lambda tends to infinity for each fixed finite N and shift2',
        'scope': 'entropy convexity and the translated-profile entropy formula are analytic; their scaling and limiting scalar expression are checked here',
    }


def signed_budget():
    nu, D, P, delta = s.symbols('nu D P delta', real=True)
    increment = s.Rational(3,2)*P-s.Rational(15,4)*nu*D
    cost = s.Rational(3,2)*P-s.Rational(15,8)*nu*D
    zero(cost-increment-s.Rational(15,8)*nu*D,
         'the requested signed excess dominates the critical moment increment')
    N = s.symbols('N', integer=True, positive=True)
    # Three independent small errors are chosen after N is fixed:
    # separated actual evolution, concentration/background, and endpoints.
    zero(N*delta-3*N*delta/8-s.Rational(5,8)*N*delta,
         'positive margin survives three chosen approximation errors')
    require(s.Rational(5,8)>s.Rational(1,2), 'strict final packing margin')
    zero(s.Rational(3,4)+s.Rational(1,2)-s.Rational(5,4),
         'the already-paid parent history vanishes at order T^(5/4) for pure swirl')
    zero(N*delta/2-N*delta/4-N*delta/4,
         'the actual integrating-factor loss leaves a positive core budget margin')
    return {
        'identity': 'signed_excess=Delta M+(15nu/8) integral Dcrit',
        'family': 'smooth Schwartz initially pure swirls; actual unforced intervals at one fixed positive nu and below any fixed H>0',
        'lower_bound': 'Delta M >= c N and signed_excess >= c N, with fixed c>0',
        'paid_core': 'with original rho fixed and eta0=0, integral ||q_paid||_infinity <= C(nu,rho)*sqrt(C4(0))*T^(5/4); choose concentration so the w(T)M(T) loss is below N delta/4',
        'reflection': 'choose an even number of packets with centers in symmetric pairs; the same bound applies to the four signed-history core target',
        'initial_resources': 'E, each selected finite circulation moment, and max circulation converge to those of one fixed Gaussian background; source KL tends to zero',
        'refuted_budget': 'a signed-excess allowance locally bounded in only those displayed coarse resources, even though the ledger separately starts with the full M0',
        'refuted_state_correction': 'M+F(coarse resources) cannot be nonincreasing when F is continuous at the fixed background resource vector',
        'not_refuted': 'an allowance proportional to M0, finer critical initial geometry, a full-datum history reserve, or regularity',
        'scope': 'finite simultaneous prepared bursts; no fixed-datum infinite renewal or blowup is asserted',
    }


if __name__ == '__main__':
    print(json.dumps({'scaling':scalings(),
                      'packing_and_entropy':packing_and_entropy(),
                      'signed_budget':signed_budget()},indent=2))
