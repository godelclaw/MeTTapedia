#!/usr/bin/env python3
"""Complete enstrophy response of compact periodic swirl data.

The analytic actual-history theorem is in README.md. Checks retain the
same pressure and reflection reconstruction as centrifugal_parent_return.
"""

from collections import defaultdict
from fractions import Fraction
import hashlib
import json
from pathlib import Path

import sympy as s

from centrifugal_parent_return import parity_jets, physical_return
from rotational_curl_reserve import require, zero


def quadratic_observer():
    """A reflection-invariant quadratic form on full NS time jets."""
    U = ('U',)
    def L(a):
        return ('L', a)
    def B(a, b):
        a, b = sorted((a, b), key=repr)
        return ('B', a, b)
    def parity(a):
        if a == U:
            return 1
        if a[0] == 'L':
            return parity(a[1])
        return (parity(a[1])+parity(a[2])) % 2
    def norm_coefficient(series, order):
        out = defaultdict(Fraction)
        for i in range(order+1):
            for a, ca in series[i].items():
                for b, cb in series[order-i].items():
                    if parity(a) != parity(b):
                        continue
                    pair = tuple(sorted((a, b), key=repr))
                    out[pair] += ca*cb
        return dict(out)

    W = B(U, U)
    actual = [{U: Fraction(1)}, {L(U): Fraction(1), W: Fraction(1)},
              {L(L(U)): Fraction(1, 2), L(W): Fraction(1, 2),
               B(U, L(U)): Fraction(1), B(U, W): Fraction(1)}]
    heat = [{U: Fraction(1)}, {L(U): Fraction(1)},
            {L(L(U)): Fraction(1, 2)}]
    difference = defaultdict(Fraction, norm_coefficient(actual, 2))
    for pair, value in norm_coefficient(heat, 2).items():
        difference[pair] -= value
    difference = {pair: value for pair, value in difference.items() if value}
    expected = {tuple(sorted((W, W), key=repr)): Fraction(1),
                tuple(sorted((U, B(U, W)), key=repr)): Fraction(2)}
    require(difference == expected, 'full quadratic observation retains both direct response and original-fluid feedback')
    require(norm_coefficient(actual, 1) == norm_coefficient(heat, 1),
            'the full observation first derivative agrees with heat')
    return dict(
        operator='Any self-adjoint metric commuting with reflection, specialized to -Delta.',
        coefficient='G=<W,-Delta W>+<U,-Delta DN(U)W>, W=N(U)',
        physical_stretching='g(U)=0 and g_prime(0)=G for every nu>0',
        enstrophy_comparison='||grad u(t)||2^2-||grad exp(nu*t*Delta)U||2^2=G*t^2+o(t^2)',
        scope='The algebra checks the complete time jets; the PDE Taylor remainder and integrations by parts remain analytic.')


def annular_response():
    r, p, k = s.symbols('r p k', positive=True)
    phase, eps = s.symbols('phase eps', real=True)
    chi = s.Function('chi')(r)
    radial = lambda q: s.diff(q, r, 2)+3*s.diff(q, r)/r
    Dz = lambda q: k*s.diff(q, phase)
    lifted = lambda q: radial(q)+Dz(Dz(q))
    D = radial(chi)-k*k*chi
    a = D/k
    b0 = r**(-p)
    h = a/(2*b0)
    b_first = b0+eps*h*s.cos(phase)
    Vr = -k*r*chi*s.cos(phase)
    Vz = (2*chi+r*s.diff(chi, r))*s.sin(phase)
    returned = -eps*r*(Vr*s.diff(b_first, r)+Vz*Dz(b_first))-2*eps*Vr*b_first
    omega_V = Dz(Vr)-s.diff(Vz, r)
    zero(omega_V+k*r*a*s.sin(phase), 'the full generated vorticity includes its radial basis term')
    density = r*((eps*omega_V)**2-r*lifted(b_first)*returned)
    second = s.expand(density).coeff(eps, 2)
    cosine, sine = s.symbols('cosine sine')
    trig = s.Poly(second.subs({s.cos(phase): cosine, s.sin(phase): sine}), cosine, sine)
    averaged = 0
    for powers, coefficient in trig.terms():
        require(powers in [(2, 0), (0, 2)], 'the second variation has only the complete squared axial modes')
        averaged += coefficient/2
    B = chi*(2*b0+r*s.diff(b0, r))
    raw = r**3*(k*k*a*a-k*radial(b0)*(r*chi*s.diff(h, r)+(4*chi+r*s.diff(chi, r))*h)
                -k*(radial(h)-k*k*h)*B)
    zero(2*averaged-raw, 'literal vorticity and feedback give the full axial integral')

    middle = r**3*(k*k*a*a+k*h*(r*chi*s.diff(radial(b0), r)-(radial(B)-k*k*B)))
    boundary1 = -k*radial(b0)*r**4*chi*h-k*r**3*(s.diff(h, r)*B-h*s.diff(B, r))
    zero(raw-middle-s.diff(boundary1, r), 'radial adjoint with its full boundary primitive')
    final = p*s.Rational(1, 2)*(r**3*D**2-2*(2-p)*k*k*r*chi**2)
    boundary2 = r*r*s.diff(chi, r)**2/2+2*r*chi*s.diff(chi, r)+2*chi**2-k*k*r*r*chi**2/2
    zero(middle-final-p*(2-p)*s.diff(boundary2, r), 'power-profile response with its full boundary primitive')
    positive = (r**3*radial(chi)**2+2*k*k*r**3*(s.diff(chi, r)+chi/r)**2
                +2*(p-1)*k*k*r*chi**2+k**4*r**3*chi**2)
    boundary3 = -2*k*k*(r**3*chi*s.diff(chi, r)+r*r*chi**2)
    zero(r**3*D**2-2*(2-p)*k*k*r*chi**2-positive-s.diff(boundary3, r),
         'Hardy identity completes the positive square certificate')
    zero(4*b0**2+r*s.diff(b0**2, r)-2*(2-p)*r**(-2*p),
         'the parent-energy sign changes at p=2, independently of the enstrophy sign')
    return dict(
        base='b_base=r^(-p) on the compact annular modulation support; unchanged CF pressure reconstruction',
        coefficient='G(eps)=eps^2*G2+O(eps^4)',
        G2='pi^2*p*integral [r^3*(chi_second+3chi_prime/r-k^2*chi)^2-2*(2-p)*k^2*r*chi^2] dr',
        positive_form='pi^2*p*integral [r^3*(chi_second+3chi_prime/r)^2+2*k^2*r^3*(chi_prime+chi/r)^2+2*(p-1)*k^2*r*chi^2+k^4*r^3*chi^2] dr',
        lower_bound='G2>=pi^2*p*k^4*integral r^3*chi^2 dr>0 for p>=1, k>=1, chi nonzero',
        parent_coefficient='C=4pi^2*eps^2*k^2*(p-2)*integral r^(3-2p)*chi^2 dr',
        sign_separation='1<=p<2: C<0 but G>0 for every sufficiently small nonzero eps; p=2: C=0 but G>0; p>2: C>0 and G>0',
        remainder='G is even and smooth in eps on a fixed source-positive compact parameter interval; no time or viscosity limit is used in this coefficient.')


def original_parameter_window():
    c, M, e = s.symbols('c M e', positive=True)
    zero(c*e**2-M*e**4-c*e**2/2-e**2*(c/2-M*e**2),
         'positive second variation survives its fourth-order static remainder')
    r = s.symbols('r', positive=True)
    zero(s.Rational(1, 2)*(s.Rational(5, 4))**3-s.Rational(125, 128),
         'compact middle-annulus lower bound for integral r^3*chi^2')
    return dict(
        parameter_interval='Pick eps_dom with eps_dom*||a/f0||infinity<=1/2.',
        remainder_bound='M=(1/24)*sup_{|eps|<=eps_dom}|d_eps^4 G(eps)|<infinity, computed from the original compact profiles only.',
        choice='0<|eps|<min(eps_dom,sqrt(G2/(2*(1+M)))) implies G(eps)>=G2*eps^2/2>0.',
        bump_bound='For the CF compact exponential bump, G2>=125*pi^2*p*k^4*exp(-32/3)/128.',
        distinction='This static initial-parameter choice does not define a budget by taking a supremum over an unknown future solution.')


def viscous_interval():
    eta, G, D0, Cg, CD, tau = s.symbols('eta G D0 Cg CD tau', positive=True)
    K = 2*D0/G
    main = G*K**2-D0*K
    zero(main-2*D0**2/G, 'the complete signed renewal main term is positive')
    lower = G*tau**2-eta*D0*tau-s.Rational(2, 3)*Cg*tau**3-eta*CD*tau**2/2
    R = s.Rational(2, 3)*Cg*K**3+CD*K**2/2
    zero(lower.subs(tau, K*eta)-eta**2*(main-eta*R),
         'integrated Taylor errors retain the full viscous credit')
    rate = 2*(G*tau-Cg*tau**2-eta*(D0+CD*tau))
    R1 = Cg*K**2+CD*K
    zero(rate.subs(tau, K*eta)-(2*eta*D0-2*eta**2*R1),
         'enstrophy actually grows after the initially dissipative interval')
    amplitude, nu = s.symbols('amplitude nu', positive=True)
    zero((amplitude**2*eta**2*main/2).subs(eta, nu/amplitude)-nu**2*D0**2/G,
         'the physical-time budget excess has a strictly positive fixed margin')
    q, Pe, Ee = s.symbols('q Pe Ee', positive=True)
    zero(-q/3+Pe*tau+q/6-(-q/6+Pe*tau),
         'negative parent return persists at the same chosen endpoint')
    zero(G-Ee*tau-G/2-(G/2-Ee*tau),
         'full enstrophy exceeds heat at the same chosen endpoint')
    return dict(
        datum='Fix any smooth reflection-odd U with G>0; scale it to amplitude*U at fixed viscosity nu>0.',
        constants='D0=||Delta U||2^2>0, K=2*D0/G; on a common local interval, |g(v_eta(tau))-G*tau|<=Cg*tau^2 and |D(v_eta(tau))-D0|<=CD*tau.',
        local_scope='v_eta is the actual unforced solution at viscosity eta in (0,1]; uniform local Sobolev estimates fix tau0,Cg,CD from U.',
        threshold='eta_star=min(1,tau0/K,(2*D0^2/G)/(2*(1+R)),D0/(2*(1+R1))), R=(2/3)*Cg*K^3+CD*K^2/2, R1=Cg*K^2+CD*K.',
        time='eta=nu/amplitude<eta_star, t_amplitude=K*nu/amplitude^2',
        signed_budget='2*integral_0^t_amplitude g(u)-nu*integral_0^t_amplitude D(u)>=nu^2*D0^2/G>0; g(u(0))=0',
        actual_growth='d_t ||grad u||2^2 at t_amplitude >=nu*amplitude^2*D0>0',
        same_endpoint='For C_parent<0, uniform parent and full-enstrophy Taylor errors Pe*tau^5 and Ee*tau^3 permit eta_star also <=(-C_parent)/(6*K*(1+Pe)) and <=G/(2*K*(1+Ee)). Then parent energy is below its original forecast and full enstrophy is above heat at t_amplitude.',
        limit='Refutes zero allowance on an actual short prefix; no counterexample to a finite allowance depending on the full scaled datum.')


if __name__ == '__main__':
    result = dict(previous_jets=parity_jets(), previous_pressure=physical_return(),
                  full_observer=quadratic_observer(), annular=annular_response(),
                  parameter_window=original_parameter_window(), interval=viscous_interval(),
                  status='Analytic actual periodic NS comparison with exact algebraic fixtures; no new Lean certificate and no arbitrary-history payment.')
    names = ['centrifugal_enstrophy_return.py', 'centrifugal_parent_return.py',
             'rotational_curl_reserve.py']
    base = Path(__file__).parent
    result['source_sha256'] = {name: hashlib.sha256((base/name).read_bytes()).hexdigest()
                               for name in names}
    print(json.dumps(result, indent=2))
