#!/usr/bin/env python3
"""Exact fixtures for the cubic quotient's heat dissipation and fine work.

The all-data variational and heat-semigroup arguments are analytic in
README.md. These checks retain full Fourier products in both physical
three-dimensional fixtures and certify their complete remainder constants.
They do not certify an arbitrary-history payment or a PDE in Lean.
"""

import hashlib
import json
from pathlib import Path

import sympy as s
import optimal_cubic_gauge as og

f, wh, am, Q = og.f, og.wh, og.am, og.Q
require, zero = og.require, og.zero


def heat_geometry():
    r, a, b = s.symbols('r a b', positive=True)
    # a=|partial w|^2; b=|partial |w||^2, with 0<=b<=a.
    diffusion = r*(a+b)
    z_gradient = r*(a+s.Rational(5, 4)*b)
    dual_gradient_over_r = r*(a+3*b)
    zero(diffusion-s.Rational(8, 9)*z_gradient-r*(a-b)/9,
         'heat dissipation controls the complete transformed vector gradient')
    zero(s.Rational(16, 9)*z_gradient-dual_gradient_over_r
         -s.Rational(7, 9)*r*(a-b),
         'the dual derivative is controlled by the same transformed vector')
    zero(s.Rational(16, 9)*s.Rational(9, 8)-2,
         'weighted dual derivative costs at most twice quotient dissipation')
    nu, J, D, C, B = s.symbols('nu J D C B', positive=True)
    coefficient = 3*s.sqrt(6)*C*B
    kappa = 54*C*C*B*B/nu
    zero(nu*D/4+kappa*J-coefficient*s.sqrt(J*D)
         -(s.sqrt(nu*D)/2-coefficient*s.sqrt(J/nu))**2,
         'the full coarse interaction is absorbed with the stated coefficient')
    return {'transformed_field': 'z=|w|^(1/2)w',
            'gradient_bound': 'integral |grad z|^2 <= (9/8) Dq',
            'dual_bound': 'integral |grad F|^2/|w| <= 2 Dq; zero integrand at w=0',
            'coarse_coefficient': 'kappa=54 C_Pi,3^2 ||kernel_l||_2^2 E0/nu'}


def constant_and_zero_crossing():
    x, t = s.symbols('x t', real=True)
    A, nu = s.symbols('A nu', positive=True)
    # Integrate one positive half-wave; |sin| supplies the other half.
    J0 = s.integrate(s.sin(x)**3, (x, 0, s.pi))/(3*s.pi)
    D0 = 2*s.integrate(s.sin(x)*s.cos(x)**2, (x, 0, s.pi))/s.pi
    z_grad0 = s.Rational(9, 4)*s.integrate(
        s.sin(x)*s.cos(x)**2, (x, 0, s.pi))/s.pi
    zero(J0-4/(9*s.pi), 'exact cubic stock of the nodal shear')
    zero(D0-3*J0, 'the nodal shear retains complete viscous diffusion')
    zero(z_grad0-s.Rational(9, 8)*D0,
         'the heat-Sobolev gradient constant is sharp at a scalar shear')
    zero(s.diff(A**3*s.exp(-3*nu*t)*J0, t)
         +nu*A**3*s.exp(-3*nu*t)*D0,
         'actual unforced nodal shear has the exact history balance')
    shear = A*s.exp(-nu*t)*s.sin(x)
    zero(s.diff(shear, t)-nu*s.diff(shear, x, 2),
         'the transverse shear satisfies its actual pressure-free NS equation')
    for constants in ((1, 2, -1), (0, 0, 0)):
        v = [f.clean({f.ORIGIN: Q(c)}) for c in constants]
        wh.same_vectors(wh.project(v), v, 'constant and zero fields are solenoidal')
        wh.same_vectors(og.adv(v, v), [{}, {}, {}], 'constant-flow convection is zero')
        wh.same_vectors([f.lap(a) for a in v], [{}, {}, {}],
                        'constant-flow heat dissipation is zero')
    return {'nodal_shear': 'u=A exp(-nu t) sin(z)e1; optimizer w=u vanishes on planes; P=0 and J_prime=-nu Dq.',
            'constant_flow': 'For nonzero constant u on T3, Dq=0 while J>0. The periodic Sobolev L2 term cannot be dropped.',
            'zero_flow': 'u=w=F=0 gives J=Dq=P=0; no inverse magnitude or division by energy is used.'}


def cutoff(vector, ell):
    return [f.clean({k: c/(1+ell**2*sum(a*a for a in k))**2
                     for k, c in component.items()}) for component in vector]


def physical_fixture(sign):
    base, G = og.datum(sign)
    h, j = f.dot(base, G), f.dot(G, G)
    w1 = wh.addv(G, wh.scalev(-Q(1)/2, og.scalar_vector(h, base)))
    w2 = wh.addv(og.scalar_vector(f.add(f.scale(-Q(1)/4, j),
                                       f.scale(Q(5)/8, f.mul(h, h))), base),
                  wh.scalev(-Q(1)/2, og.scalar_vector(h, G)))
    ws = [base, w1, w2]
    us = [wh.project(w) for w in ws]
    full = []
    for n in range(3):
        conv = wh.addv(*(og.adv(us[a], us[n-a]) for a in range(n+1)))
        value = -am.pairing(base, conv)
        if n:
            prev = wh.addv(*(og.adv(us[a], us[n-1-a]) for a in range(n)))
            value -= am.pairing(G, prev)
        full.append(value)
    require(full == [f.ZERO, f.ZERO, Q(sign)/12],
            'the original full physical nonlinear work is retained')
    diffusion = [-am.pairing(base, [f.lap(a) for a in us[n]])
                 -(am.pairing(G, [f.lap(a) for a in us[n-1]]) if n else f.ZERO)
                 for n in range(3)]
    require(diffusion == [Q(1), f.ZERO, Q(61)/16],
            'the quotient dissipation retains the complete physical Laplacian')
    expected = {Q(1).x/2: -Q(2707)/44100,
                Q(1).x: -Q(89)/4608,
                Q(2).x: Q(21848)/342225}
    rows = []
    for ell in (Q(1)/2, Q(1), Q(2)):
        lo = [cutoff(u, ell) for u in us]
        hi = [wh.addv(u, wh.scalev(-1, l)) for u, l in zip(us, lo)]
        for n in range(3):
            for v in (lo[n], hi[n]):
                f.equal(f.trace(f.jac(v)), {}, 'both pieces stay solenoidal')
                require(og.wiener(v) <= og.wiener(us[n]),
                        'the Bessel multiplier and its complement contract this Fourier norm')
        fine = []
        for n in range(3):
            fine_conv = wh.addv(*(og.adv(hi[a], hi[n-a]) for a in range(n+1)))
            coarse_conv = wh.addv(*(
                wh.addv(og.adv(lo[a], us[n-a]), og.adv(hi[a], lo[n-a]))
                for a in range(n+1)))
            full_conv = wh.addv(*(og.adv(us[a], us[n-a]) for a in range(n+1)))
            wh.same_vectors(wh.addv(fine_conv, coarse_conv), full_conv,
                            'complete joint interaction reconstructs before projection')
            wh.same_vectors(wh.project(wh.addv(fine_conv, coarse_conv)),
                            wh.project(full_conv), 'physical pressure projection is retained')
            value = -am.pairing(base, fine_conv)
            if n:
                prev = wh.addv(*(og.adv(hi[a], hi[n-1-a]) for a in range(n)))
                value -= am.pairing(G, prev)
            fine.append(value)
        require(fine == [f.ZERO, f.ZERO, sign*expected[ell.x]],
                'exact cutoff-dependent signed fine-work coefficient')
        rows.append({'ell': str(ell), 'fine': list(map(str, fine)),
                     'coarse': [str(a-b) for a, b in zip(full, fine)]})
    return {'sign': sign, 'full': list(map(str, full)),
            'diffusion': list(map(str, diffusion)), 'cutoffs': rows}, (base, G, h, j, w1, us[1])


def complete_remainder(data):
    old = og.remainder(data)
    eps = Q(1).x/(2**32)
    c_min = Q(89).x/4608
    require(eps < Q(1).x/(2**28), 'new parameter lies inside the earlier full-series domain')
    require(10**7*eps < c_min/2,
            'the complete remainder is smaller than half every displayed fine coefficient')
    amplitude_over_nu = 4/(c_min*eps*eps)
    require(amplitude_over_nu*c_min*eps*eps/2-Q(2).x/4 == Q(3).x/2,
            'positive fine work can exceed its quarter-diffusion payment')
    return {'epsilon': str(eps), 'C3_strict_upper': '10000000',
            'exact_previous_C3': old['C3'], 'minimum_absolute_coefficient': str(c_min),
            'amplitude_over_nu': str(amplitude_over_nu),
            'bound': '|P_fine-sign*c_ell*epsilon^2| <= 10000000 epsilon^3',
            'physical_consequence': 'At ell=1 with sign=-1 and the stated amplitude, P_fine-nu Dq/4 >= (3/2)nu A^3 initially and on a short actual interval with a smaller margin.',
            'limitation': 'The full nonlinear work is negative on that fixture. This rejects automatic fine-work absorption, not the complete coarse-paid bound or any finite original-data allowance.'}


if __name__ == '__main__':
    fixtures = [physical_fixture(sign) for sign in (1, -1)]
    dependencies = [Path(__file__), Path(og.__file__), Path(f.__file__),
                    Path(wh.__file__), Path(am.__file__)]
    report = {'candidate': 'J(u)=min_{Pi w=u} integral |w|^3/3; F=|w|w; Dq=-<F,Delta u>.',
              'heat_geometry': heat_geometry(),
              'calibrations': constant_and_zero_crossing(),
              'physical_fixtures': [row[0] for row in fixtures],
              'remainders': [complete_remainder(row[1]) for row in fixtures],
              'status': 'Exact algebra and Fourier/remainder constants passed; variational, semigroup, Sobolev and local-PDE arguments are analytic, not Lean-certified.',
              'open': 'One finite original-data allowance for the signed fine work on every same-datum prefix remains unproved on both domains.',
              'source_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in dependencies}}
    print(json.dumps(report, indent=2), flush=True)
