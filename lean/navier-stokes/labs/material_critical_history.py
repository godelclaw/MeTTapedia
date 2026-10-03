#!/usr/bin/env python3
"""Material critical mass, diffusion in labels, and a physical metric payment.

All fixtures and sign enclosures are exact. The actual positive-viscosity
interval and the general history bound are analytic arguments in README.md.
"""

import json
import sympy as sp
from helicity_renewal import f, pm, Q, zero, sobolev_pair, conjugate
from helical_second_return import certified_interval


def scalar_pair(v, w, power=1):
    return sobolev_pair([v, {}, {}], [w, {}, {}], power)


def original_profile():
    coefficients = {0: 11, 2: -7, 4: 4, 6: -2, 8: 1}
    coefficients.update({-n: a for n, a in list(coefficients.items()) if n})
    h = {(m, n, 0): f.QQ_I.convert(Q(a, 2))
         for m in (-1, 1) for n, a in coefficients.items()}
    for k, a in h.items():
        if h[tuple(-x for x in k)] != conjugate(a):
            raise ArithmeticError('Initial profile must be real')
    return h, coefficients


def operators(h):
    cy = {(0, 1, 0): f.QQ_I.convert(Q(1, 2)), (0, -1, 0): f.QQ_I.convert(Q(1, 2))}
    sy = {(0, 1, 0): -f.II/2, (0, -1, 0): f.II/2}
    hx, hy = f.diff(h, 0), f.diff(h, 1)
    L0 = f.lap(h)
    L1 = f.add(f.scale(-2, f.mul(cy, f.diff(hx, 1))), f.mul(sy, hx))
    L2 = f.mul(f.mul(cy, cy), f.diff(hx, 0))
    for theta in (Q(0), Q(1), Q(256)):
        D = lambda v: f.add(f.diff(v, 1), f.scale(-theta, f.mul(cy, f.diff(v, 0))))
        full = f.add(L0, f.scale(theta, L1), f.scale(theta*theta, L2))
        factored = f.add(f.diff(hx, 0), D(D(h)))
        if f.add(full, f.scale(-1, factored)):
            raise ArithmeticError('Exact pulled-back Laplacian factorization')
        zero(scalar_pair(h, full, 0)+scalar_pair(hx, hx, 0)+scalar_pair(D(h), D(h), 0),
             'physical diffusion always dissipates L2 in material labels')
    return L0, L1, L2


def material_sign():
    h, a = original_profile()
    L0, L1, L2 = operators(h)
    P0 = sp.expand(sum(sp.Integer(1+n*n)**sp.Rational(3, 2)*v*v for n, v in a.items()))
    P2 = sp.expand(sum(sp.sqrt(1+n*n)*v*(sp.Rational(v, 2)
         +sp.Rational(a.get(n-2, 0)+a.get(n+2, 0), 4)) for n, v in a.items()))
    expected = 22-sp.Rational(7, 2)*sp.sqrt(5)-2*sp.sqrt(17)-sp.sqrt(37)
    zero(P2-expected, 'exact indefinite critical multiplication form')
    for actual, target in [(2*scalar_pair(h, L0), -P0),
                           (2*scalar_pair(h, L1), 0),
                           (2*scalar_pair(h, L2), -P2)]:
        zero(actual-target, 'full critical diffusion polynomial in theta')
    lo, hi = certified_interval(P2)
    if not -sp.Rational(4, 25) < lo < hi < -sp.Rational(3, 20):
        raise ArithmeticError('Strict negative multiplication form')
    instant = sp.expand(-(P0+256**2*P2)/2)
    if not certified_interval(instant)[0] > 1900:
        raise ArithmeticError('Strict instantaneous material critical production')

    S = 512
    G = f.add(f.scale(S, L0), f.scale(Q(S*S, 2), L1), f.scale(Q(S**3, 3), L2))
    gamma = sp.expand(-S+2*scalar_pair(h, G))
    zero(gamma+S*(1+P0)+sp.Rational(S**3, 3)*P2, 'parent decay retained')
    gamma_lo, gamma_hi = certified_interval(gamma)
    if not gamma_lo > 3000000:
        raise ArithmeticError('Full material velocity has positive first viscosity variation')

    # Explicit reference-only constants for the whole-interval H1 remainder.
    # Frequencies obey 1+|k|^2<=66 and sum |a_n|=39.
    if sum(abs(v) for v in a.values()) != 39 or max(2+n*n for n in a) != 66:
        raise ArithmeticError('Profile norm bounds')
    R = 39*66**3  # exceeds ||h0||_H5 and lower Sobolev norms
    cS = S+2*S*S
    aS = 1+24*S+64*S*S
    bS = 12*S*S+64*S**3
    Gstar = S*aS*R
    C = 3*S*R*(bS+S*aS*aS)
    E = (R+Gstar+C)**2+S*S
    mu0 = sp.Rational(1, 2*(E+cS*S+1))
    if not (0 < mu0 < 1 and mu0*cS*S < 1 and mu0*E < sp.Rational(1, 2)):
        raise ArithmeticError('Uniform positive-viscosity remainder margin')
    if not gamma_lo-mu0*E > sp.Rational(1, 2):
        raise ArithmeticError('Actual positive-viscosity increase over initial mass')
    return dict(profile='cos x (11-14cos2y+8cos4y-4cos6y+2cos8y)',
        initial_modes=len(h), first_variation_modes=len(G),
        P0=str(P0), P2=str(P2), P2_interval=list(map(str, (lo, hi))),
        instantaneous_pair_at_theta256=str(instant),
        rescaled_horizon=S, complete_first_variation=str(gamma),
        complete_first_variation_interval=list(map(str, (gamma_lo, gamma_hi))),
        remainder_constants=dict(R=R, cS=cS, aS=aS, bS=bS, Gstar=Gstar, C=C, E=E),
        mu_upper=str(mu0), actual_increase_lower='A^2 mu/2 at t=512/A when B=A',
        scope='strict exact margins; whole-interval PDE error estimate is analytic')


def coordinate_identity():
    x, y, theta = sp.symbols('x y theta', real=True)
    H = sp.Function('H')
    w = H(x-theta*sp.sin(y), y)
    pulled_lap = (sp.diff(w, x, 2)+sp.diff(w, y, 2)).subs(x, x+theta*sp.sin(y)).doit()
    target = sp.diff(H(x, y), x, 2)+sp.diff(H(x, y), y, 2)
    target += -2*theta*sp.cos(y)*sp.diff(H(x, y), x, y)
    target += theta*sp.sin(y)*sp.diff(H(x, y), x)
    target += theta**2*sp.cos(y)**2*sp.diff(H(x, y), x, 2)
    zero(pulled_lap-target, 'actual coordinate chain rule for an arbitrary scalar')
    metric = sp.Matrix([[1+theta**2*sp.cos(y)**2, -theta*sp.cos(y)],
                        [-theta*sp.cos(y), 1]])
    zero(metric.det()-1, 'diffusion metric has determinant one')
    return dict(operator='L_theta=partial_x^2+(partial_y-theta cos y partial_x)^2',
        diffusion_metric_determinant=1,
        caution='determinant one does not make fixed-label fractional diffusion contractive')


def full_critical_payment():
    A, K0, nu, t, alpha = sp.symbols('A K0 nu t alpha', positive=True)
    source = A*K0*sp.exp(-3*nu*t)
    payment = A*K0/(3*nu)
    reserve = payment*sp.exp(-3*nu*t)
    zero(sp.integrate(source, (t, 0, sp.oo))-payment, 'total absolute physical metric work')
    zero(sp.diff(reserve, t)+source, 'same original resource across all time segments')
    parent_cost = -alpha*A**2*(1-sp.exp(-2*nu*t))/2
    zero(parent_cost-(A**2*sp.exp(-2*nu*t)/2-A**2/2
        +2*(1-alpha)*nu*sp.integrate(A**2*sp.exp(-2*nu*t)/2, (t, 0, t))),
        'parent heat contribution to the complete critical criterion')
    h, _ = original_profile()
    zero(scalar_pair(h, h, 0)-sp.Rational(261, 2), 'initial directional resource in the fixture')
    return dict(full_criterion_allowance=str(payment),
        initial_resource='K0=|| |partial_x|^(1/2) w0 ||_2^2',
        scope='any smooth transported profile, arbitrary amplitudes, stated unforced shear class',
        OPEN='a full-data payment for metric deformation by unrestricted interacting parents')


if __name__ == '__main__':
    print(json.dumps(dict(status='all exact checks passed', coordinates=coordinate_identity(),
        material_increase=material_sign(), physical_payment=full_critical_payment(),
        certification='exact identities and rational bounds; physical history remains analytic'), indent=2))
