#!/usr/bin/env python3
"""Algebra for fixed-energy concentration of the actual critical NS budget.

Full Fourier jets retain pressure and every output. Uniform local PDE
estimates, localization and expanding-torus limits are analytic in README.md;
these checks do not certify a solution interval or an unforced singularity.
"""

import json
from collections import defaultdict
import sympy as sp
from helicity_renewal import (
    f, pm, Q, add, scale, cross, projection, eqv, velocity_time_jets,
    zero, parents, modes, coefficient, conjugate, sobolev_pair, helical_source,
)
from helical_second_return import certified_interval


def closed_triad():
    """A positive-helicity fixture with a nonzero mixed viscous curvature."""
    u = [{}, {}, {}]
    for k, a in [((3, 0, 0), [0, 1, f.II]),
                 ((0, 4, 0), [-1, 0, f.II]),
                 ((-3, -4, 0), [4*f.II, -3*f.II, -5])]:
        for j in range(3):
            u[j][k] = f.QQ_I.convert(a[j])/2
            u[j][tuple(-x for x in k)] = conjugate(u[j][k])
    return [f.clean(p) for p in u]


def full_curvature(u, label):
    lap = lambda v: [f.lap(p) for p in v]
    N = lambda v: projection(cross(v, f.curl(v)))
    derivative = lambda v: projection(add(cross(v, f.curl(u)), cross(u, f.curl(v))))
    for k in modes(u):
        length = int(sp.sqrt(sum(j*j for j in k)))
        if coefficient(f.curl(u), k) != [length*a for a in coefficient(u, k)]:
            raise ArithmeticError('Initial fixture must have exact positive helicity')
    b = N(u)
    # Coefficients of the FULL viscosity polynomial, not viscosity samples.
    v1 = {0: b, 1: lap(u)}
    v2 = {0: derivative(b), 1: add(lap(b), derivative(lap(u))), 2: lap(lap(u))}
    curvature = defaultdict(lambda: sp.Integer(0))
    for i, v in v1.items():
        for j, w in v1.items():
            curvature[i+j] += 2*sobolev_pair(v, w)
    for j, w in v2.items():
        curvature[j] += 2*sobolev_pair(u, w)
    birth, _ = helical_source(b)
    lower, _ = certified_interval(birth)
    if lower <= 0:
        raise ArithmeticError('A strictly positive negative-sector birth is required')
    B3, P5 = sobolev_pair(u, b, 3), sobolev_pair(u, u, 5)
    target = {0: 4*birth, 1: -4*B3, 2: 4*P5}
    for j in curvature.keys() | target.keys():
        zero(curvature[j]-target.get(j, 0), 'all-viscosity critical-mass curvature')
    if label == 'closed_triad':
        zero(B3+72, 'mixed curvature must not be discarded')
    for nu in (Q(1), Q(3, 2)):
        jets, pressures = velocity_time_jets(u, nu, 2)
        eqv(jets[1], add(*(scale(nu**j, v) for j, v in v1.items())),
            'independent actual advective first jet with canonical pressure')
        eqv(jets[2], add(*(scale(nu**j, v) for j, v in v2.items())),
            'independent actual advective second jet with all source outputs')
        zero(sp.Rational(2*pm.mean(f.dot(u, jets[1])))
             +2*sp.Rational(nu)*sobolev_pair(u, u, 2), 'unforced kinetic balance')
        zero(2*sobolev_pair(u, jets[1])+2*sp.Rational(nu)*sobolev_pair(u, u, 3),
             'critical mass initially decreases by viscosity')
        if not any(pressures):
            raise ArithmeticError('Canonical pressure must be present')
    return dict(fixture=label, negative_source_mass=str(birth),
        rational_positive_lower=str(lower), mixed_pairing=str(B3),
        initial_modes=len(modes(u)), source_modes=len(modes(b)),
        curvature='M_second(0)=4A-4mu B3+4mu^2 P5',
        scope='entire viscosity polynomial, with independent positive-viscosity PDE jets')


def scaling_and_payment():
    lam, nu = sp.symbols('lambda nu', positive=True)
    amplitude, clock = lam**sp.Rational(3, 2), lam**sp.Rational(5, 2)
    mu = nu/sp.sqrt(lam)
    zero(amplitude*clock-amplitude**2*lam, 'time derivative and full quadratic source')
    zero(amplitude*clock*mu-nu*amplitude*lam**2, 'physical viscosity stays nu')
    pressure_scale = lam**3
    zero(pressure_scale*lam-amplitude*clock, 'pressure gradient scaling')
    E, M, L, J, Z = (amplitude**2/lam**3, amplitude**2/lam**2,
        amplitude**2, amplitude**3/lam, amplitude**2/lam)
    for value, expected in ((E, 1), (M, lam), (L, lam**3),
                            (J, lam**sp.Rational(7, 2)), (Z, lam**2)):
        zero(value-expected, 'Sobolev and cubic scaling')
    zero(J/clock-lam, 'integrated critical production')
    zero(nu*L/clock-lam*mu, 'integrated critical dissipation')
    zero(nu*Z/clock-nu/sp.sqrt(lam), 'vanishing kinetic loss on the burst interval')
    a, tau, Lstar, K = sp.symbols('a tau Lstar K', positive=True)
    # Uniform remainder <= K tau^2 and tau <= sqrt(a)/(2K).
    zero(tau*sp.sqrt(a)-K*tau**2-tau*sp.sqrt(a)/2
         -tau*(sp.sqrt(a)/2-K*tau), 'negative-sector norm lower bound')
    zero(a*tau**2/2-2*(a*tau/(8*Lstar))*Lstar*tau-a*tau**2/4,
         'uniform critical-mass gain at the allowed viscosity threshold')
    E0, A0, A1 = sp.symbols('E0 A0 A1', nonnegative=True)
    envelope = A0*E0**2+2*A1*E0**sp.Rational(5, 2)/(5*nu)
    zero(envelope.subs(E0, 1)-A0-2*A1/(5*nu), 'uniformly finite quartet price at unit energy')
    return dict(velocity_scaling='lambda^(3/2) v_(nu/sqrt(lambda))(lambda^(5/2)t,lambda x)',
        energy_scale=str(E), critical_mass_scale=str(M), critical_dissipation_scale=str(L),
        cubic_production_scale=str(J), burst_time='tau0 lambda^(-5/2)',
        guaranteed_critical_gain='(a tau0^2/4) lambda',
        kinetic_energy_loss_upper='2nu Zstar tau0 lambda^(-1/2)',
        quartet_sum_envelope=str(envelope),
        scope='scaling and scalar implications; physical uniform interval and periodization are analytic')


if __name__ == '__main__':
    print(json.dumps(dict(status='all exact checks passed',
        full_curvatures=[full_curvature(parents('full'), 'four_parent'),
                         full_curvature(closed_triad(), 'closed_triad')],
        scaling_and_payment=scaling_and_payment(),
        OPEN='finite allowance from the FULL original datum for every same-datum prefix',
        scope='no new Lean certificate; no blowup or indefinite renewal claimed'), indent=2))
