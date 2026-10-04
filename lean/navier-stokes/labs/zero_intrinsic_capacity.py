#!/usr/bin/env python3
"""A vanishing intrinsic capacity misses complete nonlinear heat renewal.

Every Fourier output of the pressure and source is retained. The positive
viscosity calculations are exact initial tangents of the full equation.
Persistence on an actual local solution and the all-policy conclusion are
analytic arguments in README.md, not Lean certificates.
"""

import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path

import sympy as s
import pressure_history_source as f
import heat_work_reserve as h
from cyclic_pressure_history import velocity_time_jets
from generated_fourth_moment import fourth_work, vector_pair
from heat_remainder_pressure import plus, times, require
from pressure_quadratic_storage import mode


WAVES = [((0, 1, 1), (1, 1, -1)),
         ((0, 1, -1), (-1, -1, -1)),
         ((1, -1, 0), (-1, -1, -2))]


def datum():
    fields = [mode(k, polarization, 1) for k, polarization in WAVES]
    return [f.add(*(v[j] for v in fields)) for j in range(3)]


def zero(value, label):
    require(s.expand(value) == 0, label)


def checks():
    u = datum()
    f.equal(f.trace(f.jac(u)), {}, 'The literal datum is incompressible')
    require(abs(s.Matrix([k for k, _ in WAVES]).det()) == 2,
            'The three wave vectors span three-dimensional space')
    for row in u:
        require(f.ORIGIN not in row, 'The datum has zero spatial mean')
        f.equal(f.lap(row), f.scale(-2, row), 'All input modes have squared frequency two')
        require(all(row.get(tuple(-j for j in k)) == f.QQ_I(a.x, -a.y)
                    for k, a in row.items()), 'The datum is a real field')

    n = h.nonlinear(u)
    source_modes = set().union(*n)
    rates = sorted({sum(i*i for i in k) for k in source_modes})
    require(rates == [2, 4, 6], 'The complete source leaves the input frequency shell')
    require(f.add(n[0], f.scale(-1, n[1])),
            'The actual nonlinear tangent leaves the initial velocity-polarization plane')
    z = h.heat(u)
    F = h.profile(z)
    I = h.variation(z, h.nonlinear(z))
    G = h.variation(z, h.heat(n))
    zero(F, 'Initial pressure work vanishes on the entire free-heat curve')
    zero(I+h.q**12/3, 'Intrinsic work is strictly negative at every finite heat age')
    expected = h.q**10*(11-13*h.q**4)/6
    zero(G-expected, 'Complete heat renewal has two competing output decay rates')
    covariance = h.q**10*(1-h.q**2)*(11+13*h.q**2)/6
    zero(G-I-covariance, 'The missing work is a strictly positive heat-nonlinearity commutator')

    # Split the already-computed full source, then reconstruct it exactly.
    # No projected-shell evolution is substituted for the fluid equation.
    channels, recovered = [], [{}, {}, {}]
    for rate in rates:
        part = [{k: a for k, a in row.items() if sum(i*i for i in k) == rate} for row in n]
        recovered = plus(recovered, part)
        response = h.variation(z, h.heat(part))
        coefficient = {2: s.Rational(11, 6), 4: s.Integer(0), 6: -s.Rational(13, 6)}[rate]
        zero(response-coefficient*h.q**(8+rate), 'Exact contribution of each complete source channel')
        channels.append(dict(squared_frequency=rate, coefficient=str(coefficient),
                             source_modes=len(set().union(*part)), profile=str(s.factor(response))))
    for actual, reconstructed in zip(n, recovered):
        f.equal(actual, reconstructed, 'The channel decomposition retains every source mode')
    zero(s.Rational(11, 6)-s.Rational(13, 6)+s.Rational(1, 3),
         'The instantaneous channel sum is negative')

    # Differentiate the original scalar pressure functional independently,
    # rather than relying only on its two equivalent first-variation forms.
    perturbed = h.profile(h.heat(plus(u, times(h.EPS, n))))
    zero(s.expand(perturbed).coeff(h.eps, 1)-G,
         'Direct polynomial differentiation reproduces the full renewal')
    heat_direction = h.variation(z, h.heat([f.lap(row) for row in u]))
    zero(heat_direction, 'Viscosity contributes zero to the initial heat-work profile derivative')

    lower = h.integrate(G, s.Rational(1, 4))
    require(lower == s.Rational(65147, 2293760) > s.Rational(1, 36),
            'The signed heat integral is a strictly positive lower bound for its positive part')
    zero(h.integrate(G)-s.Rational(1, 35), 'The signed whole-age integral is also positive')
    # q=exp(-s); the only sign change is q^4=11/13. The finite
    # window q in [1/2,1] contains both signs. The derivative of the
    # positive-part functional uses max(G,0), never the signed G itself.
    require(s.Rational(1, 16) < s.Rational(11, 13) < 1,
            'Both signs occur inside the prescribed heat window')
    intrinsic_negative_margin = s.Rational(1, 3)*s.Rational(1, 2)**12
    require(intrinsic_negative_margin == s.Rational(1, 12288),
            'Intrinsic negativity has a uniform margin on the complete compact window')

    work, diffusion, moment = fourth_work(u)
    require((work, diffusion, moment) == (Q(0), Q(239, 2), Q(239, 4)),
            'The complete physical fourth moment and diffusion are exact')
    require(vector_pair(u, u) == 6, 'The normalized initial squared kinetic norm is six')
    ratio = 72
    margin = ratio**2*lower-s.Rational(239, 2)
    require(margin > s.Rational(49, 2) > 0,
            'Amplitude 72nu makes the actual reserve increase despite complete viscous dissipation')

    actual_rows = []
    for nu in (Q(1), Q(2, 7)):
        amplitude = ratio*nu
        initial = times(amplitude, u)
        tangent = velocity_time_jets(initial, nu, 1)[0][1]
        physical_profile = h.variation(h.heat(initial), h.heat(tangent))
        zero(physical_profile-amplitude**6*G,
             'The actual positive-viscosity tangent gives the full heat-work directional derivative')
        receiver = [f.mul(f.dot(initial, initial), row) for row in initial]
        moment_rate = vector_pair(receiver, tangent)
        require(moment_rate == -nu*amplitude**4*diffusion,
                'The full initial fourth-moment balance retains transport and pressure')
        normalized_lower = s.factor((moment_rate+h.integrate(physical_profile, s.Rational(1, 4))/nu)
                                    /(nu*amplitude**4))
        zero(normalized_lower-margin, 'Independent positive-viscosity reserve-rate lower bound')
        energy_rate = 2*vector_pair(initial, tangent)
        require(energy_rate == -24*nu*amplitude**2 < 0,
                'The same unforced tangent strictly loses kinetic energy')
        actual_rows.append(dict(viscosity=str(nu), amplitude=str(amplitude),
                                normalized_reserve_rate_lower=str(normalized_lower),
                                squared_L2_rate=str(energy_rate)))

    # Check the physical dilation used in the analytic arbitrary-window
    # extension; this multiplies every input and every generated frequency.
    dilation = 2
    dilated = [{tuple(dilation*j for j in k): dilation*a for k, a in row.items()} for row in u]
    dilated_z = h.heat(dilated)
    zero(h.profile(dilated_z), 'Dilation preserves the zero pressure-work profile')
    zero(h.variation(dilated_z, h.nonlinear(dilated_z))-dilation**8*I.subs(h.q, h.q**4),
         'Intrinsic work has the complete NS dilation and heat-age scaling')
    zero(h.variation(dilated_z, h.heat(h.nonlinear(dilated)))-dilation**8*G.subs(h.q, h.q**4),
         'All generated output rates scale with the physical dilation')
    require(fourth_work(dilated) == (work, dilation**6*diffusion, dilation**4*moment),
            'Physical quartic dissipation and fourth moment have their stated dilation weights')

    result = dict(waves=[dict(frequency=k, polarization=v, amplitude='cosine') for k, v in WAVES],
                  input_modes=len(set().union(*u)), complete_source_modes=len(source_modes),
                  heat_work=str(F), intrinsic_work=str(s.factor(I)), complete_renewal=str(s.factor(G)),
                  covariance_work=str(s.factor(covariance)),
                  source_channels=channels, window='0 <= s <= log(2)',
                  intrinsic_negative_margin=str(intrinsic_negative_margin),
                  selected_renewal_lower=str(lower), fourth_moment=str(moment),
                  quartic_diffusion=str(diffusion), amplitude_over_viscosity=ratio,
                  normalized_reserve_rate_lower=str(margin), actual_tangents=actual_rows,
                  dilation_check=dict(integer=dilation, moment_degree=4, diffusion_degree=6,
                                      renewal_degree=8, heat_age_degree=2),
                  scope='Exact complete Fourier identities and positive-viscosity initial tangents. Vanishing capacity and growth on an actual local NS interval, and the resulting obstruction for arbitrary scalar weight policies, are analytic, not Lean-certified. The heat window is prescribed; other reserves and original-data integrated allowances are not refuted.')
    root = Path(__file__).resolve().parent
    names = ['zero_intrinsic_capacity.py', 'heat_work_reserve.py', 'pressure_history_source.py',
             'cyclic_pressure_history.py', 'generated_fourth_moment.py', 'heat_remainder_pressure.py',
             'pressure_quadratic_storage.py', 'pressure_gradient_stock.py']
    result['source_sha256'] = {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in names}
    return result


if __name__ == '__main__':
    print(json.dumps(checks(), indent=2))
