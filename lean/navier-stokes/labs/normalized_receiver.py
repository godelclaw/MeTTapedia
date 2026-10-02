#!/usr/bin/env python3
"""Normalized receiver reserves and the first generated stretching burst.

The finite Fourier and scalar checks are exact. Localization and positive
viscosity evolution on a common rescaled interval are analytic in README.md.
Auxiliary weights change the observation, not the fluid equation.
"""

import json
from fractions import Fraction as Q

import receiver_concentration as rc
from covariance_poisson_corrector import planar_belt
from refeeding_stretching import linear_cubic_term

s, f = rc.s, rc.f


def physical_jet(u, nu=Q(1), full=False):
    project = (lambda v: v) if full else s.oscillation
    capacity = rc.capacity if full else s.capacity
    derivative = rc.derivative if full else s.capacity_derivative
    w, h = project(u), project(s.nonlinear(u))
    Aw = s.minus_laplacian(w)
    n = project(s.nonlinear(w))
    Z, D = s.inner(w, Aw), s.inner(Aw, Aw)
    H, C, g = s.forecast(w, nu), capacity(w, nu), s.cubic(w)
    Zd = -2*nu*D+2*s.inner(Aw, h)
    Hd = -2*g+s.forecast_derivative(w, h, nu)
    Cd = -s.inner(n, n)/nu+derivative(w, h, nu)
    direction = s.vector_add(s.vector_scale(-nu, Aw), h)
    s.require(Zd == 2*s.inner(Aw, direction)
              and Hd == s.forecast_derivative(w, direction, nu)
              and Cd == derivative(w, direction, nu),
              'all three rates use the complete physical tangent and generated mean')
    s.require(H*H <= 2*Z*C, 'heat-square Cauchy-Schwarz is satisfied by the field')
    return dict(Z=Z, H=H, C=C, Zd=Zd, Hd=Hd, Cd=Cd, g=g, D=D,
                Dfull=s.inner(s.minus_laplacian(u), s.minus_laplacian(u)))


def common_weight(j, beta=Q(8)):
    Z, H, C, Zd, Hd, Cd = (j[k] for k in ('Z', 'H', 'C', 'Zd', 'Hd', 'Cd'))
    s.require(Z > 0 and C >= 0 and beta >= 8, 'nondegenerate normalized reserve')
    den = Z+beta*C
    weight = Z/den
    weight_rate = beta*(C*Zd-Z*Cd)/den**2
    value = Z/2+weight*(H+C)
    rate = Zd/2+weight*(Hd+Cd)+weight_rate*(H+C)
    by_partials = ((Q(1, 2)+beta*C*(H+C)/den**2)*Zd
                   +weight*Hd+Z*(Z-beta*H)*Cd/den**2)
    s.require(rate == by_partials, 'complete weight derivative agrees with both partial derivatives')
    s.require(Z/4 <= value <= 7*Z/8, 'common normalization remains enstrophy coercive')
    return value, rate, weight_rate*(H+C)


def square_root_failure():
    u = s.vector_scale(Q(100), s.real_field(s.seed()))
    j = physical_jet(u)
    Z, C, H = j['Z'], j['C'], j['H']
    den, theta_sq = Z+8*C, Z/(Z+8*C)
    rational = (Q(1, 2)+8*C*C/den**2)*j['Zd']+theta_sq**2*j['Cd']+2*j['g']-j['Dfull']/2
    radical_coefficient = j['Hd']+4*H*C*j['Zd']/(Z*den)-4*H*j['Cd']/den
    target = j['Dfull']
    s.require(H == j['g'] == 0 and radical_coefficient > 0 and rational < 0,
              'the failing seed has no current stretching or signed heat forecast')
    s.require(radical_coefficient**2*theta_sq > (target-rational)**2,
              'exact radical comparison: square-root payment excess exceeds full dissipation')
    return {'amplitude': 100, 'excess_gt_full_dissipation': True,
            'forecast_and_stretching_zero': True}


def initial_generation_certificate(u, full=False):
    project = (lambda v: v) if full else s.oscillation
    capacity = rc.capacity if full else s.capacity
    derivative = rc.derivative if full else s.capacity_derivative
    w, h = project(u), project(s.nonlinear(u))
    A = s.minus_laplacian(w)
    Z, D = s.inner(w, A), s.inner(A, A)
    C = capacity(w)
    R, N2 = s.forecast_derivative(w, h), s.inner(project(s.nonlinear(w)), project(s.nonlinear(w)))
    s.require(s.cubic(w) == s.forecast(w) == derivative(w, h) == 0,
              'single vertical band has zero cubic and quintic observations initially')
    s.require(Z > 0 and C > 0 and D > 0, 'nonzero physical seed and source stock')
    c = C/Z
    linear = R-N2-24*c*D
    quadratic = 8*c*R-112*c*c*D
    s.require(linear < 0 and quadratic < 0,
              'the initial common-weight payment polynomial has negative coefficients')
    s.require(R < 14*c*D, 'quadratic sign persists for every beta at least eight')
    return {'RZ_over_CD': float(R/(c*D)), 'linear': str(linear),
            'quadratic': str(quadratic), 'all_amplitudes_and_viscosities': True}


def scaled_initial_checks(u):
    A = s.minus_laplacian(u)
    Z, D = s.inner(u, A), s.inner(A, A)
    c = s.capacity(u)/Z
    R = s.forecast_derivative(u, s.oscillation(s.nonlinear(u)))
    n = s.oscillation(s.nonlinear(u))
    N2 = s.inner(n, n)
    for amplitude, frequency, nu, beta in ((Q(1), 1, Q(1), Q(8)),
                                          (Q(100), 2, Q(2, 7), Q(8)),
                                          (Q(1000), 3, Q(3, 2), Q(16))):
        v = s.vector_scale(amplitude, s.dilation(u, frequency))
        j = physical_jet(v, nu)
        _, rate, weight_term = common_weight(j, beta)
        s.require(rate+2*j['g'] < nu*j['Dfull']/2,
                  'actual initial payment for the complete scaled field')
        r = (amplitude/(nu*frequency))**2
        polynomial = (-Q(3, 2)*D+r*(R-N2-3*beta*c*D)
                      +r*r*(beta*c*R-beta*(Q(3, 2)*beta+2)*c*c*D))
        excess = (rate+2*j['g']-nu*j['Dfull']/2)/(nu*amplitude**2*frequency**4)
        s.require(excess*(1+beta*c*r)**2 == polynomial,
                  'scaled physical rate equals the claimed initial-payment polynomial')
        s.require(weight_term != 0, 'the changing normalization is not silently frozen')


def independent_tangent_check():
    u = s.real_field(s.seed())
    u = s.vector_add(u, s.vector_scale(Q(1, 10), s.nonlinear(u)))
    nu = Q(2, 7)
    direction = s.vector_add(s.nonlinear(u), s.vector_scale(-nu, s.minus_laplacian(u)))
    observations = {}
    for k in (-2, -1, 1, 2):
        w = s.oscillation(s.vector_add(u, s.vector_scale(k, direction)))
        observations[k] = (s.inner(w, s.minus_laplacian(w)), s.forecast(w, nu), s.capacity(w, nu))
    polarized = tuple((8*(observations[1][i]-observations[-1][i])
                       -observations[2][i]+observations[-2][i])/12 for i in range(3))
    j = physical_jet(u, nu)
    s.require(polarized == (j['Zd'], j['Hd'], j['Cd']),
              'independent polynomial polarization retains the full generated-mean tangent')
    s.require(any(s.vertical_mean(u)) and any(s.vertical_mean(direction)),
              'neither the existing nor the changing mean is omitted')
    _, _, weight_term = common_weight(j)
    s.require(weight_term != 0, 'the tested observer genuinely evolves')


def full_history_seed():
    u = s.real_field(s.seed())
    h = s.nonlinear(u)
    generation = linear_cubic_term(u, h)
    s.require(generation == Q(892051, 1092000) > 0,
              'the complete physical nonlinearity generates positive stretching')
    s.require(linear_cubic_term(u, s.vector_scale(-1, s.minus_laplacian(u))) == 0,
              'viscosity does not change the zero initial cubic observation to first order')
    certificate = initial_generation_certificate(u, full=True)
    packets = []
    limit = generation*rc.envelope_moment(4)
    for length in (32, 128):
        v = rc.envelope(u, length)
        f.equal(f.trace(f.jac(v)), {}, 'packet is exactly divergence free')
        generated = linear_cubic_term(v, s.nonlinear(v))
        s.require(s.cubic(v) == s.forecast(v) == rc.derivative(v, s.nonlinear(v)) == 0,
                  'packet retains exact odd-degree zeros and all generated outputs')
        s.require(generated > 0 and abs(generated/limit-1) < Q(1, 20),
                  'positive stretching generation survives the finite curl envelope')
        packets.append({'length': length, 'positive': True,
                        'relative_error': float(generated/limit-1)})
    return {'Euler_stretching_derivative': str(generation),
            'initial_payment': certificate, 'envelopes': packets}


def original_heat_bank():
    u = s.real_field(s.seed())
    # q=exp(-nu*t) is rational at these observation times. Every original
    # heat rate is retained, so this is the original heat history, not NS.
    values = []
    for q in (Q(1), Q(3, 4), Q(1, 2)):
        v = rc.field({k: tuple(q**sum(x*x for x in k)*a for a in z)
                      for k, z in s.modes(u).items()})
        nu = Q(2, 7)
        source_squared = s.inner(s.nonlinear(v), s.nonlinear(v))
        rate = rc.derivative(v, s.vector_scale(-nu, s.minus_laplacian(v)), nu)
        s.require(rate == -source_squared/nu < 0,
                  'the original heat bank spends its source square at every tested age')
        values.append(rc.capacity(v, nu))
    s.require(values[0] > values[1] > values[2] > 0,
              'the original bank decreases without any restart credit')
    return {'source_loss_identity': True, 'three_ages_strictly_decrease': True,
            'scope': 'original heat bank; actual first-burst domination is analytic'}


def main():
    root_failure = square_root_failure()
    seed = s.real_field(s.seed())
    initial = {'seed': initial_generation_certificate(seed)}
    scaled_initial_checks(seed)
    for length in (2, 16, 32):
        initial[f'belt_{length}'] = initial_generation_certificate(planar_belt(length))
    independent_tangent_check()
    history_seed = full_history_seed()
    bank = original_heat_bank()
    print(json.dumps({'status': 'all exact checks passed',
                      'square_root_failure': root_failure,
                      'common_weight_initial_certificates': initial,
                      'actual_history_seed': history_seed,
                      'original_heat_bank': bank,
                      'scope': 'finite algebra; localized positive-viscosity history comparison is analytic'},
                     indent=2))


if __name__ == '__main__':
    main()
