#!/usr/bin/env python3
"""Complete pressure-gradient costs through the first nonlinear return.

All viscous amplitude histories and Fourier outputs are retained. Exact
exponential-polynomial integration has no time grid. The analytic uniform
remainder in README.md is required for every actual all-time payment claim.
This checker is not a Lean certificate or a finite-mode NS solution.
"""

import hashlib
import json
from fractions import Fraction as Q
from math import factorial, prod

import paired_stretching_history as e
import pressure_history_source as f
from cyclic_pressure_history import velocity_time_jets
from pressure_adaptive_storage import avg
from pressure_impulse_payment import signed_cascade
from pressure_impulse_return import viscosity_jets
from pressure_oblique_return import cubic_forecast_jets, datum, wave


def weighted_datum(m, weights):
    a, b, c = weights
    return [f.add(f.scale(a, wave((0, 1, 0))), f.scale(-m*b, wave((0, 0, 1)))),
            f.scale(b, wave((0, 0, 1))), f.scale(c, wave((1, m, 0)))]


def pressure_pair(p, q):
    """Literal spatial gradient pairing, using opposite Fourier modes."""
    return e.add(*(e.scale(sum(x*x for x in k),
                          e.multiply(v, q.get(tuple(-x for x in k), {})))
                   for k, v in p.items()))


def histories(m, weights=(Q(1), Q(1), Q(1)), independent=False):
    initial = weighted_datum(m, weights)
    f.equal(f.trace(f.jac(initial)), {}, 'Actual solenoidal original parents')
    modes = set().union(*initial)
    heat = {q: tuple({(sum(k*k for k in q), 0): Q(str(row[q].y))}
                     if q in row else {} for row in initial) for q in modes}
    velocity, _, pressure = e.evolve_amplitudes(heat, 5)
    e.require(not pressure[2], 'The whole quadratic heat pressure vanishes')
    for level in pressure:
        e.require(all(level.get(tuple(-x for x in k)) == value for k, value in level.items()),
                  'Real even canonical pressure at every retained amplitude degree')
    if independent:
        literal, literal_p = velocity_time_jets(initial, Q(1), 4)
        for n in range(4):
            for i in range(3):
                field = f.add(*({q: f.II*f.QQ_I(e.jet(a[i], n)) for q, a in level.items()}
                                for level in velocity[1:]))
                f.equal(field, literal[n][i], 'Independent full NS velocity time derivatives')
            field = f.add(*({q: f.QQ_I(e.jet(a, n)) for q, a in level.items()}
                            for level in pressure[1:]))
            f.equal(field, literal_p[n], 'Independent full canonical pressure time derivatives')
    leading = pressure_pair(pressure[3], pressure[3])
    odd = e.scale(2, pressure_pair(pressure[3], pressure[4]))
    born = pressure_pair(pressure[4], pressure[4])
    returned = e.scale(2, pressure_pair(pressure[3], pressure[5]))
    e.require(not odd, 'Translation parity removes the entire odd-degree time profile')
    return leading, born, returned


def accumulated(rate):
    value = e.heat_convolution(rate, 0)
    e.require(e.derivative(value) == rate and e.jet(value, 0) == 0,
              'The cost starts only once and keeps its complete rate')
    e.require(value.get((0, 0), Q(0)) == e.integral_infinity(rate),
              'Independent antiderivative and half-line integral agree')
    return value


def fingerprint(profile):
    return hashlib.sha256(json.dumps(e.encode(profile), separators=(',', ':')).encode()).hexdigest()


def basic_checks():
    rows, profiles = [], {}
    expected = {0: Q(-38219, 24576000),
                1: Q(-175983211031, 619636469760000),
                2: Q(17557198287809721676707083, 177077463696816376920145920000),
                4: Q(357921113113644286739772839106768698810618863,
                     1617418565719323850646018594609421413095833600000000)}
    for m in (0, 1, 2, 4):
        leading, born, returned = histories(m, independent=m in (2, 4))
        correction = e.add(born, returned)
        A, B = accumulated(leading), accumulated(correction)
        alpha, beta = e.integral_infinity(leading), e.integral_infinity(correction)
        e.require(alpha > 0 and beta == expected[m], 'Exact full-time original and correction stocks')
        certificate = signed_cascade(correction, -1 if m < 2 else 1) if m != 2 else None
        first = e.jet(correction, 4)/factorial(4)
        e.require(all(e.jet(correction, n) == 0 for n in range(4)),
                  'No earlier physical return is omitted')
        if m == 2:
            e.require(alpha == Q(1901, 1960200) and first == Q(-1843, 304920) and beta > 0,
                      'Early depletion is followed by a strictly adverse total correction')
            e.require(e.jet(B, 5)/factorial(5) == Q(-1843, 1524600),
                      'Exact initially negative accumulated return')
            slow = min(rate for rate, _ in correction)
            e.require(slow == 4 and correction[(4, 0)] == Q(1, 1152)
                      and all(power == 0 for rate, power in correction if rate == 4),
                      'A retained slow source supplies the positive late tail')
        rows.append(dict(m=m, original_stock=str(alpha), complete_correction=str(beta),
                         source_birth=str(e.integral_infinity(born)),
                         original_return=str(e.integral_infinity(returned)),
                         first_rate_coefficient=str(first), sign_certificate=certificate,
                         correction_profile_sha256=fingerprint(correction)))
        profiles[m] = leading, correction
    return rows, profiles


def initial_viscous_comparison():
    """Independent whole-viscosity check of the m=2 early physical sign."""
    initial = datum(2)
    _, p = viscosity_jets(initial, 4)
    pc = cubic_forecast_jets(initial)
    def coefficients(p):
        g = [f.grad(a) for a in p]
        return [avg(f.dot(g[1], g[1])), avg(f.dot(g[1], g[2])),
                avg(f.dot(g[2], g[2]))/4+avg(f.dot(g[1], g[3]))/3]
    import sympy as s
    delta = [s.factor(a-b) for a, b in zip(coefficients(p), coefficients(pc))]
    e.require(delta == [0, 0, -s.Rational(1843, 304920)],
              'Actual-minus-cubic pressure cost has the same early sign at every viscosity')
    return list(map(str, delta))


def family_checks(base):
    """The basis is justified analytically by degree, symmetry and pair solutions."""
    def normalized(weights):
        a, born, returned = histories(4, weights)
        factor = Q(prod(weights))**2
        e.require(factor > 0, 'Nonzero weights for normalized coefficient checks')
        e.require(e.scale(1/factor, a) == base[0], 'Same joint cubic forecast factor')
        return e.scale(1/factor, e.add(born, returned))
    doubled_a, doubled_b = normalized((2, 1, 1)), normalized((1, 2, 1))
    pa = e.scale(Q(1, 3), e.add(doubled_a, e.scale(-1, base[1])))
    pb = e.scale(Q(1, 3), e.add(doubled_b, e.scale(-1, base[1])))
    pc = e.add(base[1], e.scale(-1, pa), e.scale(-1, pb))
    parents = pa, pb, pc
    for weights in ((1, 1, 2), (2, 3, 1), (Q(1, 4), Q(1), Q(1))):
        e.require(normalized(weights) == e.add(*(e.scale(x*x, h) for x, h in zip(weights, parents))),
                  'Unused joint-parent fixture checks the entire time profile')
    certificates = [signed_cascade(p, sign) for p, sign in zip(parents, (1, -1, -1))]
    beta = [e.integral_infinity(p) for p in parents]
    ratio = -(beta[1]+beta[2])/beta[0]
    e.require(Q(8616, 100000) < ratio < Q(8617, 100000),
              'Exact joint-parent integrated cancellation boundary')
    e.require(beta[0]/16+beta[1]+beta[2] < 0,
              'One-quarter first parent has a strictly favorable full correction')
    # Previously established impulse boundary is below this rational value.
    # This arithmetic does not recompute that separate stochastic observation.
    e.require(Q(392, 10000) < Q(1, 16) < ratio,
              'The selected shape lies between the two established boundary ranges')
    # Check literal parent reversals and the finite jets of the separately
    # justified all-time pressure-free triangular coordinate-plane solutions.
    original = weighted_datum(4, (2, 3, 5))
    for index, shift in enumerate(((0, 1, 0), (0, 0, 1), (1, 0, 0))):
        weights = [2, 3, 5]
        weights[index] *= -1
        expected = weighted_datum(4, weights)
        for field, target in zip(original, expected):
            translated = {q: c*(1 if sum(k*d for k, d in zip(q, shift)) % 2 == 0 else -1)
                          for q, c in field.items()}
            f.equal(translated, target, 'Half-period translation reverses only one original parent')
    for weights in ((0, 3, 5), (2, 0, 5), (2, 3, 0)):
        _, p = velocity_time_jets(weighted_datum(4, weights), Q(2, 7), 4)
        e.require(all(not a for a in p), 'Pressure-free coordinate-plane consistency checks')
    # Independent angle/mode formula for the entire cubic stock, with rate19
    # and its two complete output rates11,27. No fitted time data is used.
    independent = Q(0)
    for r in (11, 27):
        independent += (Q(8, 38**3)+Q(4, 19-r)*(Q(1, (19+r)**2)-Q(1, 38**2))
                        +Q(1, (19-r)**2)*(Q(1, 2*r)-Q(2, 19+r)+Q(1, 38)))/Q(4*r)
    e.require(independent == e.integral_infinity(base[0]) == Q(116161, 9332512200),
              'Independent cubic pressure-mode integration recovers the leading stock')
    return dict(original_stock=str(independent), parent_corrections=list(map(str, beta)),
                profile_certificates=certificates, profile_sha256=list(map(fingerprint, parents)),
                cancellation_a_squared=str(ratio),
                quarter_parent_correction=str(beta[0]/16+beta[1]+beta[2]),
                uniform_payment='C(T)<=(abc)^2[A+beta_a*a^2+beta_b*b^2+beta_c*c^2+M*(a^2+b^2+c^2)^2]',
                limitation='A common small-data radius and remainder M are analytic, not numerically evaluated')


def tail_constants():
    """Scalar constants for the separate analytic Fourier and NS tail proof."""
    import sympy as s
    n = s.Symbol('n', integer=True, positive=True)
    shells = s.expand((2*n+1)**3-(2*n-1)**3)
    e.require(s.expand(26*n*n-shells) == 2*(n*n-1),
              'Each nonzero integer cube shell has at most 26*n^2 modes')
    e.require(Q(26)*Q(25, 4) < 13**2,
              'sqrt(2)<3/2 makes the Fourier Agmon constant strictly below 13')
    e.require(Q(13, 26) == Q(1, 2) and 13**2 == 169,
              'The entry threshold absorbs half the enstrophy dissipation')
    return dict(entry='||grad u(T)||2<=nu/26',
                tail='integral_T^infinity ||grad p||2^2<=169*||grad u(T)||2^4/nu',
                scope='Fourier shell algebra checked; analytic Agmon, NS and continuation arguments in README.md')


if __name__ == '__main__':
    cases, profiles = basic_checks()
    print(json.dumps(dict(status='All exact checks passed', fixtures=cases,
                          full_viscosity_early_comparison=initial_viscous_comparison(),
                          family=family_checks(profiles[4]),
                          tail=tail_constants(),
                          scope='Complete amplitude histories; actual all-time payment uses a separate uniform analytic remainder',
                          limitation='Small-data regime; no arbitrary-data payment, singularity construction or new Lean certificate'), indent=2))
