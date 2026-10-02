#!/usr/bin/env python3
"""Full-source receiver renewal and concentration scalings.

Exact Fourier fixtures retain the entire Leray source, including vertical
mean outputs. The Schwartz packet limit, torus concentration and local NS
interpretation are analytic arguments in README.md, not certified here.
"""

import json
from fractions import Fraction as Q
from math import comb

import coarse_receiver_history as c

s, f = c.s, c.f


def source_blocks(u, v):
    """Full -P div(H_r u tensor H_r v), with original heat rates."""
    result = {}
    for p, a in s.modes(u).items():
        for q, b in s.modes(v).items():
            k = tuple(x+y for x, y in zip(p, q))
            kk = sum(x*x for x in k)
            if not kk:
                continue  # A constant output has zero divergence.
            value = tuple(-f.II*s.dot(a, k)*(b[j]-k[j]*s.dot(k, b)/kk)
                          for j in range(3))
            key = (k, sum(x*x for wave in (p, q) for x in wave))
            old = result.get(key, (f.ZERO,)*3)
            result[key] = tuple(x+y for x, y in zip(old, value))
    return {key: value for key, value in result.items() if any(value)}


def capacity(u, nu=Q(1), q=Q(1)):
    n = source_blocks(u, u)
    if q != 1:
        n = c.filtered_blocks(n, q)
    return s.heat_pair(n, n, nu)


def derivative(u, direction, nu=Q(1), q=Q(1)):
    n = source_blocks(u, u)
    dn = s.add_blocks(source_blocks(u, direction), source_blocks(direction, u))
    if q != 1:
        n, dn = c.filtered_blocks(n, q), c.filtered_blocks(dn, q)
    return 2*s.heat_pair(n, dn, nu)


def field(modes):
    return [{k: a[j] for k, a in modes.items() if a[j]} for j in range(3)]


def cross(a, b):
    return tuple(a[(j+1) % 3]*b[(j+2) % 3]-a[(j+2) % 3]*b[(j+1) % 3]
                 for j in range(3))


def envelope(u, length):
    """curl[(1+cos(x/length)/2) curl(-Delta)^-1 u]."""
    out = {}
    for k, a in s.modes(u).items():
        kk = sum(j*j for j in k)
        potential = tuple(f.II*x/kk for x in cross(k, a))
        for shift, weight in ((-1, Q(1, 4)), (0, Q(1)), (1, Q(1, 4))):
            wave = (k[0]+Q(shift, length), k[1], k[2])
            value = tuple(weight*f.II*x for x in cross(wave, potential))
            old = out.get(wave, (f.ZERO,)*3)
            out[wave] = tuple(x+y for x, y in zip(old, value))
    return field(out)


def envelope_moment(power):
    return sum((Q(comb(power, 2*j)*comb(2*j, j), 16**j)
                for j in range(power//2+1)), Q(0))


def full_identity(u, nu=Q(1)):
    f.equal(f.trace(f.jac(u)), {}, 'solenoidal full input')
    h, Au = s.nonlinear(u), s.minus_laplacian(u)
    collapsed = {}
    for (k, _), a in source_blocks(u, u).items():
        old = collapsed.get(k, (f.ZERO,)*3)
        collapsed[k] = tuple(x+y for x, y in zip(old, a))
    c.same(field(collapsed), h, 'full source includes every pressure and mean output')
    heat = s.vector_scale(-nu, Au)
    s.require(derivative(u, heat, nu) == -s.inner(h, h)/nu,
              'full heat lifetime spends the full source endpoint')
    s.require(s.inner(u, h) == 0, 'unforced kinetic transfers cancel')
    s.require(s.inner(Au, h) == s.cubic(u), 'physical enstrophy identity')
    linear = {(k, sum(j*j for j in k)): tuple(nu*sum(j*j for j in k)*v for v in a)
              for k, a in s.modes(u).items()}
    square = s.add_blocks(linear, source_blocks(u, u))
    value = s.inner(Au, u)/2+s.forecast(u, nu)+capacity(u, nu)
    s.require(value == s.heat_pair(square, square, nu) > 0,
              'full joint storage is the actual nonnegative heat square')
    direction = s.vector_add(heat, h)
    physical = (s.inner(Au, direction)+s.forecast_derivative(u, direction, nu)
                +derivative(u, direction, nu)+2*s.cubic(u))
    split = (-nu*s.inner(Au, Au)-s.inner(h, h)/nu+s.inner(Au, h)
             +s.forecast_derivative(u, h, nu)+derivative(u, h, nu))
    s.require(physical == split,
              'the complete joint-storage derivative keeps every physical term')
    return h


def scaling_check(u, nu, root):
    lam, amplitude = root**2, root**3
    scaled = s.vector_scale(amplitude, s.dilation(u, lam))
    h, scaled_h = s.nonlinear(u), s.nonlinear(scaled)
    jacobian = lam**-3
    Au, scaled_Au = s.minus_laplacian(u), s.minus_laplacian(scaled)
    s.require(jacobian*s.inner(scaled, scaled) == s.inner(u, u),
              'whole-space concentration preserves energy, including the volume factor')
    s.require(jacobian*s.inner(scaled, scaled_Au) == lam**2*s.inner(u, Au),
              'enstrophy concentration scaling')
    s.require(jacobian*s.inner(scaled_Au, scaled_Au) == lam**4*s.inner(Au, Au),
              'dissipation concentration scaling')
    s.require(jacobian*capacity(scaled, nu) == root**6*capacity(u)/nu**2,
              'initial source capacity scales as lambda cubed')
    s.require(jacobian*derivative(scaled, scaled_h, nu)
              == root**11*derivative(u, h)/nu**2,
              'complete quintic renewal scales as lambda to eleven halves')
    s.require(jacobian*s.forecast_derivative(scaled, scaled_h, nu)
              == root**10*s.forecast_derivative(u, h)/nu,
              'quartic forecast renewal is a lower concentration order')
    s.require(jacobian*s.inner(scaled_h, scaled_h) == root**10*s.inner(h, h),
              'the full endpoint source loss has the same quartic order')
    s.require(jacobian*s.cubic(scaled) == root**9*s.cubic(u),
              'physical cubic stretching is retained at its own order')
    fine = derivative(scaled, scaled_h, nu)-derivative(scaled, scaled_h, nu, Q(1, 2))
    total = derivative(scaled, scaled_h, nu)
    s.require(fine > total*Q(999, 1000) > 0,
              'the fixed-cutoff fine part retains the concentrating positive renewal')
    return {'lambda': str(lam), 'nu': str(nu),
            'fine_fraction_gt_999_over_1000': True, 'volume_factor_retained': True}


def polarization_check(u):
    nu = Q(2, 7)
    direction = s.vector_add(s.nonlinear(u), s.vector_scale(-nu, s.minus_laplacian(u)))
    values = {j: capacity(s.vector_add(u, s.vector_scale(j, direction)), nu)
              for j in (-2, -1, 1, 2)}
    central = (8*(values[1]-values[-1])-values[2]+values[-2])/12
    s.require(central == derivative(u, direction, nu),
              'independent exact quartic polarization of the full NS tangent')


def main():
    minus, plus = s.matched_fields()
    hm, hp = full_identity(minus), full_identity(plus)
    coefficient = derivative(minus, hm)
    expected = Q(85124461354557274284120223753665783495727,
                 812632148219367449108260185060000000000000000)
    s.require(coefficient == expected > 0, 'positive full-source coefficient')
    s.require(derivative(plus, hp) == -coefficient,
              'hidden phase reverses the sign even with all outputs retained')
    s.require(s.inner(minus, minus) == s.inner(plus, plus)
              and capacity(minus) == capacity(plus), 'matched energy and initial source capacity')
    s.require(any(s.vertical_mean(hm)) and any(s.vertical_mean(hp)),
              'actual nonlinear directions generate a vertical mean')
    polarization_check(minus)
    rows = [scaling_check(minus, nu, root) for nu, root in ((Q(1), Q(2)), (Q(2, 7), Q(3)))]
    packets = []
    limit = coefficient*envelope_moment(5)
    for length in (32, 128):
        u = envelope(minus, length)
        f.equal(f.trace(f.jac(u)), {}, 'envelope differentiation keeps exact solenoidality')
        value = derivative(u, s.nonlinear(u))
        s.require(value > 0 and abs(value/limit-1) < Q(1, 20),
                  'finite envelope keeps positive renewal near its fifth-moment limit')
        packets.append({'length': length, 'positive': True,
                        'relative_error': float(value/limit-1)})
    print(json.dumps({'status': 'all exact checks passed',
                      'full_source_coefficient': str(coefficient),
                      'concentration_scaling': rows, 'envelopes': packets,
                      'scope': 'finite Fourier algebra; spatial localization and NS intervals are analytic'},
                     indent=2))


if __name__ == '__main__':
    main()
