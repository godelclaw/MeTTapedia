#!/usr/bin/env python3
"""Exact lower envelopes for scalar pressure schedules in the unit interval.

The complete NS amplitude histories come from joint_generated_pressure.
Positive convolution kernels certify a bound for all measurable weights
in [0,1], including choices that know the future. The uniform actual-flow
remainder and finite-prefix implication are analytic in README.md.
"""

import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path

import paired_stretching_history as e
from joint_generated_pressure import pressure_profiles
from pressure_gradient_stock import fingerprint


def cascade_parts(profile):
    """Reconstruct the profile from nonnegative exponential convolutions.

    If f_(j+1)=(d/dt+r_j)f_j and d_j=f_j(0), then f_0 is the sum
    of d_j times the convolution of exp(-r_i*t), 0<=i<=j. The terminal
    profile is zero. This identity is checked exactly, not sampled.
    """
    rates = [r for r in sorted({r for r, _ in profile}, reverse=True)
             for _ in range(1+max(j for rr, j in profile if rr == r))]
    e.require(rates and all(r > 0 for r in rates), 'Every kernel decays')
    current, kernel, positive, negative = profile, {}, {}, {}
    data, negative_stages = [], []
    product = 1
    positive_mass, negative_mass = Q(0), Q(0)
    for n, rate in enumerate(rates):
        kernel = {(rate, 0): Q(1)} if n == 0 else e.heat_convolution(kernel, rate)
        product *= rate
        e.require(e.integral_infinity(kernel) == Q(1, product),
                  'The convolution mass is the product of reciprocal rates')
        coefficient = e.jet(current, 0)
        data.append((rate, str(coefficient)))
        if coefficient >= 0:
            positive = e.add(positive, e.scale(coefficient, kernel))
            positive_mass += coefficient/product
        else:
            negative = e.add(negative, e.scale(-coefficient, kernel))
            negative_mass -= coefficient/product
            negative_stages.append(dict(order=n, coefficient=str(coefficient),
                                        rates=rates[:n+1], mass=str(-coefficient/product)))
        current = e.add(e.derivative(current), e.scale(rate, current))
    e.require(not current, 'The differential cascade terminates identically')
    e.require(e.add(positive, e.scale(-1, negative)) == profile,
              'Positive and negative convolution parts reconstruct every coefficient')
    e.require(e.integral_infinity(positive) == positive_mass
              and e.integral_infinity(negative) == negative_mass,
              'Independent exact integration agrees with both kernel masses')
    certificate = dict(levels=len(rates), positive_mass=str(positive_mass),
                       negative_mass=str(negative_mass), negative_stages=negative_stages,
                       cascade_sha256=hashlib.sha256(json.dumps(data).encode()).hexdigest())
    return positive, negative, certificate


def checks():
    archive = json.loads(Path(__file__).with_name('joint_generated_pressure_results.json').read_text())
    expected = {2: Q(379575675594414491, 69783259618809741312000),
                4: Q(2425387668477001, 199951519253004288000000)}
    rows = []
    for m in (2, 4):
        stock, _, profiles = pressure_profiles(m, (Q(1),)*3)
        original = next(row for row in archive['histories'] if row['m'] == m and row['weights'] == ['1']*3)
        e.require([fingerprint(p) for p in profiles] == original['profile_sha256'],
                  'The full histories agree with the preceding committed archive')
        c, b, a = profiles
        parts = [cascade_parts(p) for p in profiles]
        e.require(not parts[0][1], 'The self-pressure square has a positive convolution certificate')
        bp, bn, _ = parts[1]
        ap, an, _ = parts[2]
        lower = e.add(c, e.scale(-1, bn), e.scale(-1, an))
        # Polynomial identity in theta. Each displayed coefficient multiplies
        # a nonnegative kernel and a nonnegative factor on [0,1].
        certified_coefficients = [e.add(lower, bn, an), e.add(bp, e.scale(-1, bn)),
                                  e.add(ap, e.scale(-1, an))]
        e.require(certified_coefficients == list(profiles),
                  'B(t,theta)-lower=theta*b+ +(1-theta)*b- +theta^2*a+ +(1-theta^2)*a-')
        margin = e.integral_infinity(lower)
        e.require(margin == expected[m] and margin > 0,
                  'Every measurable [0,1] schedule has a strictly positive full-time excess')
        value = e.tail_integral(lower)
        e.require(e.add(e.derivative(value), lower) == {} and e.jet(value, 0) == margin,
                  'The lower value solves its terminal-zero differential equation')
        if m == 4:
            e.require(not bn and not an, 'Every instantaneous coefficient is nonnegative for m4')
        else:
            e.require([row['order'] for row in parts[1][2]['negative_stages']] == [4]
                      and [row['order'] for row in parts[2][2]['negative_stages']] == [4],
                      'Only the fourth cascade datum contributes the early negative work')
            e.require(margin > Q(997, 1000)*e.integral_infinity(c),
                      'Even optimal timing cannot cancel more than three tenths of one percent of the self cost')
        rows.append(dict(m=m, leading_stock=str(stock), certificates=[part[2] for part in parts],
                         self_pressure_cost=str(e.integral_infinity(c)),
                         uniform_excess_lower_bound=str(margin), approximate_lower_bound=float(margin),
                         lower_profile_sha256=fingerprint(lower), value_profile_sha256=fingerprint(value),
                         weight_class='every measurable theta:[0,infinity)->[0,1]'))
    return dict(histories=rows,
                scope='Exact complete coefficients and convolution certificates; uniform actual NS and finite-time conclusions are analytic')


if __name__ == '__main__':
    print(json.dumps(checks(), indent=2))
