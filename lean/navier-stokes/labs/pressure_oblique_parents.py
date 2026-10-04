#!/usr/bin/env python3
"""Joint parent strengths in the oblique pressure-history return.

The complete Fourier recurrences retain pressure and every generated mode.
Initial time coefficients and integrated viscous amplitude coefficients are
separate observations. Neither is an arbitrary-amplitude payment theorem.
The polynomial identification uses the symmetries and triangular vanishing
described in README.md, with unused fixtures checking the calculation.
"""

import argparse
from fractions import Fraction as Q
import json
from math import factorial, prod

import pressure_history_source as f
from cyclic_pressure_history import velocity_time_jets
from pressure_impulse_return import (impulse_fourth_coefficients, material_fourth_coefficients,
                                    specialize)
from pressure_oblique_return import cubic_forecast_jets, require, wave


def datum(weights):
    a, b, c = weights
    return [f.add(f.scale(a, wave((0, 1, 0))), f.scale(-4*b, wave((0, 0, 1)))),
            f.scale(b, wave((0, 0, 1))), f.scale(c, wave((1, 4, 0)))]


def joint_factor(weights):
    value = Q(prod(weights))**4
    require(value > 0, 'Nonzero parent strengths for the normalized observation')
    return value


def time_coefficient(weights, independent=False):
    """Normalized t^10 coefficient in the Euler calibration, not a stock."""
    initial = datum(weights)
    f.equal(f.trace(f.jac(initial)), {}, 'Physical solenoidal initial datum')
    velocity, pressure = velocity_time_jets(initial, Q(0), 4)
    require(not pressure[0], 'Canonical initial pressure is zero')
    gradient = [f.grad(p) for p in pressure]
    coefficients = material_fourth_coefficients(velocity, gradient)
    require(not coefficients[1] and all(not a.y for a in coefficients),
            'Real pressure-history coefficients with vanishing odd time coefficient')
    if independent:
        require(coefficients == impulse_fourth_coefficients(velocity, gradient, Q(0)),
                'Independent conditional moment PDE agrees with complete material jets')
    return Q(str(coefficients[2].x))/joint_factor(weights)


def identify(base, doubled_a, doubled_b):
    """Coefficients in the already justified even homogeneous quadratic basis."""
    a, b = (doubled_a-base)/3, (doubled_b-base)/3
    return a, b, base-a-b


def evaluate(parts, weights):
    return sum(d*w*w for d, w in zip(parts, weights))


def initial_checks():
    triples = [(1, 1, 1), (2, 1, 1), (1, 2, 1)]
    parts = identify(*(time_coefficient(w) for w in triples))
    expected = (Q(26318361166557175, 2420399620275918336),
                Q(-5376840697027201, 3059844721195046400),
                Q(-47651626133272979, 7818859471173087744))
    require(parts == expected, 'Exact signed parent contributions')
    for weights in [(1, 1, 2), (2, 3, 1)]:
        observed = time_coefficient(weights, independent=weights == (1, 1, 2))
        require(observed == evaluate(parts, weights), 'Unused full physical parent-weight fixture')
    for weights, nu in [((1, 1, 2), Q(2, 7)), ((2, 3, 1), Q(5, 9))]:
        initial = datum(weights)
        velocity, pressure = velocity_time_jets(initial, nu, 4)
        actual = impulse_fourth_coefficients(velocity, [f.grad(p) for p in pressure], nu)
        forecast = [specialize(p, nu) for p in cubic_forecast_jets(initial)]
        reference = impulse_fourth_coefficients([[{}, {}, {}] for _ in range(5)],
                                               [f.grad(p) for p in forecast], nu)
        require([a-b for a, b in zip(actual, reference)]
                == [f.ZERO, f.ZERO, f.QQ_I(joint_factor(weights)*evaluate(parts, weights))],
                'Positive-viscosity physical moments minus the matched viscous forecast')
    # Check the translation action directly on the original Fourier fields.
    original = datum((2, 3, 5))
    for index, shift in enumerate([(0, 1, 0), (0, 0, 1), (1, 0, 0)]):
        changed = [2, 3, 5]
        changed[index] *= -1
        translated = [{q: value*(1 if sum(k*s for k, s in zip(q, shift)) % 2 == 0 else -1)
                       for q, value in field.items()} for field in original]
        for a, b in zip(translated, datum(changed)):
            f.equal(a, b, 'Half-period translation reverses just one parent')
    # These finite jets check the literal triangular solutions explained
    # in the derivation; finite jets alone would not prove all-time vanishing.
    for weights in [(0, 3, 5), (2, 0, 5), (2, 3, 0)]:
        _, pressure = velocity_time_jets(datum(weights), Q(2, 7), 4)
        require(all(not p for p in pressure), 'Pressure-free triangular coordinate-plane jets')
    return dict(status='Exact joint initial-return coefficients checked',
                coefficients=list(map(str, parts)), signs=[1, -1, -1],
                scope='Euler calibration and positive-viscosity comparison jets; not an integrated allowance')


def viscous_history(weights, alpha):
    """Normalized degree-fourteen coefficient over the whole viscous clock."""
    import paired_stretching_history as e
    from pressure_impulse_payment import history_from_fields
    initial = datum(weights)
    modes = set().union(*initial)
    heat = {q: tuple({(sum(k*k for k in q), 0): Q(str(row[q].y))}
                     if q in row else {} for row in initial) for q in modes}
    velocity, _, pressure = e.evolve_amplitudes(heat, 5)
    require(not pressure[2], 'Complete quadratic heat pressure vanishes')
    coefficients = history_from_fields(velocity, pressure)
    require(all(rate > 0 or power == 0 for degree in (12, 14)
                for rate, power in coefficients[degree]),
            'The complete retained coefficients have finite limits at infinite viscous time')
    scale = joint_factor(weights)
    require(coefficients[12].get((0, 0), Q(0)) == scale*alpha,
            'Complete leading stock retains the joint parent factor')
    return e.scale(1/scale, coefficients[14])


def cancellation_checks(cancellation):
    """Exact early depletion and late recovery of the same time profile."""
    import paired_stretching_history as e
    profile = {(rate, power): Q(value) for rate, power, value in cancellation['history']}
    require(Q(cancellation['a_squared']) > 0 and profile,
            'A nonzero cancellation history with three nonzero parents')
    require(not profile.get((0, 0), Q(0)) and all(rate > 0 for rate, _ in profile),
            'The integrated correction vanishes with no nondecaying remainder')
    require(all(e.jet(profile, n) == 0 for n in range(10)),
            'Every earlier time coefficient vanishes')
    early = e.jet(profile, 10)/factorial(10)
    rate = min(r for r, _ in profile)
    require(rate == 6 and all(power == 0 for r, power in profile if r == rate),
            'The slowest remaining exponential has rate six and no polynomial prefactor')
    tail = profile[(rate, 0)]
    require(early < 0 and tail < 0, 'Initial depletion and approach to zero from below')
    derivative = e.derivative(profile)
    require(derivative[(rate, 0)] == -rate*tail > 0,
            'The full profile eventually has strictly positive time derivative')
    return dict(initial_time_order=10, initial_coefficient=str(early),
                late_rate=rate, late_coefficient=str(tail),
                late_derivative_coefficient=str(-rate*tail),
                scope='Signs of the complete amplitude coefficient; actual-flow transfer uses a separate remainder')


def integrated_checks():
    import paired_stretching_history as e
    from pressure_oblique_stock import check
    stock = check()
    alpha, beta = Q(stock['original_stock']), Q(stock['additional_stock'])
    base = {(rate, power): Q(value) for rate, power, value in stock['fields']['14']}
    histories = [e.scale(Q(1, 3), e.add(viscous_history(weights, alpha), e.scale(-1, base)))
                 for weights in [(2, 1, 1), (1, 2, 1)]]
    histories.append(e.add(base, *(e.scale(-1, v) for v in histories)))
    require(viscous_history((1, 1, 2), alpha)
            == e.add(histories[0], histories[1], e.scale(4, histories[2])),
            'Unused complete viscous history checks every time coefficient of the parent polynomial')
    parts = tuple(v.get((0, 0), Q(0)) for v in histories)
    require(sum(parts) == beta, 'The original integrated correction is recovered')
    cancellation = None
    if parts[0]:
        ratio = -(parts[1]+parts[2])/parts[0]
        if ratio > 0:
            remainder = e.add(e.scale(ratio, histories[0]), histories[1], histories[2])
            require(not remainder.get((0, 0), Q(0)), 'The selected ratio cancels the integrated correction')
            cancellation = dict(a_squared=str(ratio), history=e.encode(remainder))
            if remainder:
                rate = min(r for r, _ in remainder)
                power = max(p for r, p in remainder if r == rate)
                cancellation['leading_tail'] = dict(rate=rate, power=power,
                                                    coefficient=str(remainder[(rate, power)]))
            cancellation['checks'] = cancellation_checks(cancellation)
    return dict(status='Exact integrated joint-parent coefficients checked',
                original_normalized_stock=str(alpha), coefficients=list(map(str, parts)),
                signs=[(a > 0)-(a < 0) for a in parts],
                cancellation=cancellation, histories=list(map(e.encode, histories)),
                scope='Viscous amplitude coefficients; higher returns and the actual-flow remainder are separate')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--integrated', action='store_true',
                        help='Also recompute the complete viscous history and its independent unit stock')
    args = parser.parse_args()
    print(json.dumps(initial_checks(), indent=2), flush=True)
    if args.integrated:
        print(json.dumps(integrated_checks(), indent=2), flush=True)
