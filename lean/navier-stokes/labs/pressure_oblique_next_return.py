#!/usr/bin/env python3
"""The complete next pressure return at a cancelled first integrated correction.

The even parent polynomial is justified by translation symmetry and the
pressure-free coordinate planes described in README.md. A fourth parent
value checks the entire reconstructed time profile. These are exact
amplitude coefficients; an actual-flow statement also needs a remainder.
"""

import argparse
from fractions import Fraction as Q
import json
from math import factorial
import time

import paired_stretching_history as e
import pressure_impulse_payment as p
from pressure_moment_observation import observed_history
from pressure_oblique_parents import cancellation_checks, datum, joint_factor
from pressure_oblique_return import require


def physical_fields(weights, degree):
    initial = datum(weights)
    modes = set().union(*initial)
    heat = {q: tuple({(sum(k*k for k in q), 0): Q(str(row[q].y))}
                     if q in row else {} for row in initial) for q in modes}
    velocity, _, pressure = e.evolve_amplitudes(heat, degree-9)
    require(not pressure[2], 'The complete heat-parent pressure vanishes')
    return velocity, pressure


def fixtures():
    """Compare complete lower histories and an established next-order result."""
    for weights in [(1, 1, 1), (2, 1, 1)]:
        velocity, pressure = physical_fields(weights, 14)
        complete = p.history_from_fields(velocity, pressure, 14)
        observed, _ = observed_history(velocity, pressure, 14)
        require(observed == complete,
                'Every observed time coefficient agrees with the unfiltered moment recurrence')
    velocity, _, pressure = e.amplitude_fields((1, 1, 1), order=7, radii=(1, 1, 1))
    observed, _ = observed_history(velocity, pressure, 16)
    higher = observed[16]
    require(all(e.jet(higher, n) == 0 for n in range(12)),
            'Established orthogonal next-return origin order')
    require(e.jet(higher, 12)/factorial(12) == Q(106168693607, 2059433164800),
            'Established independent orthogonal time coefficient')
    require(higher.get((0, 0)) == Q(
        152490621712563288522860694365656656374065925339476309,
        35951541890842638215113438256286222765113462489088000000000),
        'Established complete orthogonal integrated next coefficient')
    return dict(status='Complete lower histories and the established degree-sixteen fixture agree')


def case(a):
    require(a in (1, 2, 3, 4), 'The prepared interpolation and validation parents')
    weights = (a, 1, 1)
    velocity, pressure = physical_fields(weights, 16)
    coefficients, counts = observed_history(velocity, pressure, 16)
    factor = joint_factor(weights)
    normalized = {degree: e.scale(1/factor, value) for degree, value in coefficients.items()}
    return dict(a=a, normalized={str(n): e.encode(v) for n, v in normalized.items()},
                required_modes=counts)


def interpolate(values, nodes, x):
    result = {}
    for node, value in zip(nodes, values):
        weight = Q(1)
        for other in nodes:
            if other != node:
                weight *= (Q(x)-other)/(Q(node)-other)
        result = e.add(result, e.scale(weight, value))
    return result


def assemble(cases):
    require(len(cases) == 4 and sorted(row['a'] for row in cases) == [1, 2, 3, 4],
            'Three interpolation cases and a distinct unused validation case')
    fields = {row['a']: {int(n): {(r, j): Q(c) for r, j, c in value}
                         for n, value in row['normalized'].items()} for row in cases}
    for a, values in fields.items():
        require(set(values) == set(range(12, 17)) and not values[13] and not values[15],
                'All requested degrees and exact odd symmetry are retained')
        require(values[12] == fields[1][12], 'One complete leading history with the joint factor')
        require(all(r > 0 or j == 0 for n in (12, 14, 16) for r, j in values[n]),
                'Finite limits for all complete coefficient histories')
    base, doubled = fields[1][14], fields[2][14]
    parent_a = e.scale(Q(1, 3), e.add(doubled, e.scale(-1, base)))
    other_parents = e.add(base, e.scale(-1, parent_a))
    for a in (3, 4):
        require(fields[a][14] == e.add(e.scale(a*a, parent_a), other_parents),
                'Unused complete history validates the linear parent polynomial')
    beta_a = parent_a.get((0, 0), Q(0))
    require(beta_a > 0, 'A nondegenerate positive first-parent coefficient')
    ratio = -other_parents.get((0, 0), Q(0))/beta_a
    require(Q(3919, 100000) < ratio < Q(3920, 100000),
            'The cancellation ratio agrees with its independently checked bracket')
    previous = e.add(e.scale(ratio, parent_a), other_parents)
    require(not previous.get((0, 0), Q(0)), 'The first integrated correction cancels exactly')
    previous_checks = cancellation_checks(dict(a_squared=str(ratio), history=e.encode(previous)))
    next_values = [fields[a][16] for a in (1, 2, 3)]
    require(interpolate(next_values, (1, 4, 9), 16) == fields[4][16],
            'The unused fourth parent checks EVERY time coefficient of the justified quadratic basis')
    next_profile = interpolate(next_values, (1, 4, 9), ratio)
    gamma = next_profile.get((0, 0), Q(0))
    require(Q(-10264, 10**19) < gamma < Q(-10263, 10**19),
            'Exact strictly negative next integrated return at the cancelled ratio')
    return dict(status='Complete cancelled-ratio next return identified',
                a_squared=str(ratio), alpha=str(fields[1][12].get((0, 0), Q(0))),
                gamma=str(gamma), sign=(gamma > 0)-(gamma < 0),
                cancelled_previous=e.encode(previous), previous_checks=previous_checks,
                next_profile=e.encode(next_profile),
                scope='Exact full viscous amplitude coefficients. Actual-flow payment or failure requires a uniform remainder.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fixtures', action='store_true', help='Only the independent recurrence checks')
    parser.add_argument('--a', type=int, choices=(1, 2, 3, 4), help='Compute one complete parent case')
    parser.add_argument('--assemble', nargs=4, metavar='JSON', help='Combine four saved --a outputs')
    args = parser.parse_args()
    start = time.monotonic()
    if args.fixtures:
        result = fixtures()
    elif args.a is not None:
        result = case(args.a)
    elif args.assemble:
        with_files = []
        for path in args.assemble:
            with open(path) as source:
                with_files.append(json.load(source))
        result = assemble(with_files)
    else:
        fixtures()
        result = assemble([case(a) for a in (1, 2, 3, 4)])
    result['elapsed'] = time.monotonic()-start
    print(json.dumps(result, indent=2), flush=True)
