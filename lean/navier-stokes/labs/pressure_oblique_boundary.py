#!/usr/bin/env python3
"""The complete cancellation boundary of an oblique pressure-history stock.

Translation symmetry, analytic pressure divisibility and homogeneous degree
justify the six-term parent basis; interpolation alone does not prove it.
Two unused cases check every reconstructed time coefficient. The analytic
actual-flow transfer and its small-amplitude restriction are in README.md.
"""

import argparse
from fractions import Fraction as Q
import json
import time

import sympy as s

import paired_stretching_history as e
from pressure_oblique_next_return import assemble as cancelled_case, case_weights
from pressure_oblique_return import require


FIT = ((1, 1, 1), (2, 1, 1), (3, 1, 1), (1, 2, 1), (1, 3, 1), (1, 1, 2))
UNUSED = ((4, 1, 1), (1, 1, 3))
CASES = FIT + UNUSED


def basis(weights):
    a, b, c = weights
    return (a**4, b**4, c**4, a*a*b*b, a*a*c*c, b*b*c*c)


def assemble(cases):
    require(len(cases) == len(CASES)
            and {tuple(row['weights']) for row in cases} == set(CASES),
            'Six physical interpolation cases and two distinct unused cases')
    fields = {tuple(row['weights']):
              {int(n): {(r, j): Q(c) for r, j, c in values}
               for n, values in row['normalized'].items()} for row in cases}
    leading = fields[(1, 1, 1)][12]
    for row in fields.values():
        require(set(row) == set(range(12, 17)) and not row[13] and not row[15],
                'All requested degrees and exact odd-amplitude symmetry')
        require(row[12] == leading, 'The complete joint-factor leading profile')
        require(all(r >= 0 and j >= 0 and (r > 0 or j == 0)
                    for n in (12, 14, 16) for r, j in row[n]),
                'Every complete coefficient has a finite infinite-time limit')

    base = fields[(1, 1, 1)][14]
    parents = [e.scale(Q(1, 3), e.add(fields[w][14], e.scale(-1, base)))
               for w in ((2, 1, 1), (1, 2, 1))]
    parents.append(e.add(base, *(e.scale(-1, v) for v in parents)))
    for weights, row in fields.items():
        require(row[14] == e.add(*(e.scale(a*a, v) for a, v in zip(weights, parents))),
                'The entire lower parent polynomial, including unused histories')
    beta = [v.get((0, 0), Q(0)) for v in parents]
    require(beta[0] > 0 and beta[1] < 0 and beta[2] < 0,
            'The exact signs of the first integrated parent correction')
    rb, rc = -beta[1]/beta[0], -beta[2]/beta[0]

    matrix = s.Matrix([basis(w) for w in FIT])
    inverse = matrix.inv()
    require(matrix*inverse == s.eye(6), 'Exact inverse of the justified six-term basis')
    quartic = [e.add(*(e.scale(Q(str(inverse[i, j])), fields[w][16])
                       for j, w in enumerate(FIT))) for i in range(6)]
    for weights, row in fields.items():
        require(row[16] == e.add(*(e.scale(v, f) for v, f in zip(basis(weights), quartic))),
                'Every time coefficient agrees, including both unused cases')

    A, B, C, D, E, F = quartic
    boundary = [e.add(e.scale(rb*rb, A), B, e.scale(rb, D)),
                e.add(e.scale(2*rb*rc, A), e.scale(rc, D), e.scale(rb, E), F),
                e.add(e.scale(rc*rc, A), C, e.scale(rc, E))]
    limits = [v.get((0, 0), Q(0)) for v in boundary]
    brackets = [(Q(-81027, 10**20), Q(-81026, 10**20)),
                (Q(-21431, 10**20), Q(-21430, 10**20)),
                (Q(-17829, 10**22), Q(-17828, 10**22))]
    require(all(lo < v < hi < 0 for v, (lo, hi) in zip(limits, brackets)),
            'All three boundary coefficients have exact strictly negative brackets')

    # Negative integrated degree sixteen is insufficient if degree fourteen
    # has a slower positive tail. Check the complete boundary's late sign.
    tail = parents[0].get((6, 0), Q(0))
    require(tail < 0 and {(r, j): c for (r, j), c in parents[0].items() if r == 6}
            == {(6, 0): tail}, 'The first parent has a strictly negative rate-six tail')
    require(all(r == 0 or r >= 6 for v in parents for r, j in v)
            and all(r != 6 for v in parents[1:] for r, j in v),
            'No competing term at this or a slower positive decay rate')
    first_boundary = [e.add(e.scale(rb, parents[0]), parents[1]),
                      e.add(e.scale(rc, parents[0]), parents[2])]
    require(all(not v.get((0, 0), Q(0)) for v in first_boundary),
            'The entire first integrated boundary correction cancels')
    previous = cancelled_case([dict(a=row['weights'][0], normalized=row['normalized'])
                               for row in cases if tuple(row['weights'][1:]) == (1, 1)])
    require(rb+rc == Q(previous['a_squared'])
            and e.add(*boundary) == {(r, j): Q(c) for r, j, c in previous['next_profile']}
            and sum(limits) == Q(previous['gamma']),
            'The earlier cancellation shape agrees in every time coefficient')
    return dict(status='Complete cancellation boundary is strictly depleting',
                fit=FIT, unused=UNUSED, alpha=str(leading.get((0, 0), Q(0))),
                beta=list(map(str, beta)), boundary_coordinates=list(map(str, (rb, rc))),
                quartic_profiles=list(map(e.encode, quartic)),
                boundary_profiles=list(map(e.encode, boundary)),
                boundary_coefficients=list(map(str, limits)),
                boundary_brackets=[list(map(str, pair)) for pair in brackets],
                first_parent_tail=str(tail),
                scope='Exact complete viscous coefficients. All-time payment uses the analytic small-data remainder.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    choice = parser.add_mutually_exclusive_group()
    choice.add_argument('--weights', type=int, nargs=3, metavar=('A', 'B', 'C'),
                        help='Compute one of the eight specified complete histories')
    choice.add_argument('--assemble', nargs=8, metavar='JSON',
                        help='Combine eight saved --weights outputs, in any order')
    args = parser.parse_args()
    start = time.monotonic()
    if args.weights is not None:
        require(tuple(args.weights) in CASES, 'A specified interpolation or unused physical case')
        result = case_weights(tuple(args.weights))
    elif args.assemble:
        records = []
        for path in args.assemble:
            with open(path) as source:
                records.append(json.load(source))
        result = assemble(records)
    else:
        result = assemble([case_weights(weights) for weights in CASES])
    result['elapsed'] = time.monotonic()-start
    print(json.dumps(result, indent=2), flush=True)
