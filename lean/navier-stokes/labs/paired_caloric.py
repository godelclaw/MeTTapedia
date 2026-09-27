#!/usr/bin/env python3
"""Exact five-input separation by the largest and third-largest shells.

Both parents of the nonlinear direction are retained individually in
the shell labels. This partitions the full source calculation; it does
not evolve a closed subset of Fourier modes.
"""
from fractions import Fraction as F
import json

from fourier_interactions import (A, B, ZERO, dot, pair, project,
                                  radius_squared, require, scale, sine, validate, add)
from caloric_force import mode_source
from separated_caloric import ceiling_three_halves, derivative, dyadic_index, fixture, sector
from inner_caloric import ceiling_eleven_eighths, inner_split


def quadratic_parent_shells(u):
    grouped = {}
    for p, a in u.items():
        for q, b in u.items():
            k = tuple(x+y for x, y in zip(p, q))
            if radius_squared(k) == 0:
                continue
            labels = tuple(sorted((dyadic_index(radius_squared(p)),
                                   dyadic_index(radius_squared(q)))))
            value = project(k, tuple(dot(a, q)*x for x in b))
            key = (k, labels)
            grouped[key] = tuple(x+y for x, y in zip(grouped.get(key, ZERO), value))
    return {key: a for key, a in grouped.items() if any(a)}


def split(u, nu=F(1), output_floor=0, outer_separation=3,
          inner_separation=4, pair_separation=4):
    require(nu > 0 and output_floor >= 0 and pair_separation >= 4,
            'positive viscosity and valid pair parameters')
    cutoff_squared = F(4)**output_floor
    v = {k: a for k, a in u.items() if radius_squared(k) >= cutoff_squared}
    shell = {k: dyadic_index(radius_squared(k)) for k in v}
    grouped = quadratic_parent_shells(v)
    by_output, full_n = {}, {}
    for (k, labels), a in grouped.items():
        by_output.setdefault(k, []).append((labels, a))
        full_n[k] = tuple(x+y for x, y in zip(full_n.get(k, ZERO), a))
    full_n = {k: a for k, a in full_n.items() if any(a)}
    require(full_n == B(v, v), 'two-parent shell grouping retains the complete source')
    totals = {name: F(0) for name in ('inner', 'pair', 'coupled')}
    counts = {name: 0 for name in totals}
    pair_positions = {}
    for p, a in v.items():
        for q, b in v.items():
            if sector(p, q, output_floor, outer_separation) != 'keep':
                continue
            k = tuple(x+y for x, y in zip(p, q))
            source = mode_source(p, a, q, b)
            if not any(source):
                continue
            for ell, c in v.items():
                h = tuple(x-y for x, y in zip(k, ell))
                if radius_squared(h) < cutoff_squared or h not in by_output:
                    continue
                if sector(ell, h, output_floor, outer_separation) != 'keep':
                    continue
                outer_labels = (shell[p], shell[q], shell[ell])
                rate = sum(radius_squared(x) for x in (p, q, ell, h))
                for inner_labels, direction in by_output[h]:
                    tangent = tuple(x+y for x, y in zip(
                        mode_source(ell, c, h, direction),
                        mode_source(h, direction, ell, c)))
                    value = 2*dot(source, tangent)/(nu**2*rate)
                    labels = outer_labels+inner_labels
                    decreasing = sorted(labels, reverse=True)
                    n, m = decreasing[0], decreasing[2]
                    if inner_labels[1] >= ceiling_eleven_eighths(max(outer_labels))+inner_separation:
                        selected = 'inner'
                    elif n >= ceiling_three_halves(m)+pair_separation:
                        selected = 'pair'
                        positions = tuple(i for i, label in enumerate(labels) if label > m)
                        require(len(positions) == 2 and decreasing[1] >= n-1,
                                'exactly two high inputs in adjacent enlarged bands')
                        pair_positions[positions] = pair_positions.get(positions, F(0))+value
                    else:
                        selected = 'coupled'
                    totals[selected] += value
                    counts[selected] += (value != 0)
    high_n = {k: a for k, a in full_n.items() if radius_squared(k) >= cutoff_squared}
    require(sum(totals.values()) == derivative(v, high_n, nu, output_floor, outer_separation),
            'disjoint three-part partition equals the full retained derivative')
    previous, _, _ = inner_split(u, nu, output_floor, outer_separation, inner_separation)
    require(totals['inner'] == previous['far'],
            'inner sector agrees with the independent coarser grouping')
    energy, palinstrophy = pair(v, v), pair(A(v), A(v))
    lattice_constant = F(10**7)
    require(totals['pair']**2 <= lattice_constant**2*F(2)**(-6*pair_separation)
            *energy**3*palinstrophy**2/nu**4,
            'conservative periodic isolated-pair bound')
    return totals, counts, pair_positions


def column_check():
    require(F(80**2*2**9, 6**3*3**6)*F(136, 7)**2 < 100**2,
            'continuum constant using pi greater than three')
    require(80**2*2**9*81**2*3*F(136, 7)**2 < 10**14,
            'conservative periodic constant')
    reports = []
    for separation in (4, 9, 15):
        bound = F(8, 7)*F(2)**(-3*separation)
        ratios = []
        for n in range(95):
            total = sum((F(8)**(ceiling_three_halves(m)-n)
                         for m in range(61)
                         if n >= ceiling_three_halves(m)+separation), F(0))
            require(total <= bound, 'all-pair column sum')
            ratios.append(total/bound)
        reports.append({'separation': separation,
                        'largest_sampled_column_ratio': float(max(ratios))})
    return reports


def field_checks():
    reports = []
    for parameter in (3, 9, 17):
        u = fixture(parameter)
        validate(u)
        for nu in (F(1), F(1, 2)):
            for floor in (0, 2):
                totals, counts, positions = split(u, nu, floor)
                reports.append({'parent_frequency': 2**(parameter+4),
                                'viscosity': str(nu), 'output_floor_index': floor,
                                'returns': {k: str(v) for k, v in totals.items()},
                                'nonzero_ordered_counts': counts,
                                'pair_positions': {str(k): str(v) for k, v in positions.items() if v}})
        positive, _, _ = split(u)
        negative, _, _ = split(scale(F(-1), u))
        require(all(negative[k] == -positive[k] for k in positive),
                'quintic sign reversal in every sector')
        doubled = {k: tuple((2 if dyadic_index(radius_squared(k)) > 2 else 1)*x for x in a)
                   for k, a in u.items()}
        doubled_totals, _, _ = split(doubled)
        require(doubled_totals['inner'] == 4*positive['inner']
                and doubled_totals['pair'] == 4*positive['pair'],
                'two high original inputs in both separated sectors of this fixture')
    return reports


def generated_check():
    from caloric_localization import parents, POSITIVE_COEFFICIENT
    u = parents()
    v = {k: a for k, a in B(u, u).items() if radius_squared(k) >= 16}
    totals, counts, _ = split(v, output_floor=2)
    require(totals['inner'] == 0 and totals['pair'] == 0
            and totals['coupled'] == POSITIVE_COEFFICIENT,
            'positive generated-child renewal lies in the coupled sector')
    return {'returns': {k: str(v) for k, v in totals.items()},
            'nonzero_ordered_counts': counts}


def scalar_product_coefficients(u, v):
    result = {}
    for p, a in u.items():
        for q, b in v.items():
            k = tuple(x+y for x, y in zip(p, q))
            # Both stored velocity coefficients carry a factor of i.
            result[k] = result.get(k, F(0))-dot(a, b)
    return {k: x for k, x in result.items() if x}


def pressure_free_check():
    reports = []
    for sign in (1, -1):
        u = add(sine((0, 1, 0), (F(1), F(0), F(0))),
                sine((1, 0, 0), (F(0), F(0), F(1))),
                sine((1, 1, 0), (F(0), F(0), F(sign))))
        raw = {}
        for p, a in u.items():
            for q, b in u.items():
                k = tuple(x+y for x, y in zip(p, q))
                value = tuple(dot(a, q)*x for x in b)
                raw[k] = tuple(x+y for x, y in zip(raw.get(k, ZERO), value))
        raw = {k: a for k, a in raw.items() if any(a)}
        n = B(u, u)
        require(raw == n and all(a[0] == a[1] == 0 and k[2] == 0 for k, a in raw.items()),
                'unprojected source is already solenoidal and purely vertical')
        speed_squared = scalar_product_coefficients(u, u)
        work = scalar_product_coefficients(u, n)
        fourth_dot = 4*sum(x*work.get(tuple(-a for a in k), F(0))
                          for k, x in speed_squared.items())
        require(fourth_dot == 0, 'zero Euler derivative of the velocity fourth moment')
        require(pair(A(u), n) == -F(sign, 4), 'signed physical enstrophy production')
        values, _, _ = split(u)
        require(values == {'inner': F(0), 'pair': F(0), 'coupled': F(sign*161, 19200)},
                'nonzero coupled renewal in the pressure-free shear calibration')
        reports.append({'phase_sign': sign, 'coupled_return_at_unit_viscosity': str(values['coupled']),
                        'enstrophy_production': str(pair(A(u), n)),
                        'euler_fourth_moment_derivative': str(fourth_dot)})
    return reports


def main():
    result = {'status': 'all rational checks passed',
              'scope': 'finite five-input identities; whole-space bound is analytic',
              'columns': column_check(), 'fields': field_checks(),
              'generated_core': generated_check(),
              'pressure_free_calibration': pressure_free_check()}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
