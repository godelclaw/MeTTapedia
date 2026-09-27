#!/usr/bin/env python3
"""Exact separated-inner-parent checks for the caloric renewal.

Expand the full Navier--Stokes source inside the derivative slot, keeping
all five original inputs. The heat rate of that slot is its OUTPUT
frequency squared; its two parents are not independently heat-evolved.
Finite calculations use the normalized 2*pi torus, not whole-space
quadrature or a certified time-dependent PDE computation.
"""
from fractions import Fraction as F
import json

from fourier_interactions import (A, B, ZERO, dot, pair, project,
                                  radius_squared, require, scale, validate)
from caloric_force import mode_source
from separated_caloric import derivative, dyadic_index, fixture, sector


def ceiling_eleven_eighths(m):
    return (11*m+7)//8


def nonlinear_shells(u):
    """Full quadratic source, grouped by output and maximal input shell."""
    result = {}
    for p, a in u.items():
        for q, b in u.items():
            k = tuple(x+y for x, y in zip(p, q))
            if radius_squared(k) == 0:
                continue
            n = dyadic_index(max(radius_squared(p), radius_squared(q)))
            value = project(k, tuple(dot(a, q)*x for x in b))
            key = (k, n)
            result[key] = tuple(x+y for x, y in zip(result.get(key, ZERO), value))
    return {key: a for key, a in result.items() if any(a)}


def inner_split(u, nu, output_floor, outer_separation, inner_separation):
    """Split the retained quintic return before summing its original inputs."""
    require(nu > 0 and output_floor >= 0 and inner_separation >= 4,
            'positive viscosity and valid separation parameters')
    cutoff_squared = F(4)**output_floor
    v = {k: a for k, a in u.items() if radius_squared(k) >= cutoff_squared}
    sources = nonlinear_shells(v)
    by_output = {}
    full_n = {}
    for (k, n), a in sources.items():
        by_output.setdefault(k, []).append((n, a))
        full_n[k] = tuple(x+y for x, y in zip(full_n.get(k, ZERO), a))
    full_n = {k: a for k, a in full_n.items() if any(a)}
    require(full_n == B(v, v), 'complete Navier--Stokes source grouped by parent shell')
    totals = {'far': F(0), 'remaining': F(0)}
    counts = {'far': 0, 'remaining': 0}
    band_terms = {}
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
                h2 = radius_squared(h)
                if h2 < cutoff_squared or h not in by_output:
                    continue
                if sector(ell, h, output_floor, outer_separation) != 'keep':
                    continue
                m = dyadic_index(max(radius_squared(p), radius_squared(q),
                                     radius_squared(ell)))
                # The three undifferentiated rates plus the direction output.
                heat_rate = radius_squared(p)+radius_squared(q)+radius_squared(ell)+h2
                for n, direction in by_output[h]:
                    tangent = tuple(x+y for x, y in zip(
                        mode_source(ell, c, h, direction),
                        mode_source(h, direction, ell, c)))
                    value = 2*dot(source, tangent)/(nu**2*heat_rate)
                    selected = ('far' if n >= ceiling_eleven_eighths(m)+inner_separation
                                else 'remaining')
                    totals[selected] += value
                    counts[selected] += (value != 0)
                    if selected == 'far' and value:
                        band_terms[m, n] = band_terms.get((m, n), F(0))+value
    high_n = {k: a for k, a in full_n.items() if radius_squared(k) >= cutoff_squared}
    require(sum(totals.values()) == derivative(v, high_n, nu, output_floor, outer_separation),
            'five-input partition equals the complete masked derivative')
    energy = pair(v, v)
    palinstrophy = pair(A(v), A(v))
    # Lattice counting has a different constant from the continuum proof.
    lattice_constant = F(1000000)
    require(totals['far']**2 <= lattice_constant**2*F(2)**(-8*inner_separation)
            *energy**3*palinstrophy**2/nu**4,
            'conservative periodic inner-parent absorption')
    return totals, counts, band_terms


def column_check():
    require(F(36*2**11, 6**3*3**6) < 1,
            'continuum prefactor using pi greater than three')
    require(F(272, 15)**2*36*81**2*3*2**11 < 10**12,
            'conservative periodic constant')
    result = []
    for separation in (4, 9, 15):
        bound = F(16, 15)*F(2)**(-4*separation)
        columns = []
        for n in range(95):
            total = sum((F(16)**(ceiling_eleven_eighths(m)-n)
                         for m in range(61)
                         if n >= ceiling_eleven_eighths(m)+separation), F(0))
            require(total <= bound, 'summed inner-parent column bound')
            columns.append(total/bound)
        result.append({'separation': separation,
                       'max_sampled_column_ratio': float(max(columns))})
    return result


def field_checks():
    reports = []
    positive = None
    for parent_parameter in (3, 9, 17):
        u = fixture(parent_parameter)
        validate(u)
        for nu in (F(1), F(1, 2)):
            for output_floor in (0, 2):
                totals, counts, bands = inner_split(u, nu, output_floor, 3, 4)
                reports.append({
                    'parent_frequency': 2**(parent_parameter+4),
                    'viscosity': str(nu), 'output_floor_index': output_floor,
                    'far_return': str(totals['far']),
                    'remaining_return_rounded': float(totals['remaining']),
                    'nonzero_ordered_counts': counts,
                    'far_bands': [{'outer_shell': m, 'inner_shell': n, 'return': str(t)}
                                  for (m, n), t in sorted(bands.items()) if t]})
                if output_floor == 0:
                    candidate = nu**2*totals['far']
                    require(candidate > 0, 'nonzero positive separated inner contribution')
                    if positive is None:
                        positive = candidate
                    require(candidate == positive,
                            'fixed low recipient and source despite growing cancelling parents')
        reversed_totals, _, _ = inner_split(scale(F(-1), u), F(1), 0, 3, 4)
        require(reversed_totals['far'] == -positive, 'quintic sign reversal')
        boundary = parent_parameter+1
        at_boundary, _, _ = inner_split(u, F(1), 0, 3, boundary)
        above_boundary, _, _ = inner_split(u, F(1), 0, 3, boundary+1)
        require(at_boundary['far'] == positive and above_boundary['far'] == 0,
                'exact dyadic separation boundary')
    return reports


def generated_check():
    from caloric_localization import parents, POSITIVE_COEFFICIENT
    u = parents()
    v = {k: a for k, a in B(u, u).items() if radius_squared(k) >= 16}
    totals, counts, _ = inner_split(v, F(1), 2, 3, 4)
    require(totals['far'] == 0 and totals['remaining'] == POSITIVE_COEFFICIENT,
            'positive generated-child renewal remains after both separations')
    return {'far_return': str(totals['far']),
            'remaining_return': str(totals['remaining']),
            'nonzero_ordered_counts': counts}


def main():
    result = {'status': 'all rational checks passed',
              'scope': 'finite five-input Fourier algebra; all-shell estimate is analytic',
              'columns': column_check(), 'fields': field_checks(),
              'generated_core': generated_check()}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
