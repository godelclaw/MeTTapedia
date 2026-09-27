#!/usr/bin/env python3
"""Exact checks for separated-parent absorption in a caloric source.

Finite Fourier checks use normalized volume on the 2*pi torus. Its
conservative lattice constant is 200; the whole-space analytic constant
10 is proved separately in ns_forced_tail_budget.tex. No finite evolution
or continuum error enclosure is asserted here.
"""
from fractions import Fraction as F
import json

from fourier_interactions import (A, B, ZERO, add, inverse_curl, pair,
    project, radius_squared, require, scale, sine, stretching, validate)
from caloric_force import block_pair, mode_source


def dyadic_index(square):
    value = F(square)
    require(value > 0, 'positive frequency radius')
    j = (value.numerator.bit_length()-value.denominator.bit_length())//2
    while value < F(4)**j:
        j -= 1
    while value >= F(4)**(j+1):
        j += 1
    return j


def ceiling_three_halves(j):
    return (3*j+1)//2


def sector(p, q, output_floor, separation):
    k = tuple(a+b for a, b in zip(p, q))
    k2 = radius_squared(k)
    if k2 == 0:
        return 'zero'
    j = dyadic_index(k2)
    if j < output_floor:
        return 'low'
    n = dyadic_index(max(radius_squared(p), radius_squared(q)))
    return 'far' if n >= ceiling_three_halves(j)+separation else 'keep'


def blocks(u, v, output_floor, separation, selected):
    result = {}
    for p, a in u.items():
        for q, b in v.items():
            if sector(p, q, output_floor, separation) != selected:
                continue
            k = tuple(x+y for x, y in zip(p, q))
            key = (k, radius_squared(p)+radius_squared(q))
            value = mode_source(p, a, q, b)
            result[key] = tuple(x+y for x, y in zip(result.get(key, ZERO), value))
    return {key: a for key, a in result.items() if any(a)}


def collapse(blocks_by_rate):
    result = {}
    for (k, _), a in blocks_by_rate.items():
        result[k] = tuple(x+y for x, y in zip(result.get(k, ZERO), a))
    return {k: a for k, a in result.items() if any(a)}


def capacity(u, nu, j, r, selected='keep'):
    source = blocks(u, u, j, r, selected)
    return block_pair(source, source, nu)


def derivative(u, h, nu, j, r, selected='keep'):
    source = blocks(u, u, j, r, selected)
    tangent = add(blocks(u, h, j, r, selected), blocks(h, u, j, r, selected))
    return 2*block_pair(source, tangent, nu)


def schur_check(jmax=30, nmax=80):
    reports = []
    for r in (3, 8, 12):
        matrix = [[F(2)**(ceiling_three_halves(j)-n)
                   if n >= ceiling_three_halves(j)+r else F(0)
                   for n in range(nmax+1)] for j in range(jmax+1)]
        bound = F(2)**(1-r)
        require(all(sum(row) <= bound for row in matrix), 'Schur row bound')
        require(all(sum(row[n] for row in matrix) <= bound for n in range(nmax+1)),
                'Schur column bound')
        for j in range(jmax+1):
            c = ceiling_three_halves(j)
            if c+r <= nmax:
                require(sum(matrix[j])+F(2)**(c-nmax) == bound,
                        'row bound including its exact infinite geometric tail')
        d = [F(n+2, (n+1)**2) for n in range(nmax+1)]
        lhs = sum(sum(a*b for a, b in zip(row, d))**2 for row in matrix)
        rhs = bound**2*sum(x*x for x in d)
        require(lhs <= rhs, 'finite squared-operator bound without a shell-count factor')
        reports.append({'separation': r, 'rows': jmax+1, 'columns': nmax+1,
                        'squared_operator_ratio': float(lhs/rhs)})
    for ell in range(25):
        for squared in (4**ell, F(5, 4)*4**ell, 4**(ell+1)-F(1, 2)):
            members = [n for n in range(28) if F(4)**(n-1) <= squared < F(4)**(n+1)]
            require(members == [ell, ell+1], 'two adjacent enlarged parent bands')
            require(sum(F(16)**n for n in members) <= 17*squared*squared,
                    'fourth-order band overlap weight')
    return reports


def fixture(r):
    n = 2**(r+4)
    k = (4, 4, 0)
    p = (n, 0, 0)
    q = (4-n, 4, 0)
    u = {}
    for mode, a in ((p, (0, 1, 0)), (q, (0, 0, 1)), (k, (0, 0, 1)),
                    ((1, 2, 3), project((1, 2, 3), (F(1), F(0), F(0))))):
        u[mode] = tuple(F(x) for x in a)
        u[tuple(-x for x in mode)] = tuple(-F(x) for x in a)
    validate(u)
    return u


def check_field(u, nu, j, r):
    validate(u)
    sources = {name: collapse(blocks(u, u, j, r, name)) for name in ('keep', 'far', 'low')}
    full_m = inverse_curl(stretching(u))
    require(add(*sources.values()) == full_m, 'complete stretching-source partition')
    for source in sources.values():
        validate(source)
    au, nonlinearity = A(u), B(u, u)
    energy, enstrophy, palinstrophy = pair(u, u), pair(u, au), pair(au, au)
    far = sources['far']
    lattice_constant = F(200)
    require(pair(far, far) <= lattice_constant**2*F(2)**(-2*r)*energy*palinstrophy,
            'conservative periodic far-source bound')
    far_capacity = capacity(u, nu, j, r, 'far')
    require(0 <= far_capacity <= lattice_constant**2*F(2)**(-2*r)*energy*enstrophy/(2*nu**2),
            'conservative periodic far-capacity bound')
    require(derivative(u, scale(-nu, au), nu, j, r) == -pair(sources['keep'], sources['keep'])/nu,
            'heat translation for the retained pair mask')
    force = sine((2, -1, 1), (F(1, 7), F(1, 7), -F(1, 7)))
    actual_rhs = add(nonlinearity, scale(-nu, au), force)
    actual_kdot = derivative(u, actual_rhs, nu, j, r)
    # Independent polarization of the quartic functional at this actual direction.
    def value(z):
        return capacity(add(u, scale(F(z), actual_rhs)), nu, j, r)
    require(actual_kdot == (8*(value(1)-value(-1))-value(2)+value(-2))/12,
            'independent quartic polarization of the masked derivative')
    defect = add(sources['keep'], scale(-nu, au))
    cost = nu*palinstrophy+pair(defect, defect)/nu
    twice_gdot = 2*pair(au, actual_rhs)+actual_kdot
    right = (derivative(u, nonlinearity, nu, j, r)
             +derivative(u, force, nu, j, r)+2*pair(au, force)
             +2*pair(au, sources['low'])+2*pair(au, far))
    require(twice_gdot+cost == right, 'modified positive balance with the full actual RHS')
    return {'viscosity': str(nu), 'output_floor_index': j, 'separation': r,
            'source_mode_counts': {name: len(v) for name, v in sources.items()},
            'far_source_squared_norm': str(pair(far, far)),
            'far_enstrophy_work': str(pair(au, far)),
            'far_capacity_rounded': float(far_capacity)}


def generated_check():
    from caloric_localization import parents, POSITIVE_COEFFICIENT
    u = parents()
    require(all(radius_squared(k) < 16 for k in u), 'initially empty parent tail')
    v = {k: a for k, a in B(u, u).items() if radius_squared(k) >= 16}
    h = {k: a for k, a in B(v, v).items() if radius_squared(k) >= 16}
    coefficient = derivative(v, h, F(1), 2, 3)
    require(coefficient == POSITIVE_COEFFICIENT,
            'the retained core still contains the positive generated-child example')
    return {'retained_coefficient': str(coefficient), 'parent_tail_initially_empty': True}


def main():
    result = {'status': 'all rational checks passed',
              'scope': 'finite periodic algebra; whole-space and all-shell estimates are analytic',
              'schur': schur_check(),
              'fields': [check_field(fixture(r), nu, j, r)
                         for r in (3, 8) for j in (0, 2, 3) for nu in (F(1), F(1, 2))],
              'generated_core': generated_check()}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
