#!/usr/bin/env python3
"""Exact checks of the forced caloric stretching identity on the 2*pi torus.

The analytic whole-space force estimate is in ns_forced_tail_budget.tex.
These rational finite Fourier calculations check the functional and its
forced derivative, not that estimate or a time-dependent PDE enclosure.
Every convolution output and every interfering heat rate is retained.
"""
from fractions import Fraction as F
import json

from fourier_interactions import (A, B, ZERO, add, cross, dot, inverse_curl,
                                  pair, project, radius_squared, require,
                                  scale, sine, stretching, validate)


def heat_blocks(u):
    """Imaginary coefficients of M(exp(t*Delta)u), indexed by decay rate."""
    blocks = {}
    for p, a in u.items():
        for q, b in u.items():
            k = tuple(x+y for x, y in zip(p, q))
            r = radius_squared(k)
            if not r:
                continue
            coefficient = dot(cross(p, a), q)
            value = tuple(coefficient*x/r for x in cross(k, b))
            key = (k, radius_squared(p)+radius_squared(q))
            blocks[key] = tuple(x+y for x, y in zip(blocks.get(key, ZERO), value))
    return {k: v for k, v in blocks.items() if any(v)}


def capacity(u, nu):
    blocks = heat_blocks(u)
    return sum((dot(v, w)/(nu*nu*(r+s))
                for (k, r), v in blocks.items()
                for (l, s), w in blocks.items() if k == l), F(0))


def derivative(u, direction, nu):
    """Exact polarization of the quartic polynomial K(u+z*direction)."""
    def value(z):
        return capacity(add(u, scale(F(z), direction)), nu)
    return (8*(value(1)-value(-1))-value(2)+value(-2))/12


def check_case(name, u, raw_force, nu):
    validate(u)
    force = {k: v for k, a in raw_force.items() if any(v := project(k, a))}
    validate(force)
    n = B(u, u)
    au = A(u)
    m = inverse_curl(stretching(u))
    collapsed = {}
    for (k, _), v in heat_blocks(u).items():
        collapsed[k] = tuple(x+y for x, y in zip(collapsed.get(k, ZERO), v))
    require(add(collapsed, scale(-1, m)) == {}, 'full projected stretching source')
    pi = pair(au, n)
    require(pair(au, m) == pi, 'stretching/source pairing')
    z = pair(m, m)/nu
    heat_derivative = derivative(u, scale(-nu, au), nu)
    require(heat_derivative == -z, 'heat translation derivative')
    renewal = derivative(u, n, nu)
    force_derivative = derivative(u, force, nu)
    actual = add(n, scale(-nu, au), force)
    actual_derivative = derivative(u, actual, nu)
    require(actual_derivative == -z+renewal+force_derivative,
            'forced physical derivative retains all directions')
    force_work = pair(au, raw_force)
    require(force_work == pair(au, force), 'gradient force does no work')
    dissipation = nu*pair(au, au)
    material = add(m, scale(-nu, au))
    cost = dissipation+pair(material, material)/nu
    twice_gdot = 2*(pi-dissipation+force_work)+actual_derivative
    require(twice_gdot+cost == renewal+force_derivative+2*force_work,
            'complete forced caloric identity')
    return {'case': name, 'viscosity': str(nu), 'capacity': str(capacity(u, nu)),
            'signed_renewal': str(renewal), 'force_capacity_work': str(force_derivative),
            'direct_force_work': str(force_work), 'positive_cost': str(cost),
            'twice_capacity_energy_derivative': str(twice_gdot)}


def main():
    u = add(sine((1, 0, 0), (0, 1, 1)),
            sine((0, 1, 0), (1, 0, 1)),
            sine((1, 1, 0), (1, -1, 1)),
            sine((1, 1, -1), (1, 1, 2)))
    force = add(sine((1, 0, 0), (0, 2, -1)),
                sine((1, 0, 1), (1, 0, -1)))
    gradient = add(sine((1, 0, 0), (3, 0, 0)),
                   sine((1, 1, -1), (2, 2, -2)))
    rows = []
    for nu in (F(1), F(1, 1000)):
        rows.append(check_case('solenoidal_force', u, force, nu))
        with_gradient = check_case('same_force_plus_gradient', u, add(force, gradient), nu)
        require({k: v for k, v in rows[-1].items() if k != 'case'} ==
                {k: v for k, v in with_gradient.items() if k != 'case'},
                'force projection leaves the complete ledger unchanged')
        rows.append(with_gradient)
        rows.append(check_case('pure_gradient_force', u, gradient, nu))
        require(rows[-1]['force_capacity_work'] == '0', 'pure gradient force is projected out')
    print(json.dumps({'scope': 'Exact rational identities; no time evolution or Lean certificate.',
                      'rows': rows}, indent=2))


if __name__ == '__main__':
    main()
