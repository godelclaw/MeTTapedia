#!/usr/bin/env python3
"""Exact caloric stretching, force and frequency-split checks on the 2*pi torus.

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


def mode_source(p, a, q, b):
    k = tuple(x+y for x, y in zip(p, q))
    r = radius_squared(k)
    if not r:
        return ZERO
    coefficient = dot(cross(p, a), q)
    return tuple(coefficient*x/r for x in cross(k, b))


def bilinear_heat_blocks(u, v):
    """Ordered curl/gradient parents, indexed by their total heat rate."""
    blocks = {}
    for p, a in u.items():
        for q, b in v.items():
            k = tuple(x+y for x, y in zip(p, q))
            value = mode_source(p, a, q, b)
            key = (k, radius_squared(p)+radius_squared(q))
            blocks[key] = tuple(x+y for x, y in zip(blocks.get(key, ZERO), value))
    return {k: v for k, v in blocks.items() if any(v)}


def heat_blocks(u):
    """Imaginary coefficients of M(exp(t*Delta)u), indexed by decay rate."""
    return bilinear_heat_blocks(u, u)


def block_pair(left, right, nu):
    by_mode = {}
    for (k, s), w in right.items():
        by_mode.setdefault(k, []).append((s, w))
    return sum((dot(v, w)/(nu*nu*(r+s))
                for (k, r), v in left.items()
                for s, w in by_mode.get(k, ())), F(0))


def capacity(u, nu):
    blocks = heat_blocks(u)
    return block_pair(blocks, blocks, nu)


def parent_derivative(u, direction, nu):
    """Derivative from both ordered parent slots; no source outputs discarded."""
    tangent = add(bilinear_heat_blocks(u, direction),
                  bilinear_heat_blocks(direction, u))
    return 2*block_pair(heat_blocks(u), tangent, nu)


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
    require(actual_derivative == parent_derivative(u, actual, nu),
            'parent derivative agrees with quartic polarization')
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


def check_low_split(u, cutoff_squared, nu=F(1)):
    v = {k: a for k, a in u.items() if radius_squared(k) >= cutoff_squared}
    low = add(u, scale(-1, v))
    nu_full, nv = B(u, u), B(v, v)
    low_input = add(B(low, u), B(v, low))
    require(low_input == add(nu_full, scale(-1, nv)), 'complete low-input split')
    low_output = {k: a for k, a in nv.items() if radius_squared(k) < cutoff_squared}
    high_output = add(nv, scale(-1, low_output))
    full = parent_derivative(u, nu_full, nu)
    high = parent_derivative(v, high_output, nu)
    low_direction = parent_derivative(u, low_input, nu)
    low_capacity = parent_derivative(u, nv, nu)-parent_derivative(v, nv, nu)
    low_receiver = parent_derivative(v, low_output, nu)
    require(full == high+low_direction+low_capacity+low_receiver,
            'five-parent high/low split retains low outputs')
    return {'cutoff_squared': str(cutoff_squared), 'high_input_modes': len(v),
            'complete_self_source_modes': len(nv), 'low_output_modes': len(low_output),
            'full_renewal': str(full), 'all_high_renewal': str(high),
            'low_input_direction': str(low_direction),
            'low_capacity_parent': str(low_capacity),
            'low_output_renewal': str(low_receiver)}


def check_mode_kernel():
    checks = 0
    # Include near-opposite parents with arbitrarily small relative output.
    for n in (1, 2, 17, 1000000):
        for p, q in (((n, 1, 0), (-n, 0, 1)),
                     ((n, 0, 0), (-n, 1, 0)),
                     ((n, 1, 0), (-n, -1, 0))):
            for a in ((F(1), F(2), F(3)), (F(-2), F(1), F(0))):
                b = (F(3), F(-1), F(2))
                value = mode_source(p, a, q, b)
                require(dot(value, value) <= radius_squared(p)*dot(a, a)*dot(b, b),
                        'inverse curl cancels the output derivative')
                checks += 1
    for p2 in (0, 1, 4, 289, 10**12):
        for r2 in (0, 1, 9, 400, 10**12):
            denominator = p2+r2+2
            require(4*p2*r2 <= denominator**2, 'ordered quartic kernel <= 1/2')
            checks += 1
    return checks


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
    split_field = add(u, sine((1, -1, 0), (1, 1, 2)),
                      sine((2, 0, 0), (0, 1, 1)),
                      sine((2, 1, 0), (1, -2, 3)))
    splits = [check_low_split(split_field, q) for q in (F(0), F(3, 2), F(7, 2), F(6))]
    require(any(r['low_output_renewal'] != '0' for r in splits),
            'the fixture exercises nonzero low-output renewal')
    reverse = check_low_split(scale(-1, split_field), F(3, 2))
    for key in ('full_renewal', 'all_high_renewal', 'low_input_direction',
                'low_capacity_parent', 'low_output_renewal'):
        require(F(reverse[key]) == -F(splits[1][key]), 'signed quintic reversal')
    print(json.dumps({'scope': 'Exact rational identities; no time evolution or Lean certificate.',
                      'rows': rows, 'low_splits': splits,
                      'reversed_field_split': reverse,
                      'mode_kernel_checks': check_mode_kernel()}, indent=2))


if __name__ == '__main__':
    main()
