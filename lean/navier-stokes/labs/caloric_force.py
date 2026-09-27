#!/usr/bin/env python3
"""Exact caloric stretching, force and frequency-split checks on the 2*pi torus.

The analytic whole-space force estimate is in ns_forced_tail_budget.tex.
These rational finite Fourier calculations check the functional and its
forced derivative, not that estimate or a time-dependent PDE enclosure.
Convolutions are formed in full before output projections; all interference
between parent heat rates is retained.
"""
from fractions import Fraction as F
import itertools
import json
import math

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


def block_pair(left, right, nu, output_floor_squared=F(0)):
    by_mode = {}
    for (k, s), w in right.items():
        if radius_squared(k) >= output_floor_squared:
            by_mode.setdefault(k, []).append((s, w))
    return sum((dot(v, w)/(nu*nu*(r+s))
                for (k, r), v in left.items()
                for s, w in by_mode.get(k, ())), F(0))


def capacity(u, nu, output_floor_squared=F(0)):
    blocks = heat_blocks(u)
    return block_pair(blocks, blocks, nu, output_floor_squared)


def parent_derivative(u, direction, nu, output_floor_squared=F(0)):
    """Both ordered parent slots, with optional projection after convolution."""
    tangent = add(bilinear_heat_blocks(u, direction),
                  bilinear_heat_blocks(direction, u))
    return 2*block_pair(heat_blocks(u), tangent, nu, output_floor_squared)


def derivative(u, direction, nu, output_floor_squared=F(0)):
    """Exact polarization of the quartic polynomial K(u+z*direction)."""
    def value(z):
        return capacity(add(u, scale(F(z), direction)), nu, output_floor_squared)
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


def low_lattice_count(cutoff_squared):
    """All nonzero low modes, independent of the field's active support."""
    ceiling = -(-cutoff_squared.numerator // cutoff_squared.denominator)
    radius = math.isqrt(ceiling)+1
    return sum(0 < radius_squared(k) < cutoff_squared
               for k in itertools.product(range(-radius, radius+1), repeat=3))


def check_stretching_output(u, force, cutoff_squared, nu=F(1)):
    """Keep the nonlinear direction output distinct from the M source output."""
    validate(u)
    validate(force)
    n, au = B(u, u), A(u)
    m = inverse_curl(stretching(u))
    low_m = {k: a for k, a in m.items() if radius_squared(k) < cutoff_squared}
    count = low_lattice_count(cutoff_squared)
    energy, gradient = pair(u, u), pair(au, u)
    low_cost = pair(low_m, low_m)/nu
    low_capacity = capacity(u, nu)-capacity(u, nu, cutoff_squared)
    require(0 <= low_capacity <= count*energy**2/(4*nu**2),
            'low stretching capacity is bounded by kinetic energy alone')
    require(low_cost <= count*energy*gradient/nu,
            'low stretching loss is energy-integrable')
    actual = add(n, scale(-nu, au), force)
    d_high = parent_derivative(u, actual, nu, cutoff_squared)
    require(d_high == derivative(u, actual, nu, cutoff_squared),
            'filtered parent derivative agrees with exact polarization')
    low_derivative = parent_derivative(u, actual, nu)-d_high
    low_renewal = parent_derivative(u, n, nu)-parent_derivative(u, n, nu, cutoff_squared)
    low_force = parent_derivative(u, force, nu)-parent_derivative(u, force, nu, cutoff_squared)
    require(low_derivative == -low_cost+low_renewal+low_force,
            'low stretching history retains full actual velocity direction')
    energy_derivative = 2*pair(u, actual)
    require(energy_derivative == -2*nu*gradient+2*pair(u, force),
            'actual kinetic energy retains only viscosity and force work')
    reserve_derivative = count*energy*energy_derivative/(2*nu**2)-low_derivative
    reserve_balance = (reserve_derivative+low_renewal+low_force
                       -count*energy*pair(u, force)/nu**2)
    require(reserve_balance == low_cost-count*energy*gradient/nu <= 0,
            'initial kinetic reserve pays repeated low-output renewal')
    pi, force_work = pair(au, n), pair(au, force)
    dissipation = nu*pair(au, au)
    material = add(m, scale(-nu, au))
    full_cost = dissipation+pair(material, material)/nu
    high_renewal = parent_derivative(u, n, nu, cutoff_squared)
    high_force = parent_derivative(u, force, nu, cutoff_squared)
    twice_gdot = 2*(pi-dissipation+force_work)+d_high
    require(twice_gdot+full_cost == high_renewal+low_cost+high_force+2*force_work,
            'high stretching capacity retains the original positive cost')

    v = {k: a for k, a in u.items() if radius_squared(k) >= cutoff_squared}
    nv = B(v, v)
    low_n = {k: a for k, a in nv.items() if radius_squared(k) < cutoff_squared}
    high_n = add(nv, scale(-1, low_n))
    fully_high = parent_derivative(v, high_n, nu, cutoff_squared)
    low_inputs = parent_derivative(u, add(n, scale(-1, nv)), nu, cutoff_squared)
    low_parents = (parent_derivative(u, nv, nu, cutoff_squared)
                   -parent_derivative(v, nv, nu, cutoff_squared))
    low_nonlinear_output = parent_derivative(v, low_n, nu, cutoff_squared)
    require(high_renewal == fully_high+low_inputs+low_parents+low_nonlinear_output,
            'both internal frequencies are retained before the high split')
    return {'cutoff_squared': str(cutoff_squared), 'low_lattice_modes': count,
            'low_stretching_capacity': str(low_capacity),
            'low_stretching_cost': str(low_cost),
            'low_stretching_renewal': str(low_renewal),
            'low_stretching_force': str(low_force),
            'fully_high_renewal': str(fully_high),
            'nonlinear_low_output_renewal': str(low_nonlinear_output)}


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
    output_splits = [check_stretching_output(split_field, force, q)
                     for q in (F(0), F(3, 2), F(7, 2), F(6))]
    reversed_output = check_stretching_output(scale(-1, split_field), force, F(3, 2))
    for key in ('low_stretching_renewal', 'fully_high_renewal',
                'nonlinear_low_output_renewal'):
        require(F(reversed_output[key]) == -F(output_splits[1][key]),
                'signed reversal also holds after the stretching output split')
    require(F(reversed_output['low_stretching_renewal']) > 0,
            'the low stretching sector need not have a favorable sign')
    near_opposite = []
    for size in (4, 1000, 1000000):
        parents = add(sine((size, 1, 0), (F(1, size), -1, 0)),
                      sine((1-size, 0, 1), (F(1, size-1), 0, 1)))
        near_opposite.append(check_stretching_output(parents, {}, F(4)))
        require(F(near_opposite[-1]['low_stretching_capacity']) > 0,
                'high parents contribute to low stretching outputs')
        near_opposite[-1]['parent_frequency_parameter'] = size
    print(json.dumps({'scope': 'Exact rational identities; no time evolution or Lean certificate.',
                      'rows': rows, 'low_splits': splits,
                      'reversed_field_split': reverse,
                      'stretching_output_splits': output_splits,
                      'reversed_stretching_output_split': reversed_output,
                      'near_opposite_stretching_outputs': near_opposite,
                      'mode_kernel_checks': check_mode_kernel()}, indent=2))


if __name__ == '__main__':
    main()
