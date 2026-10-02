#!/usr/bin/env python3
"""Nonnegative receiver storage, nonlinear renewal, and an energy-cube repair.

Exact rational Fourier algebra, with every nonlinear output retained before
the stated vertical-mean projection. Smooth NS and heat-integral arguments
are analytic in README.md. No closed Galerkin evolution is used.
"""

import json
from fractions import Fraction as Q

import pressure_history_source as f
from receiver_heat_corrector import (
    cubic, dilation, dot, forecast, forecast_derivative, inner,
    minus_laplacian, modes, nonlinear, oscillation, real_field, require,
    seed, vector_add, vector_scale, vertical_mean,
)


def add_blocks(*blocks):
    result = {}
    for block in blocks:
        for key, value in block.items():
            old = result.get(key, (f.ZERO,)*3)
            result[key] = tuple(x+y for x, y in zip(old, value))
    return {key: value for key, value in result.items() if any(value)}


def source_blocks(u, v):
    """Pi[-P((S_s u.grad)S_s v)], indexed by output and original heat rate.

    This is the full advective source, not the inverse-curl stretching
    source in caloric_force.py. Distinct parent rates are kept separately.
    """
    result = {}
    for p, a in modes(u).items():
        for q, b in modes(v).items():
            k = tuple(x+y for x, y in zip(p, q))
            if k[2] == 0:
                continue
            kk = sum(x*x for x in k)
            value = tuple(-f.II*dot(a, q)*(b[j]-k[j]*dot(k, b)/kk)
                          for j in range(3))
            rate = sum(x*x for wave in (p, q) for x in wave)
            key = (k, rate)
            old = result.get(key, (f.ZERO,)*3)
            result[key] = tuple(x+y for x, y in zip(old, value))
    return {key: value for key, value in result.items() if any(value)}


def heat_pair(left, right, nu=Q(1)):
    """(1/nu) integral of the real spatial pairing of two heated blocks."""
    require(nu > 0, 'positive viscosity')
    by_mode = {}
    for (k, rate), value in right.items():
        by_mode.setdefault(k, []).append((rate, value))
    total = f.ZERO
    for (k, r), a in left.items():
        for s, b in by_mode.get(tuple(-j for j in k), []):
            require(r+s > 0, 'non-mean output has strictly positive heat rate')
            total += dot(a, b)/(nu**2*(r+s))
    require(total.y == 0, 'real data give a real integrated pairing')
    return Q(str(total.x))


def capacity(w, nu=Q(1)):
    source = source_blocks(w, w)
    return heat_pair(source, source, nu)


def capacity_derivative(w, direction, nu=Q(1)):
    source = source_blocks(w, w)
    tangent = add_blocks(source_blocks(w, direction), source_blocks(direction, w))
    return 2*heat_pair(source, tangent, nu)


def storage(w, nu=Q(1)):
    return inner(minus_laplacian(w), w)/2+forecast(w, nu)+capacity(w, nu)


def square_storage(w, nu=Q(1)):
    linear = {(k, sum(j*j for j in k)): tuple(nu*sum(j*j for j in k)*v for v in a)
              for k, a in modes(w).items()}
    complete = add_blocks(linear, source_blocks(w, w))
    return heat_pair(complete, complete, nu)


def storage_derivative(w, direction, nu=Q(1)):
    return (inner(minus_laplacian(w), direction)
            + forecast_derivative(w, direction, nu)
            + capacity_derivative(w, direction, nu))


def matched_fields():
    """The two original data in receiver_heat_corrector, equation (194)."""
    r = real_field(seed())
    source = oscillation(nonlinear(r))
    y = [{}, {}, {}]
    for k, weight in zip(((2, -1, 2), (3, -2, 2), (3, -1, 2)),
                         (Q(1), Q(559, 2376), Q(-3311, 4335))):
        pair = (k, tuple(-j for j in k))
        part = [{ell: a for ell, a in row.items() if ell in pair} for row in source]
        y = vector_add(y, vector_scale(weight, part))
    return [vector_add(r, vector_scale(Q(sign, 10), y)) for sign in (-1, 1)]


def identity_checks():
    r = real_field(seed())
    u = vector_add(r, vector_scale(Q(1, 10), nonlinear(r)))
    w = oscillation(u)
    nu = Q(2, 7)
    Aw = minus_laplacian(w)
    full_source = oscillation(nonlinear(u))
    self_source = oscillation(nonlinear(w))
    require(any(vertical_mean(u)) and full_source != self_source,
            'the full test retains a nonzero mean and its receiver coupling')
    f.equal(f.trace(f.jac(u)), {}, 'actual datum is divergence free')
    require(inner(u, nonlinear(u)) == 0, 'all internal kinetic transfers cancel')
    require(inner(Aw, nonlinear(w)) == cubic(w), 'independent cubic observations agree')
    collapsed = {}
    for (k, _), value in source_blocks(w, w).items():
        collapsed[k] = tuple(x+y for x, y in zip(collapsed.get(k, (f.ZERO,)*3), value))
    collapsed = {k: v for k, v in collapsed.items() if any(v)}
    require(collapsed == modes(self_source), 'independent Leray source reconstruction')
    require(storage(w, nu) == square_storage(w, nu) > 0,
            'all three terms equal the direct heat-integrated square')
    heat_direction = vector_scale(-nu, Aw)
    require(capacity_derivative(w, heat_direction, nu) == -inner(self_source, self_source)/nu,
            'heat spends the complete source capacity')
    direction = vector_add(heat_direction, full_source)
    lhs = storage_derivative(w, direction, nu)+2*cubic(w)
    rhs = (-nu*inner(Aw, Aw)-inner(self_source, self_source)/nu
           + inner(Aw, full_source)+forecast_derivative(w, full_source, nu)
           + capacity_derivative(w, full_source, nu))
    require(lhs == rhs, 'actual equation keeps both full nonlinear derivatives and mean feeding')
    # An independent quartic polarization checks all four differentiated slots.
    values = {z: capacity(vector_add(w, vector_scale(z, full_source)), nu)
              for z in (-2, -1, 1, 2)}
    polarized = (8*(values[1]-values[-1])-values[2]+values[-2])/12
    require(polarized == capacity_derivative(w, full_source, nu),
            'capacity derivative agrees with exact polynomial polarization')
    return {'nu': str(nu), 'storage': str(storage(w, nu)),
            'complete_defect': str(rhs), 'mean_retained': True}


def renewal_and_repair_checks():
    rows = []
    for sign, w in zip((-1, 1), matched_fields()):
        source = oscillation(nonlinear(w))
        Aw = minus_laplacian(w)
        require(vertical_mean(w) == [{}, {}, {}], 'matched data start with zero vertical mean')
        require(forecast(w) == cubic(w) == 0, 'matched cubic observations vanish')
        row = {'sign': sign, 'energy': inner(w, w), 'enstrophy': inner(Aw, w),
               'D': inner(Aw, Aw), 'capacity': capacity(w),
               'quartic': forecast_derivative(w, source)-inner(source, source),
               'quintic': capacity_derivative(w, source)}
        require(storage(w) == square_storage(w) > 0, 'matched storage is positive')
        require(capacity_derivative(w, vector_scale(-1, Aw)) == -inner(source, source),
                'matched capacity also obeys exact heat spending')
        rows.append(row)
    for key in ('energy', 'enstrophy', 'D', 'capacity', 'quartic'):
        require(rows[0][key] == rows[1][key], 'matched phases retain '+key)
    E, Z, D = (rows[0][key] for key in ('energy', 'enstrophy', 'D'))
    b, p = rows[0]['quartic'], rows[0]['quintic']
    require(b < 0 and p == -rows[1]['quintic'] > 0,
            'favorable quartic production conceals opposite quintic renewal')
    amplitude = Q(512)
    ratio = 2*(-D+amplitude**2*b+amplitude**3*p)/D
    require(ratio > 265, 'positive square storage fails the half-dissipation payment')

    # Add gamma*E(u)^3/nu^4 using FULL fluid energy, never receiver energy.
    # Its inviscid derivative is zero; its viscous derivative is negative.
    gamma = Q(1, 10**8)
    q = 6*gamma*E**2*Z
    require(q > 0 and p**2+4*q*b < 0,
            'strict negative discriminant pays either quintic phase at EVERY real amplitude')
    # b +/- p*r-q*r^2 = -(sqrt(q)*r -/+ p/(2sqrt(q)))^2 + b+p^2/(4q).
    # The rational discriminant check proves the sign without numerical roots.
    scaled = []
    w = matched_fields()[0]
    for nu, frequency, amplitude in ((Q(1, 7), 1, Q(512, 7)), (Q(3), 3, Q(48))):
        u = vector_scale(amplitude, dilation(w, frequency))
        source = oscillation(nonlinear(u))
        tangent = vector_add(source, vector_scale(-nu, minus_laplacian(u)))
        actual = storage_derivative(u, tangent, nu)+2*cubic(u)
        expected = (-nu*amplitude**2*frequency**4*D
                    + amplitude**4*frequency**2*b/nu
                    + amplitude**5*frequency*p/nu**2)
        require(actual == expected, 'direct full-source computation verifies viscosity and frequency scaling')
        corrected = actual-6*gamma*inner(u, u)**2*inner(minus_laplacian(u), u)/nu**3
        require(corrected < -nu*inner(minus_laplacian(u), minus_laplacian(u)),
                'energy cube supplies a strict initial margin at tested dilations')
        scaled.append({'nu': str(nu), 'frequency': frequency, 'amplitude': str(amplitude),
                       'repaired_initial_cost': str(corrected)})
    return {'matched_data': [{k: str(v) for k, v in row.items()} for row in rows],
            'square_storage_cost_over_half_dissipation_at_512nu': str(ratio),
            'energy_cube_coefficient': str(gamma),
            'negative_discriminant': str(p**2+4*q*b),
            'direct_scaled_checks': scaled,
            'repair_scope': 'all amplitudes and integer harmonic dilations of the two stated initial data',
            'physical_conclusion': 'each repaired actual NS flow has a positive short payment interval, analytically',
            'open': 'a bound that persists when the actual solution leaves these initial-data rays'}


if __name__ == '__main__':
    print(json.dumps({'identities': identity_checks(),
                      'renewal_and_repair': renewal_and_repair_checks()}, indent=2))
