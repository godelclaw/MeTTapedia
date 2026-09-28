#!/usr/bin/env python3
"""Paired caloric renewal in an approximately polarized Fourier belt.

Exact rational finite Fourier checks on the normalized 2*pi torus.
The all-frequency estimate and lattice counting argument are analytic,
not certified by these samples or by Lean. Both nonlinear parent slots,
the generated axial component, and its actual heat rate are retained.
"""
from fractions import Fraction as F
from math import sqrt
import json

from fourier_interactions import (A, B, dot, pair, project,
                                  radius_squared, require, scale, validate)
from caloric_force import mode_source, parent_derivative, derivative


BETA = F(4)
CONSTANT = 30000000000
FAMILIES = {
    'comparable': [(4, 1, 1), (1, 4, -1), (2, 1, 1), (1, 2, 1), (2, 2, -2)],
    'small_root': [(101, 1, 1), (-100, 0, 1), (2, 1, 1), (1, 2, 1), (-2, -2, 0)],
    'inner_cancellation': [(4, 1, 1), (1, 4, -1), (2, 1, 1),
                           (1025, 2, 1), (-1022, 2, -2)],
}


def paired(p, a, q, b):
    return tuple(x+y for x, y in zip(mode_source(p, a, q, b),
                                     mode_source(q, b, p, a)))


def fixture(base, size, axial):
    require(tuple(x+y for x, y in zip(base[0], base[1])) ==
            tuple(sum(k[j] for k in base[2:]) for j in range(3)),
            'five-input frequency conservation')
    result = {}
    for j, k in enumerate(base):
        m = max(abs(k[0]), abs(k[1]))
        p = (k[0]*size**2, k[1]*size**2, k[2]*size)
        plane = (F(-k[1], m), F(k[0], m), F(0))
        tilted = project(p, (F(0), F(0), F(axial, size*m)))
        a = tuple(F(j+1, 3)*(x+y) for x, y in zip(plane, tilted))
        result[p] = a
        result[tuple(-x for x in p)] = tuple(-x for x in a)
    validate(result)
    return result


def planar_projection(u):
    """An alternative, solenoidal direction used only to test its difference."""
    result = {}
    for k, a in u.items():
        h = (-k[1], k[0], 0)
        h2 = radius_squared(h)
        if h2:
            v = tuple(dot(a, h)*x/h2 for x in h)
            if any(v):
                result[k] = v
    validate(result)
    return result


def paired_expansion(u, cutoff_squared=F(0)):
    total, wrong_heat = F(0), F(0)
    terms = {'ordinary': 0, 'inner_dominant': 0}
    max_sampled_ratio = 0.
    for p, a in u.items():
        for q, b in u.items():
            k = tuple(x+y for x, y in zip(p, q))
            if radius_squared(k) < cutoff_squared:
                continue
            left = paired(p, a, q, b)
            if not any(left):
                continue
            for c, v in u.items():
                r = tuple(x-y for x, y in zip(k, c))
                r2 = radius_squared(r)
                if not r2 or r2 < cutoff_squared:
                    continue
                for d, w in u.items():
                    e = tuple(x-y for x, y in zip(r, d))
                    if e not in u:
                        continue
                    z = u[e]
                    raw = tuple(dot(w, e)*x for x in z)
                    direction = project(r, raw)
                    product = dot(w, w)*dot(z, z)
                    require(dot(direction, direction) <= r2*product,
                            'nonlinear output derivative bound')
                    require((direction[2]-raw[2])**2 <= r[2]**2*product,
                            'axial pressure retains the output axial factor')
                    require(raw[2]**2 <= radius_squared(e)*dot(w, w)*z[2]**2,
                            'axial transport differentiates its own parent')
                    right = paired(c, v, r, direction)
                    rate = sum(radius_squared(x) for x in (p, q, c, r))
                    value = dot(left, right)/rate
                    total += value
                    wrong_rate = rate-r2+radius_squared(d)+radius_squared(e)
                    wrong_heat += dot(left, right)/wrong_rate
                    s2 = max(radius_squared(x) for x in (p, q, c))
                    ell2 = max(radius_squared(d), radius_squared(e))
                    label = 'inner_dominant' if ell2 > 64*s2 else 'ordinary'
                    terms[label] += (value != 0)
                    # Only this diagnostic ratio uses floating point. Exact
                    # identities and the final norm inequality are separate.
                    bound = float(BETA**2)*(360+264*(ell2/s2)**.25)
                    products = dot(a, a)*dot(b, b)*dot(v, v)*product
                    observed = float(abs(value))/sqrt(float(products))
                    require(observed <= bound*(1+1e-13), 'sampled quintic kernel')
                    max_sampled_ratio = max(max_sampled_ratio, observed/bound)
    return total, wrong_heat, terms, max_sampled_ratio


def field_check(name, size, axial, masked):
    u = fixture(FAMILIES[name], size, axial)
    floor = F(size**2)
    for p, a in u.items():
        require(radius_squared(p) >= floor**2, 'fixed high-frequency floor')
        require(F(p[2])**4 <= BETA**4*radius_squared(p), 'frequency belt')
        require(a[2]**4*radius_squared(p) <= BETA**4*dot(a, a)**2,
                'small axial velocity fraction')
    cutoff_squared = 4*floor**2 if masked else F(0)
    nonlinear = {k: v for k, v in B(u, u).items()
                 if radius_squared(k) >= cutoff_squared}
    total, wrong_heat, terms, ratio = paired_expansion(u, cutoff_squared)
    expected = parent_derivative(u, nonlinear, F(1), cutoff_squared)
    require(total == expected, 'paired five-input sum equals the actual derivative')
    if name == 'comparable' and size == 8:
        require(total == derivative(u, nonlinear, F(1), cutoff_squared),
                'independent quartic polarization')
    energy, dissipation = pair(u, u), pair(A(u), A(u))
    # Fourth powers remove every square and fourth root from the bound.
    require(total**4*floor <= CONSTANT**4*BETA**8*(BETA+1)**6
            *energy**6*dissipation**4, 'all-frequency norm bound on the fixture')
    reduced = parent_derivative(u, planar_projection(nonlinear), F(1), cutoff_squared)
    if name == 'comparable' and size == 8 and axial and not masked:
        require(total > 0 and reduced < 0, 'planarizing the generated mode reverses the sign')
        require(wrong_heat < 0, 'incorrect nonlinear heat rate also reverses the sign')
        require(parent_derivative(scale(-1, u), nonlinear, F(1)) == -total,
                'quintic sign reversal with its unchanged quadratic source')
    require(wrong_heat != total, 'the correct output heat rate matters')
    return {'family': name, 'horizontal_scale': size**2,
            'initial_axial_component': bool(axial), 'both_output_masks': masked,
            'signed_renewal': str(total), 'renewal_rounded': float(total),
            'planarized_direction_renewal': float(reduced),
            'wrong_heat_rate_renewal': float(wrong_heat),
            'generated_axial_modes': sum(v[2] != 0 for v in nonlinear.values()),
            'nonzero_terms': terms, 'max_sampled_kernel_ratio': ratio}


def constant_check():
    # Bounds used in the analytic dyadic summation:
    # 32^(3/2)<192, 2^(15/4)<16, 2^(-13/4)<1/8.
    require(32**3 < 192**2 and 2**15 < 16**4 and 8**4 < 2**13,
            'radical constants in the lattice and geometric sums')
    require(360+3*264 < 1200 and 2*624**2 < 900**2,
            'two regions of the paired kernel estimate')
    ordinary = 10*1200*192*16*(3*256)
    separated = 900*192*16*2*(2*16)
    require(ordinary+separated < CONSTANT, 'uniform final constant')
    columns = []
    for n in range(50):
        # Raising the common scale factor to the fourth power is unnecessary
        # here: dominate 2^(-13j/4) by 2^(-3j), an exact geometric series.
        col = sum((F(1, 8)**j for j in range(n+1)), F(0))
        require(col < 2, 'inner-parent geometric column')
        columns.append(col)
    return {'ordinary_constant': ordinary, 'inner_constant': separated,
            'total_bound': CONSTANT, 'largest_sampled_geometric_column': str(max(columns))}


def main():
    rows = [field_check(name, size, axial, masked)
            for name in FAMILIES for size, axial in ((8, 0), (8, 1), (32, 1))
            for masked in (False, True)]
    require(any(r['nonzero_terms']['inner_dominant'] for r in rows),
            'nonvanishing cancelling inner-parent sector')
    print(json.dumps({'status': 'all rational checks passed',
                      'scope': 'finite Fourier algebra; infinite-shell estimate is analytic',
                      'constants': constant_check(), 'fields': rows}, indent=2))


if __name__ == '__main__':
    main()
