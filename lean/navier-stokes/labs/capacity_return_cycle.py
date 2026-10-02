#!/usr/bin/env python3
"""An actual local return of source capacity with positive stretching cost.

The full Fourier jets and scalar return brackets are checked exactly.
Uniform local NS existence, the return interval and the oscillatory-parent
realization are analytic arguments in README.md, not certified by Python.
"""

import json
from fractions import Fraction as Q

import descendant_geometry_separation as a

s, f, rc, d = a.s, a.f, a.rc, a.d


def envelope():
    v = [{}, {}, {}]
    for k, c in zip(((1, 0, 1), (1, -1, 1), (2, 0, 1), (2, -1, 1)), (1, 1, -4, 3)):
        for j, z in enumerate((-k[1], k[0], 0)):
            v[j] = f.add(v[j], d.mode(k, c*z))
    f.equal(f.trace(f.jac(v)), {}, 'the release envelope is exactly solenoidal')
    s.require(not v[2] and s.inner(v, v) == 56,
              'the horizontal envelope meets the actual release construction hypotheses')
    return v


def physical_jet(w, mu):
    n, Aw = s.nonlinear(w), s.minus_laplacian(w)
    direction = s.vector_add(n, s.vector_scale(-mu, Aw))
    source_rate = a.source_derivative(w, direction)
    acceleration = s.vector_add(source_rate, s.vector_scale(-mu, s.minus_laplacian(direction)))
    blocks = rc.source_blocks(w, w)
    first = s.add_blocks(rc.source_blocks(w, direction), rc.source_blocks(direction, w))
    second = s.add_blocks(rc.source_blocks(w, acceleration), rc.source_blocks(acceleration, w),
                          a.c.scale(2, rc.source_blocks(direction, direction)))
    Z, D, g = s.inner(w, Aw), s.inner(Aw, Aw), s.cubic(w)
    Cp = rc.derivative(w, direction)
    Cpp = 2*s.heat_pair(first, first)+2*s.heat_pair(blocks, second)
    s.require(Cp == rc.derivative(w, n)-mu*s.inner(n, n),
              'full heat capacity loses the full source square at viscosity mu')
    s.require(2*s.inner(w, direction) == -2*mu*Z,
              'the complete flow spends kinetic energy without forcing')
    return dict(mu=mu, capacity_rate=Cp, capacity_second_rate=Cpp,
                enstrophy_rate=2*g-2*mu*D, core_cost=2*g-Q(3, 4)*mu*D,
                uniform_core_lower_at_seed=2*g-mu*D,
                stretching_rate=s.inner(s.minus_laplacian(direction), n)+s.inner(Aw, source_rate),
                kinetic_rate=-2*mu*Z), direction, acceleration


def independent_second_derivative(w, mu, row, direction, acceleration):
    C0 = rc.capacity(w)
    sums = {}
    for j in (1, 2):
        sums[j] = (rc.capacity(s.vector_add(w, s.vector_scale(j, direction)))
                   + rc.capacity(s.vector_add(w, s.vector_scale(-j, direction)))-2*C0)
    hessian = (16*sums[1]-sums[2])/12
    s.require(hessian+rc.derivative(w, acceleration) == row['capacity_second_rate'],
              'quartic polarization independently verifies the full physical second derivative')
    # Convert the physical viscosity to one without changing spatial frequencies.
    physical = s.vector_scale(1/mu, w)
    actual_direction = s.vector_add(s.nonlinear(physical), s.vector_scale(-1, s.minus_laplacian(physical)))
    for x, y in zip(actual_direction, s.vector_scale(1/mu**2, direction)):
        f.equal(x, y, 'amplitude and time rescaling gives exactly viscosity one')
    s.require(rc.capacity(physical) == C0/mu**4,
              'the capacity return is preserved by the physical amplitude scaling')


def return_brackets():
    # Normalize a^2/kappa=1 and time by a/kappa. Curvature lies in [-3/2,-1/2].
    lower = lambda t: t-Q(3, 4)*t*t
    upper = lambda t: t-Q(1, 4)*t*t
    start, middle, end = Q(1, 8), Q(1), Q(5)
    s.require(lower(start) == Q(29, 256) > 0,
              'the comparison starts on the initial increasing side')
    s.require(lower(middle)-upper(start) == Q(33, 256) > 0,
              'capacity at the middle is strictly above the starting level')
    s.require(upper(end)-lower(start) == -Q(349, 256) < 0,
              'capacity at the end is strictly below the starting level')
    s.require(1-Q(3, 2)*start > 0 and 1-end/2 < 0,
              'strict concavity gives the increasing and decreasing sides')
    s.require(middle-start == Q(7, 8) and end-start == Q(39, 8),
              'the actual return duration has fixed positive comparison bounds')
    return dict(start=start, middle=middle, end=end,
                middle_gap=lower(middle)-upper(start), end_gap=upper(end)-lower(start))


def main():
    w = s.nonlinear(envelope())
    n, Aw = s.nonlinear(w), s.minus_laplacian(w)
    P, N2 = rc.derivative(w, n), s.inner(n, n)
    mu_star = P/N2
    s.require(Q(1, 100) < mu_star < Q(1, 50), 'the critical viscosity is strictly positive')
    critical, direction, acceleration = physical_jet(w, mu_star)
    s.require(critical['capacity_rate'] == 0 and critical['capacity_second_rate'] < -45000,
              'the actual NS tangent is a strict local capacity maximum')
    s.require(critical['enstrophy_rate'] > 50 and critical['uniform_core_lower_at_seed'] > 200,
              'enstrophy and the unpaid stretching grow at this maximum')
    independent_second_derivative(w, mu_star, critical, direction, acceleration)
    rows = []
    for theta in (Q(0), Q(1, 100), Q(1, 1000)):
        mu = (1-theta)*mu_star
        row, _, _ = physical_jet(w, mu)
        s.require(row['capacity_rate'] == theta*P and row['capacity_second_rate'] < 0,
                  'capacity has the exact launch slope and strictly downward curvature')
        s.require(row['enstrophy_rate'] > 0 and row['uniform_core_lower_at_seed'] > 0,
                  'the complete physical cost retains its strict sign')
        _, counts = a.selected_sources(w, 4*s.inner(w, w), mu, Q(1, 8))
        s.require(counts[:2] == [0, 0], 'both previously paid regions are empty at the initial seed')
        rows.append(dict(theta=theta, **row))
    s.require(all(sum(x*x for x in k) < 49 for k in s.modes(w)),
              'the fixed-band high input initially vanishes')
    s.require(any(s.vertical_mean(w)) and any(s.vertical_mean(n)),
              'the existing and newly generated mean motions remain')
    result = dict(status='all exact checks passed', E=s.inner(w, w), Z=s.inner(w, Aw),
                  D=s.inner(Aw, Aw), g=s.cubic(w), C1=rc.capacity(w), P=P, N2=N2,
                  critical_viscosity=mu_star, rows=rows, brackets=return_brackets(),
                  scope='exact jets and scalar brackets; actual solution returns and their parent realization analytic')
    print(json.dumps(result, default=str, indent=2))


if __name__ == '__main__':
    main()
