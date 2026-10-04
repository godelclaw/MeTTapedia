#!/usr/bin/env python3
"""Interacting planar pressure histories and their three-dimensional defects.

Exact Fourier and viscosity-polynomial checks retain all nonlinear outputs.
The all-time pressure payment and smooth PDE comparisons in README.md are
analytic, not Lean certificates or numerical trajectory enclosures.
"""

import json
from fractions import Fraction as Q
from math import comb, factorial

import sympy as s
import pressure_history_source as f
from cyclic_entropy_depletion import material_jets
from planar_parent_reserve import average, feedback_datum, mode
from pressure_impulse_return import (NU, RING, mean, product_jet, require,
                                     specialize, viscosity_jets)


def datum(n, passive=False):
    psi = f.add(mode((0, 1, 0), 1), mode((n, 1, 0), Q(1, n)))
    theta = f.add(mode((1, 0, 0), 1, True), mode((0, 2, 0), 1)) if passive else {}
    return [f.scale(-1, f.diff(psi, 1)), f.diff(psi, 0), theta]


def moment_coefficients(velocity, gradient):
    """t^4,t^5,t^6 of the complete pressure-impulse fourth moment.

    Unlike the earlier zero-initial-pressure recurrence, g(0) may be nonzero.
    Missing nonzero derivatives are rejected by product_jet.
    """
    g = [[v[i] for v in gradient] for i in range(3)]

    def step(a, source, n):
        transport = []
        for k in range(n+1):
            if not a[n-k]:
                continue
            require(k < len(velocity), 'Every evolving advecting parent is retained')
            transport.append(f.scale(comb(n, k), f.adv(velocity[k], a[n-k])))
        return f.add(f.scale(NU, f.lap(a[n])), f.scale(-1, f.add(*transport)), source)

    first = [[{}] for _ in range(3)]
    for n in range(3):
        for i in range(3):
            first[i].append(step(first[i], g[i][n], n))
    second = [[[{}] for _ in range(3)] for _ in range(3)]
    for n in range(4):
        for i in range(3):
            for j in range(3):
                source = f.add(product_jet(first[i], g[j], n),
                               product_jet(first[j], g[i], n))
                second[i][j].append(step(second[i][j], source, n))
    trace = [f.add(*(second[i][i][n] for i in range(3))) for n in range(5)]
    third = [[{}] for _ in range(3)]
    for n in range(5):
        for i in range(3):
            source = f.add(f.scale(2, f.add(*(product_jet(second[i][j], g[j], n)
                                             for j in range(3)))),
                           product_jet(trace, g[i], n))
            third[i].append(step(third[i], source, n))
    return [RING.convert(4*mean(f.add(*(product_jet(third[i], g[i], n)
                                      for i in range(3))))/factorial(n+1))
            for n in range(3, 6)]


def material_coefficients(velocity, gradient):
    """Independent Euler material-trajectory calculation through impulse t^3."""
    v = [[specialize(a, 0) for a in row] for row in velocity]
    g = [[specialize(a, 0) for a in row] for row in gradient]
    jets = [material_jets([row[i] for row in g], v) for i in range(3)]
    a = [row[0] for row in jets]
    b = [f.scale(Q(1, 2), row[1]) for row in jets]
    c = [f.scale(Q(1, 6), row[2]) for row in jets]
    aa, ab = f.dot(a, a), f.dot(a, b)
    return [mean(f.mul(aa, aa)), 4*mean(f.mul(aa, ab)),
            mean(f.add(f.scale(4, f.mul(aa, f.dot(a, c))),
                       f.scale(2, f.mul(aa, f.dot(b, b))), f.scale(4, f.mul(ab, ab))))]


def sampling_checks():
    rows, horizontal = [], {}
    for n, passive, expected in [(2, False, -Q(150421, 707200)),
                                  (4, False, Q(103721143, 1613300000)),
                                  (4, True, Q(103721143, 1613300000))]:
        u = datum(n, passive)
        f.equal(f.trace(f.jac(u)), {}, 'Actual solenoidal initial datum')
        require(all(mean(a) == f.ZERO for a in u), 'Zero mean velocity')
        require(all(k[2] == 0 for a in u for k in a), 'Exact planar dependence')
        omega = f.curl(u)[2]
        require(bool(f.adv(u, omega)), 'The parent really interacts nonlinearly')
        v, pressure = viscosity_jets(u, 3)
        g = [f.grad(p) for p in pressure]
        require(bool(pressure[0]), 'Nonzero original pressure')
        zero = [[{}, {}, {}] for _ in v]
        actual, brownian = moment_coefficients(v, g), moment_coefficients(zero, g)
        require([a-b for a, b in zip(actual, brownian)] ==
                [RING.zero, RING.zero, RING.convert(expected)],
                'Same-pressure sampling defect at every viscosity, without fitting')
        for drift, coefficients in ((v, actual), (zero, brownian)):
            require([c.evaluate(NU, f.ZERO) for c in coefficients] ==
                    material_coefficients(drift, g), 'Independent material-path check')
        A = [specialize(a, 0) for a in g[0]]
        B = [specialize(a, 0) for a in g[1]]
        LA = [f.adv(u, a) for a in A]
        aa, al, ab = f.dot(A, A), f.dot(A, LA), f.dot(A, B)
        mixing = mean(f.add(f.mul(aa, f.dot(LA, LA)), f.scale(2, f.mul(al, al))))
        correlation = mean(f.add(f.mul(aa, f.dot(LA, B)), f.scale(2, f.mul(al, ab))))
        require(not mixing.y and mixing.x > 0 and not correlation.y,
                'Real signed correlation and positive mixing form')
        require(-(mixing+2*correlation)/6 == f.QQ_I(expected),
                'Complete changing-source and sampling decomposition')
        if passive:
            require((pressure, actual, brownian) == horizontal[n],
                    'The selected passive vertical component leaves pressure sampling unchanged')
        else:
            horizontal[n] = pressure, actual, brownian
        bound = Q(1)+(n*n+1)/Q(n)
        require(mean(f.mul(omega, omega)).x == (1+((n*n+1)/Q(n))**2)/2,
                'Original parent enstrophy')
        require(sum(omega.values(), f.ZERO) == -f.QQ_I(bound),
                'The elementary vorticity supremum bound is attained at the origin')
        rows.append(dict(n=n, passive_vertical=passive, initial_vorticity_linf=str(bound),
                         initial_vorticity_l2_squared=str(mean(f.mul(omega, omega)).x),
                         actual_t4_t5_t6=list(map(str, actual)),
                         brownian_t4_t5_t6=list(map(str, brownian)),
                         sampling_t6=str(expected), mixing=str(mixing.x),
                         source_correlation=str(correlation.x)))
    return rows


def pressure_split_checks():
    """The actual mean pressure retains both Reynolds stress and hidden pressure."""
    rows = []
    samples = [(f'feedback phase {phase}', feedback_datum(Q(1), phase)) for phase in (-1, 1)]
    original = feedback_datum(Q(1), 1)
    samples.append(('initially hidden only', [f.add(a, f.scale(-1, average(a))) for a in original]))
    for name, u in samples:
        f.equal(f.trace(f.jac(u)), {}, 'Full physical initial solenoidality')
        mean_u = list(map(average, u))
        parent = mean_u[:2]+[{}]
        hidden = [f.add(a, f.scale(-1, b)) for a, b in zip(u, mean_u)]
        R = [[average(f.mul(hidden[i], hidden[j])) for j in range(3)] for i in range(3)]
        full_p = f.tensor_pressure(f.tensor(u, u))
        parent_p = f.tensor_pressure(f.tensor(parent, parent))
        reynolds_p = f.tensor_pressure(R)
        f.equal(average(full_p), f.add(parent_p, reynolds_p),
                'Canonical mean pressure keeps the entire Reynolds contribution')
        fluct_p = f.add(full_p, f.scale(-1, average(full_p)))
        force = [f.scale(-1, f.add(*(f.diff(R[i][j], j) for j in range(2))))
                 for i in range(3)]
        F = f.curl(force)[2]
        omega = f.curl(parent)[2]
        v, _ = viscosity_jets(u, 1)
        omega_rate = f.add(f.diff(average(v[1][1]), 0),
                           f.scale(-1, f.diff(average(v[1][0]), 1)))
        f.equal(omega_rate, f.add(f.scale(NU, f.lap(omega)),
                                 f.scale(-1, f.adv(parent, omega)), F),
                'The actual 3D mean vorticity retains its internal source')
        values = [mean(f.dot(f.grad(p), f.grad(p))).x
                  for p in (parent_p, reynolds_p, fluct_p)]
        gradient_square = f.dot(f.grad(full_p), f.grad(full_p))
        impulse_t4 = mean(f.mul(gradient_square, gradient_square)).x
        require(values[1] > 0 and values[2] > 0 and bool(F),
                'Both pressure defects and vorticity replenishment are present')
        require(impulse_t4 > 0, 'Positive full physical pressure impulse leading coefficient')
        if name == 'initially hidden only':
            require(not omega and values[0] == 0, 'Zero original planar reserve')
        rows.append(dict(fixture=name, parent_gradient_l2_squared=str(values[0]),
                         reynolds_gradient_l2_squared=str(values[1]),
                         fluctuating_gradient_l2_squared=str(values[2]),
                         actual_impulse_t4=str(impulse_t4),
                         vorticity_source_l2_squared=str(mean(f.mul(F, F)).x),
                         signed_parent_enstrophy_work=str(mean(f.mul(omega, F)).x)))
    return rows


def reserve_algebra():
    C, nu, M, a, f2, finf, slack = s.symbols('C nu M a f2 finf slack', positive=True)
    R = C*M*a/nu
    rate = s.diff(R, M)*finf+s.diff(R, a)*(-nu*a+f2-slack)
    bill = C*(a*finf+M*f2)/nu
    require(s.expand(rate+C*M*a-bill+C*M*slack/nu) == 0,
            'The full derivative retains both source bills')
    return dict(reserve=str(R), source_bill=str(bill),
                negative_remainder=str(-C*M*slack/nu),
                scope='Scalar identity; operator bounds, stochastic payment and PDE passage are analytic')


if __name__ == '__main__':
    print(json.dumps(dict(status='All exact checks passed', sampling=sampling_checks(),
                          physical_splits=pressure_split_checks(), algebra=reserve_algebra(),
                          scope='Exact full Fourier and polynomial identities; no new Lean certificate'), indent=2))
