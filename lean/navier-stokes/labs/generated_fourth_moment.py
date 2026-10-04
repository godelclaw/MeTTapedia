#!/usr/bin/env python3
"""Signed fourth-moment work of actual generated velocity.

The heat reference is fixed at the original datum. Complete NS tangents,
canonical pressures and all generated Fourier outputs are retained. The
arbitrary-amplitude reduction and viscous interval conclusions are analytic
in README.md, not Lean certificates or a finite-mode evolution.
"""

import json
from fractions import Fraction as Q

import pressure_history_source as f
from heat_remainder_pressure import plus, times, mean, require
from cyclic_pressure_history import velocity_time_jets
from pressure_gradient_stock import weighted_datum
from pressure_quadratic_storage import mode


def pair(a, b):
    """Full spatial integral, evaluated directly at opposite Fourier modes."""
    value = sum((v*b.get(tuple(-x for x in k), f.ZERO) for k, v in a.items()), f.ZERO)
    require(not value.y, 'The spatial integral is real')
    return Q(str(value.x))


def vector_pair(a, b):
    return sum((pair(x, y) for x, y in zip(a, b)), Q(0))


def pressure(u):
    p = f.tensor_pressure(f.tensor(u, u))
    f.equal(p, f.green(f.trace(f.matmul(f.jac(u), f.jac(u)))),
            'The complete tensor and gradient Poisson sources agree')
    return p


def mixed_pressure(a, b):
    return f.tensor_pressure([[f.add(f.mul(a[i], b[j]), f.mul(b[i], a[j]))
                               for j in range(3)] for i in range(3)])


def fourth_work(w):
    p, magnitude = pressure(w), f.dot(w, w)
    work = -pair(magnitude, f.adv(w, p))
    require(work == pair(p, f.adv(w, magnitude)),
            'Signed pressure work agrees after incompressible integration by parts')
    gradient_square = f.add(*(f.mul(a, a) for row in f.jac(w) for a in row))
    diffusion = pair(magnitude, gradient_square)+sum(
        (pair(f.diff(magnitude, k), f.diff(magnitude, k))/2 for k in range(3)), Q(0))
    require(diffusion > 0, 'The tested generated field has genuine diffusion cost')
    return work, diffusion, pair(magnitude, magnitude)


def physical_jets(initial, nu):
    actual, _ = velocity_time_jets(initial, nu, 2)
    heat1 = [f.scale(nu, f.lap(a)) for a in initial]
    heat2 = [f.scale(nu, f.lap(a)) for a in heat1]
    w1, w2 = plus(actual[1], times(-1, heat1)), plus(actual[2], times(-1, heat2))
    magnitude = f.dot(w1, w1)
    receiver = [f.mul(magnitude, a) for a in w1]
    pv1 = mixed_pressure(initial, heat1)
    force1 = [f.scale(-1, f.add(f.adv(heat1, initial[i]), f.adv(initial, heat1[i]),
                               f.diff(pv1, i))) for i in range(3)]
    gm1 = f.grad(mixed_pressure(initial, w1))
    expected = [f.add(f.scale(nu, f.lap(w1[i])), f.scale(-1, f.adv(initial, w1[i])),
                      f.scale(-1, f.adv(w1, initial[i])), force1[i], f.scale(-1, gm1[i]))
                for i in range(3)]
    for a, b in zip(w2, expected):
        f.equal(a, b, 'The actual second generated derivative retains every heat coupling and pressure')
    work, diffusion, y4 = fourth_work(w1)
    z = vector_pair(receiver, w2)
    parent_work = -vector_pair(receiver, [f.adv(w1, a) for a in initial])
    mixed_work = -vector_pair(receiver, gm1)
    heat_work = vector_pair(receiver, force1)
    require(z+nu*diffusion == parent_work+mixed_work+heat_work,
            'The complete fourth-moment balance holds through degree four in physical time')
    require(vector_pair(receiver, [f.adv(initial, a) for a in w1]) == 0,
            'Actual original transport cancels in the integrated fourth moment')
    return dict(viscosity=str(nu), self_pressure_work_coefficient=str(work),
                diffusion_coefficient=str(diffusion), fourth_moment_coefficient=str(y4),
                next_velocity_pairing=str(z), parent_work_coefficient=str(parent_work),
                mixed_work_coefficient=str(mixed_work), heat_work_coefficient=str(heat_work))


def target_field():
    fields = [mode((0, 1, -1), (-1, -1, -1), 1),
              mode((0, 1, 0), (-1, 0, 1), 0, -1),
              mode((0, 0, 1), (0, -1, 0), 2),
              mode((1, 1, 0), (1, -1, -1), Q(1, 8))]
    return [f.add(*(v[j] for v in fields)) for j in range(3)]


def shear_generated(n):
    target, direction, slow_mode = target_field(), (1, 2, 3), (2, -1, 0)
    h = f.add(mode(slow_mode, (1, 0, 0), 1)[0],
              mode(tuple(2*x for x in slow_mode), (1, 0, 0), 1)[0])
    receiver = [{tuple(n*x for x in k): f.II*a/(n*sum(direction[j]*k[j] for j in range(3)))
                 for k, a in row.items()} for row in target]
    u = [f.add(f.scale(direction[j], h), receiver[j]) for j in range(3)]
    target_fast = [{tuple(n*x for x in k): a for k, a in row.items()} for row in target]
    shear = [f.scale(d, h) for d in direction]
    for i in range(3):
        f.equal(f.add(*(f.scale(direction[j], f.diff(receiver[i], j)) for j in range(3))),
                f.scale(-1, target_fast[i]), 'The receiver encodes the prescribed directional derivative')
        f.equal(f.adv(shear, shear[i]), {}, 'The original shear has no self-advection')
    f.equal(f.trace(f.jac(u)), {}, 'The complete datum is divergence free')
    require(all(mean(a) == 0 for a in u), 'There is no constant sweeping velocity')
    h5 = h
    for _ in range(4):
        h5 = f.mul(h5, h)
    target_work = fourth_work(target)[0]
    require(target_work == Q(51, 320) and mean(h5) == Q(25, 8),
            'The prescribed geometry and slow modulation have positive signed work')
    acceleration = velocity_time_jets(u, Q(0), 1)[0][1]
    work, diffusion, size = fourth_work(acceleration)
    require(work > 0, 'The complete generated source has positive self-pressure work')
    # Nonzero viscosity has the same first heat-subtracted derivative.
    viscous = velocity_time_jets(u, Q(2, 7), 1)[0][1]
    for i in range(3):
        f.equal(f.add(viscous[i], f.scale(Q(-2, 7), f.lap(u[i]))), acceleration[i],
                'Positive viscosity does not alter the first generated coefficient')
    return dict(scale=n, input_modes=len(set().union(*u)), generated_modes=len(set().union(*acceleration)),
                target_work=str(target_work), modulation_fifth_moment=str(mean(h5)),
                asymptotic_work_per_scale=str(target_work*mean(h5)),
                generated_work=str(work), generated_work_approximate=float(work),
                generated_diffusion=str(diffusion), generated_diffusion_approximate=float(diffusion),
                generated_fourth_moment=str(size))


def checks():
    rows = []
    fixtures = [(2, (Q(1),)*3), (4, (Q(1),)*3), (4, (Q(1, 4), Q(1), Q(1)))]
    expected = [Q(-53, 2520), Q(-20842, 772065), Q(-1963091, 1581189120)]
    for (m, weights), coefficient in zip(fixtures, expected):
        cases = [physical_jets(weighted_datum(m, weights), nu) for nu in (Q(1), Q(2, 7))]
        require(all(Q(row['self_pressure_work_coefficient']) == coefficient for row in cases),
                'Complete earlier geometries initially deplete signed self-pressure work')
        rows.append(dict(m=m, weights=list(map(str, weights)), cases=cases))
    nonsymmetric = physical_jets(plus(f.fixture(), mode((1, 1, 2), (1, 1, -1), Q(1, 7))), Q(2, 7))
    require(Q(nonsymmetric['parent_work_coefficient']) != 0
            and Q(nonsymmetric['mixed_work_coefficient']) != 0,
            'Both heat coupling terms are nonzero in the independent physical identity check')
    return dict(earlier_geometries=rows, nonsymmetric_balance=nonsymmetric,
                adverse_generated_geometry=shear_generated(32),
                scope='Exact complete NS jets and generated work; all-prefix reduction and positive-viscosity interval arguments are analytic')


if __name__ == '__main__':
    print(json.dumps(checks(), indent=2))
