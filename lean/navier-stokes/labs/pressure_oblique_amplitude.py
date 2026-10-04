#!/usr/bin/env python3
"""Finite-amplitude discovery test of an original oblique pressure allowance.

The full sixteen-field numerical history starts once from exact prescribed
Fourier data. The leading stock is independently computed by ordered-time
Brownian integration. Numerical agreement or an excess is not a continuum
bound; the small-amplitude analytic theorem has separate hypotheses.
"""

import argparse
from fractions import Fraction as Q
import json
import time

import numpy as np

from pressure_oblique_certificate import exact_float, initial_identity, make_flow
from pressure_oblique_parents import datum, joint_factor
from pressure_oblique_stock import brownian_stock, physical_fields
from pressure_prefix_control import require


def leading_stock(amplitude, nu, weights):
    _, pressure = physical_fields()
    alpha, calibration = brownian_stock(pressure[3])
    stock = joint_factor(weights)*Q(amplitude)**12*alpha/Q(nu)**8
    return stock, alpha, calibration


def checks():
    """Independent rational field, energy and complete initial PDE jets."""
    from cellular_parent_history import PAIRS
    from cyclic_pressure_history import velocity_time_jets
    from pressure_history_control import jets
    import pressure_history_source as f

    weights, amplitude, nu, n = (Q(1, 8), Q(1), Q(1, 8)), 8., 1., 32
    initial = [f.scale(Q(amplitude), component) for component in datum(weights)]
    flow = make_flow(n, nu, amplitude, weights=weights)
    expected = np.zeros_like(flow.initial)
    energy = Q(0)
    for j, field in enumerate(initial):
        for k, value in field.items():
            re, im = Q(str(value.x)), Q(str(value.y))
            expected[tuple(q % n for q in k)+(j,)] = complex(exact_float(re*n**3),
                                                           exact_float(im*n**3))
            energy += (re*re+im*im)/2
    require(np.array_equal(flow.initial, expected) and Q(flow.energy0) == energy == Q(545, 2),
            'Independent full original datum, zero original moments and kinetic energy')
    initial_identity(expected/n**3, amplitude, weights=weights)
    changed = expected/n**3
    changed[0, 0, 0, 3] = 1.
    try:
        initial_identity(changed, amplitude, weights=weights)
    except ArithmeticError:
        pass
    else:
        raise ArithmeticError('Preloaded pressure history must be rejected')

    u, pressure = velocity_time_jets(initial, Q(nu), 2)
    g0, g1 = f.grad(pressure[0]), f.grad(pressure[1])
    first = u[1]+g0+[{} for _ in range(10)]
    second = u[2]+[f.add(f.scale(Q(nu), f.lap(g0[j])),
                         f.scale(-1, f.adv(u[0], g0[j])), g1[j]) for j in range(3)]
    second += [f.scale(2, f.mul(g0[i], g0[j])) for i, j in PAIRS]+[{} for _ in range(4)]
    errors = []
    for observed, fields in zip(jets(flow, flow.initial), (first, second)):
        literal = np.zeros_like(observed)
        require(len(fields) == 16, 'All physical and conditional-moment derivatives')
        for j, field in enumerate(fields):
            for k, value in field.items():
                require(max(map(abs, k)) < n/3, 'Every exact initial jet output is retained')
                literal[tuple(q % n for q in k)+(j,)] = n**3*complex(float(value.x), float(value.y))
        error = float(np.max(abs(observed-literal))/max(1., np.max(abs(literal))))
        require(error < 2e-12, 'Numerical initial derivatives agree with complete rational NS/moment jets')
        errors.append(error)
    stock, alpha, calibration = leading_stock(amplitude, nu, weights)
    require(stock == 4096*alpha and Q(18862, 10**12) < stock < Q(18863, 10**12),
            'Exact joint parent scaling of the independently calibrated stock')
    return dict(status='Original weighted datum and stock checks passed', energy=str(energy),
                jet_relative_errors=errors, stock=str(stock), alpha=str(alpha),
                calibration=calibration,
                scope='Exact initial data and calibration; numerical PDE jets checked within floating tolerance')


def run(n, nu, amplitude, weights, dt, final, report_interval):
    require(n > 12 and n % 2 == 0 and min(nu, amplitude, dt, final, report_interval) > 0,
            'Even retained grid and positive physical parameters')
    require(all(np.isfinite(v) for v in (nu, amplitude, dt, final, report_interval)),
            'Finite numerical parameters')
    steps, stride = round(final/dt), round(report_interval/dt)
    require(steps >= 1 and stride >= 1 and steps*Q(dt) == Q(final)
            and stride*Q(dt) == Q(report_interval), 'Exact integer time-step counts')
    stock, alpha, _ = leading_stock(amplitude, nu, weights)
    flow = make_flow(n, nu, amplitude, weights=weights)
    state, spent, start = flow.initial.copy(), 0., time.monotonic()
    yield dict(n=n, nu=nu, amplitude=amplitude, weights=list(map(str, weights)),
               dt=dt, final=final, stock=str(stock), stock_approx=float(stock), alpha=str(alpha),
               scope='Numerical discovery only; no continuum or rounding enclosure')
    for step in range(1, steps+1):
        state, cost = flow.step(state, dt)
        spent += cost[0]
        require(np.all(np.isfinite(state)), 'Finite numerical history')
        if step % stride == 0 or step == steps:
            row = flow.report(step*dt, state, spent, lambda _: float(stock))
            row['elapsed'] = time.monotonic()-start
            yield row
    yield dict(status='Numerical prefix complete', elapsed=time.monotonic()-start)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prefix', action='store_true')
    parser.add_argument('--n', type=int, default=32)
    parser.add_argument('--nu', type=float, default=1.)
    parser.add_argument('--amplitude', type=float, default=8.)
    parser.add_argument('--weights', nargs=3, type=Q, default=(Q(1, 8), Q(1), Q(1, 8)))
    parser.add_argument('--dt', type=float, default=1/512)
    parser.add_argument('--final', type=float, default=.5)
    parser.add_argument('--report-interval', type=float, default=.125)
    args = parser.parse_args()
    if args.prefix:
        for result in run(args.n, args.nu, args.amplitude, tuple(args.weights),
                          args.dt, args.final, args.report_interval):
            print(json.dumps(result), flush=True)
    else:
        print(json.dumps(checks(), indent=2))
