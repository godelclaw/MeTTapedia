#!/usr/bin/env python3
"""A fast oblique receiver generates a slower parent and pressure tail.

The exact check uses complete NS amplitude coefficients and independent
physical time jets. Transfer to actual small-data asymptotics is analytic
in README.md. Optional full-history prefixes are numerical discovery,
not continuum enclosures or Lean certificates.
"""

import argparse
import json
import time
from fractions import Fraction as Q
from math import factorial

import paired_stretching_history as e
import pressure_history_source as f
from cyclic_pressure_history import velocity_time_jets
from pressure_oblique_return import datum
from pressure_oblique_stock import physical_fields, check as stock_check
from pressure_impulse_payment import require


def exact_checks():
    velocity, pressure = physical_fields()
    chain = []
    coefficient = {(17, 0): Q(-1, 2)}
    for j in range(5):
        q = (1, 4-j, 0)
        require(all(q not in velocity[k] for k in range(1, j+1)),
                'The receiver mode is first generated at the stated degree')
        require(velocity[j+1][q] == ({}, {}, coefficient),
                'The complete coefficient agrees with the descending shear chain')
        require(all(e.jet(coefficient, k) == 0 for k in range(j))
                and e.jet(coefficient, j) == -Q(1, 2**(j+1)),
                'The full coefficient retains its exact first time derivative')
        chain.append(dict(degree=j+1, mode=q, field=e.encode(coefficient),
                          first_time_coefficient=str(-Q(1, 2**(j+1)*factorial(j)))))
        if j < 4:
            coefficient = e.scale(Q(1, 2), e.heat_convolution(
                e.multiply({(1, 0): Q(1)}, coefficient), 1+(3-j)**2))
    require(coefficient[(1, 0)] == Q(-1, 92160), 'Nonzero slow receiver tail')
    literal, _ = velocity_time_jets(datum(4), Q(1), 5)
    require(literal[4][2][(1, 0, 0)] == -f.II/32,
            'Independent full physical time jets identify the new receiver')

    # Pressure degree six needs velocities only through degree five.
    _, sixth = e.project(e.field_add(e.advection(velocity[i], velocity[6-i])
                                    for i in range(1, 6)))
    slow = []
    for degree in range(6):
        row = [{}, {}, {}]
        for q, components in velocity[degree].items():
            require(all(r >= 1 and (r != 1 or j == 0)
                        for a in components for r, j in a), 'No slower or resonant first-rate coefficient')
            if sum(x*x for x in q) == 1:
                for i, a in enumerate(components):
                    if a.get((1, 0)):
                        row[i][q] = f.II*f.QQ_I(a[(1, 0)])
            else:
                require(all((1, 0) not in a for a in components), 'Only first eigenmodes have rate one')
        slow.append(row)
    independent = f.add(*(f.tensor_pressure(f.tensor(slow[i], slow[6-i])) for i in range(1, 6)))
    observed = {q: f.QQ_I(a[(2, 0)]) for q, a in sixth.items() if a.get((2, 0))}
    f.equal(observed, independent, 'Independent pressure recovery from the asymptotic first eigenmodes')
    expected = {(a, 0, b): f.QQ_I(Q(-1, 46080)) for a in (-1, 1) for b in (-1, 1)}
    f.equal(observed, expected, 'The generated slow parent creates a reciprocal pressure tail')
    q = (1, 0, 1)
    require(all(not pressure[k].get(q) for k in range(1, 6)), 'This pressure mode is absent at lower degrees')
    require(all(r >= 2 and (r != 2 or j == 0) for r, j in sixth[q]), 'The pressure tail has exact rate two')
    require(all(r >= 11 for a in pressure[3].values() for r, _ in a), 'Original cubic pressure has rate at least eleven')
    return dict(status='All exact checks passed', chain=chain,
                slow_velocity_limit='-1/92160', slow_pressure_limit='-1/46080',
                pressure_mode=q, pressure_field=e.encode(sixth[q]),
                actual_scope='Nonzero slow tails on actual sufficiently small flows, by the analytic uniform-decay argument',
                limitation='A pointwise forecast obstruction, not failure of the integrated corrected stock',
                certification='Exact coefficients; actual-flow transfer is analytic, not Lean-certified')


def numerical_prefix(n, nu, amplitude, dt, final, exact, residuals=False):
    """Full evolving velocity and inherited moments; no amplitude truncation."""
    import numpy as np
    import mpmath as mp
    from reciprocal_pressure_payment import make_flow
    from pressure_history_residual import spatial_residual

    require(n >= 36 and n % 2 == 0 and nu > 0 and amplitude > 0
            and dt > 0 and final > 0, 'Valid physical parameters and a grid retaining the leading moment correlations')
    steps = round(final/dt)
    require(steps > 0 and abs(steps*dt-final) < 1e-12, 'Integral number of physical time steps')
    alpha, beta = (float(Q(exact[k])) for k in ('original_stock', 'additional_stock'))
    require(alpha > 0 and beta > 0, 'Positive original stocks')
    mp.mp.dps = 70
    def coefficient(degree, t):
        tau = mp.mpf(str(nu))*mp.mpf(str(t))
        return float(mp.fsum(mp.mpf(Q(c).numerator)/Q(c).denominator*tau**j*mp.exp(-r*tau)
                            for r, j, c in exact['fields'][str(degree)]))
    flow = make_flow(n, nu)
    flow.initial.fill(0)
    for j, component in enumerate(datum(4)):
        for q, value in component.items():
            flow.initial[tuple(x % n for x in q)+(j,)] = amplitude*complex(float(value.x), float(value.y))*n**3
    flow.energy0 = 19*amplitude**2/4
    state, spent, start = flow.initial.copy(), 0., time.time()
    epsilon = amplitude/nu
    scale = nu**4*epsilon**12
    stock = scale*(alpha+2*epsilon**2*beta)
    yield dict(n=n, nu=nu, amplitude=amplitude, dt=dt, final=final,
               original_stock=scale*alpha, corrected_stock=stock,
               scope='Floating Fourier-Galerkin history; no continuum enclosure')
    for step in range(1, steps+1):
        state, cost = flow.step(state, dt)
        spent += cost[0]
        require(np.isfinite(state).all(), 'Finite numerical state')
        if step % max(1, round(.125/(nu*dt))) == 0 or step == steps:
            t = step*dt
            row = flow.report(t, state, spent, lambda _: stock)
            A, B = coefficient(12, t), coefficient(14, t)
            row.update(n=n, nu=nu, amplitude=amplitude, dt=dt, elapsed=time.time()-start,
                       forecast_A=A, correction_B=B, normalized_phi=row['phi']/scale,
                       normalized_correction=(row['phi']/scale-A)/epsilon**2,
                       next_remainder=(row['phi']/scale-A-epsilon**2*B)/epsilon**4,
                       old_stock_ratio=row['phi']/(scale*alpha),
                       divergence=float(np.sqrt(np.sum(abs(np.sum(flow.K*state[..., :3], axis=-1))**2))/n**3),
                       generated_receiver_sine=float(-2*state[1, 0, 0, 2].imag/n**3))
            if residuals and (abs(nu*t-.125) < 1e-12 or abs(nu*t-.25) < 1e-12
                              or abs(nu*t-.5) < 1e-12 or step == steps):
                row['spatial_residual'] = spatial_residual(state, flow.rhs(state)[0])
            yield row
    yield dict(completed=True, amplitude=amplitude, elapsed=time.time()-start)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prefix', action='store_true')
    parser.add_argument('--coefficients', help='Reuse JSON output of pressure_oblique_stock.py for numerical discovery')
    parser.add_argument('--n', type=int, default=36)
    parser.add_argument('--nu', type=float, default=1.)
    parser.add_argument('--amplitude', type=float, nargs='+', default=[.25, .5, 1., 2.])
    parser.add_argument('--dt', type=float, default=1/256)
    parser.add_argument('--final', type=float, default=1.5)
    parser.add_argument('--residuals', action='store_true')
    args = parser.parse_args()
    if args.prefix:
        if args.coefficients:
            with open(args.coefficients) as source:
                exact = json.load(source)
        else:
            exact = stock_check()
        for amplitude in args.amplitude:
            for record in numerical_prefix(args.n, args.nu, amplitude, args.dt, args.final, exact, args.residuals):
                print(json.dumps(record), flush=True)
    else:
        require(not args.coefficients, 'Cached stocks are only used by numerical discovery')
        print(json.dumps(exact_checks(), indent=2))
