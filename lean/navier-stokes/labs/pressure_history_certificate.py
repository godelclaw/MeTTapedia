#!/usr/bin/env python3
"""Enclosed pressure-history comparison for one shared reference.

Each accepted interval encloses the full physical residual, field majorants
and scalar comparison. Original moments and path error persist across seams.
This is an analytic/computational certificate under the explicit arithmetic
model of pressure_prefix_certificate, not a Lean certificate. Its finite
reference examples do not establish an arbitrary-data history bound.
"""

import argparse
from fractions import Fraction as Q
import hashlib
import json
import time

import numpy as np
from pressure_history_control import initial_controls, jets
from pressure_operator_enclosure import OperatorEnclosure
from pressure_polynomial_enclosure import rational_upper, residual_bounds, sqrt_upper
from pressure_prefix_certificate import (arithmetic_check, bernstein, control_step,
                                         exp_upper, require)
from reciprocal_pressure_payment import make_flow

MAJORANTS = ('S', 'Splus', 'D', 'V0', 'V1', 'V2', 'G0', 'G1', 'G2',
             'epsilon0', 'epsilon1', 'rI', 'rQ', 'rT', 'rPhi')


def root2(q):
    return Q(sqrt_upper(q))


def root4(q):
    return root2(root2(q))


def propagate(old, row, h, nu, velocity_step=control_step, enstrophy_source=None):
    """Outward version of the physical comparison (788)--(794).

    All nonnegative polynomial arithmetic is exact rational arithmetic on
    the supplied binary64 bounds. Roots are checked by squaring; the path
    exponential uses a Taylor remainder enclosure. Original errors are zero;
    all later errors and cumulative accounts must be passed in via old.
    Optional callbacks must supply valid velocity and enstrophy comparisons
    for the same physical error; their analytic hypotheses are not checked here.
    """
    require(h > 0 and nu > 0 and np.isfinite(h+nu), 'Positive finite physical parameters')
    require(all(np.isfinite(row[k]) and row[k] >= 0 for k in MAJORANTS)
            and all(np.isfinite(v) and v >= 0 for v in old.values()),
            'Finite nonnegative comparison inputs')
    vel = velocity_step(old['X'], old['Y'], row, h, nu)
    x, y = Q(vel['Xmax']), Q(vel['Ymax'])
    r, o, hq, nq = {k: Q(row[k]) for k in MAJORANTS}, {k: Q(v) for k, v in old.items()}, Q(h), Q(nu)
    kappa = 27*(26*Q(22, 7))**2/(32*nq**3)
    source = (2*r['S']*y*y+r['D']*x*y+kappa*y**6+r['epsilon1']*y
              if enstrophy_source is None else enstrophy_source(x, y, r, kappa))
    require(source >= 0, 'Nonnegative upper bound for the physical enstrophy source')
    rhs = 2*hq*source
    dissipation = (o['Y']**2+rhs)/nq
    energy_rhs = o['energy_rhs']+rhs
    A0 = o['V0_squared']+hq*r['V0']**2
    A1 = o['linear_pressure']+hq*(2*r['V1']*y+r['V2']*x)
    A2 = o['Y_squared']+hq*y*y
    direct = 3*(r['V0']*root2(hq*dissipation)+hq*(2*r['V1']*y+r['V2']*x)
                +40*root2(y)*root4(hq)*root4(dissipation)**3)
    local_sum = o['local_pressure_sum']+direct
    cumulative = 3*(root2(A0*energy_rhs/nq)+A1
                    +40*root4(A2)*root4(energy_rhs/nq)**3)
    exponential = Q(exp_upper(rational_upper(hq*r['Splus'])))
    path = exponential*(o['path']+3*hq*y)
    trajectory = o['trajectory_sum']+hq*r['G1']*path
    e1 = o['e1']+hq*r['rI']
    e2 = o['e2']+hq*(2*r['G0']*e1+r['rQ'])
    e3 = o['e3']+hq*(4*r['G0']*e2+r['rT'])
    e4 = o['e4']+hq*(4*r['G2']*e3+r['rPhi'])
    result = dict(path=path, impulse=min(local_sum, cumulative)+trajectory,
                  e1=e1, e2=e2, e3=e3, e4=e4, energy_rhs=energy_rhs,
                  V0_squared=A0, linear_pressure=A1, Y_squared=A2,
                  local_pressure_sum=local_sum, cumulative_pressure=cumulative,
                  trajectory_sum=trajectory, dissipation=dissipation)
    result = {k: rational_upper(v) for k, v in result.items()}
    result.update(vel)
    return result


def pressure_upper(reference_phi, controls):
    require(np.isfinite(reference_phi), 'Finite scalar Bernstein upper bound')
    return rational_upper((root4(max(Q(0), Q(reference_phi)+Q(controls['e4'])))
                           +Q(controls['impulse']))**4)


def fixed_tail(gradient, phi):
    """Fixed viscosity-1/4 consumer, including the whole inherited impulse."""
    require(Q(gradient) <= Q(1, 64) and Q(phi) <= 4,
            'Actual small-gradient and inherited fourth-moment tolerances')
    return dict(future_impulse_radius='75/448', completed_phi_upper='63/10',
                heat_stock='757/120', gap_to_stock=str(Q(757, 120)-Q(63, 10)),
                scope='Analytic small-gradient tail with the original pressure history')


def scalar_checks():
    """Independent high-precision evaluation of every propagated quantity."""
    from decimal import Decimal as D, localcontext
    row = dict(S=.125, Splus=.25, D=2., V0=1., V1=1.5, V2=2.,
               G0=.25, G1=.75, G2=.125, epsilon0=2.**-24, epsilon1=2.**-23,
               rI=2.**-20, rQ=2.**-19, rT=2.**-18, rPhi=2.**-17)
    old = {key: 2.**-18 for key in initial_controls()}
    h, nu = .0625, .25
    observed = propagate(old, row, h, nu)
    vel = control_step(old['X'], old['Y'], row, h, nu)
    with localcontext() as context:
        context.prec = 100
        o, r = {k: D(v) for k, v in old.items()}, {k: D(v) for k, v in row.items()}
        x, y, t, v = D(vel['Xmax']), D(vel['Ymax']), D(h), D(nu)
        sqrt = lambda z: z.sqrt()
        fourth = lambda z: z.sqrt().sqrt()
        rhs = 2*t*(2*r['S']*y*y+r['D']*x*y
                   +27*(26*D(22)/7)**2/(32*v**3)*y**6+r['epsilon1']*y)
        dissipation = (o['Y']**2+rhs)/v
        energy = o['energy_rhs']+rhs
        a0 = o['V0_squared']+t*r['V0']**2
        a1 = o['linear_pressure']+t*(2*r['V1']*y+r['V2']*x)
        a2 = o['Y_squared']+t*y*y
        local = o['local_pressure_sum']+3*(r['V0']*sqrt(t*dissipation)
                +t*(2*r['V1']*y+r['V2']*x)+40*sqrt(y)*fourth(t)*fourth(dissipation)**3)
        cumulative = 3*(sqrt(a0*energy/v)+a1+40*fourth(a2)*fourth(energy/v)**3)
        path = (t*r['Splus']).exp()*(o['path']+3*t*y)
        trajectory = o['trajectory_sum']+t*r['G1']*path
        e1 = o['e1']+t*r['rI']
        e2 = o['e2']+t*(2*r['G0']*e1+r['rQ'])
        e3 = o['e3']+t*(4*r['G0']*e2+r['rT'])
        e4 = o['e4']+t*(4*r['G2']*e3+r['rPhi'])
        expected = dict(path=path, impulse=min(local, cumulative)+trajectory,
                        e1=e1, e2=e2, e3=e3, e4=e4, energy_rhs=energy,
                        V0_squared=a0, linear_pressure=a1, Y_squared=a2,
                        local_pressure_sum=local, cumulative_pressure=cumulative,
                        trajectory_sum=trajectory, dissipation=dissipation)
        for key, value in expected.items():
            require(D(observed[key]) >= value and D(observed[key])-value < D('1e-12'),
                    'Outward scalar bounds include the independent high-precision formula: '+key)
        phi = pressure_upper(.5, observed)
        exact_phi = (fourth(D('.5')+D(observed['e4']))+D(observed['impulse']))**4
        require(D(phi) >= exact_phi and D(phi)-exact_phi < D('1e-12'),
                'Outward pressure fourth moment includes its independent formula')
    second = propagate(observed, row, h, nu)
    for key in ('e1', 'e2', 'e3', 'e4', 'path', 'energy_rhs', 'V0_squared',
                'linear_pressure', 'Y_squared', 'local_pressure_sum', 'trajectory_sum'):
        require(second[key] > observed[key], 'The later slab inherits earlier costs: '+key)
    reset = propagate(initial_controls(), row, h, nu)
    require(second['impulse'] > reset['impulse'] and second['e4'] > reset['e4'],
            'Resetting the comparison at a seam would discard a nonzero history')
    require(pressure_upper(-1., dict(e4=0., impulse=0.)) == 0,
            'A signed reference scalar is clipped only after adding its error')
    tail = fixed_tail(1/64, 4.)
    require((Q(99, 70)+Q(75, 448))**4 < Q(63, 10) < Q(757, 120),
            'Complete mixed past/future tail cost fits the original stock')
    return dict(status='Outward scalar comparison and inherited-history checks passed',
                tested_quantities=len(expected), first=observed, second=second, tail=tail)


def initial_identity(a):
    """The exact common datum is (sin y+sin z,sin x,sin x)."""
    n = a.shape[0]
    expected = np.zeros_like(a)
    for axis, component in ((1, 0), (2, 0), (0, 1), (0, 2)):
        for sign in (-1, 1):
            k = [0, 0, 0]
            k[axis] = sign % n
            expected[tuple(k)+(component,)] = -.5j*sign
    require(np.array_equal(a, expected), 'Exact analytic initial velocity and zero original moments')


def digest(a):
    return hashlib.sha256(a.tobytes(order='C')).hexdigest()


def run(n, nu, dt, h, final):
    require(n >= 12 and n % 2 == 0 and min(nu, dt, h, final) > 0,
            'Even retained grid and positive physical/time parameters')
    steps, slabs = round(h/dt), round(final/h)
    require(steps >= 1 and slabs >= 1 and steps*Q(dt) == Q(h)
            and slabs*Q(h) == Q(final), 'Exact integral time steps and consecutive slabs')
    flow, operator = make_flow(n, nu, 1.), OperatorEnclosure(n)
    state, controls = flow.initial.copy(), initial_controls()
    first, second = jets(flow, state)
    previous, maximum_phi = None, 0.
    start = time.time()
    yield dict(n=n, nu=nu, dt=dt, h=h, final=final,
               datum='(sin y+sin z,sin x,sin x)',
               scope='Complete interval and arithmetic enclosures; analytic comparison, not Lean-certified')
    for slab in range(slabs):
        initial, f0, j0 = state.copy(), first, second
        for _ in range(steps):
            state, _ = flow.step(state, dt)
        first, second = jets(flow, state)
        raw = [a/n**3 for a in bernstein(initial, state, f0, first, j0, second, h)]
        if previous is None:
            initial_identity(raw[0])
        else:
            require(np.array_equal(previous, raw[0]), 'Every field shares its exact stored interval endpoint')
        initial_hash, final_hash = digest(raw[0]), digest(raw[-1])
        previous = raw[-1].copy()
        residual, radii, metadata, _ = operator.residual(raw, h, nu, with_majorants=True)
        bounds = residual_bounds(residual, radii, normalized=True)
        del residual
        row = dict(metadata.pop('majorants'), **{k: v['bound'] for k, v in bounds.items()})
        try:
            controls = propagate(controls, row, h, nu)
        except (ArithmeticError, OverflowError) as ex:
            yield dict(time=rational_upper((slab+1)*Q(h)), status='comparison failed',
                       reason=str(ex), row=row, previous_control=controls, elapsed=time.time()-start)
            return
        upper = pressure_upper(row['reference_phi_upper'], controls)
        maximum_phi = max(maximum_phi, upper)
        gradient = rational_upper(Q(row['final_H1'])+Q(controls['Y']))
        record = dict(time=rational_upper((slab+1)*Q(h)), status='interval accepted',
                      grids=metadata, row=row, control=controls, residual_bounds=bounds,
                      initial_endpoint_sha256=initial_hash, final_endpoint_sha256=final_hash,
                      actual_phi_upper=upper, maximum_actual_phi_upper=maximum_phi,
                      actual_final_H1_upper=gradient, elapsed=time.time()-start)
        if nu == .25 and gradient <= 1/64 and maximum_phi <= 4:
            record['tail'] = fixed_tail(gradient, maximum_phi)
            yield record
            yield dict(status='original heat stock paid for all time', elapsed=time.time()-start)
            return
        yield record
    yield dict(status='requested finite prefix accepted; tail not certified',
               elapsed=time.time()-start)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prefix', action='store_true')
    parser.add_argument('--n', type=int, default=40)
    parser.add_argument('--nu', type=float, default=.25)
    parser.add_argument('--dt', type=float, default=1/128)
    parser.add_argument('--h', type=float, default=1/16)
    parser.add_argument('--final', type=float, default=1/8)
    args = parser.parse_args()
    arithmetic_check()
    if args.prefix:
        for record in run(args.n, args.nu, args.dt, args.h, args.final):
            print(json.dumps(record), flush=True)
    else:
        print(json.dumps(scalar_checks(), indent=2))
