#!/usr/bin/env python3
"""Relative-vorticity cancellation for a retained pressure-history control.

The curl identity lowers one available H1 comparison rate. The original
L2 bound, curvature work, nonlinear error and inherited pressure moments
remain present. Physical transfer is analytic in README.md. These exact
algebraic and outward scalar checks are not Lean certificates.
"""

import argparse
import json
from fractions import Fraction as Q
from math import ceil, log2

import numpy as np
import pressure_history_source as f
from pressure_history_certificate import propagate as pressure_propagate, pressure_upper
from pressure_polynomial_enclosure import rational_upper
from pressure_prefix_certificate import add, mul, up, exp_upper, require, control_step


def velocity_step(X, Y, row, h, nu):
    """Choose either valid H1 supersolution; retain the original L2 control.

    The vorticity branch needs Splus and the Wiener Hessian bound V2.
    The supplied row and original endpoint errors must be valid upper bounds.
    A failed scalar bootstrap is not a physical counterexample.
    """
    require(h > 0 and nu > 0 and min(X, Y) >= 0, 'Positive parameters and nonnegative initial errors')
    a = float(up(row['S']-nu))
    Xend = add(mul(X, exp_upper(float(up(a*h)))),
               mul(row['epsilon0'], mul(h, exp_upper(max(0., float(up(a*h)))))))
    x = max(X, Xend)
    kappa = rational_upper(27*(26*Q(22, 7))**2/(32*Q(nu)**3))
    branches = [(float(up(2*row['S']-nu/2)), row['D']),
                (float(up(row['Splus']-nu/2)), mul(1.5, row['V2']))]
    data = []
    for b, curvature in branches:
        exponential = exp_upper(float(up(b*h)))
        forcing = mul(h, exp_upper(max(0., float(up(b*h)))))
        source = add(mul(curvature, x), row['epsilon1'])
        linear = add(mul(Y, exponential), mul(source, forcing))
        data.append((forcing, linear))
    B = add(mul(1.01, max(Y, min(v for _, v in data))), 2.**-90)
    for _ in range(40):
        power = B
        for _ in range(4):
            power = mul(power, B)
        candidates = [add(linear, mul(forcing, mul(kappa, power))) for forcing, linear in data]
        endpoint = min(candidates)
        if max(Y, endpoint) < B:
            return dict(X=Xend, Y=endpoint, Xmax=x, Ymax=B)
        B = add(mul(1.01, max(B, endpoint)), 2.**-90)
        require(np.isfinite(B) and B < 1, 'Relative-vorticity bootstrap failed before its diagnostic ceiling')
    raise ArithmeticError('Neither complete H1 comparison closed on this interval')


def enstrophy_source(x, y, r, kappa):
    """The smaller complete source pays the same physical dissipation."""
    linear = min(2*r['S']*y*y+r['D']*x*y,
                 r['Splus']*y*y+Q(3, 2)*r['V2']*x*y)
    return linear+kappa*y**6+r['epsilon1']*y


def propagate(old, row, h, nu):
    return pressure_propagate(old, row, h, nu, velocity_step=velocity_step,
                              enstrophy_source=enstrophy_source)


def physical_fixture(v, w, residual, nu):
    mean = lambda a: a.get(f.ORIGIN, f.ZERO)
    for field in (v, w, residual):
        f.equal(f.trace(f.jac(field)), {}, 'Complete solenoidal fields')
    omega, eta = f.curl(v), f.curl(w)
    transport = [f.adv(omega, a) for a in w]
    I = mean(f.dot(eta, transport))
    terms = []
    for i, j, k, sign in [(0, 1, 2, 1), (1, 2, 0, 1), (2, 0, 1, 1),
                           (0, 2, 1, -1), (2, 1, 0, -1), (1, 0, 2, -1)]:
        for ell in range(3):
            terms.append(f.scale(sign, f.mul(w[i], f.mul(f.diff(omega[ell], j), f.diff(w[k], ell)))))
    commutator = mean(f.add(*terms))
    require(2*I == commutator, 'Nonconstant transport/curl commutator after integration by parts')
    J = mean(f.dot(eta, [f.adv(w, a) for a in omega]))

    def nonlinear(u):
        pressure = f.tensor_pressure(f.tensor(u, u))
        return [f.add(f.scale(-1, f.adv(u, a)), f.scale(-1, f.diff(pressure, j)))
                for j, a in enumerate(u)]
    u = [f.add(a, b) for a, b in zip(v, w)]
    tangent = [f.add(a, f.scale(-1, b), f.scale(nu, f.lap(c)), f.scale(-1, r))
               for a, b, c, r in zip(nonlinear(u), nonlinear(v), w, residual)]
    actual = mean(f.dot(eta, f.curl(tangent)))
    stretch = mean(f.dot(eta, [f.adv(eta, a) for a in v]))
    self_stretch = mean(f.dot(eta, [f.adv(eta, a) for a in w]))
    convective_laplacian = mean(f.dot([f.adv(w, a) for a in w], [f.lap(a) for a in w]))
    require(self_stretch == convective_laplacian,
            'Self stretching equals the convective Laplacian pairing with a positive sign')
    dissipation = mean(f.dot([f.lap(a) for a in w], [f.lap(a) for a in w]))
    residual_work = mean(f.dot(eta, f.curl(residual)))
    require(actual == stretch+I-J+self_stretch-nu*dissipation-residual_work,
            'Independent complete projected NS tangent gives the full relative enstrophy balance')
    gradient_norm = mean(f.add(*(f.mul(f.diff(a, j), f.diff(a, j)) for a in w for j in range(3))))
    require(mean(f.dot(eta, eta)) == gradient_norm, 'Physical curl norm equals the solenoidal gradient norm')
    return {key: str(value) for key, value in dict(I=I, twice_I=commutator, J=J,
        stretching=stretch, self_stretching=self_stretch, dissipation=dissipation,
        residual_work=residual_work, actual=actual).items()}


def scalar_checks():
    """Independent high-precision endpoints for both complete branches."""
    from decimal import Decimal as D, localcontext
    from pressure_history_control import initial_controls
    base = dict(S=1., Splus=.5, D=2., V0=1., V1=1.5, V2=2.,
                G0=.25, G1=.75, G2=.125, epsilon0=2.**-24, epsilon1=2.**-23,
                rI=2.**-20, rQ=2.**-19, rT=2.**-18, rPhi=2.**-17)
    cases = [base, dict(base, Splus=4., V2=8.),
             dict(base, S=.0625, Splus=.0625),
             dict(base, epsilon0=0., epsilon1=0.)]
    results = []
    for row in cases:
        X, Y, h, nu = 2.**-18, 2.**-12, .0625, .25
        observed = velocity_step(X, Y, row, h, nu)
        with localcontext() as context:
            context.prec = 100
            r = {k: D(v) for k, v in row.items()}
            t, v, x, y = D(h), D(nu), D(observed['Xmax']), D(observed['Ymax'])
            kappa = 27*(26*D(22)/7)**2/(32*v**3)
            a = r['S']-v
            xe = D(X)*(a*t).exp()+t*max(D(0), a*t).exp()*r['epsilon0']
            require(D(observed['X']) >= xe, 'Outward L2 endpoint')
            endpoints = []
            for b, curvature in [(2*r['S']-v/2, r['D']),
                                  (r['Splus']-v/2, D('1.5')*r['V2'])]:
                source = curvature*x+kappa*y**5+r['epsilon1']
                endpoints.append(D(Y)*(b*t).exp()+t*max(D(0), b*t).exp()*source)
            ye = min(endpoints)
            require(D(observed['Y']) >= ye and D(observed['Y'])-ye < D('1e-12'),
                    'Outward endpoint includes an independently computed complete branch')
            require(max(D(Y), ye) < y, 'Whole-interval supersolution closes strictly')
            start = initial_controls(); start.update(X=X, Y=Y, energy_rhs=Y*Y)
            physical = propagate(start, row, h, nu)
            source = min(2*r['S']*y*y+r['D']*x*y,
                         r['Splus']*y*y+D('1.5')*r['V2']*x*y)+kappa*y**6+r['epsilon1']*y
            energy = D(start['energy_rhs'])+2*t*source
            require(D(physical['energy_rhs']) >= energy
                    and D(physical['energy_rhs'])-energy < D('1e-12'),
                    'Dissipation uses the smaller complete physical source, rounded outward')
            coarser = pressure_propagate(start, row, h, nu, velocity_step=velocity_step)
            require(physical['energy_rhs'] <= coarser['energy_rhs']
                    and physical['impulse'] <= coarser['impulse'],
                    'The improved dissipation source preserves the pressure consumer')
        results.append(dict(X=observed['X'], Y=observed['Y'], energy_rhs=physical['energy_rhs']))
    return results


def checks():
    import sympy as s
    from pressure_oblique_return import datum, wave
    from cyclic_pressure_history import velocity_time_jets
    from pressure_history_control import initial_controls
    w = [wave((0, 1, 0)), wave((0, 0, 1)), wave((1, 0, 0))]
    v = [f.mul(wave((0, 1, 0), True), wave((0, 0, 1))), {}, {}]
    residual = [{}, {}, f.scale(Q(1, 7), wave((1, 0, 0)))]
    first = physical_fixture(v, w, residual, Q(2, 7))
    require(first['I'] == '-1/4' and first['twice_I'] == '-1/2', 'The tested commutator is nonzero')
    v = datum(4)
    jets, _ = velocity_time_jets(v, Q(1), 2)
    w = [f.add(f.scale(Q(2, 3), a), f.scale(Q(1, 5), b)) for a, b in zip(v, jets[1])]
    second = physical_fixture(v, w, residual, Q(3, 5))
    require(second['J'] == '571/300', 'Independent oblique fixture retains nonzero curvature work')
    a = s.Matrix(s.symbols('a:3', real=True)); b = s.Matrix(s.symbols('b:3', real=True))
    require(s.expand(a.cross(b).dot(a.cross(b))+a.dot(b)**2-a.dot(a)*b.dot(b)) == 0,
            'Cross-product contraction used in the pointwise commutator bound')
    row = dict(S=1., Splus=.5, D=2., V0=1., V1=1.5, V2=2.,
               G0=.25, G1=.75, G2=.125, epsilon0=2.**-24, epsilon1=2.**-23,
               rI=2.**-20, rQ=2.**-19, rT=2.**-18, rPhi=2.**-17)
    X, Y, h, nu = 2.**-18, 2.**-12, .0625, .25
    old = control_step(X, Y, row, h, nu)
    new = velocity_step(X, Y, row, h, nu)
    require(new['X'] == old['X'] and new['Y'] < old['Y'], 'The new branch lowers H1 loss without changing L2 loss')
    stiff = dict(row, Splus=4., V2=8.)
    fallback = velocity_step(X, Y, stiff, h, nu)
    require(fallback['Y'] <= old['Y']*(1+1e-12), 'A worse curl branch does not remove the original comparison')
    start = initial_controls(); start.update(X=X, Y=Y, energy_rhs=Y*Y)
    controls = propagate(start, row, h, nu)
    later = propagate(controls, row, h, nu)
    require(later['e4'] > controls['e4'] and later['trajectory_sum'] > controls['trajectory_sum'],
            'Improved velocity control keeps the inherited moments and path error')
    return dict(status='All physical identity and scalar-consumer checks passed',
                fixtures=[first, second], old_velocity=old, new_velocity=new,
                independent_scalar_cases=scalar_checks(),
                inherited_pressure=controls, later_pressure=later,
                scope='General periodic analytic comparison with exact fixtures; not an arbitrary-data payment or Lean certificate')


def replay(records):
    """Replay a saved slabs.probes output; its floating inputs stay unenclosed."""
    from pressure_history_control import initial_controls
    metadata = next(r for r in records if all(k in r for k in ('n', 'nu', 'h')))
    h, nu = metadata['h'], metadata['nu']
    old, new, time = initial_controls(), initial_controls(), Q(0)
    for record in records:
        if 'time' not in record:
            continue
        require(Q(record['time']) == time+Q(h), 'Saved intervals must be consecutive from zero')
        time += Q(h)
        row = record.get('polynomial', record.get('row'))
        rate = max(abs(row['S']-nu), abs(2*row['S']-nu/2), abs(row['Splus']-nu/2), row['Splus'])
        count = 2**max(0, ceil(log2(max(1., 2*h*rate))))
        step = h/count
        require(count*Q(step) == Q(h), 'Scalar subdivisions cover the same exact interval')
        result = dict(time=float(time), scalar_substeps=count,
                      scope='Outward scalar replay of unenclosed input majorants')
        for label, current, advance in [('original', old, pressure_propagate), ('vorticity', new, propagate)]:
            if current is None:
                continue
            try:
                for _ in range(count):
                    current = advance(current, row, step, nu)
                result[label] = current
                if 'reference_phi_slab_upper' in record:
                    result[label+'_phi_upper'] = pressure_upper(record['reference_phi_slab_upper'], current)
            except ArithmeticError as error:
                result[label+'_failure'] = str(error)
                current = None
            if label == 'original':
                old = current
            else:
                new = current
        yield result
        if new is None:
            return


def spatial_probes(grids):
    """Full velocity residual at exact interpolant endpoints of the oblique test.

    The pressure is reconstructed from the evolving velocity. Conditional
    pressure moments are not evolved here; this isolates a velocity error.
    The enlarged spatial product retains all quadratic outputs. It is a
    floating diagnostic, not a certified time interval.
    """
    import time
    from pressure_prefix_control import VelocityFlow
    from pressure_oblique_return import datum
    for n in grids:
        require(n >= 18 and n % 2 == 0, 'Even grid retains the original oblique datum')
        start = time.time()
        flow = VelocityFlow(n, 1.)
        flow.initial.fill(0)
        for j, field in enumerate(datum(4)):
            for q, value in field.items():
                flow.initial[tuple(k % n for k in q)+(j,)] = 8*complex(float(value.x), float(value.y))*n**3
        state = flow.initial.copy()
        for k in range(1, 65):
            state, _ = flow.step(state, 1/1024)
            if k in (16, 64):
                tangent = flow.heat[..., None]*state+flow.rhs(state)[0]
                row = flow.sample(state, tangent)
                yield dict(n=n, time=k/1024, **row, elapsed=time.time()-start,
                           scope='Complete spatial residual of Galerkin tangent; floating diagnostic only')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--replay', metavar='SAVED_JSONL')
    mode.add_argument('--spatial-probe', action='store_true')
    parser.add_argument('--grids', type=int, nargs='+', default=[48, 64, 96])
    args = parser.parse_args()
    if args.replay:
        with open(args.replay) as source:
            for result in replay([json.loads(line) for line in source if line.strip()]):
                print(json.dumps(result), flush=True)
    elif args.spatial_probe:
        for result in spatial_probes(args.grids):
            print(json.dumps(result), flush=True)
    else:
        print(json.dumps(checks(), indent=2))
