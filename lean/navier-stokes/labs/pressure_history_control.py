#!/usr/bin/env python3
"""Pressure-history error controls with the original accumulated impulse.

The analytic comparison in README.md couples the actual and reference
stochastic paths and uses velocity-error dissipation. Reference conditional
moments have a triangular residual control. The optional prefix samples
residuals in time: it is a feasibility test, NOT a continuum certificate.
Default checks combine exact algebra with independent rational Fourier jets.
"""

import argparse
import json
import time
from fractions import Fraction as Q
from math import comb

import numpy as np
from cellular_parent_history import PAIRS
from pressure_history_residual import complete_operator, enlarge, frequencies, require
from pressure_prefix_certificate import control_step
from pressure_prefix_control import evaluate, hermite
from reciprocal_pressure_payment import make_flow


def jets(flow, state):
    """First two time derivatives of the retained quadratic/cubic system."""
    nonlinear, _ = flow.rhs(state)
    first = flow.heat[..., None]*state+nonlinear
    plus, _ = flow.rhs(state+first)
    minus, _ = flow.rhs(state-first)
    vp, _ = flow.rhs(first)
    vm, _ = flow.rhs(-first)
    derivative = (plus-minus-vp+vm)/2
    return first, flow.heat[..., None]*first+derivative


def sample(flow, value, tangent):
    """Complete spatial products at ONE time, without rounding enclosure."""
    n, m = flow.n, 2*flow.n
    K = frequencies(m)
    k2 = np.sum(K*K, axis=-1)
    large = enlarge(value)
    nonlinear, gh = complete_operator(large)
    residual = enlarge(tangent)+flow.nu*k2[..., None]*large-nonlinear

    def l2(a, weight=1):
        return float(np.sqrt(np.sum(abs(a)**2*weight)/m**6))

    gradients = np.stack([flow.ifft(1j*K[..., j, None]*large[..., :3])
                          for j in range(3)], axis=-1)
    strain = (gradients+gradients.swapaxes(-1, -2))/2
    sizes = np.sqrt(np.sum(abs(value[..., :3])**2, axis=-1))/n**3
    V0 = float(sizes.sum())
    V1 = float(np.sum(np.sqrt(flow.k2)*sizes))
    V2 = float(np.sum(flow.k2*sizes))
    eig = np.linalg.eigvalsh(strain)
    # Solenoidality improves the strain-Hessian Lipschitz constant to V2/2.
    margin = np.sqrt(3)*np.pi*V2/(4*n)
    Sm = min(V1/2, float((-eig[..., 0]).max())+margin)
    Sp = min(V1/2, float(eig[..., -1].max())+margin)
    gsizes = np.sqrt(np.sum(abs(gh)**2, axis=-1))/m**3
    weights = np.array([1 if i == j else 2 for i, j in PAIRS])
    return dict(S=Sm, Splus=Sp, D=V2, V0=V0, V1=V1, V2=V2,
                epsilon0=l2(residual[..., :3]),
                epsilon1=l2(residual[..., :3], k2[..., None]),
                rI=l2(residual[..., 3:6]), rQ=l2(residual[..., 6:12], weights),
                rT=l2(residual[..., 12:15]),
                rPhi=float(abs(residual[0, 0, 0, 15])/m**3),
                G0=float(gsizes.sum()), G1=float(np.sum(np.sqrt(k2)*gsizes)),
                G2=l2(gh), reference_H1=float(np.sqrt(np.sum(flow.k2*sizes**2))))


def initial_controls():
    return dict.fromkeys(('X', 'Y', 'path', 'impulse', 'e1', 'e2', 'e3', 'e4',
                          'energy_rhs', 'V0_squared', 'linear_pressure', 'Y_squared',
                          'local_pressure_sum', 'trajectory_sum'), 0.)


def propagate(old, row, h, nu):
    """Feasibility arithmetic; valid inequalities require enclosed inputs.

    All errors start at the original datum. The cumulative dissipation
    account never charges a fresh initial gradient at a later seam.
    This floating implementation does not enclose its own rounding.
    """
    require(h > 0 and nu > 0 and all(v >= 0 for v in row.values()),
            'Positive slab and viscosity, nonnegative norm majorants')
    vel = control_step(old['X'], old['Y'], row, h, nu)
    X, Y = vel['Xmax'], vel['Ymax']
    kappa = 27*(26*22/7)**2/(32*nu**3)
    rhs = 2*h*(2*row['S']*Y**2+row['D']*X*Y+kappa*Y**6+row['epsilon1']*Y)
    dissipation = (old['Y']**2+rhs)/nu
    energy_rhs = old['energy_rhs']+rhs
    V0_squared = old['V0_squared']+h*row['V0']**2
    linear_pressure = old['linear_pressure']+h*(2*row['V1']*Y+row['V2']*X)
    Y_squared = old['Y_squared']+h*Y**2
    direct = 3*(row['V0']*np.sqrt(h*dissipation)
                +h*(2*row['V1']*Y+row['V2']*X)
                +40*np.sqrt(Y)*h**.25*dissipation**.75)
    local_sum = old['local_pressure_sum']+direct
    cumulative = 3*(np.sqrt(V0_squared*energy_rhs/nu)+linear_pressure
                    +40*Y_squared**.25*(energy_rhs/nu)**.75)
    path = np.exp(row['Splus']*h)*(old['path']+3*Y*h)
    trajectory = old['trajectory_sum']+h*row['G1']*path
    e1 = old['e1']+h*row['rI']
    e2 = old['e2']+h*(2*row['G0']*e1+row['rQ'])
    e3 = old['e3']+h*(4*row['G0']*e2+row['rT'])
    e4 = old['e4']+h*(4*row['G2']*e3+row['rPhi'])
    result = dict(X=vel['X'], Y=vel['Y'], path=float(path),
                  impulse=float(min(local_sum, cumulative)+trajectory),
                  e1=e1, e2=e2, e3=e3, e4=e4, energy_rhs=energy_rhs,
                  V0_squared=V0_squared, linear_pressure=linear_pressure,
                  Y_squared=Y_squared, local_pressure_sum=float(local_sum),
                  cumulative_pressure=float(cumulative), trajectory_sum=float(trajectory),
                  Xmax=X, Ymax=Y, dissipation=dissipation)
    require(all(np.isfinite(v) for v in result.values()), 'Finite comparison controls')
    return result


def independent_jets():
    """Full rational NS and moment derivatives, independent of polarization."""
    import pressure_history_source as f
    from cyclic_pressure_history import velocity_time_jets
    from joint_pressure_return import seed

    nu, delta = Q(2, 7), Q(3, 4)
    flow = make_flow(12, float(nu), float(delta))
    u, p = velocity_time_jets(seed(delta), nu, 2)
    g0, g1 = f.grad(p[0]), f.grad(p[1])
    first = u[1]+g0+[{} for _ in range(10)]
    second = u[2]+[f.add(f.scale(f.QQ_I(nu), f.lap(g0[j])),
                         f.scale(-1, f.adv(u[0], g0[j])), g1[j]) for j in range(3)]
    second += [f.scale(2, f.mul(g0[i], g0[j])) for i, j in PAIRS]
    second += [{} for _ in range(4)]
    errors = []
    for observed, fields in zip(jets(flow, flow.initial), (first, second)):
        expected = np.zeros_like(observed)
        require(len(fields) == 16, 'All velocity and conditional-moment fields are checked')
        for j, field in enumerate(fields):
            for k, a in field.items():
                require(max(map(abs, k)) < flow.n/3, 'The fixture retains every generated output')
                expected[tuple(q % flow.n for q in k)+(j,)] = complex(float(a.x), float(a.y))*flow.n**3
        error = float(np.max(abs(observed-expected))/max(1., np.max(abs(expected))))
        require(error < 2e-13, 'Both complete derivatives match independent rational Fourier jets')
        errors.append(error)
    row = sample(flow, flow.initial, jets(flow, flow.initial)[0])
    residual = max(row[k] for k in ('epsilon0', 'epsilon1', 'rI', 'rQ', 'rT', 'rPhi'))
    require(residual < 2e-12, 'Independent complete spatial residual at the exact initial tangent')
    return dict(relative_errors=errors, initial_residual_max=residual)


def exact_checks():
    import sympy as s
    from pressure_impulse_envelope import polynomial_interval
    from reciprocal_pressure_payment import coefficients

    x, y, a, b = s.symbols('x y a b')
    poly = lambda x, y: x*x+3*x*y+2*y*y+x**3+5*x*x*y+7*x*y*y+11*y**3
    derivative = (poly(x+a, y+b)-poly(x-a, y-b)-poly(a, b)+poly(-a, -b))/2
    require(s.expand(derivative-a*s.diff(poly(x, y), x)-b*s.diff(poly(x, y), y)) == 0,
            'Cubic polarization retains the full mixed derivative')
    n = s.symbols('n')
    require(s.expand((2*n+1)**3-(2*n-1)**3) == 24*n*n+2,
            'Exact lattice-shell count for the spatial L4 bridge')
    require(24*2+Q(2)*Q(4, 3) < 3**4 and 26*Q(22, 7) < 10**2,
            'Sobolev constant three and Agmon constant ten')
    require(2+s.sqrt(3) < 4, 'Symmetric tensor source uses the Frobenius norm')
    nu, seam = Q(1, 4), Q(1, 64)
    theta = 2*27*(26*4)**2/(32*nu**3)*seam**4/nu
    require(theta < Q(3, 10), 'The actual small-gradient tail stays in its basin')
    dissipation = seam**2/(nu*Q(7, 10))
    radius = 120*dissipation
    require(dissipation == Q(5, 3584) and radius == Q(75, 448),
            'The same full tail dissipation pays the remaining pressure impulse')
    root = Q(99, 70)
    require(root**4 > 4 and (root+radius)**4 < Q(63, 10) < Q(757, 120),
            'Inherited and future fourth-root costs fit the original heat stock')
    lower, _ = polynomial_interval(coefficients(Q(1), degree=8)[8], Q(3))
    require(4**4*lower > Q(63, 10), 'The sharper heat curve also pays the tail after time12')
    return dict(status='Exact control constants and tail seam passed',
                tail=dict(nu='1/4', actual_gradient_upper='1/64', actual_phi_upper='4',
                          future_impulse_radius=str(radius), completed_phi_upper=str((root+radius)**4),
                          heat_stock='757/120'),
                scope='Conditional analytic comparison; no strong numerical prefix is certified')


def run(n, nu, delta, dt, h, final):
    require(n >= 12 and n % 2 == 0 and min(nu, dt, h, final) > 0,
            'Even retained grid and positive physical/time parameters')
    steps, slabs = round(h/dt), round(final/h)
    require(steps >= 1 and slabs >= 1 and abs(steps*dt-h) < 1e-12
            and abs(slabs*h-final) < 1e-12, 'Integral time steps and comparison slabs')
    flow = make_flow(n, nu, delta)
    state, controls = flow.initial.copy(), initial_controls()
    first, second = jets(flow, state)
    start = time.time()
    stock = (Q(11, 2048)*(1+delta**8)+Q(427, 30720)*delta**4)/nu**4
    yield dict(n=n, nu=nu, delta=delta, dt=dt, h=h, final=final,
               scope='Sampled time controls without rounding; not a continuum certificate')
    for slab in range(slabs):
        initial, f0, j0 = state.copy(), first, second
        for _ in range(steps):
            state, _ = flow.step(state, dt)
        first, second = jets(flow, state)
        coeff = hermite(initial, state, f0, first, j0, second, h)
        rows = [sample(flow, *evaluate(coeff, tau, h)) for tau in (0., .5, 1.)]
        row = {k: max(r[k] for r in rows) for k in rows[0]}
        try:
            controls = propagate(controls, row, h, nu)
        except (ArithmeticError, OverflowError) as ex:
            yield dict(time=(slab+1)*h, status='control failed', reason=str(ex),
                       row=row, previous=controls)
            break
        scalar = [float(c[0, 0, 0, 15].real/n**3) for c in coeff]
        upper = max(sum(scalar[j]*comb(k, j)/comb(5, j) for j in range(k+1)) for k in range(6))
        root = max(0., upper+controls['e4'])**.25+controls['impulse']
        yield dict(time=(slab+1)*h, control=controls, row=row,
                   endpoint_epsilon1=[rows[0]['epsilon1'], rows[-1]['epsilon1']],
                   phi=float(state[0, 0, 0, 15].real/n**3),
                   reference_phi_slab_upper=upper, final_reference_H1=rows[-1]['reference_H1'],
                   conditional_phi_bound=root**4, heat_stock=float(stock))
    yield dict(elapsed=time.time()-start)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prefix', action='store_true')
    parser.add_argument('--n', type=int, default=32)
    parser.add_argument('--nu', type=float, default=.25)
    parser.add_argument('--delta', type=float, default=1.)
    parser.add_argument('--dt', type=float, default=1/128)
    parser.add_argument('--h', type=float, default=1/16)
    parser.add_argument('--final', type=float, default=18.)
    args = parser.parse_args()
    if args.prefix:
        for row in run(args.n, args.nu, args.delta, args.dt, args.h, args.final):
            print(json.dumps(row), flush=True)
    else:
        print(json.dumps(dict(algebra=exact_checks(), physical_jets=independent_jets()), indent=2))
