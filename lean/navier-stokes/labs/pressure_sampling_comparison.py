#!/usr/bin/env python3
"""Two pressure-history observations of one unforced numerical NS flow.

The physical observer follows drift u; the auxiliary observer follows zero
drift with the same viscosity and the same evolving pressure. Each retains
its original first, symmetric second, contracted third and mean fourth
moments. Neither observer changes the fluid. Prefixes are numerical
discovery tests, without continuum or rounding enclosures.
"""

import argparse
from fractions import Fraction as Q
import json
import time

import numpy as np

from cellular_parent_history import PAIRS
from pressure_oblique_amplitude import leading_stock
from pressure_oblique_certificate import make_flow
from pressure_prefix_control import VelocityFlow, require


class SamplingComparison(VelocityFlow):
    def __init__(self, n, nu, amplitude, weights, auxiliary_drift=0.):
        super().__init__(n, nu)
        self.base = make_flow(n, nu, amplitude, weights=weights)
        self.initial = np.zeros((n, n, n, 29), complex)
        self.initial[..., :16] = self.base.initial
        self.auxiliary_drift = auxiliary_drift

    def pressure_gradient(self, velocity):
        u, gradient = self.ifft(velocity), self.grad_hat(velocity)
        adv = self.fft(sum(u[..., j, None]*gradient[j] for j in range(3)))
        gh = -self.K*self.inv[..., None]*np.sum(self.K*adv, axis=-1)[..., None]
        return gh*self.mask[..., None]

    def rhs(self, state):
        original, loss = self.base.rhs(state[..., :16])
        g = self.ifft(self.pressure_gradient(state[..., :3]))
        moments = self.ifft(state[..., 16:])
        nonlinear = np.zeros_like(moments)
        if self.auxiliary_drift:
            u, gradient = self.ifft(state[..., :3]), self.grad_hat(state[..., 16:])
            nonlinear -= self.auxiliary_drift*sum(u[..., j, None]*gradient[j] for j in range(3))
        nonlinear[..., :3] += g
        second = np.zeros(moments.shape[:-1]+(3, 3))
        for j, (a, b) in enumerate(PAIRS):
            second[..., a, b] = second[..., b, a] = moments[..., 3+j]
            nonlinear[..., 3+j] += moments[..., a]*g[..., b]+moments[..., b]*g[..., a]
        nonlinear[..., 9:12] += 2*np.einsum('...ij,...j->...i', second, g) \
            +np.trace(second, axis1=-2, axis2=-1)[..., None]*g
        auxiliary = self.fft(nonlinear)*self.mask[..., None]
        auxiliary[..., 12] = 0
        auxiliary[0, 0, 0, 12] = 4*np.mean(np.sum(g*moments[..., 9:12], axis=-1))*self.n**3
        gradient_l4 = np.mean(np.sum(g*g, axis=-1)**2)**.25
        return np.concatenate((original, auxiliary), axis=-1), np.r_[loss, gradient_l4]

    def report(self, t, state, spent, stock):
        physical = self.base.report(t, state[..., :16], spent[0], lambda _: stock)
        alternate = np.concatenate((state[..., :3], state[..., 16:]), axis=-1)
        auxiliary = self.base.report(t, alternate, spent[0], lambda _: stock)
        return dict(time=t, physical=physical, brownian=auxiliary,
                    physical_over_brownian=physical['phi']/auxiliary['phi'] if auxiliary['phi'] else None,
                    integrated_pressure_gradient_l4=float(spent[1]),
                    absolute_source_cost_over_stock=float(spent[1]**4/stock))


def checks():
    """Check the generator, independent Fourier pressure, and observer isolation."""
    import sympy as s
    import pressure_history_source as f
    from joint_pressure_return import seed

    p, g = s.symbols('p0:3'), s.symbols('g0:3')
    square = sum(a*a for a in p)
    directional = lambda v: s.expand(sum(b*s.diff(v, a) for a, b in zip(p, g)))
    for i in range(3):
        require(directional(p[i]) == g[i], 'First moment source')
        require(s.expand(directional(square*p[i])-2*p[i]*sum(a*b for a, b in zip(p, g))
                         -square*g[i]) == 0, 'Contracted third moment source')
        for j in range(3):
            require(s.expand(directional(p[i]*p[j])-p[i]*g[j]-p[j]*g[i]) == 0,
                    'Symmetric second moment source')
    require(s.expand(directional(square**2)-4*square*sum(a*b for a, b in zip(p, g))) == 0,
            'Spatially averaged fourth moment source')

    n = 24
    flow = SamplingComparison(n, 1., 8., (Q(1, 8), Q(1), Q(1, 8)))
    state = flow.initial.copy()
    state[..., :3] = 0
    initial = seed(Q(1))
    for j, field in enumerate(initial):
        for k, value in field.items():
            state[tuple(v % n for v in k)+(j,)] = n**3*complex(float(value.x), float(value.y))
    expected = np.zeros_like(state[..., :3])
    pressure = f.grad(f.tensor_pressure(f.tensor(initial, initial)))
    require(any(pressure), 'The independent test has nonzero initial pressure')
    for j, field in enumerate(pressure):
        for k, value in field.items():
            expected[tuple(v % n for v in k)+(j,)] = n**3*complex(float(value.x), float(value.y))
    relative = lambda a, b: float(np.max(abs(a-b))/max(1., np.max(abs(b))))
    pressure_error = relative(flow.pressure_gradient(state[..., :3]), expected)
    require(pressure_error < 2e-14, 'Independent exact Fourier pressure gradient')
    first, _ = flow.rhs(state)
    require(relative(first[..., 3:6], expected) < 2e-14
            and relative(first[..., 16:19], expected) < 2e-14,
            'Both original histories receive the same actual pressure')

    # Nonzero moments test the whole triangular recurrence, including transport.
    x = 2*np.pi*np.arange(n)/n
    X, Y, Z = np.meshgrid(x, x, x, indexing='ij')
    v = np.stack((np.sin(X)+np.cos(Y), np.cos(Z), np.sin(X+Y)), axis=-1)
    moment = np.zeros((n, n, n, 13))
    moment[..., :3] = v
    for j, (a, b) in enumerate(PAIRS):
        moment[..., 3+j] = v[..., a]*v[..., b]
    moment[..., 9:12] = np.sum(v*v, axis=-1)[..., None]*v
    moment[..., 12] = np.mean(np.sum(v*v, axis=-1)**2)
    state[..., 3:16] = state[..., 16:] = flow.fft(moment)
    flow.auxiliary_drift = 1.
    result, _ = flow.rhs(state)
    same_error = relative(result[..., 16:], result[..., 3:16])
    require(same_error < 2e-14, 'Identical drift gives the same complete moment operator')
    flow.auxiliary_drift = 0.
    altered = state.copy()
    altered[..., 16:] *= 7
    a, _ = flow.rhs(state)
    b, _ = flow.rhs(altered)
    require(np.array_equal(a[..., :16], b[..., :16]), 'Auxiliary history cannot change the physical subsystem')
    require(np.max(abs(a[..., 16:28]-result[..., 16:28])) > 1,
            'Removing drift really changes a nonconstant retained history')

    coupled, _ = flow.step(state, 1/1024)
    original, _ = flow.base.step(state[..., :16], 1/1024)
    step_error = relative(coupled[..., :16], original)
    require(step_error < 2e-14, 'Full numerical step preserves the original physical subsystem')
    require(np.all(flow.initial[..., 3:] == 0), 'Both original histories start once at zero')
    return dict(status='Generator and same-fluid observer checks passed',
                pressure_relative_error=pressure_error, equal_drift_relative_error=same_error,
                physical_step_relative_error=step_error,
                scope='Exact polynomial identities and rational pressure fixture; numerical operator comparisons')


def signed_sampling_jets():
    """The exact leading sampling difference has both signs at every viscosity."""
    import pressure_history_source as f
    from pressure_oblique_parents import datum
    from pressure_impulse_return import (NU, RING, impulse_fourth_coefficients,
                                         material_fourth_coefficients, specialize, viscosity_jets)

    cases = [((Q(1, 8), Q(1), Q(1, 8)), Q(833091743463037, 122316692502153978351452160)),
             ((Q(1), Q(1), Q(1)), -Q(324841148871529, 227832593959111680))]
    results = []
    for weights, expected in cases:
        initial = datum(weights)
        f.equal(f.trace(f.jac(initial)), {}, 'Actual divergence-free original datum')
        require(all(field.get((0, 0, 0), f.ZERO) == f.ZERO for field in initial),
                'Zero spatial mean, without a Galilean sampling artifact')
        velocity, pressure = viscosity_jets(initial, 4)
        require(not pressure[0], 'Both impulses start at second time order')
        gradient = [f.grad(p) for p in pressure]
        zero_drift = [[{}, {}, {}] for _ in velocity]
        physical = impulse_fourth_coefficients(velocity, gradient, NU)
        brownian = impulse_fourth_coefficients(zero_drift, gradient, NU)
        difference = [a-b for a, b in zip(physical, brownian)]
        require(difference == [RING.zero, RING.zero, RING.convert(expected)],
                'Exact viscosity-polynomial identity, with no interpolation')
        for drift, coefficients in ((velocity, physical), (zero_drift, brownian)):
            independent = material_fourth_coefficients(drift, gradient)
            require([c.evaluate(NU, f.ZERO) for c in coefficients] == independent,
                    'Independent material-path expansion checks both inviscid limits')
        A = [specialize(v, 0) for v in gradient[1]]
        B = [specialize(v, 0) for v in gradient[2]]
        LA = [f.adv(initial, v) for v in A]
        aa, al, ab = f.dot(A, A), f.dot(A, LA), f.dot(A, B)
        mean = lambda field: field.get((0, 0, 0), f.ZERO)
        mixing = mean(f.add(f.mul(aa, f.dot(LA, LA)), f.scale(2, f.mul(al, al))))
        correlation = mean(f.add(f.mul(aa, f.dot(LA, B)), f.scale(2, f.mul(al, ab))))
        require(not mixing.y and mixing.x > 0 and not correlation.y,
                'The frozen-source mixing form is positive')
        require(-(mixing+correlation)/144 == f.QQ_I(expected),
                'Signed evolving-source correlation gives the complete leading sampling defect')
        results.append(dict(weights=list(map(str, weights)),
                            physical_t8_t9_t10=list(map(str, physical)),
                            brownian_t8_t9_t10=list(map(str, brownian)),
                            difference_t10=str(expected), sign=1 if expected > 0 else -1,
                            mixing_form=str(mixing.x), source_correlation=str(correlation.x),
                            minus_correlation_over_mixing=str(-correlation.x/mixing.x)))
    return dict(status='Both signs verified for the same-pressure sampling comparison',
                cases=results, viscosity='Polynomial identity for every viscosity; no fitted coefficients',
                scope='Exact NS and moment jets; actual positive-time comparison uses smooth local PDE evolution')


def run(n, nu, amplitude, weights, dt, final, report_interval):
    require(n > 12 and n % 2 == 0 and min(nu, amplitude, dt, final, report_interval) > 0,
            'Even retained grid and positive parameters')
    require(all(np.isfinite(a) for a in (nu, amplitude, dt, final, report_interval)), 'Finite parameters')
    steps, stride = round(final/dt), round(report_interval/dt)
    require(steps > 0 and stride > 0 and steps*Q(dt) == Q(final)
            and stride*Q(dt) == Q(report_interval), 'Exact integer step counts')
    stock, _, _ = leading_stock(amplitude, nu, weights)
    flow = SamplingComparison(n, nu, amplitude, weights)
    state, spent, start = flow.initial.copy(), np.zeros(2), time.monotonic()
    yield dict(n=n, nu=nu, amplitude=amplitude, weights=list(map(str, weights)), dt=dt,
               final=final, stock=str(stock), stock_approx=float(stock),
               scope='Numerical discovery only; same NS pressure, distinct observers, no continuum enclosure')
    for step in range(1, steps+1):
        state, cost = flow.step(state, dt)
        spent += cost
        require(np.all(np.isfinite(state)), 'Finite joint numerical state')
        if step % stride == 0 or step == steps:
            result = flow.report(step*dt, state, spent, float(stock))
            result['elapsed'] = time.monotonic()-start
            yield result
    yield dict(status='Sampling comparison complete', elapsed=time.monotonic()-start)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prefix', action='store_true')
    parser.add_argument('--jets', action='store_true')
    parser.add_argument('--n', type=int, default=32)
    parser.add_argument('--nu', type=float, default=1.)
    parser.add_argument('--amplitude', type=float, default=8.)
    parser.add_argument('--weights', nargs=3, type=Q, default=(Q(1, 8), Q(1), Q(1, 8)))
    parser.add_argument('--dt', type=float, default=1/1024)
    parser.add_argument('--final', type=float, default=.5)
    parser.add_argument('--report-interval', type=float, default=.125)
    args = parser.parse_args()
    require(not (args.prefix and args.jets), 'Select either numerical histories or exact time jets')
    if args.jets:
        print(json.dumps(signed_sampling_jets(), indent=2))
    elif args.prefix:
        for result in run(args.n, args.nu, args.amplitude, tuple(args.weights),
                          args.dt, args.final, args.report_interval):
            print(json.dumps(result), flush=True)
    else:
        print(json.dumps(checks(), indent=2))
