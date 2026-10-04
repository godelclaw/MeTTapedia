#!/usr/bin/env python3
"""Finite-amplitude discovery for the original joint pressure-gradient stock.

The complete resolved velocity evolves without parent resets. Padded products
retain every pressure output of that state, including modes beyond the
velocity cutoff. These floating-point Galerkin histories are not continuum
enclosures. The analytic small-data payment and tail consumer are separate.
"""

import argparse
from fractions import Fraction as Q
import json
import time

import numpy as np

from pressure_gradient_stock import weighted_datum
from reciprocal_parent_history import Flow


ALPHA = Q(116161, 9332512200)


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


class GradientFlow(Flow):
    """Reuse the established integrating-factor RK4 velocity integrator."""

    def __init__(self, n, nu, amplitude, weights=(Q(1, 4), Q(1), Q(1))):
        require(n >= 24 and n % 4 == 0, 'Grid is a multiple of four, at least 24')
        require(np.isfinite(nu) and np.isfinite(amplitude) and nu > 0 and amplitude > 0,
                'Positive finite viscosity and amplitude')
        self.n, self.nu = n, nu
        self.m = 3*n//2
        self.pad = (self.m-n)//2
        frequencies = np.fft.fftfreq(n)*n
        self.K = np.stack(np.meshgrid(frequencies, frequencies, frequencies, indexing='ij'), axis=-1)
        self.k2 = np.sum(self.K*self.K, axis=-1)
        self.heat = -nu*self.k2
        self.mask = np.all(abs(self.K) < n/3, axis=-1)
        frequencies = np.fft.fftfreq(self.m)*self.m
        self.Kp = np.stack(np.meshgrid(frequencies, frequencies, frequencies, indexing='ij'), axis=-1)
        self.kp2 = np.sum(self.Kp*self.Kp, axis=-1)
        self.invp = np.divide(1, self.kp2, out=np.zeros_like(self.kp2), where=self.kp2 != 0)
        self.initial = self.encode(weighted_datum(4, tuple(Q(amplitude)*Q(x) for x in weights)))
        self.energy0 = float(np.sum(abs(self.initial/n**3)**2))

    def encode(self, fields):
        state = np.zeros((self.n, self.n, self.n, 3), dtype=complex)
        for j, field in enumerate(fields):
            for k, z in field.items():
                require(max(map(abs, k)) < self.n/3, 'Every prescribed mode is retained')
                state[tuple(x % self.n for x in k)+(j,)] = self.n**3*complex(float(z.x), float(z.y))
        return state

    def enlarged(self, state):
        p = self.pad
        return np.fft.ifftshift(np.pad(np.fft.fftshift(state, axes=(0, 1, 2)),
            ((p, p), (p, p), (p, p), (0, 0))), axes=(0, 1, 2))*(self.m/self.n)**3

    def operator(self, state):
        padded = self.enlarged(state)
        u = self.ifft(padded)
        adv = sum(u[..., j, None]*self.ifft(1j*self.Kp[..., j, None]*padded)
                  for j in range(3))
        negative_advection = self.fft(-adv)
        gradient = self.Kp*(self.invp*np.sum(self.Kp*negative_advection, axis=-1))[..., None]
        projected = negative_advection-gradient
        p = self.pad
        nonlinear = np.fft.ifftshift(np.fft.fftshift(projected, axes=(0, 1, 2))[
            p:p+self.n, p:p+self.n, p:p+self.n], axes=(0, 1, 2))*(self.n/self.m)**3
        nonlinear *= self.mask[..., None]
        cost = float(np.sum(abs(gradient)**2)/self.m**6)
        return nonlinear, cost, gradient

    def rhs(self, state):
        nonlinear, cost, _ = self.operator(state)
        dissipation = 2*self.nu*float(np.sum(self.k2[..., None]*abs(state/self.n**3)**2))
        return nonlinear, np.array([cost, dissipation])

    def report(self, t, state, ledger, stock):
        nonlinear, rate, _ = self.operator(state)
        density = np.sum(abs(state/self.n**3)**2, axis=-1)
        energy = float(np.sum(density))
        h1_squared = float(np.sum(self.k2*density))
        high = np.any(abs(self.K) > .8*self.n/3, axis=-1)
        div = np.sum(self.K*state, axis=-1)/self.n**3
        negative = (-np.arange(self.n)) % self.n
        reflected = state[np.ix_(negative, negative, negative)]
        tail = 169*h1_squared**2/self.nu
        return dict(time=t, cost=float(ledger[0]), cost_over_original_stock=float(ledger[0]/stock),
                    pressure_gradient_rate=rate, energy=energy, H1=float(np.sqrt(h1_squared)),
                    numerical_tail_entry=bool(np.sqrt(h1_squared) <= self.nu/26),
                    numerical_tail_allowance=tail,
                    cost_plus_tail_over_stock=float((ledger[0]+tail)/stock),
                    energy_balance_error=energy-self.energy0+float(ledger[1]),
                    nonlinear_energy_work=float(np.real(np.vdot(state, nonlinear))/self.n**6),
                    divergence_L2sq=float(np.sum(abs(div)**2)),
                    conjugacy_error=float(np.max(abs(state-np.conj(reflected)))/self.n**3),
                    mean_maximum=float(np.max(abs(state[0, 0, 0]))/self.n**3),
                    high_enstrophy_fraction=float(np.sum((density*self.k2)[high])/h1_squared)
                    if h1_squared else 0.)


def checks():
    """Independent physical operators and all-output pressure measurements."""
    import pressure_history_source as f
    from cyclic_pressure_history import velocity_time_jets
    amplitude, nu, weights = Q(2), Q(2, 7), (Q(1, 4), Q(1), Q(1))
    initial = weighted_datum(4, tuple(amplitude*x for x in weights))
    flow = GradientFlow(24, float(nu), float(amplitude), weights)
    velocity, _ = velocity_time_jets(initial, nu, 1)
    rhs, rate, _ = flow.operator(flow.initial)
    exact = flow.encode([f.add(du, f.scale(-nu, f.lap(u))) for du, u in zip(velocity[1], initial)])
    operator_error = float(np.max(abs(rhs-exact))/flow.n**3)
    require(operator_error < 2e-12 and rate < 1e-24, 'Independent complete initial NS operator')
    probe = [f.add(u, f.scale(Q(1, 7), du)) for u, du in zip(initial, velocity[1])]
    pressure = f.green(f.trace(f.matmul(f.jac(probe), f.jac(probe))))
    exact_gradient = f.grad(pressure)
    exact_rate = sum((z.x*z.x+z.y*z.y for field in exact_gradient for z in field.values()), f.ZERO.x)
    outside = sum((z.x*z.x+z.y*z.y for field in exact_gradient for k, z in field.items()
                   if max(map(abs, k)) >= flow.n/3), f.ZERO.x)
    _, measured, gradient = flow.operator(flow.encode(probe))
    reference = np.zeros_like(gradient)
    for j, field in enumerate(exact_gradient):
        for k, z in field.items():
            require(max(map(abs, k)) < flow.m/2, 'All pressure outputs fit the product grid')
            reference[tuple(x % flow.m for x in k)+(j,)] = flow.m**3*complex(float(z.x), float(z.y))
    pressure_error = float(np.max(abs(gradient-reference))/flow.m**3)
    require(outside > 0 and pressure_error < 2e-11 and abs(measured-float(exact_rate)) < 2e-10,
            'Complete canonical pressure includes strictly positive cost outside the velocity band')
    # This single parent is an exact heat flow and has no nonlinear pressure.
    heat_flow = GradientFlow(24, 1., 1., (Q(1), Q(0), Q(0)))
    state, ledger = heat_flow.initial.copy(), np.zeros(2)
    for _ in range(16):
        state, spent = heat_flow.step(state, 1/64)
        ledger += spent
    expected = heat_flow.initial*np.exp(.25*heat_flow.heat)[..., None]
    heat_error = float(np.max(abs(state-expected))/heat_flow.n**3)
    require(heat_error < 1e-13 and ledger[0] < 1e-26,
            'Exact decaying shear is reproduced without artificial pressure spending')
    # Independent canonical pressures verify the complete spatial error
    # identity used by the analytic accumulated-cost comparison.
    v = initial
    w = [f.scale(Q(1, 7), du) for du in velocity[1]]
    u = [f.add(a, b) for a, b in zip(v, w)]
    canonical = lambda z: f.green(f.trace(f.matmul(f.jac(z), f.jac(z))))
    pressure_difference = f.grad(f.add(canonical(u), f.scale(-1, canonical(v))))
    adv_difference = [f.add(f.adv(v, w[j]), f.adv(w, v[j]), f.adv(w, w[j])) for j in range(3)]
    complete = f.grad(f.green(f.trace(f.jac(adv_difference))))
    for a, b in zip(pressure_difference, complete):
        f.equal(a, b, 'Canonical pressure difference retains both cross terms and self interaction')
    mean_square = lambda z: f.dot(z, z).get(f.ORIGIN, f.ZERO).x
    require(0 < mean_square(complete) <= mean_square(adv_difference),
            'Nonzero full pressure projection is an L2 contraction on the exact fixture')
    return dict(status='Physical operator and pressure checks passed', initial_operator_error=operator_error,
                pressure_coefficient_error=pressure_error, pressure_cost_error=abs(measured-float(exact_rate)),
                exact_probe_cost=str(exact_rate), exact_cost_outside_velocity_band=str(outside),
                heat_error=heat_error, heat_cost=float(ledger[0]),
                exact_pressure_difference_cost=str(mean_square(complete)),
                scope='Exact Fourier reference with floating comparisons; no PDE enclosure')


def run(n, nu, amplitude, dt, final, report_interval):
    require(all(np.isfinite(x) and x > 0 for x in (nu, amplitude, dt, final, report_interval)),
            'Positive finite numerical parameters')
    steps, stride = round(final/dt), round(report_interval/dt)
    require(steps >= 1 and stride >= 1 and steps*Q(dt) == Q(final)
            and stride*Q(dt) == Q(report_interval), 'Exact integer timestep counts')
    flow = GradientFlow(n, nu, amplitude)
    stock = Q(amplitude)**6*ALPHA/(16*Q(nu)**3)
    state, ledger, start = flow.initial.copy(), np.zeros(2), time.monotonic()
    yield dict(n=n, pressure_grid=flow.m, nu=nu, amplitude=amplitude, weights=['1/4', '1', '1'],
               dt=dt, final=final, stock=str(stock), stock_approx=float(stock),
               scope='Numerical Galerkin discovery only; no continuum or rounding enclosure')
    yield flow.report(0., state, ledger, float(stock))
    for step in range(1, steps+1):
        state, spent = flow.step(state, dt)
        ledger += spent
        require(np.all(np.isfinite(state)) and np.all(np.isfinite(ledger)), 'Finite numerical history')
        if step % stride == 0 or step == steps:
            row = flow.report(step*dt, state, ledger, float(stock))
            row['elapsed'] = time.monotonic()-start
            yield row
    yield dict(status='Numerical prefix complete', elapsed=time.monotonic()-start)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prefix', action='store_true')
    parser.add_argument('--n', type=int, default=24)
    parser.add_argument('--nu', type=float, default=1.)
    parser.add_argument('--amplitude', type=float, default=2.)
    parser.add_argument('--dt', type=float, default=1/512)
    parser.add_argument('--final', type=float, default=8.)
    parser.add_argument('--report-interval', type=float, default=.25)
    args = parser.parse_args()
    if args.prefix:
        for row in run(args.n, args.nu, args.amplitude, args.dt, args.final, args.report_interval):
            print(json.dumps(row), flush=True)
    else:
        print(json.dumps(checks(), indent=2))
