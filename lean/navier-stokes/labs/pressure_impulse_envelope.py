#!/usr/bin/env python3
"""A combined pressure envelope, with a counterexample to rate domination.

The default exact check retains the complete amplitude coefficients through
degree sixteen. Analytic remainders and actual-flow conclusions are in
README.md. Optional Fourier prefixes are discovery experiments, not continuum
certificates. They retain the conditional pressure moments without restarting.
"""

import argparse
import json
from fractions import Fraction as Q
from math import factorial

import paired_stretching_history as e
from pressure_impulse_payment import history, require, signed_cascade


def exp_negative_interval(t, order=120):
    """Rational enclosure from the positive exponential series and its tail."""
    t = Q(t)
    require(t >= 0 and order+2 > t, 'A geometric majorant bounds the remaining terms')
    term, total = Q(1), Q(1)
    for n in range(1, order+1):
        term *= t/n
        total += term
    tail = term*t/(order+1)/(1-t/(order+2))
    return 1/(total+tail), 1/total


def polynomial_interval(field, t):
    lower, upper = exp_negative_interval(t)
    lo = hi = Q(0)
    for (rate, degree), value in field.items():
        require(rate >= 0 and degree >= 0, 'Nonnegative integer exponential rates and degrees')
        coefficient = value*Q(t)**degree
        a, b = lower**rate, upper**rate
        lo += coefficient*(a if coefficient >= 0 else b)
        hi += coefficient*(b if coefficient >= 0 else a)
    return lo, hi


def exact_checks():
    fields = history(1, degree=16)
    a, b, c = fields[12], fields[14], fields[16]
    leading, depletion = Q(99, 512), Q(20641, 152064)
    reinforcement = Q(106168693607, 2059433164800)
    margin = depletion**2/leading-reinforcement
    require(margin == Q(2972406502169, 67961294438400) and margin > 0,
            'The combined envelope pays the positive next correction at the nonlinear clock origin')
    for field, order, expected in [(a, 8, leading), (b, 10, -depletion),
                                    (c, 12, reinforcement)]:
        require(all(e.jet(field, n) == 0 for n in range(order)), 'Complete lower time jets vanish')
        require(e.jet(field, order)/factorial(order) == expected, 'Exact leading time coefficient')

    # H/F0 is the complete next difference from the rational envelope.
    h = e.add(e.multiply(a, c), e.scale(-1, e.multiply(b, b)))
    require(e.jet(h, 20)/factorial(20) == -leading*margin,
            'The joint gap begins at the twentieth time order')
    certificate = signed_cascade(e.derivative(h), -1)
    require(certificate['first_nonzero']['order'] == 19,
            'A uniform small-time margin is supplied by the finite sign certificate')

    # G'=K/F0^2 for G=F16-F14^2/F0. Rate comparison can fail although G<0.
    rate = e.add(e.multiply(e.multiply(a, a), e.derivative(c)),
                 e.scale(-2, e.multiply(e.multiply(a, b), e.derivative(b))),
                 e.multiply(e.multiply(b, b), e.derivative(a)))
    lo, hi = polynomial_interval(rate, Q(12))
    require(Q(3, 10**41) < lo <= hi < Q(4, 10**41),
            'Strictly positive rate defect at time twelve, certified by rational endpoints')
    limits = [field[(0, 0)] for field in (a, b, c)]
    slow = [field[(6, 3)] for field in (a, b, c)]
    slow_gap = slow[2]-2*limits[1]*slow[1]/limits[0]+limits[1]**2*slow[0]/limits[0]**2
    require(slow_gap < 0, 'The gap approaches its limiting value from below at sufficiently late times')
    return dict(status='all exact checks passed',
                comparison='Phi_epsilon <= epsilon^12 F0^2/(F0-epsilon^2 F14)',
                scope='all-time small-amplitude comparison and a uniform strong-amplitude initial interval are analytic',
                initial_margin=str(margin), joint_gap_derivative=certificate,
                rate_defect_at_twelve={'lower': '3/10^41', 'upper': '4/10^41'},
                slow_gap_coefficient=str(slow_gap),
                limitation='the combined envelope for arbitrary amplitudes over arbitrary horizons is OPEN')


def material_check():
    """Independent Euler material paths, without stochastic moment recurrences."""
    import pressure_history_source as f
    from cyclic_pressure_history import seed, velocity_time_jets
    from cyclic_entropy_depletion import material_jets

    velocity, pressure = velocity_time_jets(seed(Q(1)), Q(0), 6)
    gradients = [f.grad(p) for p in pressure]
    paths = [material_jets([row[i] for row in gradients], velocity) for i in range(3)]
    impulse = [[{}, {}]+[f.scale(Q(1, factorial(n+1)), row[n]) for n in range(1, 6)]
               for row in paths]
    squares = {n: f.add(*(f.mul(impulse[i][r], impulse[i][n-r]) for i in range(3)
                          for r in range(2, 7) if 2 <= n-r <= 6)) for n in range(4, 9)}
    expected = {8: Q(99, 512), 10: -Q(20641, 152064),
                12: Q(106168693607, 2059433164800)}
    for n, value in expected.items():
        coefficient = f.add(*(f.mul(squares[r], squares[n-r]) for r in range(4, 9)
                              if 4 <= n-r <= 8)).get((0, 0, 0), f.ZERO)
        require(coefficient == f.QQ_I(value), ('Independent complete material-path coefficient', n))
    return dict(status='independent Euler material-path coefficients passed',
                coefficients={n: str(v) for n, v in expected.items()})


def numerical_prefixes(n, viscosities, dt, final):
    import time
    import mpmath as mp
    import numpy as np
    from reciprocal_parent_history import Flow
    from cellular_parent_history import PAIRS
    from cyclic_pressure_history import seed

    mp.mp.dps = 60
    coefficients = history(1)

    def evaluate(field, t):
        return mp.fsum(mp.mpf(c.numerator)/c.denominator*t**j*mp.exp(-rate*t)
                       for (rate, j), c in field.items())

    def bound(nu, t):
        if not t:
            return 0.
        t = mp.mpf(str(t))
        if not nu:
            a, d = mp.mpf(99)/512, mp.mpf(20641)/152064
            return float(a*a*t**8/(a+d*t*t))
        v = mp.mpf(str(nu))
        a, b = evaluate(coefficients[12], v*t), evaluate(coefficients[14], v*t)
        return float(v**-8*a*a/(a-v**-2*b))

    class ImpulseFlow(Flow):
        def __init__(self, nu):
            self.n, self.nu = n, nu
            frequencies = np.rint(np.fft.fftfreq(n)*n)
            self.K = np.stack(np.meshgrid(frequencies, frequencies, frequencies, indexing='ij'), axis=-1)
            self.k2 = np.sum(self.K**2, axis=-1)
            self.inv = np.divide(1., self.k2, out=np.zeros_like(self.k2), where=self.k2 > 0)
            self.heat = -nu*self.k2
            self.mask = np.all(abs(self.K) < n/3, axis=-1)
            self.high = self.mask & np.any(abs(self.K) > .8*n/3, axis=-1)
            self.initial = np.zeros((n, n, n, 16), complex)
            for j, field in enumerate(seed(Q(1))):
                for k, value in field.items():
                    self.initial[tuple(q % n for q in k)+(j,)] = complex(float(value.x), float(value.y))*n**3

        def rhs(self, state):
            values, gradient = self.ifft(state), self.grad_hat(state)
            u = values[..., :3]
            adv = sum(u[..., j, None]*gradient[j] for j in range(3))
            ah = self.fft(adv)
            gh = -self.K*self.inv[..., None]*np.sum(self.K*ah[..., :3], axis=-1)[..., None]
            gh *= self.mask[..., None]
            g = self.ifft(gh)
            nonlinear = -adv
            nonlinear[..., 3:6] += g
            second = np.zeros(values.shape[:-1]+(3, 3))
            for j, (a, b) in enumerate(PAIRS):
                second[..., a, b] = second[..., b, a] = values[..., 6+j]
                nonlinear[..., 6+j] += values[..., 3+a]*g[..., b]+values[..., 3+b]*g[..., a]
            nonlinear[..., 12:15] += 2*np.einsum('...ij,...j->...i', second, g) \
                +np.trace(second, axis1=-2, axis2=-1)[..., None]*g
            result = self.fft(nonlinear)*self.mask[..., None]
            result[..., :3] = -ah[..., :3]*self.mask[..., None]-gh
            # The final observation is spatially integrated; transport and diffusion cancel.
            result[..., 15] = 0
            result[0, 0, 0, 15] = 4*np.mean(np.sum(g*values[..., 12:15], axis=-1))*n**3
            loss = self.nu*np.mean(sum(np.sum(q[..., :3]**2, axis=-1) for q in gradient))
            return result, np.array([loss])

        def report(self, t, state, spent):
            values = self.ifft(state)
            first = values[..., 3:6]
            second = np.zeros(values.shape[:-1]+(3, 3))
            for j, (a, b) in enumerate(PAIRS):
                second[..., a, b] = second[..., b, a] = values[..., 6+j]
            ud = self.k2*np.sum(abs(state[..., :3])**2, axis=-1)
            md = np.sum(abs(state[..., 3:15])**2, axis=-1)
            energy = np.mean(np.sum(values[..., :3]**2, axis=-1))/2
            phi = state[0, 0, 0, 15].real/n**3
            envelope = bound(self.nu, t)
            return dict(time=t, phi=float(phi), envelope=envelope,
                        ratio=float(phi/envelope) if envelope else 0.,
                        energy_balance=float(energy+spent-.75),
                        high_velocity_fraction=float(np.sum(ud[self.high])/max(np.sum(ud), 1e-300)),
                        high_moment_fraction=float(np.sum(md[self.high])/max(np.sum(md), 1e-300)),
                        minimum_covariance=float(np.linalg.eigvalsh(
                            second-first[..., None]*first[..., None, :]).min()))

    require(n >= 12 and n % 2 == 0 and dt > 0 and final > 0
            and all(v >= 0 for v in viscosities), 'Valid numerical discovery parameters')
    steps = int(round(final/dt))
    require(steps > 0 and abs(steps*dt-final) < 1e-10, 'The final time is an integer number of steps')
    for nu in viscosities:
        flow = ImpulseFlow(nu)
        state, spent, start, observations = flow.initial.copy(), 0., time.time(), []
        for step in range(1, steps+1):
            state, cost = flow.step(state, dt)
            spent += cost[0]
            if step % max(1, round(.125/dt)) == 0 or step == steps:
                observations.append(flow.report(step*dt, state, spent))
        yield dict(scope='dealiased Fourier approximation; no continuum error enclosure',
                   n=n, nu=nu, dt=dt, elapsed=time.time()-start, observations=observations)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prefix', action='store_true', help='run numerical discovery prefixes instead of exact certificates')
    parser.add_argument('--material-check', action='store_true', help='check the leading terms independently on Euler material paths')
    parser.add_argument('--n', type=int, default=24)
    parser.add_argument('--nu', type=float, nargs='+', default=[.05, .25, 1.])
    parser.add_argument('--dt', type=float, default=.005)
    parser.add_argument('--final', type=float, default=2.)
    args = parser.parse_args()
    if args.material_check:
        require(not args.prefix, 'Select either the independent material check or numerical prefixes')
        print(json.dumps(material_check(), indent=2))
    elif args.prefix:
        for result in numerical_prefixes(args.n, args.nu, args.dt, args.final):
            print(json.dumps(result), flush=True)
    else:
        print(json.dumps(exact_checks(), indent=2))
