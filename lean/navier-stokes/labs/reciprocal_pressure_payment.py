#!/usr/bin/env python3
"""Whole-time first-return depletion for reciprocal pressure parents.

Exact amplitude derivatives keep the complete projected NS vector field
and conditional pressure moments. Finite differential cascades certify
their signs for every time, not just sampled times. The small-amplitude
actual-flow remainder is analytic in README.md, not a Lean certificate.
Optional Fourier prefixes are discovery tests without continuum enclosures.
"""

import argparse
import json
from fractions import Fraction as Q
from math import factorial

import sympy as s
import paired_stretching_history as e
import pressure_impulse_payment as h
import pressure_history_source as f
from cyclic_pressure_history import velocity_time_jets
from joint_pressure_return import seed


def ordered_brownian_forecast(delta):
    """Independent four-time Brownian Fourier expectation, no moment PDE."""
    initial = seed(Q(delta))
    pressure = f.tensor_pressure(f.tensor(initial, initial))
    h.require(all(not v.y for v in pressure.values()), 'Real initial pressure coefficients')
    weights = {}
    def dot(k, ell):
        return sum(a*b for a, b in zip(k, ell))
    for k1, p1 in pressure.items():
        for k2, p2 in pressure.items():
            for k3, p3 in pressure.items():
                k4 = tuple(-a-b-c for a, b, c in zip(k1, k2, k3))
                if k4 not in pressure:
                    continue
                pair = tuple(a+b for a, b in zip(k1, k2))
                rates = (8, 6+dot(k1, k1), 4+dot(pair, pair), 2+dot(k4, k4))
                # The 24 time orderings give eight copies of each pairing.
                pairings = dot(k1, k2)*dot(k3, k4)+dot(k1, k3)*dot(k2, k4) \
                    +dot(k1, k4)*dot(k2, k3)
                value = 8*pairings*p1.x*p2.x*p3.x*pressure[k4].x
                weights[rates] = weights.get(rates, Q(0))+Q(str(value))
    result = {}
    for rates, weight in weights.items():
        simplex = e.constant(1)
        for rate in rates:
            simplex = e.heat_convolution(simplex, rate)
        result = e.add(result, e.scale(weight, simplex))
    return result


def coefficients(delta, degree=10, check_jets=False, source_gain=1, transport_gain=1):
    """Nonunit gains tag operator contributions, not alternative NS flows."""
    h.require(degree in (8, 10), 'Complete leading forecast or first return')
    highest = degree-6
    initial = seed(Q(delta))
    u = [{} for _ in range(highest+1)]
    for i, component in enumerate(initial):
        for k, value in component.items():
            h.require(not value.x, 'Odd real initial velocity')
            if k not in u[1]:
                u[1][k] = [{}, {}, {}]
            u[1][k][i] = {(1, 0): Q(str(value.y))}
    pressure = {}
    for n in range(2, highest+1):
        source = e.field_add(e.advection(u[a], u[n-a]) for a in range(1, n))
        projected, pressure[n] = e.project(source)
        u[n] = {k: tuple(e.heat_convolution(v, sum(q*q for q in k)) for v in row)
                for k, row in projected.items()}
        for k, row in u[n].items():
            h.require(not e.add(*(e.scale(k[i], row[i]) for i in range(3))),
                      'Every generated velocity coefficient is divergence free')
            for i, value in enumerate(row):
                h.require(e.add(e.derivative(value), e.scale(sum(q*q for q in k), value))
                          == projected[k][i], 'Complete projected velocity equation')
                h.require(e.jet(value, 0) == 0, 'No generated parent is initially inserted')
    if check_jets:
        literal_u, literal_p = velocity_time_jets(initial, Q(1), 3)
        for n in range(3):
            for i in range(3):
                observed = f.add(*({k: f.II*f.QQ_I(e.jet(row[i], n))
                                   for k, row in field.items()} for field in u[1:]))
                f.equal(observed, literal_u[n][i], 'Independent full NS time jets')
            observed = f.add(*({k: f.QQ_I(e.jet(value, n)) for k, value in field.items()}
                               for field in pressure.values()))
            f.equal(observed, literal_p[n], 'Independent full pressure time jets')
    g = {n: [{k: e.scale(k[i], v) for k, v in pressure[n].items() if k[i]}
             for i in range(3)] for n in pressure}
    g = {n: [h.scale(source_gain**(n-2), v) for v in row] for n, row in g.items()}
    u = [{k: tuple(e.scale(transport_gain*source_gain**(n-1), v) for v in row)
          for k, row in field.items()} if n else {} for n, field in enumerate(u)]
    first = {}
    for n in range(2, highest+1):
        first[n] = [h.heat(h.add(g[n][i], *(h.transport(u[a], first[n-a][i])
                     for a in range(1, n-1)))) for i in range(3)]
    second = {}
    for n in range(4, degree-3):
        second[n] = [[h.heat(h.add(*(
            h.add(h.multiply(first[a][i], g[n-a][j]), h.multiply(first[a][j], g[n-a][i]))
            for a in first if n-a in g),
            *(h.transport(u[a], second[n-a][i][j]) for a in range(1, n-3))))
            for j in range(3)] for i in range(3)]
    third = {}
    for n in range(6, degree-1):
        third[n] = [h.heat(h.add(*(
            h.add(h.scale(2, h.add(*(h.multiply(second[a][i][j], g[n-a][j]) for j in range(3)))),
                  h.multiply(h.add(*(second[a][j][j] for j in range(3))), g[n-a][i]))
            for a in second if n-a in g),
            *(h.transport(u[a], third[n-a][i]) for a in range(1, n-5)))) for i in range(3)]
    result = {}
    for n in range(8, degree+1):
        source = e.scale(4, e.add(*(h.mean_product(third[a][i], g[n-a][i])
                                    for a in third if n-a in g for i in range(3))))
        result[n] = e.heat_convolution(source, 0)
        h.require(e.derivative(result[n]) == source and e.jet(result[n], 0) == 0,
                  'Integrated fourth moment retains its full source and original history')
        h.require(result[n].get((0, 0), Q(0)) == e.integral_infinity(source),
                  'Independent whole-half-line integral')
        if n % 2:
            h.require(not result[n], 'Physical translation removes odd amplitude degrees')
    return result


def family_checks():
    x, y, z, d = s.symbols('x y z d', real=True)
    U = s.Matrix([s.sin(y)+d*s.sin(z), s.sin(x), d*s.sin(x)])
    reflected = U.subs(z, -z)
    reflected[2] = -reflected[2]
    h.require(reflected == U.subs(d, -d), 'Reflection gives even ratio dependence')
    swapped = U.subs({y: z, z: y}, simultaneous=True)
    swapped = s.Matrix([swapped[0], swapped[2], swapped[1]])
    h.require(all(s.simplify(a-b) == 0 for a, b in zip(swapped, d*U.subs(d, 1/d))),
              'Coordinate permutation gives reciprocal coefficient symmetry')
    a2, b2 = s.symbols('a2 b2', nonnegative=True)
    h.require(s.expand(16*(a2**5+b2**5)-(a2+b2)**5
                       -5*(a2-b2)**2*(a2+b2)*(3*a2**2+2*a2*b2+3*b2**2)) == 0,
              'The pure-parent savings dominate the joint tenth-degree norm')
    samples = {delta: coefficients(Q(delta), check_jets=True) for delta in (0, 1, 2)}
    for delta, fields in samples.items():
        h.require(fields[8] == ordered_brownian_forecast(delta),
                  'Independent ordered-time Brownian expectation matches the full heat moment')
    heat_self = samples[0][8]
    heat_cross = e.add(samples[1][8], e.scale(-2, heat_self))
    heat_parts = [heat_self, heat_cross]
    h.require(samples[2][8] == e.add(e.scale(257, heat_self), e.scale(16, heat_cross)),
              'Independent check of the Brownian quartic parity basis')
    matrix = s.Matrix([[1+delta**10, delta**2+delta**8, delta**4+delta**6]
                       for delta in (0, 1, 2)])
    inverse = matrix.inv()
    returns = [e.add(*(e.scale(Q(inverse[j, k]), samples[delta][10])
                       for k, delta in enumerate((0, 1, 2)))) for j in range(3)]
    # Degree-ten homogeneity and the two physical symmetries give this
    # three-dimensional basis. This unused sample is an additional check.
    test = Q(3, 4)
    unused = coefficients(test)
    weights = [1+test**10, test**2+test**8, test**4+test**6]
    h.require(unused[10] == e.add(*(e.scale(w, b) for w, b in zip(weights, returns))),
              'Unused exact full-output ratio checks the proved polynomial basis')
    h.require(unused[8] == e.add(e.scale(1+test**8, heat_self), e.scale(test**4, heat_cross)),
              'Unused exact heat-forecast ratio')
    heat_signs = [h.signed_cascade(e.derivative(a), 1) for a in heat_parts]
    return_signs = [h.signed_cascade(e.derivative(b), -1) for b in returns]
    leading = [Q(5, 96), Q(65, 576), Q(107, 432)]
    limits = [Q(-50593, 276480000), Q(-16312927, 26671680000),
              Q(-2287499437, 2133734400000)]
    for b, sign, value, limit in zip(returns, return_signs, leading, limits):
        h.require(sign['first_nonzero']['order'] == 5
                  and e.jet(b, 6)/factorial(6) == -value, 'Complete first-return order')
        h.require(b[(0, 0)] == limit, 'Exact all-time first-return limit')
    a, b = samples[1][8], samples[1][10]
    h.require(a[(0, 0)] == Q(757, 30720), 'Balanced complete heat stock')
    h.require(b[(0, 0)] == Q(-2655323383, 711244800000), 'Balanced complete saving')
    # Independent positive-viscosity time recurrence from joint_pressure_return.
    h.require(e.jet(a, 6)/factorial(6)/4 == Q(2057, 360)
              and e.jet(a, 8)/factorial(8)/16 == Q(30547, 6720)
              and e.jet(b, 8)/factorial(8)/4 == Q(-7402001, 1451520),
              'Lower-amplitude viscous terms match the independent nu=1/2 time jets')
    return dict(status='All exact whole-time family checks passed',
                heat_basis='(1+delta^8) A0 + delta^4 A1',
                return_basis='(1+delta^10) B0 + (delta^2+delta^8) B1 + (delta^4+delta^6) B2',
                heat=[dict(field=e.encode(a), sign=cert) for a, cert in zip(heat_parts, heat_signs)],
                first_return=[dict(field=e.encode(b), sign=cert, initial=str(v), limit=str(l))
                              for b, cert, v, l in zip(returns, return_signs, leading, limits)],
                uniform_saving_constant=str(Q(5, 96*3**18)),
                balanced={'heat_limit': str(a[(0, 0)]), 'return_limit': str(b[(0, 0)])},
                scope='Full first-return coefficient; actual small-amplitude payment requires the analytic remainder')


def mechanism_checks():
    source = coefficients(Q(1), source_gain=1, transport_gain=0)[10]
    transport = coefficients(Q(1), source_gain=0, transport_gain=1)[10]
    joint = coefficients(Q(1))[10]
    mixed = e.add(joint, e.scale(-1, source), e.scale(-1, transport))
    unused = coefficients(Q(1), source_gain=2, transport_gain=3)[10]
    h.require(unused == e.add(e.scale(4, source), e.scale(6, mixed), e.scale(9, transport)),
              'Unused operator tags check the degree-two decomposition')
    expected = [Q(-259, 432), Q(-35, 96), Q(5, 36)]
    result = {}
    for name, field, sign, value in zip(('source', 'transport', 'mixed'),
                                       (source, transport, mixed), (-1, -1, 1), expected):
        h.require(e.jet(field, 6)/factorial(6) == value, 'Complete tagged first-return order')
        result[name] = dict(initial=str(value), limit=str(field[(0, 0)]),
                           sign=h.signed_cascade(e.derivative(field), sign), field=e.encode(field))
    h.require(sum(expected) == Q(-713, 864), 'The adverse mixed work is retained in the full saving')
    return dict(parts=result,
                meaning='Full first-return coefficient at equal parents; tags split equations, not actual independent fluids')


def seam_check():
    from pressure_impulse_envelope import polynomial_interval
    forecast = coefficients(Q(1), degree=8)[8]
    lower, _ = polynomial_interval(forecast, Q(3))
    h.require(4**4*lower > 6, 'At nu=1/4, time12, the actual forecast exceeds six')
    ratio, order = Q(1, 2), 12
    log_upper = sum((ratio**j/j for j in range(1, order+1)), Q(0)) \
        +ratio**(order+1)/((order+1)*(1-ratio))
    h.require(log_upper/4-Q(1, 8) < Q(1, 20), 'Wiener-small future impulse costs less than .05')
    h.require(2 < Q(6, 5)**4 and (Q(6, 5)+Q(1, 20))**4 < 6,
              'Inherited and future fourth-root costs fit the future heat forecast')
    return dict(viscosity='1/4', time=12,
                sufficient_actual_seam={'velocity_wiener_upper':'1/8', 'phi_upper':'2'},
                future_forecast_lower='6', completed_upper='625/256',
                scope='Conditional physical tail; the actual seam and preceding comparison are not certified here')


def numerical_prefix(n, nu, delta, dt, final):
    import time
    import numpy as np
    import mpmath as mp
    from pressure_prefix_control import VelocityFlow
    from cellular_parent_history import PAIRS

    h.require(n >= 12 and n % 2 == 0 and nu > 0 and dt > 0 and final > 0,
              'Positive physical parameters and even retained grid')
    steps = round(final/dt)
    h.require(abs(steps*dt-final) < 1e-10, 'Integral number of time steps')
    mp.mp.dps = 60
    field = coefficients(Q(str(delta)), degree=8)[8]
    def forecast(t):
        v, tau = mp.mpf(str(nu)), mp.mpf(str(nu))*mp.mpf(str(t))
        return float(v**-4*mp.fsum(mp.mpf(c.numerator)/c.denominator*tau**j*mp.exp(-r*tau)
                                  for (r, j), c in field.items()))

    class JointFlow(VelocityFlow):
        def __init__(self):
            super().__init__(n, nu)
            self.initial = np.zeros((n, n, n, 16), complex)
            for j, component in enumerate(seed(Q(str(delta)))):
                for k, value in component.items():
                    self.initial[tuple(q % n for q in k)+(j,)] = complex(float(value.x), float(value.y))*n**3
            self.high = self.mask & np.any(abs(self.K) > .8*n/3, axis=-1)
            self.energy0 = np.sum(abs(self.initial[..., :3])**2)/n**6/2

        def rhs(self, state):
            values, gradient = self.ifft(state), self.grad_hat(state)
            adv = sum(values[..., j, None]*gradient[j] for j in range(3))
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
            result[..., 15] = 0
            result[0, 0, 0, 15] = 4*np.mean(np.sum(g*values[..., 12:15], axis=-1))*n**3
            loss = nu*np.mean(sum(np.sum(q[..., :3]**2, axis=-1) for q in gradient))
            return result, np.array([loss])

        def report(self, t, state, spent):
            values = self.ifft(state)
            phi = float(state[0, 0, 0, 15].real/n**3)
            bound = forecast(t)
            vu = self.k2*np.sum(abs(state[..., :3])**2, axis=-1)
            vm = np.sum(abs(state[..., 3:15])**2, axis=-1)
            second = np.zeros(values.shape[:-1]+(3, 3))
            for j, (a, b) in enumerate(PAIRS):
                second[..., a, b] = second[..., b, a] = values[..., 6+j]
            first = values[..., 3:6]
            energy = np.mean(np.sum(values[..., :3]**2, axis=-1))/2
            return dict(time=t, phi=phi, forecast=bound, ratio=phi/bound if bound else 0.,
                        energy_balance=float(energy+spent-self.energy0),
                        velocity_wiener=float(np.sum(np.sqrt(np.sum(abs(state[..., :3])**2, axis=-1)))/n**3),
                        high_velocity_fraction=float(vu[self.high].sum()/max(vu.sum(), 1e-300)),
                        high_moment_fraction=float(vm[self.high].sum()/max(vm.sum(), 1e-300)),
                        minimum_covariance=float(np.linalg.eigvalsh(second-first[..., None]*first[..., None, :]).min()),
                        fourth_second_jensen_gap=float(phi-np.mean(np.trace(second, axis1=-2, axis2=-1)**2)))

    flow = JointFlow()
    state, spent, start = flow.initial.copy(), 0., time.time()
    yield dict(n=n, nu=nu, delta=delta, dt=dt, final=final,
               scope='Dealiased numerical discovery; no continuum error enclosure')
    for step in range(1, steps+1):
        state, cost = flow.step(state, dt)
        spent += cost[0]
        if step % max(1, round(.25/dt)) == 0 or step == steps:
            yield flow.report(step*dt, state, spent)
    yield dict(elapsed=time.time()-start)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prefix', action='store_true')
    parser.add_argument('--n', type=int, default=24)
    parser.add_argument('--nu', type=float, default=.25)
    parser.add_argument('--delta', type=float, default=1.)
    parser.add_argument('--dt', type=float, default=.01)
    parser.add_argument('--final', type=float, default=12.)
    args = parser.parse_args()
    if args.prefix:
        for row in numerical_prefix(args.n, args.nu, args.delta, args.dt, args.final):
            print(json.dumps(row), flush=True)
    else:
        print(json.dumps(dict(family=family_checks(), mechanism=mechanism_checks(), tail=seam_check()), indent=2))
