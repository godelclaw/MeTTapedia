#!/usr/bin/env python3
"""Velocity and complete pressure-cost enclosures for one original history.

Reuse the arithmetic model of pressure_prefix_certificate. The exact target
is one reconstructed Bernstein curve, not its rounded midpoint. The physical
comparison and tail are analytic; these calculations are not Lean proofs.
"""

import argparse
from fractions import Fraction as Q
import hashlib
import json
import time

import numpy as np

from pressure_gradient_amplitude import ALPHA, GradientFlow
from pressure_history_control import jets
from pressure_operator_enclosure import Ball, OperatorEnclosure, linear, product, resize
from pressure_polynomial_enclosure import (centered_weights, norm_polynomial,
    rational_upper, signed_inner, sqrt_upper)
from pressure_prefix_certificate import (U, EnclosedFFT, add, arithmetic_check,
    bernstein, combine, down, frequency_grid, grid_eigenvalue_upper, mul, norm,
    reconstruct, require, sum_upper)
from pressure_vorticity_control import enstrophy_source, velocity_step


def lower(value):
    return -rational_upper(-value)


def root_lower(value):
    require(value >= 0, 'Nonnegative root argument')
    result = sqrt_upper(value)
    while Q(result)**2 > value:
        result = float(down(result))
    return result


def root(value):
    return Q(sqrt_upper(value))


def shared_velocity(raw):
    """Exact PH reconstruction of shared, normalized dyadic control points."""
    require(len(raw) == 6, 'Six shared Bernstein control points')
    n = raw[0].shape[0]
    K = frequency_grid(n)
    outside = np.any(3*abs(K) >= n, axis=-1)
    require(n % 2 == 0 and all(a.shape == (n, n, n, 3)
            and a.dtype == np.dtype('complex128') and np.isfinite(a).all()
            and np.all(a[outside] == 0) for a in raw), 'Finite alias-free velocity reference')
    pairs = [reconstruct(a, K, np.sum(K*K, axis=-1)) for a in raw]
    values, radii = zip(*pairs)
    centered = [Ball(*combine(values, radii, weights)) for weights in centered_weights()]
    return centered, (Ball(*pairs[0]), Ball(*pairs[-1]))


def integrated_square(coefficients, h):
    """Enclose the entire norm-square integral, with signed mixed pairings."""
    require(h > 0, 'Positive physical interval')
    lo, hi = Q(0), Q(0)
    for i, a in enumerate(coefficients):
        for j in range(i, len(coefficients)):
            if (i+j) % 2:
                continue
            left, right = signed_inner(a.center, coefficients[j].center)
            factor = Q(h)*(1 if i == j else 2)/Q(i+j+1)
            lo += factor*left
            hi += factor*right
    require(hi >= 0, 'The computed squared polynomial has a nonnegative integral')
    error = root(Q(h))*sum((Q(a.radius) for a in coefficients), Q(0))
    return dict(lower=lower(max(Q(0), Q(root_lower(max(Q(0), lo)))-error)**2),
                upper=rational_upper((root(hi)+error)**2),
                arithmetic_L2_time_radius=rational_upper(error))


class GradientEnclosure(OperatorEnclosure):
    """Only quadratic NS outputs; no cubic moment fields are constructed."""

    def __init__(self, n):
        require(n >= 12 and n % 2 == 0, 'Even velocity grid')
        self.n, self.band = n, (n-1)//3
        self.m = 2*(2*self.band+1)
        self.fft = EnclosedFFT(1 << (4*self.band).bit_length())
        self.K, self.Kout = frequency_grid(n), frequency_grid(self.m)
        self.k2, self.k2out = np.sum(self.K*self.K, axis=-1), np.sum(self.Kout*self.Kout, axis=-1)
        self.outside_quadratic = np.any(abs(self.Kout) > 2*self.band, axis=-1)
        require(4*self.band < self.fft.n, 'All quadratic outputs lie strictly below FFT Nyquist')

    def majorants(self, velocity, gradient0, endpoints):
        v = [self.sizes(a, self.band) for a in velocity]
        V = [sum_upper([a['W'+str(j)] for a in v]) for j in range(3)]
        matrix = np.stack([a.center for a in gradient0], axis=-1)
        strain = (matrix+matrix.swapaxes(-1, -2))/2
        error = add(mul(self.fft.sqrt_volume, sum_upper([a.radius for a in gradient0])),
                    add(mul(8*U, norm(matrix)), 1.e-290))
        margin = rational_upper(Q(11)*Q(v[0]['W2'])/(4*self.fft.n)
                                +sum(Q(a['W1']) for a in v[1:])/2)
        common, simple = add(error, margin), rational_upper(Q(V[1])/2)
        Sm = max(0., min(simple, add(grid_eigenvalue_upper(-strain), common)))
        Sp = max(0., min(simple, add(grid_eigenvalue_upper(strain), common)))
        final = self.sizes(endpoints[-1], self.band)
        return dict(S=Sm, Splus=Sp, V0=V[0], V1=V[1], V2=V[2], D=V[2],
                    reference_H1=sum_upper([a['H1'] for a in v]), final_H1=final['H1'])

    def slab(self, raw, h, nu, return_coefficients=False):
        require(h > 0 and nu > 0 and np.isfinite(h+nu), 'Positive interval and viscosity')
        velocity, endpoints = shared_velocity(raw)
        physical = [self.physical(a) for a in velocity]
        gradients = [[self.physical(self.derivative(a, d)) for d in range(3)] for a in velocity]
        row = self.majorants(velocity, gradients[0], endpoints)
        adv, pressure, residual = [], [], []
        for k in range(11):
            terms = []
            for i in range(6):
                j = k-i
                if not 0 <= j < 6:
                    continue
                for d in range(3):
                    parent = Ball(physical[i].center[..., d:d+1], physical[i].radius, True)
                    terms.append(product(parent, gradients[j][d], 'transport'))
            adv.append(self.spectral(linear(terms, [Q(1)]*len(terms)), quadratic=True))
            pressure.append(self.pressure(adv[-1]))
            terms, weights = [adv[-1], pressure[-1]], [Q(1), Q(1)]
            if k < 5:
                a = velocity[k+1]
                terms.append(Ball(resize(a.center, self.m), a.radius))
                weights.append(Q(2*(k+1))/Q(h))
            if k < 6:
                terms.append(self.heat(velocity[k], nu)); weights.append(Q(1))
            residual.append(linear(terms, weights))
        del gradients, physical
        centers = [a.center for a in residual]
        radii = [a.radius for a in residual]
        h1_radii = [mul(sqrt_upper(Q(12*self.band**2)), r) for r in radii]
        eps0 = norm_polynomial(centers, radii=radii)
        eps1 = norm_polynomial(centers, self.k2out[..., None], radii=h1_radii)
        row.update(epsilon0=eps0['bound'], epsilon1=eps1['bound'])
        cost = integrated_square(pressure, h)
        result = dict(row=row, reference_cost=cost,
                      residual_details=dict(epsilon0=eps0, epsilon1=eps1),
                      grids=dict(fft=self.fft.n, output=self.m, velocity_band=self.band))
        if return_coefficients:
            result.update(residual_coefficients=residual, pressure_coefficients=pressure)
        return result


def advance(old, row, reference_cost, h, nu):
    """GA3--GA4 with inherited errors and outward rational scalar arithmetic."""
    require(all(np.isfinite(x) and x >= 0 for x in old.values())
            and all(np.isfinite(x) and x >= 0 for x in row.values()), 'Nonnegative finite input bounds')
    require(0 <= reference_cost['lower'] <= reference_cost['upper'], 'Ordered reference-cost bounds')
    vel = velocity_step(old['X'], old['Y'], row, h, nu)
    x, y, t, v = Q(vel['Xmax']), Q(vel['Ymax']), Q(h), Q(nu)
    r = {k: Q(a) for k, a in row.items()}
    kappa = 27*(26*Q(22, 7))**2/(32*v**3)
    source = enstrophy_source(x, y, r, kappa)
    dissipation = (Q(old['Y'])**2+2*t*source)/v
    # The Lie bracket of two solenoidal fields is solenoidal. Thus the
    # two mixed advections have the same gradient projection, giving the
    # sharper alternative 2*V1*X without a derivative of the error.
    linear_cost = min(r['V0']*y+r['V1']*x, 2*r['V1']*x)
    R = root(t)*linear_cost+13*root(y**3)*root(root(t*dissipation))
    interval_upper = (root(Q(reference_cost['upper']))+R)**2
    interval_lower = max(Q(0), Q(root_lower(Q(reference_cost['lower'])))-R)**2
    result = dict(X=vel['X'], Y=vel['Y'], Xmax=vel['Xmax'], Ymax=vel['Ymax'],
                  cost_upper=rational_upper(Q(old['cost_upper'])+interval_upper),
                  cost_lower=lower(Q(old['cost_lower'])+interval_lower),
                  interval_cost_upper=rational_upper(interval_upper),
                  interval_cost_lower=lower(interval_lower),
                  pressure_error_radius=rational_upper(R),
                  error_dissipation_upper=rational_upper(dissipation))
    return result


def identity(raw, amplitude):
    from pressure_gradient_stock import weighted_datum
    n = raw.shape[0]
    expected = np.zeros_like(raw)
    original = weighted_datum(4, (Q(amplitude)/4, Q(amplitude), Q(amplitude)))
    for j, component in enumerate(original):
        for k, z in component.items():
            value = complex(float(z.x), float(z.y))
            require(Q(value.real) == Q(str(z.x)) and Q(value.imag) == Q(str(z.y)),
                    'The prescribed original coefficients are exactly represented')
            expected[tuple(q % n for q in k)+(j,)] = value
    require(np.array_equal(raw, expected), 'Exact original three-parent datum, no preloaded history')


def scalar_checks():
    from decimal import Decimal as D, localcontext
    row = dict(S=1.25, Splus=.75, V0=3., V1=4., V2=5., D=5.,
               epsilon0=2.**-40, epsilon1=2.**-36)
    old = dict(X=2.**-30, Y=2.**-25, cost_lower=.125, cost_upper=.25)
    ref = dict(lower=.0625, upper=.125)
    h, nu = 1/32, 1.
    observed = advance(old, row, ref, h, nu)
    with localcontext() as context:
        context.prec = 90
        x, y, t, v = D(observed['Xmax']), D(observed['Ymax']), D(h), D(nu)
        kappa = 27*(26*D(22)/7)**2/(32*v**3)
        source = min(2*D(row['S'])*y*y+D(row['D'])*x*y,
                     D(row['Splus'])*y*y+D('1.5')*D(row['V2'])*x*y)
        source += kappa*y**6+D(row['epsilon1'])*y
        dissip = (D(old['Y'])**2+2*t*source)/v
        linear_cost = min(D(row['V0'])*y+D(row['V1'])*x, 2*D(row['V1'])*x)
        radius = t.sqrt()*linear_cost+13*(y**3).sqrt()*(t*dissip).sqrt().sqrt()
        exact_lo = D(old['cost_lower'])+max(D(0), D(ref['lower']).sqrt()-radius)**2
        exact_hi = D(old['cost_upper'])+(D(ref['upper']).sqrt()+radius)**2
        require(D(observed['cost_lower']) <= exact_lo and D(observed['cost_upper']) >= exact_hi,
                'Independent high-precision GA3--GA4 comparison includes all inherited costs')
        require(D(observed['error_dissipation_upper']) >= dissip
                and D(observed['pressure_error_radius']) >= radius,
                'Dissipation and mixed fractional powers round outward')
    return dict(status='Independent scalar cost comparison passed', control=observed)


def checks():
    import pressure_history_source as f
    from cyclic_pressure_history import velocity_time_jets
    from pressure_gradient_stock import weighted_datum
    arithmetic_check()
    n, h, nu = 24, Q(1, 16), Q(1, 4)
    flow = GradientFlow(n, float(nu), 2.)
    initial = weighted_datum(4, (Q(1, 2), Q(2), Q(2)))
    velocity, _ = velocity_time_jets(initial, nu, 1)
    # Exact dyadics give v(s)=v0+(5/32)s*u1, s in [-1,1].
    raw = [flow.encode([f.add(a, f.scale(Q(2*i-5, 32), b))
                        for a, b in zip(initial, velocity[1])])/n**3 for i in range(6)]
    enclosure = GradientEnclosure(n)
    result = enclosure.slab(raw, float(h), float(nu), True)
    w = [f.scale(Q(5, 32), a) for a in velocity[1]]
    mixed_left = [f.adv(initial, a) for a in w]
    mixed_right = [f.adv(w, a) for a in initial]
    bracket = [f.add(a, f.scale(-1, b)) for a, b in zip(mixed_left, mixed_right)]
    f.equal(f.trace(f.jac(bracket)), {}, 'The actual mixed transport bracket is solenoidal')
    require(any(bracket), 'The pressure-invisible mixed bracket is not a zero fixture')
    for a, b in zip(f.grad(f.green(f.trace(f.jac(mixed_left)))),
                    f.grad(f.green(f.trace(f.jac(mixed_right))))):
        f.equal(a, b, 'The two mixed advections have identical canonical gradient projections')
    canonical = lambda z: f.green(f.trace(f.matmul(f.jac(z), f.jac(z))))
    p0, p2 = canonical(initial), canonical(w)
    p1 = f.add(canonical([f.add(a, b) for a, b in zip(initial, w)]), f.scale(-1, p0), f.scale(-1, p2))
    exact_pressure = list(map(f.grad, (p0, p1, p2)))
    mean = lambda z: Q(str(z.get(f.ORIGIN, f.ZERO).x))
    exact_cost = h*sum((mean(f.dot(a, b))/Q(i+j+1)
                       for i, a in enumerate(exact_pressure) for j, b in enumerate(exact_pressure)
                       if (i+j) % 2 == 0), Q(0))
    bounds = result['reference_cost']
    require(0 < exact_cost and Q(bounds['lower']) <= exact_cost <= Q(bounds['upper']),
            'Independent full canonical-pressure polynomial integral is enclosed')
    # Compare every residual coefficient with the literal untruncated PDE.
    residual_exact = []
    for k in range(3):
        terms = []
        for j in range(3):
            advection = f.add(*(f.adv(a, b[j]) for i, a in enumerate((initial, w))
                                 for ell, b in enumerate((initial, w)) if i+ell == k))
            value = f.add(advection, exact_pressure[k][j])
            if k < 2:
                value = f.add(value, f.scale(-nu, f.lap((initial, w)[k][j])))
            if k == 0:
                value = f.add(value, f.scale(2/h, w[j]))
            terms.append(value)
        residual_exact.append(terms)
    for kind, exact in [('residual', residual_exact), ('pressure', exact_pressure)]:
        for k, a in enumerate(result[kind+'_coefficients']):
            target = np.zeros_like(a.center)
            conversion_squared = Q(0)
            if k < len(exact):
                for j, field in enumerate(exact[k]):
                    for mode, z in field.items():
                        value = complex(float(z.x), float(z.y))
                        target[tuple(q % enclosure.m for q in mode)+(j,)] = value
                        conversion_squared += (Q(value.real)-Q(str(z.x)))**2+(Q(value.imag)-Q(str(z.y)))**2
            # The exact Fourier fixture is rational; explicitly enclose
            # conversion of its coefficients as well as the comparison.
            difference = linear([Ball(target, sqrt_upper(conversion_squared)),
                                 Ball(a.center, 0.)], [Q(1), Q(-1)])
            require(add(difference.size, difference.radius) <= a.radius,
                    'Complete exact pressure/residual coefficients fit their arithmetic balls')
    return dict(status='Exact reconstructed-reference pressure and residual checks passed',
                exact_reference_cost=str(exact_cost), reference_cost_enclosure=bounds,
                residual_details=result['residual_details'], grids=result['grids'],
                scalar=scalar_checks(),
                scope='Stated binary64 arithmetic model and analytic comparison; not Lean-certified')


def run(n, amplitude, dt, h, final):
    arithmetic_check()
    require(min(amplitude, dt, h, final) > 0 and all(np.isfinite(x) for x in (amplitude, dt, h, final)),
            'Positive finite original amplitude and times')
    steps, slabs = round(h/dt), round(final/h)
    require(steps >= 1 and slabs >= 1 and steps*Q(dt) == Q(h) and slabs*Q(h) == Q(final),
            'Exact integer step and interval counts')
    flow, enclosure = GradientFlow(n, 1., amplitude), GradientEnclosure(n)
    state = flow.initial.copy()
    first, second = jets(flow, state)
    control = dict(X=0., Y=0., cost_lower=0., cost_upper=0.)
    previous, start = None, time.monotonic()
    stock = Q(amplitude)**6*ALPHA/16
    yield dict(n=n, amplitude=amplitude, nu=1., dt=dt, h=h, final=final, original_stock=str(stock),
               scope='Complete interval enclosures under the stated arithmetic model; analytic PDE transfer')
    for slab in range(slabs):
        initial, f0, j0 = state.copy(), first, second
        for _ in range(steps):
            state, _ = flow.step(state, dt)
        first, second = jets(flow, state)
        raw = [a/n**3 for a in bernstein(initial, state, f0, first, j0, second, h)]
        if previous is None:
            identity(raw[0], amplitude)
        else:
            require(np.array_equal(raw[0], previous), 'One exact reconstructed reference across the seam')
        previous = raw[-1].copy()
        data = enclosure.slab(raw, h, 1.)
        try:
            control = advance(control, data['row'], data['reference_cost'], h, 1.)
        except (ArithmeticError, OverflowError) as ex:
            yield dict(time=(slab+1)*h, status='comparison failed', reason=str(ex),
                       previous_control=control, **data, elapsed=time.monotonic()-start)
            return
        gradient = Q(data['row']['final_H1'])+Q(control['Y'])
        total = Q(control['cost_upper'])+169*gradient**4
        record = dict(time=(slab+1)*h, status='interval accepted', **data, control=control,
                      actual_H1_upper=rational_upper(gradient),
                      actual_cost_upper_over_stock=rational_upper(Q(control['cost_upper'])/stock),
                      cost_plus_tail_upper_over_stock=rational_upper(total/stock),
                      initial_endpoint_sha256=hashlib.sha256(raw[0].tobytes()).hexdigest(),
                      final_endpoint_sha256=hashlib.sha256(raw[-1].tobytes()).hexdigest(),
                      elapsed=time.monotonic()-start)
        if gradient <= Q(1, 26) and total <= stock:
            record['tail'] = 'PG8 pays every remaining time from the same original stock'
            yield record
            yield dict(status='original stock paid for all time under the stated arithmetic model')
            return
        yield record
    yield dict(status='finite prefix enclosed; tail payment pending', elapsed=time.monotonic()-start)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prefix', action='store_true')
    parser.add_argument('--n', type=int, default=32)
    parser.add_argument('--amplitude', type=float, default=2.)
    parser.add_argument('--dt', type=float, default=1/1024)
    parser.add_argument('--h', type=float, default=1/64)
    parser.add_argument('--final', type=float, default=1/64)
    args = parser.parse_args()
    if args.prefix:
        for row in run(args.n, args.amplitude, args.dt, args.h, args.final):
            print(json.dumps(row), flush=True)
    else:
        print(json.dumps(checks(), indent=2))
