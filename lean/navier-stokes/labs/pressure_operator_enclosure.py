#!/usr/bin/env python3
"""Full NS and joint-pressure-history residual coefficient enclosures.

The exact target is one shared reconstructed Bernstein reference. Explicit
radix-two Fourier transforms retain every quadratic and cubic output.
This supplies physical residual balls, not yet the other majorants and
scalar propagation required to certify a complete pressure-history prefix.
Arithmetic assumptions are those of pressure_prefix_certificate.
"""

import argparse
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import cached_property
import json
import time

import numpy as np
from cellular_parent_history import PAIRS
from pressure_polynomial_enclosure import (centered_weights, rational_upper, residual_bounds,
    shared_reference, signed_inner, sqrt_upper)
from pressure_prefix_certificate import (EnclosedFFT, U, add, arithmetic_check,
    bernstein, combine, down, frequency_grid, mul, norm, require, sum_upper,
    up, vector_sizes)

BLOCKS = {'u': slice(0, 3), 'I': slice(3, 6), 'Q': slice(6, 12), 'T': slice(12, 15)}


def resize(a, m):
    """Permute and pad/crop normalized Fourier coefficients, with no scaling."""
    n = a.shape[0]
    require(n % 2 == 0 and m % 2 == 0, 'Even spectral storage grids')
    if n == m:
        return a.copy()
    value = np.fft.fftshift(a, axes=(0, 1, 2))
    p = abs(m-n)//2
    if m > n:
        value = np.pad(value, ((p, p), (p, p), (p, p), (0, 0)))
    else:
        value = value[p:p+m, p:p+m, p:p+m]
    return np.fft.ifftshift(value, axes=(0, 1, 2)).copy()


@dataclass
class Ball:
    center: np.ndarray
    radius: float
    physical: bool = False

    def __post_init__(self):
        require(np.isfinite(self.radius) and self.radius >= 0,
                'A finite nonnegative field error radius')
        require(self.center.dtype in (np.dtype('float64'), np.dtype('complex128')),
                'Binary64 field arithmetic')

    @cached_property
    def size(self):
        value = norm(self.center)
        if self.physical:
            value = float(up(value/down(np.sqrt(self.center.shape[0]**3))))
        return value

    @cached_property
    def maximum(self):
        require(self.physical, 'A grid maximum is used only for grid products')
        return float(vector_sizes(self.center).max())


def linear(balls, weights):
    require(balls and len(balls) == len(weights)
            and all(b.physical == balls[0].physical for b in balls), 'Compatible ball sum')
    physical = balls[0].physical
    scale = float(up(np.sqrt(balls[0].center.shape[0]**3))) if physical else 1.
    radii = [mul(scale, b.radius) for b in balls]
    center, radius = combine([b.center for b in balls], radii, weights)
    if physical:
        radius = float(up(radius/down(np.sqrt(center.shape[0]**3))))
    return Ball(center, radius, physical)


def product(a, b, kind):
    """Grid bilinear errors in normalized L2, including fixed tensor maps."""
    require(a.physical and b.physical and a.center.shape[:3] == b.center.shape[:3],
            'Products use a common complete physical grid')
    x, y = a.center, b.center
    if kind == 'transport':
        value, constant = x*y, 1
    elif kind == 'second':
        value = np.stack([x[..., i]*y[..., j]+x[..., j]*y[..., i] for i, j in PAIRS], axis=-1)
        constant = 2
    elif kind == 'third':
        value = np.zeros(y.shape)
        for index, (i, j) in enumerate(PAIRS):
            value[..., i] += 2*x[..., index]*y[..., j]
            if i != j:
                value[..., j] += 2*x[..., index]*y[..., i]
            else:
                value += x[..., index, None]*y
        constant = 5  # 2 sqrt(2)+sqrt(3)<5 for the six stored Q components.
    elif kind == 'fourth':
        value, constant = 4*np.sum(x*y, axis=-1)[..., None], 4
    else:
        raise ArithmeticError('Unknown physical bilinear source')
    root_volume = float(up(np.sqrt(x.shape[0]**3)))
    error = sum_upper([mul(a.maximum, b.radius), mul(b.maximum, a.radius),
                       mul(root_volume, mul(a.radius, b.radius))])
    # Each fixed output component has fewer than 16 arithmetic operations.
    # The absolute tensor map is bounded by the same displayed constant.
    rounding = mul(64*U, mul(a.maximum, b.size))
    error = add(mul(constant, add(error, rounding)), 1.e-290)
    require(np.isfinite(value).all(), 'No physical product overflow')
    return Ball(value, error, True)


class OperatorEnclosure:
    def __init__(self, n):
        require(n >= 4 and n % 2 == 0, 'Even retained input grid')
        self.n, self.band = n, (n-1)//3
        self.m = 2*(3*self.band+1)
        fft_size = 1 << (6*self.band).bit_length()
        self.fft = EnclosedFFT(fft_size)
        self.K, self.Kout = frequency_grid(n), frequency_grid(self.m)
        self.k2 = np.sum(self.K*self.K, axis=-1)
        self.k2out = np.sum(self.Kout*self.Kout, axis=-1)
        self.outside_quadratic = np.any(abs(self.Kout) > 2*self.band, axis=-1)
        require(6*self.band < self.fft.n, 'Every cubic output fits strictly below Nyquist')

    def physical(self, a):
        center, radius = self.fft.physical(resize(a.center, self.fft.n), a.radius)
        return Ball(center, radius, True)

    def spectral(self, a, quadratic=False):
        center, radius = self.fft.fourier(a.center, a.radius)
        center = resize(center, self.m)
        if quadratic:
            center[self.outside_quadratic] = 0
        # The exact product has the proved support. This projection is a
        # contraction on its error; no actual generated output is removed.
        return Ball(center, radius)

    def derivative(self, a, axis):
        center = 1j*self.K[..., axis, None]*a.center
        radius = add(mul(self.band, a.radius), mul(8*U*self.band, a.size))
        return Ball(center, add(radius, 1.e-290))

    def heat(self, a, nu):
        center = nu*self.k2[..., None]*a.center
        factor = float(up(nu*(3*self.band**2)))
        radius = add(mul(factor, a.radius), mul(8*U, mul(factor, a.size)))
        return Ball(resize(center, self.m), add(radius, 1.e-290))

    def pressure(self, advection):
        inv = np.divide(1., self.k2out, out=np.zeros_like(self.k2out, dtype=float),
                        where=self.k2out != 0)
        center = -self.Kout*inv[..., None]*np.sum(self.Kout*advection.center, axis=-1)[..., None]
        radius = add(advection.radius, add(mul(64*U, advection.size), 1.e-290))
        return Ball(center, radius)

    def mean(self, a):
        lo, hi = signed_inner(a.center, np.ones_like(a.center))
        lo, hi = lo/self.fft.volume, hi/self.fft.volume
        center = float((lo+hi)/2)
        radius = rational_upper(max(Q(center)-lo, hi-Q(center))+Q(a.radius))
        return center, radius

    def residual(self, raw, h, nu):
        require(h > 0 and nu > 0 and np.isfinite(h+nu), 'Positive finite physical parameters')
        c, radii, endpoints = shared_reference(raw)
        fields = {key: [Ball(a[..., block], r) for a, r in zip(c, radii[key])]
                  for key, block in BLOCKS.items()}
        phi = [Ball(a[..., 15:16], r) for a, r in zip(c, radii['Phi'])]
        physical = {key: [self.physical(a) for a in values] for key, values in fields.items()}
        gradients = {key: [[self.physical(self.derivative(a, d)) for d in range(3)]
                           for a in values] for key, values in fields.items()}
        advection = {key: [] for key in BLOCKS}
        pressure = []
        for k in range(11):
            for key in BLOCKS:
                terms = []
                for i in range(6):
                    j = k-i
                    if not 0 <= j < 6:
                        continue
                    parent = physical['u'][i]
                    for d in range(3):
                        component = Ball(parent.center[..., d:d+1], parent.radius, True)
                        terms.append(product(component, gradients[key][j][d], 'transport'))
                value = linear(terms, [Q(1)]*len(terms))
                advection[key].append(self.spectral(value, quadratic=True))
            pressure.append(self.pressure(advection['u'][-1]))
        del gradients
        gp = [self.physical(a) for a in pressure]
        output, errors = [], {key: [] for key in ('epsilon0', 'epsilon1', 'rI', 'rQ', 'rT', 'rPhi')}
        norm_key = {'u': 'epsilon0', 'I': 'rI', 'Q': 'rQ', 'T': 'rT'}
        for k in range(16):
            row = np.zeros((self.m, self.m, self.m, 16), complex)
            sources = {key: [] for key in ('Q', 'T', 'Phi')}
            for i in range(6):
                j = k-i
                if 0 <= j < 11:
                    sources['Q'].append(product(physical['I'][i], gp[j], 'second'))
                    sources['T'].append(product(physical['Q'][i], gp[j], 'third'))
                    sources['Phi'].append(product(physical['T'][i], gp[j], 'fourth'))
            for key, block in BLOCKS.items():
                terms, weights = [], []
                if k < 5:
                    a = fields[key][k+1]
                    terms.append(Ball(resize(a.center, self.m), a.radius))
                    weights.append(Q(2*(k+1))/Q(h))
                if k < 6:
                    terms.append(self.heat(fields[key][k], nu)); weights.append(Q(1))
                if k < 11:
                    terms.append(advection[key][k]); weights.append(Q(1))
                    if key in ('u', 'I'):
                        terms.append(pressure[k]); weights.append(Q(1 if key == 'u' else -1))
                if key in ('Q', 'T'):
                    source = linear(sources[key], [Q(1)]*len(sources[key]))
                    terms.append(self.spectral(source)); weights.append(Q(-1))
                if terms:
                    value = linear(terms, weights)
                else:
                    value = Ball(np.zeros(row[..., block].shape, complex), 0.)
                row[..., block] = value.center
                radius = value.radius
                if key == 'u':
                    errors['epsilon1'].append(mul(sqrt_upper(Q(12*self.band**2)), radius))
                if key == 'Q':
                    radius = mul(sqrt_upper(Q(2)), radius)
                errors[norm_key[key]].append(radius)
            source = linear(sources['Phi'], [Q(1)]*len(sources['Phi']))
            mean, radius = self.mean(source)
            terms = [Ball(np.array([[[[-mean]]]], complex), radius)]
            weights = [Q(1)]
            if k < 5:
                a = phi[k+1]
                terms.append(Ball(a.center[0:1, 0:1, 0:1].copy(), a.radius))
                weights.append(Q(2*(k+1))/Q(h))
            scalar = linear(terms, weights)
            row[0, 0, 0, 15] = scalar.center[0, 0, 0, 0]
            errors['rPhi'].append(scalar.radius)
            output.append(row)
        return output, errors, dict(fft_grid=self.fft.n, output_grid=self.m,
                                   input_band=self.band), endpoints


def probe(n, h, dt, nu):
    from pressure_history_control import jets
    from reciprocal_pressure_payment import make_flow
    start = time.time()
    flow = make_flow(n, nu, 1.)
    initial, state = flow.initial.copy(), flow.initial.copy()
    require(h > 0 and dt > 0 and round(h/dt)*Q(dt) == Q(h), 'Exact integral time steps')
    f0, j0 = jets(flow, state)
    for _ in range(round(h/dt)):
        state, _ = flow.step(state, dt)
    f1, j1 = jets(flow, state)
    raw = [a/n**3 for a in bernstein(initial, state, f0, f1, j0, j1, h)]
    residual, radii, grids, _ = OperatorEnclosure(n).residual(raw, h, nu)
    bounds = residual_bounds(residual, radii, normalized=True)
    ratios = {key: value['bound']/value['stored_center_bound'] for key, value in bounds.items()}
    return dict(n=n, h=h, dt=dt, nu=nu, **grids, bounds=bounds,
                coefficient_radii=radii, arithmetic_ratios=ratios,
                within_factor_two=all(r <= 2 for r in ratios.values()),
                elapsed=time.time()-start,
                scope='Full residual of one exact shared reference; complete pressure-prefix controls still open')


def exact_checks():
    """Independent rational convolution on the exact reconstructed reference.

    This deliberately nonphysical moment fixture tests the complete
    operator, including every tensor slot; it is not an NS solution.
    """
    import pressure_history_source as f
    n, h, nu = 4, Q(1, 2), Q(1, 4)
    base = np.zeros((n, n, n, 16), complex)
    modes = [((1, 0, 1), (1, 2, -1), (1+2j)/16),
             ((0, 1, 1), (2, 1, -1), (-2+1j)/16),
             ((1, 1, 0), (1, -1, 2), (1-1j)/16),
             ((1, -1, 1), (1, 1, -1), (2+3j)/32)]
    for k, v, a in modes:
        entry = np.zeros(16, complex)
        entry[:3] = a*np.array(v)
        entry[3:6], entry[12:15] = entry[:3]/4, entry[:3]/16
        for j, (p, q) in enumerate(PAIRS):
            entry[6+j] = entry[(p+q) % 3]/8
        base[tuple(x % n for x in k)] = entry
        base[tuple(-x % n for x in k)] = entry.conjugate()
    for j, (p, q) in enumerate(PAIRS):
        if p == q:
            base[0, 0, 0, 6+j] = 3
    k = (0, -1, 1)
    extra_third = (1+1j)/16*np.array([1, -2, 3])
    base[tuple(x % n for x in k)+(slice(12, 15),)] = extra_third
    base[tuple(-x % n for x in k)+(slice(12, 15),)] = extra_third.conjugate()
    base[0, 0, 0, 15] = 7
    roots = np.array([1., 1j, -1., -1j])
    K = frequency_grid(n)
    raw = [(8+i)/16*base*roots[(i*K[..., 0]) % 4][..., None] for i in range(6)]
    for i, a in enumerate(raw):
        a[..., 12:15] *= roots[(i*K[..., 1]) % 4][..., None]
    residual, radii, grids, _ = OperatorEnclosure(n).residual(raw, float(h), float(nu))
    controls = []
    for a in raw:
        rows = [{} for _ in range(16)]
        for index in np.argwhere(np.any(a != 0, axis=-1)):
            k = tuple(int(x) for x in K[tuple(index)])
            positive, negative = a[tuple(index)], a[tuple(-x % n for x in k)]
            values = [f.QQ_I((Q(x.real)+Q(y.real))/2, (Q(x.imag)-Q(y.imag))/2)
                      for x, y in zip(positive, negative)]
            square = sum(x*x for x in k)
            dot = sum(k[j]*values[j] for j in range(3))
            values[:3] = [values[j]-f.QQ_I(k[j])*dot/square if square else f.ZERO for j in range(3)]
            for j, value in enumerate(values):
                if value:
                    rows[j][k] = value
        controls.append(rows)
    groups = {'epsilon0': range(3), 'epsilon1': range(3), 'rI': range(3, 6),
              'rQ': range(6, 12), 'rT': range(12, 15), 'rPhi': range(15, 16)}
    weights = [1 if p == q else 2 for p, q in PAIRS]
    m = residual[0].shape[0]
    Kout = frequency_grid(m)
    coefficients = [[f.add(*(f.scale(f.QQ_I(w), control[j]) for w, control in zip(row, controls)))
                     for j in range(16)] for row in centered_weights()]
    advection, pressure = [], []
    for k in range(11):
        terms = [(coefficients[i], coefficients[k-i]) for i in range(6) if 0 <= k-i < 6]
        adv = [f.add(*(f.adv(a[:3], b[j]) for a, b in terms)) for j in range(16)]
        advection.append(adv)
        # Independent exact Poisson solve: -Delta p = div(v.grad v).
        pressure.append(f.grad(f.green(f.add(*(f.diff(adv[j], j) for j in range(3))))))
    reports, highest = [], {}
    for power in range(16):
        exact = [{} for _ in range(16)]
        for j in range(16):
            if power < 5:
                exact[j] = f.scale(f.QQ_I(2*(power+1)/h), coefficients[power+1][j])
            if power < 6:
                exact[j] = f.add(exact[j], f.scale(-f.QQ_I(nu), f.lap(coefficients[power][j])))
            if power < 11:
                exact[j] = f.add(exact[j], advection[power][j])
        if power < 11:
            for j in range(3):
                exact[j] = f.add(exact[j], pressure[power][j])
                exact[j+3] = f.add(exact[j+3], f.scale(-1, pressure[power][j]))
        for i in range(6):
            j = power-i
            if not 0 <= j < 11:
                continue
            fields, g = coefficients[i], pressure[j]
            I, T = fields[3:6], fields[12:15]
            second = [[{} for _ in range(3)] for _ in range(3)]
            for index, (p, q) in enumerate(PAIRS):
                second[p][q] = second[q][p] = fields[6+index]
                exact[6+index] = f.add(exact[6+index], f.scale(-1, f.mul(I[p], g[q])),
                                       f.scale(-1, f.mul(g[p], I[q])))
            for index in range(3):
                exact[12+index] = f.add(exact[12+index], f.scale(-2, f.dot(second[index], g)),
                                        f.scale(-1, f.mul(f.trace(second), g[index])))
            exact[15] = f.add(exact[15], {f.ORIGIN: -4*f.dot(g, T).get(f.ORIGIN, f.ZERO)})
        require(all(all(max(map(abs, k)) <= 3 for k in row) for row in exact),
                'Independent convolution keeps every generated output')
        if power in (10, 15):
            for key, columns in groups.items():
                if power == (10 if key in ('epsilon0', 'epsilon1', 'rI') else 15):
                    highest[key] = any(exact[j] for j in columns)
        squares = {key: Q(0) for key in groups}
        for index in np.ndindex(m, m, m):
            k = tuple(int(x) for x in Kout[index])
            for j in range(16):
                if j == 15 and k != f.ORIGIN:
                    continue
                real = Q(residual[power][index+(j,)].real)
                imag = Q(residual[power][index+(j,)].imag)
                target = exact[j].get(k, f.ZERO)
                error2 = (real-Q(str(target.x)))**2+(imag-Q(str(target.y)))**2
                for key, columns in groups.items():
                    if j in columns:
                        weight = sum(x*x for x in k) if key == 'epsilon1' else weights[j-6] if key == 'rQ' else 1
                        squares[key] += weight*error2
        upper = {key: Q(radii[key][power]) for key in groups}
        require(all(squares[key] <= upper[key]**2 for key in groups),
                'Every exact physical time coefficient lies inside its returned weighted ball')
        reports.append(dict(time_power=power, exact_error_norms={k: sqrt_upper(v) for k, v in squares.items()},
                            radii={k: rational_upper(v) for k, v in upper.items()}))
    require(all(highest.values()) and len(highest) == 6,
            'Each residual group has a nonzero highest-degree term, including the fourth-moment source')
    return dict(status='Independent rational full-operator fixtures passed', grids=grids, reports=reports,
                nonzero_highest_degree=highest,
                scope='Complete operator algebra fixture; its moments are not asserted physically realizable')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--probe', action='store_true')
    parser.add_argument('--n', type=int, default=40)
    parser.add_argument('--h', type=float, default=1/16)
    parser.add_argument('--dt', type=float, default=1/128)
    parser.add_argument('--nu', type=float, default=.25)
    args = parser.parse_args()
    arithmetic_check()
    result = probe(args.n, args.h, args.dt, args.nu) if args.probe else exact_checks()
    print(json.dumps(result, indent=2), flush=True)
