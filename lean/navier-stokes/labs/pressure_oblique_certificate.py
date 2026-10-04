#!/usr/bin/env python3
"""Original datum and receiver checks for the oblique pressure certificate.

The physical consumer is pressure_history_certificate.py --oblique-amplitude.
Stored dyadics define the exact shared reference; a rounded Fourier coefficient
alone is not its observed velocity. These checks are not Lean certificates.
"""

from fractions import Fraction as Q
import json

import numpy as np
from pressure_polynomial_enclosure import rational_upper, sqrt_upper
from pressure_prefix_certificate import require


def exact_float(value):
    result = float(value)
    require(np.isfinite(result) and Q(result) == value,
            'The prescribed initial coefficient is exactly representable')
    return result


def original_datum(n, amplitude, normalization=1):
    """Exact Fourier data for A*(sin y-4sin z,sin z,sin(x+4y))."""
    require(isinstance(n, int) and n % 2 == 0 and n > 12,
            'An even grid retaining the original oblique mode without aliasing')
    require(np.isfinite(amplitude) and amplitude > 0,
            'Positive finite original amplitude')
    require(normalization in (1, n**3), 'Normalized or FFT initial coefficients')
    result = np.zeros((n, n, n, 16), dtype=complex)
    for mode, component, multiplier in [((0, 1, 0), 0, 1), ((0, 0, 1), 0, -4),
                                         ((0, 0, 1), 1, 1), ((1, 4, 0), 2, 1)]:
        for sign in (-1, 1):
            index = tuple(sign*k % n for k in mode)+(component,)
            value = -Q(amplitude)*multiplier*sign*normalization/2
            result[index] = complex(0., exact_float(value))
    return result


def initial_identity(raw, amplitude):
    require(np.array_equal(raw, original_datum(raw.shape[0], amplitude)),
            'Exact original oblique velocity and zero original pressure moments')


def make_flow(n, nu, amplitude):
    from reciprocal_pressure_payment import make_flow as reciprocal_flow
    flow = reciprocal_flow(n, nu)
    flow.initial = original_datum(n, amplitude, n**3)
    initial_identity(flow.initial/n**3, amplitude)
    flow.energy0 = exact_float(19*Q(amplitude)**2/4)
    return flow


def receiver_interval(raw, error):
    """Enclose 2*mean(u_3*sin x) from ||u-PH(raw)||_2 <= error.

    Fourier coefficients use normalized torus volume. At k=(1,0,0),
    the Leray projector fixes the third component. Hermitian reconstruction
    gives the exact sine coefficient Im raw(-k)_3 - Im raw(k)_3.
    Parseval (or Cauchy--Schwarz with 2sin x) gives radius sqrt(2)*error.
    The error bound must be supplied by the physical comparison.
    """
    n = raw.shape[0]
    require(n > 2 and raw.shape == (n, n, n, 16)
            and raw.dtype == np.dtype('complex128'), 'Normalized sixteen-field endpoint')
    require(np.isfinite(error) and error >= 0, 'Finite nonnegative physical L2 error')
    positive, negative = raw[1, 0, 0, 2], raw[n-1, 0, 0, 2]
    require(np.isfinite(positive) and np.isfinite(negative), 'Finite observed coefficient pair')
    center = Q(float(negative.imag))-Q(float(positive.imag))
    radius = Q(sqrt_upper(2*Q(error)**2))
    return dict(reference_sine_exact=str(center), radius_upper=float(radius),
                actual_sine_interval=[-rational_upper(-center+radius),
                                      rational_upper(center+radius)])


def propagate_substeps(old, row, h, nu):
    """Subdivide scalar comparisons only, retaining every inherited account."""
    from pressure_vorticity_control import propagate
    require(np.isfinite(h) and np.isfinite(nu) and h > 0 and nu > 0,
            'Positive finite physical interval and viscosity')
    rates = [abs(Q(row['S'])-Q(nu)), abs(2*Q(row['S'])-Q(nu)/2),
             abs(Q(row['Splus'])-Q(nu)/2), Q(row['Splus'])]
    count = 1
    while Q(h)*max(rates) > Q(count, 2):
        count *= 2
    step = exact_float(Q(h)/count)
    require(step > 0, 'Representable positive scalar subinterval')
    result = old
    for _ in range(count):
        result = propagate(result, row, step, nu)
    return result, count


def checks():
    """Independent physical datum and adversarial reconstructed-mode fixtures."""
    from pressure_oblique_return import datum
    from pressure_history_control import initial_controls
    from pressure_vorticity_control import propagate
    n, amplitude = 16, 8.
    raw = original_datum(n, amplitude)
    independent = np.zeros_like(raw)
    energy = Q(0)
    for j, component in enumerate(datum(4)):
        for mode, value in component.items():
            z = Q(str(value.x)), Q(str(value.y))
            independent[tuple(k % n for k in mode)+(j,)] = amplitude*complex(*map(float, z))
            energy += Q(amplitude)**2*(z[0]**2+z[1]**2)/2
            require(mode[j] == 0, 'Each original polarized mode is solenoidal')
    require(np.array_equal(raw, independent) and energy == 304,
            'Independent original Fourier field and exact kinetic energy')
    initial_identity(raw, amplitude)
    require(receiver_interval(raw, 0.)['actual_sine_interval'] == [0., 0.],
            'The generated receiver is absent initially')
    for location in [(0, 0, 0, 3), (1, 0, 0, 2), (1, 4, 0, 2)]:
        altered = raw.copy()
        altered[location] += .125
        try:
            initial_identity(altered, amplitude)
        except ArithmeticError:
            pass
        else:
            raise ArithmeticError('Reject changed initial fields or preloaded history')

    # Deliberately non-Hermitian data: reading only the positive coefficient
    # would give 6 rather than the exact reconstructed answer 8.
    raw[1, 0, 0, 2], raw[n-1, 0, 0, 2] = 7-3j, 11+5j
    raw[1, 0, 0, 0] = 123+456j  # Removed by the Leray projector at this mode.
    raw[0, 0, 0, 2] = 99  # Removed mean cannot affect the sine observation.
    observation = receiver_interval(raw, .125)
    require(observation['reference_sine_exact'] == '8', 'Retain the conjugate partner')
    lower, upper = map(Q, observation['actual_sine_interval'])
    require(lower < 8 < upper and (8-lower)**2 >= Q(1, 32)
            and (upper-8)**2 >= Q(1, 32), 'Both interval endpoints round outward')
    # The norm constant is sharp: w_3=c*sin(x) has ||w||_2^2=c^2/2
    # and observation c. An error coefficient at a different mode cannot
    # improve this bound without additional physical information.
    c = Q(3, 8)
    require(2*(2*(c/2)**2) == c*c, 'The conjugate Fourier pair attains the observation norm')

    row = dict(S=4., Splus=3., D=2., V0=1., V1=1.5, V2=2.,
               G0=.25, G1=.75, G2=.125, epsilon0=2.**-24, epsilon1=2.**-23,
               rI=2.**-20, rQ=2.**-19, rT=2.**-18, rPhi=2.**-17)
    initial = initial_controls()
    inherited, count = propagate_substeps(initial, row, .125, 1.)
    manual = propagate(propagate(initial, row, .0625, 1.), row, .0625, 1.)
    require(count == 2 and inherited == manual, 'Consecutive subintervals preserve the same history')
    reset = propagate(initial, row, .0625, 1.)
    require(inherited['e4'] > reset['e4'] and inherited['impulse'] > reset['impulse'],
            'Restarting the reserve would erase a strictly positive cost')
    return dict(status='Exact oblique datum, reconstructed receiver and inherited substeps checked',
                kinetic_energy=str(energy), adversarial_receiver=observation, scalar_substeps=count,
                scope='Exact arithmetic fixtures; no new enclosed physical prefix or Lean theorem')


if __name__ == '__main__':
    print(json.dumps(checks(), indent=2))
