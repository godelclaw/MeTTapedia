#!/usr/bin/env python3
"""Exact checks for an instantaneous alternative to caloric capacity.

On the normalized 2*pi torus, Q=||A^(-1/2)M(u)||_2^2/(2*nu^2),
where M=curl A^(-1)P[(curl u.grad)u]. Unlike the caloric capacity,
Q need not decrease along heat. The complete unforced balance includes
an additional quartic viscous term. Optional FFT checks require NumPy.
These finite calculations are not Lean certificates or PDE time enclosures.
"""
import argparse
from fractions import Fraction as F
import json

from fourier_interactions import (A, B, ZERO, add, dot, inverse_curl,
                                  pair, radius_squared, require, scale,
                                  sine, stretching, validate)
from caloric_force import capacity as caloric_capacity, mode_source


def inverse_laplacian(u):
    return {k: tuple(x/radius_squared(k) for x in v)
            for k, v in u.items() if radius_squared(k)}


def source(u):
    return inverse_curl(stretching(u))


def source_derivative(u, h):
    # Exact quadratic polarization retains both parent slots.
    return scale(F(1, 2), add(source(add(u, h)), scale(-1, source(add(u, scale(-1, h))))))


def capacity(u, nu):
    m = source(u)
    return pair(inverse_laplacian(m), m)/(2*nu*nu)


def derivative(u, h, nu):
    return pair(inverse_laplacian(source(u)), source_derivative(u, h))/(nu*nu)


def gradient_cross_source(u):
    """R sum_j ((partial_j curl u).grad)(partial_j u), directly by parents."""
    out = {}
    for p, a in u.items():
        for q, b in u.items():
            k = tuple(x+y for x, y in zip(p, q))
            value = mode_source(p, a, q, b)
            out[k] = tuple(x-dot(p, q)*y for x, y in zip(out.get(k, ZERO), value))
    return {k: v for k, v in out.items() if any(v)}


def inspect(name, u, nu):
    validate(u)
    au, n, m = A(u), B(u, u), source(u)
    c = gradient_cross_source(u)
    require(source_derivative(u, au) == add(A(m), scale(2, c)),
            'complete Laplacian product rule for projected stretching')
    heat = derivative(u, scale(-nu, au), nu)
    z = pair(m, m)/nu
    defect = -2*pair(inverse_laplacian(m), c)/nu
    require(heat == -z+defect, 'instantaneous capacity retains the viscous defect')
    nonlinear = derivative(u, n, nu)
    rhs = add(n, scale(-nu, au))
    actual = derivative(u, rhs, nu)
    require(actual == heat+nonlinear, 'actual unforced derivative')
    # Independent quartic polarization of the scalar functional.
    values = {a: capacity(add(u, scale(F(a), rhs)), nu) for a in (-2, -1, 1, 2)}
    require(actual == (8*(values[1]-values[-1])-values[2]+values[-2])/12,
            'quartic polarization of the full functional')
    pi, d = pair(au, n), pair(au, au)
    require(pair(au, m) == pi, 'physical stretching/source pairing')
    material = add(m, scale(-nu, au))
    cost = nu*d+pair(material, material)/nu
    twice_gdot = 2*(pi-nu*d)+actual
    require(twice_gdot+cost == nonlinear+defect, 'complete positive balance')
    return {'case': name, 'viscosity': nu, 'energy': pair(u, u),
            'gradient_energy': pair(au, u), 'laplacian_energy': d,
            'physical_stretching': pi, 'source_energy': pair(m, m),
            'instantaneous_capacity': capacity(u, nu),
            'caloric_capacity': caloric_capacity(u, nu),
            'heat_derivative': heat, 'nonlinear_return': nonlinear,
            'viscous_defect': defect, 'actual_derivative': actual,
            'twice_corrected_gradient_derivative': twice_gdot, 'positive_cost': cost}


def example():
    # (sin y, 0, (-1+cos(2y))*sin x).
    return add(sine((0, 1, 0), (1, 0, 0)),
               sine((1, 0, 0), (0, 0, -1)),
               sine((1, 2, 0), (0, 0, F(1, 2))),
               sine((1, -2, 0), (0, 0, F(1, 2))))


def fft_check(u, nu, size):
    """Independent physical vorticity, products, Leray source and tangent."""
    import numpy as np
    frequencies = np.rint(np.fft.fftfreq(size)*size)
    k = np.stack(np.meshgrid(frequencies, frequencies, frequencies, indexing='ij'))
    k2 = np.sum(k*k, axis=0)
    inverse = np.divide(1., k2, out=np.zeros_like(k2), where=k2 > 0)
    axes = (1, 2, 3)
    uh = np.zeros((3, size, size, size), dtype=complex)
    for mode, v in u.items():
        uh[(slice(None), *(x % size for x in mode))] = [1j*float(x) for x in v]

    def physical(h): return np.fft.ifftn(h, axes=axes).real*size**3
    def spectral(v): return np.fft.fftn(v, axes=axes)/size**3
    def cross(a, b): return np.cross(a, b, axisa=0, axisb=0, axisc=0)
    def curl(h): return physical(1j*cross(k, h))
    def gradient(h): return [physical(1j*k[j]*h) for j in range(3)]
    def image(v): return 1j*cross(k, spectral(v))*inverse

    v, omega, grad = physical(uh), curl(uh), gradient(uh)
    force = sum(omega[j]*grad[j] for j in range(3))
    mh = image(force)
    raw = -spectral(sum(v[j]*grad[j] for j in range(3)))
    nh = raw-k*np.sum(k*raw, axis=0)*inverse
    heat_h = -float(nu)*k2*uh

    def dq(h):
        curl_h, grad_h = curl(h), gradient(h)
        tangent = sum(curl_h[j]*grad[j]+omega[j]*grad_h[j] for j in range(3))
        return float(np.real(np.sum(np.conj(mh)*image(tangent)*inverse))/float(nu)**2)

    exact = inspect('fft_reference', u, nu)
    computed = {'instantaneous_capacity': float(np.sum(abs(mh)**2*inverse)/(2*float(nu)**2)),
                'heat_derivative': dq(heat_h), 'nonlinear_return': dq(nh),
                'actual_derivative': dq(nh+heat_h)}
    errors = {key: abs(value-float(exact[key]))/max(1., abs(float(exact[key])))
              for key, value in computed.items()}
    require(max(errors.values()) < 1e-12, 'independent physical/FFT derivatives')
    return {'grid': size, 'max_scaled_error': max(errors.values()), **computed}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fft-check', action='store_true')
    args = parser.parse_args()
    u = example()
    row = inspect('heat_growth_shear', u, F(1))
    expected = {'energy': F(5, 4), 'gradient_energy': F(9, 4),
                'laplacian_energy': F(29, 4), 'physical_stretching': F(0),
                'source_energy': F(17, 800), 'instantaneous_capacity': F(67, 16000),
                'caloric_capacity': F(23, 2400), 'heat_derivative': F(49, 4000),
                'nonlinear_return': F(0), 'viscous_defect': F(67, 2000)}
    require(all(row[key] == value for key, value in expected.items()),
            'independent closed-form shear constants')
    rows = [row]
    for alpha, nu in ((F(2), F(1, 2)), (F(-3), F(2)), (F(40), F(1))):
        r = inspect('scaled_heat_growth_shear', scale(alpha, u), nu)
        require(r['heat_derivative'] == F(49, 4000)*alpha**4/nu,
                'positive heat derivative at arbitrary amplitude and viscosity')
        require(r['nonlinear_return'] == 0, 'vanishing nonlinear return in this phase')
        require(r['twice_corrected_gradient_derivative'] ==
                -F(29, 2)*nu*alpha**2+F(49, 4000)*alpha**4/nu,
                'actual corrected-gradient derivative')
        rows.append(r)
    require(rows[-1]['twice_corrected_gradient_derivative'] == 8160,
            'strict increase under the complete unforced equation')
    triad = add(sine((1, 0, 0), (0, 1, 1)), sine((0, 1, 0), (1, 0, 1)),
                sine((1, 1, 0), (1, -1, 1)))
    rows.append(inspect('signed_triad', triad, F(1)))
    rows.append(inspect('noncoplanar', add(triad, sine((0, 0, 1), (1, 2, 0))), F(1, 2)))
    result = {'status': 'all rational checks passed',
              'scope': 'exact finite identities; analytic local PDE implication',
              'cases': [{key: str(value) for key, value in r.items()} for r in rows]}
    if args.fft_check:
        result['independent_fft'] = [fft_check(u, F(1), n) for n in (16, 24)]
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
