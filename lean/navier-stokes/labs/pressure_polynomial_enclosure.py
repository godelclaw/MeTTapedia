#!/usr/bin/env python3
"""Outward norm bounds for supplied pressure-residual coefficient balls.

The scalar conversion is rational; signed inner products have explicit
IEEE binary64 error bounds. This does not certify how the residual fields
were generated. The optional physical probe encloses only its stored
residual polynomial: its FFT/operator coefficient errors remain unpaid.
The shared-reference construction separately encloses the exact projected
Bernstein curve, including the moment zero modes. No Lean proof is claimed.
"""

import argparse
from fractions import Fraction as Q
from functools import lru_cache
from math import comb, isfinite, ldexp, sqrt
import json
import time

import numpy as np
from cellular_parent_history import PAIRS
from pressure_prefix_certificate import (U, add, arithmetic_check, bernstein,
    combine, frequency_grid, mul, norm, reconstruct, require, total_upper, up)


def rational_upper(value):
    result = float(value)
    require(isfinite(result), 'Finite rational-to-binary upper bound')
    return float(up(result)) if Q(result) < value else result


def sqrt_upper(value):
    """Verify the returned square root by an exact rational comparison."""
    require(value >= 0, 'Nonnegative squared-norm bound')
    if value == 0:
        return 0.
    exponent = (value.numerator.bit_length()-value.denominator.bit_length())//2
    scaled = value*Q(2)**(-2*exponent)
    result = ldexp(sqrt(float(scaled)), exponent)
    require(isfinite(result), 'Finite square-root proposal')
    while Q(result)**2 < value:
        result = float(up(result))
        require(isfinite(result), 'Finite outward square root')
    return result


def signed_inner(a, b, weight=1):
    """Enclose Re sum weight*conj(a)*b for exact stored coefficients.

    Products and additions are explicit; no BLAS dot-product accuracy is
    assumed. At most M+4 rounding factors affect any exact term. The
    deliberately larger gamma_(8(M+1)) also covers either reduction order.
    The absolute underflow allowance covers weights <=2^30 and M<=2^28.
    """
    a, b, weight = np.asarray(a), np.asarray(b), np.asarray(weight)
    require(a.dtype in (np.dtype('float64'), np.dtype('complex128'))
            and b.dtype in (np.dtype('float64'), np.dtype('complex128')),
            'Binary64 real or complex coefficient arithmetic')
    require(a.shape == b.shape and a.size <= 2**28 and a.size > 0,
            'Equal nonempty coefficient arrays in the stated arithmetic range')
    require(np.isfinite(a).all() and np.isfinite(b).all()
            and np.isfinite(weight).all() and np.all(weight >= 0)
            and np.all(weight <= 2**30) and np.all(weight == np.floor(weight)),
            'Finite coefficients and exact nonnegative integer weights')
    real = a.real*b.real
    imag = a.imag*b.imag
    terms = weight*(real+imag)
    absolute = up(weight*up(up(abs(real))+up(abs(imag))))
    require(terms.shape == a.shape and np.isfinite(terms).all()
            and np.isfinite(absolute).all(), 'No product overflow or shape expansion')
    center = float(np.sum(terms))
    require(isfinite(center), 'No signed reduction overflow')
    count = 8*(a.size+1)
    require(count*U < .01, 'Explicit inner-product gamma bound')
    gamma = Q(count, 2**53-count)
    # 1e-290 exceeds 128(M+1)^2*2^30*2^-1074 on the stated domain.
    radius = gamma*Q(total_upper(absolute))+Q(1, 10**290)
    return Q(center)-radius, Q(center)+radius


@lru_cache(maxsize=16)
def interval_matrix(degree, cells):
    """Exact map from centered powers to each subinterval's Bernstein basis."""
    require(degree >= 0 and cells > 0, 'Polynomial degree and subdivision count')
    result = []
    for cell in range(cells):
        left, width = Q(2*cell, cells)-1, Q(2, cells)
        rows = []
        for k in range(degree+1):
            rows.append(tuple(sum(Q(comb(k, j)*comb(i, j), comb(degree, j))
                                  *left**(i-j)*width**j
                                  for j in range(min(i, k)+1))
                              for i in range(degree+1)))
        result.append(tuple(rows))
    return tuple(result)


def polynomial_upper(coefficients, cells=8):
    """Outward upper bound, including signed conversion cancellation."""
    require(coefficients and all(lo <= hi for lo, hi in coefficients),
            'Nonempty ordered rational coefficient intervals')
    upper = None
    for matrix in interval_matrix(len(coefficients)-1, cells):
        for row in matrix:
            value = sum(w*(hi if w >= 0 else lo)
                        for w, (lo, hi) in zip(row, coefficients))
            upper = value if upper is None else max(upper, value)
    return upper


def norm_polynomial(coefficients, weight=1, denominator=1, radii=None, cells=8):
    """Bound ||sum a_i s^i|| on [-1,1], plus supplied norm-ball radii.

    The inner product is sum weight*conj(a)*b / denominator. Supplied
    radii must already use THIS norm, including its weights/normalization.
    Their validity is a caller obligation, never inferred from samples.
    """
    require(coefficients and denominator > 0 and int(denominator) == denominator,
            'Nonempty polynomial and exact positive integer normalization')
    count = len(coefficients)
    squared = [(Q(0), Q(0)) for _ in range(2*count-1)]
    for i, a in enumerate(coefficients):
        for j in range(i, count):
            lo, hi = signed_inner(a, coefficients[j], weight)
            if i == j:
                lo = max(Q(0), lo)
            factor = Q(1 if i == j else 2, denominator)
            oldlo, oldhi = squared[i+j]
            squared[i+j] = oldlo+factor*lo, oldhi+factor*hi
    value = polynomial_upper(squared, cells)
    radii = [0.]*count if radii is None else radii
    require(len(radii) == count and all(isfinite(r) and r >= 0 for r in radii),
            'One finite nonnegative supplied norm radius per coefficient')
    root = sqrt_upper(value)
    bound = rational_upper(Q(root)+sum(map(Q, radii)))
    return dict(bound=bound, stored_center_bound=root,
                coefficient_radius_sum=rational_upper(sum(map(Q, radii))))


def residual_bounds(residual, radii=None, cells=8, normalized=False):
    """Use the six physical norms; supplied radii are always normalized.

    With normalized=True, coefficient arrays already use normalized Fourier
    coordinates. Otherwise their squared inner products are divided by m^6.
    """
    m = residual[0].shape[0]
    require(all(a.shape == (m, m, m, 16) for a in residual), 'Complete residual fields')
    k2 = np.sum(frequency_grid(m)**2, axis=-1)
    weights = np.array([1 if i == j else 2 for i, j in PAIRS])
    groups = [('epsilon0', slice(0, 3), 1), ('epsilon1', slice(0, 3), k2[..., None]),
              ('rI', slice(3, 6), 1), ('rQ', slice(6, 12), weights),
              ('rT', slice(12, 15), 1), ('rPhi', None, 1)]
    result = {}
    for key, block, weight in groups:
        coeff = [a[..., block] if block is not None else a[0, 0, 0, 15:16]
                 for a in residual]
        result[key] = norm_polynomial(coeff, weight, 1 if normalized else m**6,
                                     None if radii is None else radii[key], cells)
    return result


def centered_weights():
    """B_i^5((1+s)/2) = binom(5,i)(1+s)^i(1-s)^(5-i)/32."""
    return [[Q(comb(5, i), 32)*sum(comb(i, j)*comb(5-i, k-j)*(-1)**(k-j)
                  for j in range(max(0, k-(5-i)), min(i, k)+1))
             for i in range(6)] for k in range(6)]


def shared_reference(raw):
    """Enclose one exact shared Bernstein curve in centered coordinates.

    Input Fourier coefficients are normalized stored dyadics. The target
    applies the SAME exact linear reconstruction to every control point:
    PH for velocity, H for the other fields. Thus shared input endpoints
    imply shared exact reconstructed endpoints. Returned rounded centered
    arrays alone are not the target and need not share exact endpoints.
    Radii below are unweighted normalized L2 for each named field block.
    Endpoint records are also balls, not assertions of exact midpoints.
    """
    require(len(raw) == 6, 'Six shared Bernstein control points')
    n = raw[0].shape[0]
    K = frequency_grid(n)
    k2 = np.sum(K*K, axis=-1)
    outside = np.any(3*abs(K) >= n, axis=-1)
    negative = (-np.arange(n)) % n
    shape = (n, n, n, 16)
    require(n % 2 == 0 and all(a.dtype == np.dtype('complex128')
            and a.shape == shape and np.isfinite(a).all()
            and np.all(a[outside] == 0) for a in raw), 'Finite alias-free raw control points')
    blocks = [('u', slice(0, 3)), ('I', slice(3, 6)), ('Q', slice(6, 12)),
              ('T', slice(12, 15)), ('Phi', slice(15, 16))]
    result = [np.zeros(shape, dtype=complex) for _ in range(6)]
    radii, endpoints = {}, {}
    for key, block in blocks:
        values, errors = [], []
        for a in raw:
            v = a[..., block]
            if key == 'u':
                v, error = reconstruct(v, K, k2)
            elif key == 'Phi':
                require(np.count_nonzero(v) == int(v[0, 0, 0, 0] != 0),
                        'The integrated fourth moment is a scalar zero mode')
                v, error = v.real.astype(complex), 0.
            else:
                partner = v[np.ix_(negative, negative, negative)].conjugate()
                v, error = (v+partner)/2, add(mul(4*U, norm(v)), 1.e-290)
            values.append(v)
            errors.append(error)
        pairs = [combine(values, errors, row) for row in centered_weights()]
        for j, (value, _) in enumerate(pairs):
            result[j][..., block] = value
        radii[key] = [radius for _, radius in pairs]
        endpoints[key] = (dict(center=values[0], radius=errors[0]),
                          dict(center=values[-1], radius=errors[-1]))
    return result, radii, endpoints


def exact_checks():
    arithmetic_check()
    field = np.zeros((4, 4, 4, 16), complex)
    field[1, 0, 0, 1] = field[3, 0, 0, 1] = .5
    offdiagonal = next(j for j, (p, q) in enumerate(PAIRS) if p != q)
    field[0, 0, 0, 6+offdiagonal] = 1
    normalized = residual_bounds([field], normalized=True)
    unnormalized = residual_bounds([64*field])
    for key, square in [('epsilon0', Q(1, 2)), ('epsilon1', Q(1, 2)), ('rQ', Q(2))]:
        require(Q(normalized[key]['bound'])**2 >= square,
                'Exact physical norm of normalized cosine/tensor fixture')
        require(abs(normalized[key]['bound']-unnormalized[key]['bound']) < 1e-12,
                'Normalized and unnormalized storage have identical physical units')
    cases = [([1., 1., 1.], [2.**80, 1., -2.**80], [1, 1, 1]),
             ([2.**-1074, 2.**-700], [2.**-1074, -2.**-700], [2, 2]),
             ([2.**-1074], [2.**1023], [1]),
             ([1+2j, -3+4j, 2.**-40-1j], [3-2j, 5+7j, 2j], [1, 7, 2])]
    for aa, bb, ww in cases:
        a, b, w = np.array(aa, complex), np.array(bb, complex), np.array(ww)
        exact = sum(int(z)*(Q(x.real)*Q(y.real)+Q(x.imag)*Q(y.imag))
                    for x, y, z in zip(a, b, w))
        lo, hi = signed_inner(a, b, w)
        require(lo <= exact <= hi, 'Signed Gram enclosure matches independent exact arithmetic')
    for exponent in [-2200, -1300, -1074, -100, 0, 700, 1900]:
        value = Q(3)*Q(2)**exponent
        require(Q(sqrt_upper(value))**2 >= value, 'Verified root including extreme underflow')
    # Independently reconstruct every monomial under the exact basis map.
    for degree in [0, 5, 30]:
        for cell in [0, 3, 7]:
            matrix = interval_matrix(degree, 8)[cell]
            for tau in [Q(1, 7), Q(4, 5)]:
                x = Q(cell, 4)-1+tau/4
                for power in range(degree+1):
                    value = sum(matrix[k][power]*comb(degree, k)*tau**k
                                *(1-tau)**(degree-k) for k in range(degree+1))
                    require(value == x**power, 'Independent exact Bernstein reconstruction')
    # The same endpoint must not be replaced by independently rounded powers.
    points = [1., 0., 0., 0., 0., 2.**-54]
    converted = [float(sum(w*Q(p) for w, p in zip(row, points)))
                 for row in centered_weights()]
    endpoint = sum(map(Q, converted))
    require(endpoint != Q(points[-1]), 'Rounding each power coefficient changes the shared endpoint')
    # Exact tensor fixture: weights include off-diagonal multiplicity.
    coeff = [np.array([complex((j+1)*(-1)**i/8, (i-j)/16) for j in range(4)])
             for i in range(6)]
    weights = np.array([1, 2, 2, 1])
    bound = norm_polynomial(coeff, weights, 8, radii=[2.**-40]*6)
    for s in [Q(-1), Q(-7, 13), Q(0), Q(3, 7), Q(1)]:
        square = sum(int(weights[j])*(sum(Q(a[j].real)*s**i for i, a in enumerate(coeff))**2
                   +sum(Q(a[j].imag)*s**i for i, a in enumerate(coeff))**2)/8 for j in range(4))
        require(Q(bound['stored_center_bound'])**2 >= square, 'Rational evaluation below full-interval bound')
    # Reconstruct a non-solenoidal, non-Hermitian fixture with nonzero means.
    raw = [np.zeros((4, 4, 4, 16), complex) for _ in range(6)]
    for i, a in enumerate(raw):
        a[1, 0, 0, :15] = np.arange(15)*(i+1)/32+1j/8
        a[1, 1, 1, :15] = np.arange(15)*(i+1)/64-1j/16
        a[0, 0, 0, :] = (i+1)*np.arange(16)/16
    centers, radii, endpoints = shared_reference(raw)
    support = [(0, 0, 0), (1, 0, 0), (-1, 0, 0), (1, 1, 1), (-1, -1, -1)]
    exact_points = []
    for a in raw:
        exact = {}
        for k in support:
            v, partner = a[tuple(q % 4 for q in k)], a[tuple(-q % 4 for q in k)]
            real = [(Q(v[j].real)+Q(partner[j].real))/2 for j in range(16)]
            imag = [(Q(v[j].imag)-Q(partner[j].imag))/2 for j in range(16)]
            square = sum(q*q for q in k)
            for part in [real, imag]:
                product = sum(k[j]*part[j] for j in range(3))
                part[:3] = [part[j]-k[j]*product/square if square else Q(0) for j in range(3)]
            exact[k] = real, imag
        exact_points.append(exact)
    for power, row in enumerate(centered_weights()):
        for key, first, last in [('u', 0, 3), ('I', 3, 6), ('Q', 6, 12), ('T', 12, 15), ('Phi', 15, 16)]:
            error2 = Q(0)
            for k in support:
                value = centers[power][tuple(q % 4 for q in k)]
                for j in range(first, last):
                    real = sum(w*e[k][0][j] for w, e in zip(row, exact_points))
                    imag = sum(w*e[k][1][j] for w, e in zip(row, exact_points))
                    error2 += (Q(value[j].real)-real)**2+(Q(value[j].imag)-imag)**2
            require(error2 <= Q(radii[key][power])**2,
                    'Exact rational projected coefficient lies in its returned field ball')
    next_raw = [raw[-1].copy() for _ in range(6)]
    _, _, following = shared_reference(next_raw)
    for key in endpoints:
        require(np.array_equal(endpoints[key][-1]['center'], following[key][0]['center'])
                and endpoints[key][-1]['radius'] == following[key][0]['radius'],
                'Identical shared reconstruction with its endpoint error')
    require(endpoints['u'][0]['center'][0, 0, 0].tolist() == [0., 0., 0.]
            and np.any(endpoints['Q'][0]['center'][0, 0, 0] != 0),
            'Velocity mean removed and moment means retained')
    return dict(status='Exact arithmetic fixtures passed',
                rounded_endpoint=str(endpoint), intended_endpoint=str(Q(points[-1])),
                fixture_norm_bound=bound, shared_reference_radii=radii,
                scope='Coefficient-ball consumer; physical coefficient generation remains separate')


def first_interval(n, h, dt, nu):
    from pressure_history_control import jets
    from pressure_history_slabs import (full_polynomial,
        interval_norm_bounds, squared_norm_polynomials)
    from reciprocal_pressure_payment import make_flow

    start = time.time()
    require(h > 0 and dt > 0 and nu > 0 and round(h/dt)*Q(dt) == Q(h), 'Exact integral time steps')
    flow = make_flow(n, nu, 1.)
    initial, state = flow.initial.copy(), flow.initial.copy()
    f0, j0 = jets(flow, state)
    for _ in range(round(h/dt)):
        state, _ = flow.step(state, dt)
    f1, j1 = jets(flow, state)
    raw = [a/n**3 for a in bernstein(initial, state, f0, f1, j0, j1, h)]
    midpoints, reference_radii, _ = shared_reference(raw)
    # This rescaling and the following numerical operator still need error
    # propagation from the supplied reference balls. Zero radii below mean
    # exactly the STORED residual coefficients, not the physical residual.
    c = [a*n**3 for a in midpoints]
    residual, _ = full_polynomial(c, h, nu)
    old = interval_norm_bounds(squared_norm_polynomials(residual))
    certified = residual_bounds(residual)
    ratios = {key: value['bound']/old[key] for key, value in certified.items()}
    require(all(value <= 1.01 for value in ratios.values()),
            'Signed Gram arithmetic costs at most one percent on this stored residual')
    return dict(n=n, h=h, dt=dt, nu=nu, stored_polynomial=certified,
                unenclosed_comparison=old, norm_ratios=ratios,
                shared_reference_coefficient_radii=reference_radii,
                scope='Stored residual centers only; physical FFT/operator errors NOT enclosed',
                elapsed=time.time()-start)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--probe', action='store_true')
    parser.add_argument('--n', type=int, default=40)
    parser.add_argument('--h', type=float, default=1/16)
    parser.add_argument('--dt', type=float, default=1/128)
    parser.add_argument('--nu', type=float, default=.25)
    args = parser.parse_args()
    arithmetic_check()
    result = first_interval(args.n, args.h, args.dt, args.nu) if args.probe else exact_checks()
    print(json.dumps(result, indent=2), flush=True)
