#!/usr/bin/env python3
"""Checks for recurrent caloric capacity in a regular two-packet shear.

The smooth flat-plateau construction and its viscous logarithmic-time
comparison are analytic arguments in ns_forced_tail_budget.tex. The
finite Fourier profiles here check heat pairings only: they are not
flat-plateau Euler solutions. All spatial means are normalized on the
2*pi torus. Optional FFT checks require NumPy.
"""
import argparse
from fractions import Fraction as F
import json

from fourier_interactions import require
from caloric_force import mode_source
from separated_caloric import sector


def convolve(a, b):
    out = {}
    for p, x in a.items():
        for q, y in b.items():
            out[p+q] = out.get(p+q, F(0))+x*y
    return {k: x for k, x in out.items() if x}


def combine(a, b, factor=F(1)):
    out = a.copy()
    for k, x in b.items():
        out[k] = out.get(k, F(0))+factor*x
    return {k: x for k, x in out.items() if x}


def shear_blocks(shear, packet, separation=None):
    """Cos(x) coefficient of inverse-curl stretching, grouped by heat rate.

    For velocity (U(y),0,phi(y)sin(x)), the stretching is
    (-U'(y)phi(y)cos(x),0,0). Both artificial heat inputs are retained.
    """
    blocks = {}
    for p, a in shear.items():
        for q, b in packet.items():
            if separation is not None and sector((0, p, 0), (1, q, 0), 0, separation) != 'keep':
                continue
            n = p+q
            value = -F(n*p, 1+n*n)*a*b
            key = (n, 1+p*p+q*q)
            blocks[key] = blocks.get(key, F(0))+value
    return {k: x for k, x in blocks.items() if x}


def heat_pair(a, b, nu=F(1)):
    by_mode = {}
    for (n, rate), value in b.items():
        by_mode.setdefault(n, []).append((rate, value))
    # The x-average of cos(x)^2 is 1/2.
    return sum((x*y/(2*nu*nu*(r+s))
                for (n, r), x in a.items()
                for s, y in by_mode.get(n, ())), F(0))


def fejer_shear(degree):
    # This is pi/(22/7) times a Fejer mean of sign(cos(y)). Thus |U|<=1.
    pi_upper = F(22, 7)
    out = {}
    for n in range(1, degree+1, 2):
        value = 2*(-1)**((n-1)//2)*(1-F(n, degree+1))/(pi_upper*n)
        out[n] = out[-n] = value
    return out


def constants_check():
    require(F(22, 7)**2 < 10, 'the stated upper bound for pi implies pi squared < 10')
    # Integral exp(-2r) min(1/4,exp(-2r)) dr, split at r=log(2).
    first, second = F(3, 32), F(1, 64)
    square_capacity_upper = (first+second)/8
    require(square_capacity_upper == F(7, 512), 'square-profile capacity bound')
    step_cross_lower = (F(1, 40)-square_capacity_upper)/4
    require(step_cross_lower == F(29, 10240), 'strict step-profile cross lower bound')
    bad_set_measure = F(1, 2**20)
    root_measure = F(1, 2**10)
    require(root_measure**2 == bad_set_measure, 'normalized transition-set size')
    # ||Phi(U,phi)-Phi(U*,phi*)|| <= (1/4)*2 sqrt(d)+(3/4)*sqrt(d).
    source_error = F(5, 4)*root_measure
    cross_error = 2*F(1, 4)*source_error
    smooth_cross_lower = step_cross_lower-cross_error
    require(cross_error == F(5, 8192), 'bilinear heat-map continuity loss')
    require(smooth_cross_lower > F(1, 512), 'positive smooth cross pairing')
    return {'square_capacity_upper': str(square_capacity_upper),
            'step_cross_lower': str(step_cross_lower),
            'transition_measure_upper': str(bad_set_measure),
            'cross_pair_error_upper': str(cross_error),
            'smooth_cross_lower': str(smooth_cross_lower),
            'simplified_smooth_cross_lower': '1/512'}


def finite_check(degree):
    u = fejer_shear(degree)
    plus = {0: F(1, 2), **{k: x/2 for k, x in u.items()}}
    minus = {0: F(1, 2), **{k: -x/2 for k, x in u.items()}}
    m0, m1 = shear_blocks(u, {0: F(1)}), shear_blocks(u, u)
    mp, mm = shear_blocks(u, plus), shear_blocks(u, minus)
    k0, k1 = heat_pair(m0, m0), heat_pair(m1, m1)
    cross = heat_pair(mp, mm)
    require(heat_pair(m0, m1) == 0, 'odd/even output orthogonality')
    require(k0 == sum((F(n**4, 4*(1+n*n)**3)*a*a for n, a in u.items()), F(0)),
            'independent single-parent heat integral')
    require(cross == (k0-k1)/4 and cross > 0, 'positive finite-profile cross pairing')
    require(k1 <= F(7, 512), 'bounded-square comparison for the finite profile')
    require(heat_pair(mp, mm, F(1, 2)) == 4*cross, 'inverse viscosity squared')
    for sign in (F(1), F(-1)):
        total = combine(mp, mm, sign)
        require(heat_pair(total, total) == heat_pair(mp, mp)+heat_pair(mm, mm)+2*sign*cross,
                'phase extrema of the capacity')
    residual = combine(convolve(u, plus), plus, F(-1))
    residual_squared = sum((x*x for x in residual.values()), F(0))
    require(residual_squared > 0, 'finite profile is explicitly not a flat-plateau Euler packet')
    masked = []
    for separation in (3, 4, 5, 8):
        p = shear_blocks(u, plus, separation)
        m = shear_blocks(u, minus, separation)
        value = heat_pair(p, m)
        k0r = shear_blocks(u, {0: F(1)}, separation)
        k1r = shear_blocks(u, u, separation)
        require(value == (heat_pair(k0r, k0r)-heat_pair(k1r, k1r))/4,
                'masked capacity retains the same phase formula')
        if separation == 8:
            require(p == mp and m == mm and value == cross,
                    'large separation recovers every parent of this finite profile')
        masked.append({'separation': separation, 'cross_pairing_rounded': float(value)})
    return {'degree': degree, 'constant_packet_capacity': str(k0),
            'square_packet_capacity': str(k1), 'cross_pairing': str(cross),
            'cross_pairing_rounded': float(cross),
            'euler_plateau_residual_squared': str(residual_squared),
            'masked_pairings': masked}


def vertical_cancellation_check():
    count = 0
    for x in (-1, 1):
        for y in (-1, 1):
            for p in (-17, -2, 0, 3, 31):
                for q in (-19, -3, 0, 2, 29):
                    a, b = (x, p, 0), (y, q, 0)
                    va, vb = (F(0), F(0), F(2)), (F(0), F(0), F(-3))
                    lhs = mode_source(a, va, b, vb)
                    rhs = mode_source(b, vb, a, va)
                    require(all(c+d == 0 for c, d in zip(lhs, rhs)),
                            'ordered purely vertical self-stretching cancels')
                    for separation in (3, 8):
                        require(sector(a, b, 0, separation) == sector(b, a, 0, separation),
                                'the source mask preserves vertical-pair cancellation')
                    count += 1
    return count


def nontrivial_mask_check():
    """Near-cancelling parents whose nonzero output is actually excluded."""
    u = {k: F(1, 4) for k in (-33, -31, 31, 33)}
    plus = {0: F(1, 2), **{k: a/2 for k, a in u.items()}}
    minus = {0: F(1, 2), **{k: -a/2 for k, a in u.items()}}
    mp, mm = shear_blocks(u, plus), shear_blocks(u, minus)
    kp, km = shear_blocks(u, plus, 3), shear_blocks(u, minus, 3)
    require(combine(mp, kp, F(-1)) == {(2, 2051): F(-1, 40), (-2, 2051): F(-1, 40)},
            'the mask removes the explicit nonzero near-cancelling output')
    require(combine(mm, km, F(-1)) == {(2, 2051): F(1, 40), (-2, 2051): F(1, 40)},
            'the opposite packet has the opposite excluded heat image')
    full, kept = heat_pair(mp, mm), heat_pair(kp, km)
    require(kept-full == F(1, 6563200), 'explicit excluded cross-capacity')
    for sign in (F(1), F(-1)):
        total = combine(kp, km, sign)
        require(heat_pair(total, total) == heat_pair(kp, kp)+heat_pair(km, km)+2*sign*kept,
                'phase extrema with a nontrivial parent exclusion')
    require(shear_blocks(u, plus, 8) == mp and shear_blocks(u, minus, 8) == mm,
            'larger separation restores these excluded parents')
    return {'shear_frequencies': sorted(u), 'excluded_output_y': [-2, 2],
            'full_cross_pairing_rounded': float(full),
            'kept_cross_pairing_rounded': float(kept),
            'kept_minus_full': str(kept-full)}


def fft_check(degree, order):
    """Physical products, inverse curl and independent heat quadrature."""
    import numpy as np
    from numpy.polynomial.legendre import leggauss

    shear = fejer_shear(degree)
    packets = [{0: F(1, 2), **{k: sign*x/2 for k, x in shear.items()}}
               for sign in (1, -1)]
    nx, ny = 16, 1 << (4*degree+2).bit_length()
    kx, ky = np.rint(np.fft.fftfreq(nx)*nx), np.rint(np.fft.fftfreq(ny)*ny)
    squared = kx[:, None]**2+ky[None, :]**2
    inverse = np.divide(1., squared, out=np.zeros_like(squared), where=squared > 0)
    cosine = np.cos(2*np.pi*np.arange(nx)/nx)[:, None]

    def packed(coefficients):
        out = np.zeros(ny, dtype=complex)
        for n, a in coefficients.items():
            out[n % ny] = ny*float(a)
        return out

    su = packed(shear)
    sp = [packed(p) for p in packets]

    def integrand(r):
        heat = np.exp(-r*ky**2)
        derivative_u = np.fft.ifft(1j*ky*heat*su).real
        images = []
        for p in sp:
            phi = np.fft.ifft(heat*p).real
            stretching_x = -np.exp(-r)*cosine*(derivative_u*phi)[None, :]
            image = -1j*ky[None, :]*np.fft.fft2(stretching_x)*inverse
            images.append(image)
        return float(np.vdot(images[0], images[1]).real/(nx*ny)**2)

    edges = [0., 1/(8*(degree+1)**2)]
    while edges[-1] < 16:
        edges.append(min(16., 2*edges[-1]))
    nodes, weights = leggauss(order)
    result = 0.
    for a, b in zip(edges, edges[1:]):
        result += (b-a)/2*sum(weight*integrand((a+b)/2+(b-a)*node/2)
                              for node, weight in zip(nodes, weights))
    expected = float(heat_pair(shear_blocks(shear, packets[0]), shear_blocks(shear, packets[1])))
    error = abs(result-expected)/expected
    require(error < 1e-10, 'independent physical cross-capacity quadrature')
    return {'degree': degree, 'grid': [nx, ny], 'quadrature_order': order,
            'cross_pairing': result, 'relative_error': error}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fft-check', action='store_true')
    args = parser.parse_args()
    result = {'status': 'all rational checks passed',
              'scope': 'heat-pair algebra and analytic constants; no PDE time enclosure',
              'constants': constants_check(),
              'vertical_pair_cancellation_cases': vertical_cancellation_check(),
              'nontrivial_parent_exclusion': nontrivial_mask_check(),
              'finite_heat_profiles': [finite_check(n) for n in (3, 7, 15, 31)]}
    if args.fft_check:
        result['independent_fft'] = [fft_check(15, n) for n in (12, 20)]
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
