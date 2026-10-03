#!/usr/bin/env python3
"""Continuous-time residual enclosures for a finite unforced NS prefix.

The approximate integrator supplies numbers, not proof premises. Each slab
is the exact Leray projection of an exactly Hermitian Bernstein polynomial
whose stored binary64 coefficients are interpreted as dyadic rationals.
The verifier uses explicit radix-two butterflies and outward scalar bounds.
Its arithmetic model is IEEE binary64 round-to-nearest, without overflow.
This is an analytic/computational certificate, not a Lean kernel proof.
"""

import argparse
from fractions import Fraction as Q
from math import comb, ceil
import json
import hashlib
import sys
import time
import numpy as np
from pressure_prefix_control import VelocityFlow, require

U = 2.**-53


def up(x):
    return np.nextafter(x, np.inf)


def down(x):
    return np.nextafter(x, -np.inf)


def arithmetic_check():
    info = np.finfo(np.float64)
    require(info.eps == 2.**-52 and info.nmant == 52, 'IEEE binary64 significand')
    require(np.float64(1)+np.float64(2.**-53) == 1
            and np.float64(1)-np.float64(2.**-54) == 1,
            'Round-to-nearest tie behavior in the elementary array operations')
    require(np.float64(2.**-1022)*np.float64(.5) > 0,
            'Gradual underflow in the arithmetic used for norm bounds')


def add(a, b):
    return float(up(a+b))


def mul(a, b):
    require(a >= 0 and b >= 0, 'Nonnegative upper-bound factors')
    return float(up(a*b))


def norm(a):
    """Upper Euclidean norm; the reduction order is immaterial."""
    a = np.asarray(a)
    require(np.isfinite(a).all(), 'Finite coefficient array')
    square = up(up(a.real*a.real)+up(a.imag*a.imag))
    count = square.size
    require(count*U < .01, 'Norm reduction has an explicit gamma bound')
    total = up(up(float(np.sum(square)))/down(1-count*U))
    return float(up(np.sqrt(total)))


def vector_sizes(a):
    square = up(up(a.real*a.real)+up(a.imag*a.imag))
    total = np.zeros(a.shape[:-1])
    for j in range(a.shape[-1]):
        total = up(total+square[..., j])
    return up(np.sqrt(total))


def total_upper(a):
    require(np.all(a >= 0) and a.size*U < .01, 'Nonnegative finite sum')
    return float(up(up(float(np.sum(a)))/down(1-a.size*U)))


def exp_upper(x):
    """Upper exp without a libm transcendental accuracy premise, |x|<=1."""
    require(abs(x) <= 1, 'Subdivide the scalar step before exponentiation')
    if x < 0:
        term, value = 1., 1.
        for j in range(1, 25):
            term = max(0., float(down(down(term*(-x))/j)))
            value = float(down(value+term))
        return float(up(1/value))
    term, value = 1., 1.
    for j in range(1, 25):
        term = float(up(up(term*x)/j))
        value = add(value, term)
    # Successive omitted terms have ratio <= x/26.
    first = float(up(up(term*x)/25))
    tail = float(up(first/down(1-up(x/26))))
    return add(value, tail)


def arctan_interval(inverse, terms=90):
    x = Q(1, inverse)
    value = sum((-1)**j*x**(2*j+1)/(2*j+1) for j in range(terms))
    next_term = (-1)**terms*x**(2*terms+1)/(2*terms+1)
    return min(value, value+next_term), max(value, value+next_term)


def twiddles(n):
    """Certify binary64 twiddles against exact rational Taylor bounds.

    Machin's identity and alternating arctangent sums enclose pi. For
    0<=angle<pi, degree-64/65 Taylor remainders and |sin'|,|cos'|<=1
    enclose the exact trigonometric values. Every stored real and imaginary
    component differs from its exact value by less than 2^-53.
    """
    alo, ahi = arctan_interval(5)
    blo, bhi = arctan_interval(239)
    pi_lo, pi_hi = 16*alo-4*bhi, 16*ahi-4*blo
    scale = 2**180
    pi_lo = Q((pi_lo*scale).__floor__(), scale)
    pi_hi = Q((pi_hi*scale).__ceil__(), scale)
    result = []
    for k in range(n//2):
        angle = Q(2*k, n)*(pi_lo+pi_hi)/2
        radius = Q(k, n)*(pi_hi-pi_lo)
        c, cs, s, ss = Q(1), Q(1), angle, angle
        for j in range(1, 33):
            c *= -angle*angle/Q((2*j-1)*(2*j))
            s *= -angle*angle/Q((2*j)*(2*j+1))
            cs += c
            ss += s
        cr = abs(c*angle*angle/Q(65*66))+radius
        sr = abs(s*angle*angle/Q(66*67))+radius
        real, imag = float(cs), -float(ss)
        require(abs(Q(real)-cs)+cr < Q(1, 2**53)
                and abs(Q(imag)+ss)+sr < Q(1, 2**53),
                'Exact rational twiddle enclosure')
        result.append(complex(real, imag))
    return np.array(result)


class EnclosedFFT:
    """Known butterfly sequence, with a global Euclidean error radius.

    A stage differs from its exact butterfly by <=16u times its exact
    norm amplification (sqrt(2)); stored twiddles have error <2u.
    With L=3 log2(n), (1+16u)^L-1 <=64Lu. Subnormal absolute
    errors are covered separately. Normalization is an exact power of two.
    Norms on physical grids use normalized counting measure.
    """
    def __init__(self, n):
        require(n >= 2 and n & (n-1) == 0, 'Radix-two transform grid')
        self.n, self.volume = n, n**3
        bits = n.bit_length()-1
        self.reverse = np.array([int(f'{i:0{bits}b}'[::-1], 2) for i in range(n)])
        self.roots = twiddles(n)
        self.gamma = 64*(3*bits)*U
        require(self.gamma < .01, 'The butterfly error product has the stated linear upper bound')
        self.sqrt_volume = float(up(np.sqrt(self.volume)))

    def transform(self, value, inverse=False):
        a = np.array(value, dtype=complex, copy=True)
        for axis in range(3):
            a = np.moveaxis(a, axis, 0)[self.reverse].copy()
            for width in (2**j for j in range(1, self.n.bit_length())):
                half = width//2
                blocks = a.reshape((self.n//width, width)+a.shape[1:])
                left, right = blocks[:, :half].copy(), blocks[:, half:].copy()
                w = self.roots[::self.n//width].reshape((1, half)+(1,)*(a.ndim-1))
                wi = -w.imag if inverse else w.imag
                # Spell out the operations used in the roundoff proof.
                real = w.real*right.real-wi*right.imag
                imag = w.real*right.imag+wi*right.real
                blocks[:, :half].real = left.real+real
                blocks[:, :half].imag = left.imag+imag
                blocks[:, half:].real = left.real-real
                blocks[:, half:].imag = left.imag-imag
            a = np.moveaxis(a, 0, axis)
        if not inverse:
            a /= self.volume
        require(np.isfinite(a).all(), 'No transform overflow')
        return a

    def physical(self, coefficients, radius=0.):
        value = self.transform(coefficients, inverse=True)
        error = add(radius, add(mul(self.gamma, norm(coefficients)), 1.e-290))
        return value.real, error

    def fourier(self, value, radius=0.):
        result = self.transform(value)
        input_norm = float(up(norm(value)/down(np.sqrt(self.volume))))
        error = add(radius, add(mul(self.gamma, input_norm), 1.e-290))
        return result, error


def project(a, K, k2):
    """Approximate exact orthogonal projection, plus its l2 error."""
    inv = np.divide(1., k2, out=np.zeros_like(k2, dtype=float), where=k2 != 0)
    result = a-K*inv[..., None]*np.sum(K*a, axis=-1)[..., None]
    return result, add(mul(64*U, norm(a)), 1.e-290)


def reconstruct(raw, K, k2):
    """Exact target is P H(raw), not the rounded returned midpoint."""
    n = raw.shape[0]
    negative = (-np.arange(n)) % n
    partner = raw[np.ix_(negative, negative, negative)].conjugate()
    hermitian = (raw+partner)/2
    hermitian[0, 0, 0] = 0
    midpoint, error = project(hermitian, K, k2)
    return midpoint, add(error, add(mul(4*U, norm(raw)), 1.e-290))


def elevation(old, new):
    return [[Q(comb(old, j)*comb(new-old, k-j), comb(new, k))
             if 0 <= k-j <= new-old else Q(0)
             for j in range(old+1)] for k in range(new+1)]


def combine(values, radii, weights):
    answer = np.zeros_like(values[0])
    radius = 0.
    for v, r, q in zip(values, radii, weights):
        if not q:
            continue
        scale = float(q)
        answer += scale*v
        magnitude = float(up(abs(scale)))
        radius = add(radius, mul(magnitude, r))
        # Includes rational-to-binary conversion, complex scaling, addition.
        radius = add(radius, mul(8*U, add(norm(answer), mul(magnitude, norm(v)))))
    return answer, radius


def bernstein(y0, y1, f0, f1, j0, j1, h):
    return [y0, y0+h*f0/5, y0+2*h*f0/5+h*h*j0/20,
            y1-2*h*f1/5+h*h*j1/20, y1-h*f1/5, y1]


def frequency_grid(n):
    ks = np.arange(n)
    ks[ks >= n//2] -= n
    return np.stack(np.meshgrid(ks, ks, ks, indexing='ij'), axis=-1)


def weighted_norm(a, k2, order):
    sizes = vector_sizes(a)
    weights = k2**order
    require(np.isfinite(weights).all(), 'Finite exact integer norm weights')
    return float(up(np.sqrt(total_upper(up(weights*up(sizes*sizes))))))


def wiener(a, k2, order):
    weight = up(np.sqrt(k2)) if order == 1 else k2
    return total_upper(up(weight*vector_sizes(a)))


def grid_eigenvalue_upper(matrix):
    """Certify a numerical eigenvalue proposal using Sylvester's criterion.

    All matrix entries are treated as exact stored dyadics at this step.
    Positive principal minors of lambda I - matrix imply lambda exceeds
    every eigenvalue. A failed test only increases the candidate padding.
    """
    proposal = float(np.max(np.linalg.eigvalsh(matrix)[..., -1]))
    padding = 2.**-40*max(1., norm(matrix)/np.sqrt(matrix.size))
    for _ in range(20):
        bound = add(proposal, padding)
        a = down(bound-matrix[..., 0, 0])
        b = down(bound-matrix[..., 1, 1])
        c = down(bound-matrix[..., 2, 2])
        x, y, z = -matrix[..., 0, 1], -matrix[..., 0, 2], -matrix[..., 1, 2]
        # Certify the matrix with lowered diagonal a,b,c. Adding back a
        # nonnegative diagonal preserves positive definiteness.
        ab = down(down(a*b)-up(x*x))
        ac = down(down(a*c)-up(y*y))
        bc = down(down(b*c)-up(z*z))
        xyz = x*y
        xyz_lo, xyz_hi = down(xyz), up(xyz)
        mixed = np.minimum(down(xyz_lo*z), down(xyz_hi*z))
        determinant = down(down(down(down(down(a*b)*c)+down(2*mixed))
                                -up(a*up(z*z)))-up(b*up(y*y)))
        determinant = down(determinant-up(c*up(x*x)))
        if np.all(a > 0) and np.all(b > 0) and np.all(c > 0) \
                and np.all(ab > 0) and np.all(ac > 0) and np.all(bc > 0) \
                and np.all(determinant > 0):
            return bound
        padding *= 2
    raise ArithmeticError('Eigenvalue upper proposal did not pass the exact-sign test')


class SlabVerifier:
    def __init__(self, n, nu):
        self.n, self.nu = n, nu
        self.K = frequency_grid(n)
        self.k2 = np.sum(self.K*self.K, axis=-1)
        self.fft = EnclosedFFT(2*n)
        self.largeK = frequency_grid(2*n)
        self.largek2 = np.sum(self.largeK*self.largeK, axis=-1)
        self.kmax = float(up(np.sqrt(float(self.k2.max()))))
        self.large_kmax = float(up(np.sqrt(float(self.largek2.max()))))
        self.w1_error = float(up(np.sqrt(total_upper(self.k2))))
        self.w2_error = float(up(np.sqrt(total_upper(self.k2**2))))
        self.elev4, self.elev5 = elevation(4, 10), elevation(5, 10)

    def enlarge(self, a):
        p = self.n//2
        return np.fft.ifftshift(np.pad(np.fft.fftshift(a, axes=(0, 1, 2)),
            ((p, p), (p, p), (p, p), (0, 0))), axes=(0, 1, 2))

    def norms(self, a, radius):
        return dict(H1=add(weighted_norm(a, self.k2, 1), mul(self.kmax, radius)),
                    C=add(wiener(a, self.k2, 1), mul(self.w1_error, radius)),
                    D=add(wiener(a, self.k2, 2), mul(self.w2_error, radius)))

    def compression(self, a, radius, D):
        gradients, errors = [], []
        for j in range(3):
            coeff = 1j*self.K[..., j, None]*a
            err = add(mul(self.kmax, radius), mul(8*U*self.kmax, norm(a)))
            value, err = self.fft.physical(self.enlarge(coeff), err)
            gradients.append(value)
            errors.append(err)
        matrix = np.stack(gradients, axis=-1)
        strain = -(matrix+matrix.swapaxes(-1, -2))/2
        # Frobenius error dominates the operator error. The sum of column
        # l2 radii bounds their Euclidean combination; grid l-infinity costs
        # sqrt(number of nodes). Symmetrization is an operator contraction.
        error = mul(self.fft.sqrt_volume, sum_upper(errors))
        error = add(error, mul(8*U, norm(matrix)))
        bound = add(grid_eigenvalue_upper(strain), error)
        # sqrt(3)<7/4, pi<22/7 give a rational spatial margin 11D/(4M).
        margin = mul(11/(4*self.fft.n), D)
        return add(bound, margin)

    def slab(self, raw, h):
        require(h > 0 and self.nu > 0, 'Positive physical time and viscosity')
        require(len(raw) == 6, 'Six complete shared Bernstein control points')
        # Arrays use normalized Fourier coefficients, with no modes outside
        # the retained box. Full products fit strictly inside the doubled box.
        for a in raw:
            outside = np.any(abs(self.K) >= self.n/3, axis=-1)
            require(np.all(a[outside] == 0), 'Exact support excludes aliasing and Nyquist ambiguity')
        pairs = [reconstruct(a, self.K, self.k2) for a in raw]
        coeff = [a for a, _ in pairs]
        radii = [r for _, r in pairs]
        sizes = [self.norms(a, r) for a, r in pairs]
        D = max(q['D'] for q in sizes)
        S0 = self.compression(coeff[0], radii[0], sizes[0]['D'])
        changes = []
        for a, r in pairs[1:]:
            diff = a-coeff[0]
            error = add(add(r, radii[0]), mul(4*U, add(norm(a), norm(coeff[0]))))
            changes.append(self.norms(diff, error)['C']/2)
        S = min(max(q['C'] for q in sizes)/2, add(S0, max(changes)))

        # Rotational form uses the same velocity/curl pairs throughout:
        # P(v.grad v) = -P(v cross curl(v)). No generated mode is discarded.
        physical, curls = [], []
        for a, r in pairs:
            value, err = self.fft.physical(self.enlarge(a), r)
            physical.append((value, err))
            ch = 1j*np.cross(self.K, a)
            cr = add(mul(self.kmax, r), mul(16*U*self.kmax, norm(a)))
            curls.append(self.fft.physical(self.enlarge(ch), cr))

        derivatives, derivative_errors, heat, heat_errors = [], [], [], []
        for j in range(5):
            q = Q(5)/Q(h)
            derivative, err = combine([coeff[j+1], coeff[j]], [radii[j+1], radii[j]], [q, -q])
            derivatives.append(derivative)
            derivative_errors.append(err)
        for a, r in pairs:
            value = self.nu*self.k2[..., None]*a
            factor = float(up(self.nu*self.k2.max()))
            error = add(mul(factor, r), mul(8*U, mul(factor, norm(a))))
            heat.append(value)
            heat_errors.append(error)

        eps0, eps1, arithmetic = 0., 0., 0.
        for k in range(11):
            products, product_errors, weights = [], [], []
            for i in range(6):
                j = k-i
                if not 0 <= j <= 5:
                    continue
                a, ar = physical[i]
                b, br = curls[j]
                product = np.cross(a, b)
                amax, bmax = float(vector_sizes(a).max()), float(vector_sizes(b).max())
                error = add(mul(amax, br), mul(bmax, ar))
                error = add(error, mul(self.fft.sqrt_volume, mul(ar, br)))
                error = add(error, mul(16*U, mul(amax, float(up(norm(b)/down(np.sqrt(self.fft.volume)))))))
                products.append(product)
                product_errors.append(error)
                weights.append(Q(comb(5, i)*comb(5, j), comb(10, k)))
            # combine's array-roundoff norm is unnormalized; convert its
            # radius by using correspondingly unnormalized input radii.
            product, pr = combine(products, [mul(self.fft.sqrt_volume, r) for r in product_errors], weights)
            pr = float(up(pr/down(np.sqrt(self.fft.volume))))
            nonlinear, nr = self.fft.fourier(product, pr)
            nonlinear, projection_error = project(nonlinear, self.largeK, self.largek2)
            nr = add(nr, projection_error)
            tangent, tr = combine(derivatives, derivative_errors, self.elev4[k])
            diffusion, dr = combine(heat, heat_errors, self.elev5[k])
            midpoint = self.enlarge(tangent+diffusion)-nonlinear
            radius = add(add(tr, dr), nr)
            radius = add(radius, mul(8*U, sum_upper([norm(tangent), norm(diffusion), norm(nonlinear)])))
            eps0 = max(eps0, add(norm(midpoint), radius))
            eps1 = max(eps1, add(weighted_norm(midpoint, self.largek2, 1), mul(self.large_kmax, radius)))
            arithmetic = max(arithmetic, mul(self.large_kmax, radius))
        return dict(S=S, D=D, epsilon0=eps0, epsilon1=eps1,
                    H1_arithmetic_radius=arithmetic, final_H1=sizes[-1]['H1'],
                    reference_H1=max(q['H1'] for q in sizes))


def sum_upper(values):
    result = 0.
    for v in values:
        result = add(result, v)
    return result


def control_step(X, Y, row, h, nu):
    """Outward supersolution on one slab, carrying both endpoint errors.

    Freeze the nonlinearity at a proposed upper B and check the resulting
    linear integral stays strictly below B. A first-exit argument validates
    this bootstrap. The exponential forcing integral is bounded by
    h*exp(max(rate,0)*h). Negative rates still give endpoint decay.
    """
    a, b = float(up(row['S']-nu)), float(up(2*row['S']-nu/2))
    eh_a = exp_upper(float(up(a*h)))
    forcing_a = mul(h, exp_upper(max(0., float(up(a*h)))))
    Xend = add(mul(X, eh_a), mul(row['epsilon0'], forcing_a))
    Xmax = max(X, Xend)
    eh_b = exp_upper(float(up(b*h)))
    forcing_b = mul(h, exp_upper(max(0., float(up(b*h)))))
    # pi<22/7. Every operation in kappa is rounded upward.
    cup = float(up(26*float(up(22/7))))
    kappa = float(up(mul(27, mul(cup, cup))/down(32*down(down(nu*nu)*nu))))
    source = add(mul(row['D'], Xmax), row['epsilon1'])
    linear = add(mul(Y, eh_b), mul(source, forcing_b))
    B = add(mul(1.01, max(Y, linear)), 2.**-90)
    for _ in range(40):
        power = B
        for _ in range(4):
            power = mul(power, B)
        Yend = add(mul(Y, eh_b), mul(add(source, mul(kappa, power)), forcing_b))
        if max(Y, Yend) < B:
            return dict(X=Xend, Y=Yend, Xmax=Xmax, Ymax=B)
        B = add(mul(1.01, max(B, Yend)), 2.**-90)
        require(np.isfinite(B) and B < 1, 'Gradient bootstrap failed before its diagnostic ceiling')
    raise ArithmeticError('Finite-slab scalar supersolution did not close')


def summarize(records, h, nu, initial_error=0.):
    """Consume accepted slabs without inferring bounds from time samples."""
    require(records and nu == .25, 'This fixed tail consumer uses viscosity 1/4')
    require(initial_error >= 0, 'A nonnegative original H1 perturbation radius')
    X, Y = initial_error, initial_error
    error_integral, reference_integral, Emax, maximum_error = 0., 0., 0., initial_error
    cup = float(up(26*float(up(22/7))))
    kappa = float(up(mul(27, mul(cup, cup))/down(32*down(down(nu*nu)*nu))))
    for index, row in enumerate(records):
        require(Q(row['end_time']) == (index+1)*Q(h), 'The scalar record covers every consecutive slab')
        verified = control_step(X, Y, row, h, nu)
        if initial_error == 0:
            require(all(verified[k] == row[k] for k in verified), 'Independent scalar replay uses identical carried endpoints')
        X, Y = verified['X'], verified['Y']
        x, y = verified['Xmax'], verified['Ymax']
        maximum_error = max(maximum_error, y)
        sixth = 1.
        for _ in range(6):
            sixth = mul(sixth, y)
        rhs = sum_upper([mul(4, mul(row['S'], mul(y, y))),
                         mul(2, mul(row['D'], mul(x, y))),
                         mul(2, mul(kappa, sixth)), mul(2, mul(row['epsilon1'], y))])
        error_integral = add(error_integral, mul(h, rhs))
        # D is a deliberately coarse but certified upper bound for ||Delta v||2.
        reference_integral = add(reference_integral, mul(h, mul(row['D'], row['D'])))
        H1 = add(row['reference_H1'], y)
        Emax = max(Emax, mul(H1, H1))
    seam = add(records[-1]['final_H1'], Y)
    require(seam <= 1/64, 'The actual gradient enclosure reaches the fixed tail tolerance')
    tail_dissipation = float(up(5/3584))
    error_payment = add(mul(initial_error, initial_error), error_integral)
    L = sum_upper([mul(2, reference_integral), float(up(mul(2, error_payment)/nu)), tail_dissipation])
    K = ceil(add(Emax, mul(nu, L)))
    return dict(actual_H1_at_seam=seam, maximum_gradient_error=maximum_error,
                initial_H1_perturbation_radius=initial_error,
                gradient_energy_upper=Emax, full_dissipation_upper=L,
                signed_renewal_allowance_constant=K,
                signed_renewal_allowance='K0 (centre) or K0+2H|g(u0)| (perturbed datum)',
                tail_dissipation_upper='5/3584', tail_critical_velocity_integral_upper='65/448',
                scope='Original cyclic datum and the stated H1 ball; normalized period-2pi torus; analytic/computational, not Lean-certified')


def generated_mode_fixture():
    """Independent Gaussian-rational NS residual with outputs outside the box."""
    import pressure_history_source as algebra
    from cyclic_pressure_history import velocity_time_jets
    datum = [{}, {}, {}]
    for k, polarization in [((3, 0, 0), (0, 1, 0)), ((3, 2, 0), (2, -3, 0))]:
        for j, a in enumerate(polarization):
            if a:
                datum[j][k] = -algebra.II*Q(a, 2)
                datum[j][tuple(-x for x in k)] = algebra.II*Q(a, 2)
    jets, _ = velocity_time_jets(datum, Q(1, 4), 1)
    squares = [Q(0), Q(0)]
    tail = Q(0)
    for component in jets[1]:
        for k, a in component.items():
            square = Q(str(a.x*a.x+a.y*a.y))
            k2 = sum(x*x for x in k)
            squares[0] += square
            squares[1] += k2*square
            if max(map(abs, k)) >= Q(16, 3):
                tail += k2*square
    require(tail > 0, 'The independent exact residual genuinely leaves the retained box')
    raw = np.zeros((16, 16, 16, 3), complex)
    for j, component in enumerate(datum):
        for k, a in component.items():
            raw[tuple(x % 16 for x in k)+(j,)] = complex(float(a.x), float(a.y))
    row = SlabVerifier(16, .25).slab([raw]*6, 1/32)
    for j, key in enumerate(('epsilon0', 'epsilon1')):
        gap = Q(row[key])**2-squares[j]
        require(0 <= gap < squares[j]/10**7,
                'Full interval residual encloses the independently computed exact rational norm')
    return dict(exact_residual_L2_squared=str(squares[0]),
                exact_residual_H1_squared=str(squares[1]),
                exact_discarded_H1_squared=str(tail),
                enclosed_L2=row['epsilon0'], enclosed_H1=row['epsilon1'])


def exact_checks():
    import sympy as s
    arithmetic_check()
    t = s.symbols('t')
    for old, new in [(4, 10), (5, 10)]:
        table = elevation(old, new)
        for j in range(old+1):
            require(s.expand(sum(s.Rational(table[k][j].numerator, table[k][j].denominator)
                                 *comb(new, k)*t**k*(1-t)**(new-k) for k in range(new+1))
                             -comb(old, j)*t**j*(1-t)**(old-j)) == 0,
                    'Exact Bernstein degree elevation')
    alo, ahi = arctan_interval(5)
    blo, bhi = arctan_interval(239)
    require(3 < 16*alo-4*bhi < 16*ahi-4*blo < Q(22, 7),
            'Exact rational pi bounds used in the physical constants')
    nu, k = s.symbols('nu k', positive=True)
    amplitude, clock = 4*nu*k, 4*nu*k*k
    require(s.expand(amplitude*clock-amplitude**2*k) == 0
            and s.expand(amplitude*clock/4-nu*amplitude*k*k) == 0,
            'Space-time dilation preserves the full unforced equation')
    payment_scale = 16*nu**2*k**4
    require(s.simplify((amplitude*k)**3/clock-payment_scale) == 0
            and s.simplify(nu*(amplitude*k*k)**2/clock-payment_scale/4) == 0,
            'The signed cubic budget and viscosity payment have identical scaling')
    # The independent DFT fixture has only rational fourth roots of unity.
    fft = EnclosedFFT(4)
    rng = np.random.default_rng(9821)
    a = rng.integers(-10, 11, (4, 4, 4, 2)).astype(complex)/16
    exact = np.zeros_like(a)
    roots = (1, -1j, -1, 1j)
    for k in np.ndindex((4, 4, 4)):
        for j in np.ndindex((4, 4, 4)):
            exact[k] += roots[sum(x*y for x, y in zip(k, j)) % 4]*a[j]/64
    observed, radius = fft.fourier(a)
    error = norm(observed-exact)
    require(error <= radius, 'Radix-two result encloses the exact rational DFT')
    back, back_radius = fft.physical(observed, radius)
    require(norm(back-a.real)/8 <= back_radius, 'Inverse DFT enclosure')
    # A second exact fixture exercises every stage of the actual 64^3 FFT.
    # Multiples-of-16 frequencies have rational fourth roots on that grid.
    large_fft = EnclosedFFT(64)
    sparse = np.zeros((64, 64, 64, 1), complex)
    sparse[16, 0, 0, 0], sparse[-16, 0, 0, 0] = -.25j, .25j
    sparse[0, 32, 0, 0], sparse[0, 0, 0, 0] = .125, .5
    exact_large = np.zeros_like(sparse.real)
    sine = np.array([0., 1., 0., -1.])[np.arange(64) % 4]
    parity = (-1.)**np.arange(64)
    exact_large[..., 0] = .5+.5*sine[:, None, None]+.125*parity[None, :, None]
    computed_large, large_radius = large_fft.physical(sparse)
    require(norm(computed_large-exact_large)/512 <= large_radius,
            'Actual-size radix-two transform encloses an exact rational trigonometric fixture')
    symmetric = rng.integers(-10, 11, (9, 3, 3)).astype(float)/16
    symmetric = (symmetric+symmetric.swapaxes(-1, -2))/2
    upper = Q(grid_eigenvalue_upper(symmetric))
    for m in symmetric:
        a, b, c = (upper-Q(m[j, j]) for j in range(3))
        x, y, z = -Q(m[0, 1]), -Q(m[0, 2]), -Q(m[1, 2])
        require(a > 0 and a*b-x*x > 0 and a*b*c+2*x*y*z-a*z*z-b*y*y-c*x*x > 0,
                'Independent rational determinants confirm the eigenvalue bound')
    # Independent sufficient eigenvalue upper bounds for diagonal fixtures.
    diagonal = np.zeros((2, 3, 3))
    diagonal[0] = np.diag([-1., 0., 2.])
    diagonal[1] = np.diag([3., -2., 1.])
    require(3 < grid_eigenvalue_upper(diagonal) < 3+1.e-8,
            'Sylvester certificate encloses an exact diagonal spectrum')
    simple = dict(S=0., D=0., epsilon0=0., epsilon1=0.)
    controlled = control_step(.001, .001, simple, Q(1, 32).__float__(), .25)
    require(0 < controlled['X'] < .001 and 0 < controlled['Y'] < .001,
            'The scalar supersolution retains decay through a dissipative slab')
    # Exact rational Taylor bounds compare the scalar exponential routine.
    for q in [Q(-1), Q(-1, 7), Q(0), Q(1, 7), Q(1)]:
        x = float(q)
        rational_x = Q(x)
        lower = sum(rational_x**j/s.factorial(j) for j in range(81))
        # Sympy evaluates only exact rationals here. A uniform Lagrange
        # remainder is <3/81! on [-1,1].
        upper = lower+Q(3, int(s.factorial(81)))
        require(Q(exp_upper(x)) > upper, 'Outward exponential exceeds exact Taylor upper bound')
    return dict(status='exact algebra, twiddles and independent DFT fixtures passed',
                DFT_error=error, DFT_enclosure=radius,
                actual_size_DFT_error=norm(computed_large-exact_large)/512,
                actual_size_DFT_enclosure=large_radius,
                independent_full_residual=generated_mode_fixture(),
                scope='Arithmetic/physical fixtures only; this command does not check a full time prefix')


def run(n, nu, dt, h, final):
    arithmetic_check()
    require(n >= 16 and n & (n-1) == 0 and h > 0 and dt > 0 and final > 0,
            'Positive times and power-of-two retained grid')
    steps = round(h/dt)
    slabs = round(final/h)
    require(Q(steps)*Q(dt) == Q(h) and Q(slabs)*Q(h) == Q(final),
            'Exactly matching dyadic integration and verification seams')
    flow, verifier = VelocityFlow(n, nu), SlabVerifier(n, nu)
    state = flow.initial.copy()
    expected = np.zeros_like(state)
    for component, k in enumerate(((0, 1, 0), (0, 0, 1), (1, 0, 0))):
        expected[k+(component,)] = -.5j*n**3
        expected[tuple((-q) % n for q in k)+(component,)] = .5j*n**3
    require(np.array_equal(state, expected), 'The original datum is exactly (sin y, sin z, sin x)')
    X, Y = 0., 0.
    previous_endpoint = None
    records, digest = [], hashlib.sha256()
    start = time.time()
    for slab in range(slabs):
        old = state.copy()
        f0, j0 = flow.jets(old)
        for _ in range(steps):
            state, _ = flow.step(state, dt)
        f1, j1 = flow.jets(state)
        raw = [np.ascontiguousarray(a/n**3) for a in bernstein(old, state, f0, f1, j0, j1, h)]
        require(previous_endpoint is None or np.array_equal(raw[0], previous_endpoint),
                'Adjacent slabs share the identical exact endpoint before projection')
        previous_endpoint = raw[-1].copy()
        for a in raw:
            digest.update(a.tobytes())
        row = verifier.slab(raw, h)
        control = control_step(X, Y, row, h, nu)
        X, Y = control['X'], control['Y']
        row.update(control)
        row['end_time'] = (slab+1)*h
        row['actual_H1_upper'] = add(row['final_H1'], Y)
        records.append(row)
        print(json.dumps(dict(slab=slab+1, total=slabs, elapsed=time.time()-start,
                              **row)), file=sys.stderr, flush=True)
    seam = records[-1]['actual_H1_upper']
    passes = nu == .25 and seam <= 1/64
    return dict(status='finite physical prefix enclosed; small-gradient handoff '+('passed' if passes else 'not reached'),
                arithmetic='explicit radix-two FFT, rational twiddle validation, outward norm/control bounds',
                scope='Analytic/computational certificate under the stated IEEE model; not Lean-certified',
                n=n, nu=nu, integration_step=dt, slab_length=h, final=final,
                curve_sha256=digest.hexdigest(), elapsed=time.time()-start,
                final_actual_H1_upper=seam, sufficient_threshold=1/64 if nu == .25 else None,
                tail_passes=passes, summary=summarize(records, h, nu) if passes else None,
                records=records)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prefix', action='store_true')
    parser.add_argument('--n', type=int, default=32)
    parser.add_argument('--nu', type=float, default=.25)
    parser.add_argument('--dt', type=float, default=1/512)
    parser.add_argument('--slab', type=float, default=1/32)
    parser.add_argument('--final', type=float, default=1/32)
    args = parser.parse_args()
    print(json.dumps(run(args.n, args.nu, args.dt, args.slab, args.final)
                     if args.prefix else exact_checks(), indent=2), flush=True)
