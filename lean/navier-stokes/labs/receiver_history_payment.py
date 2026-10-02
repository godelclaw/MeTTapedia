#!/usr/bin/env python3
"""Exact checks for source-square payment through a controlled refeeding history.

The periodic Sobolev estimates and the full-interval PDE application are
analytic in README.md. Finite fixtures retain generated mean motion,
pressure and all nonlinear outputs; they are not asserted trajectory states.
"""

import json
from fractions import Fraction as Q

import sympy as s
import pressure_history_source as f
from cellular_transfer_reversal import sqrt_upper
from receiver_source_square import (
    cubic, inner, minus_laplacian, nonlinear, oscillation, real_field,
    require, seed, storage_derivative, vector_add, vector_scale, vertical_mean,
)
from reciprocal_pattern_cycles import mode


def bessel_squared(u, order):
    weighted = [{k: (1+sum(j*j for j in k))**order*a for k, a in row.items()}
                for row in u]
    return inner(weighted, u)


def scalar_checks():
    n = s.symbols('n', integer=True, positive=True)
    require(s.expand((2*n+1)**3-(2*n-1)**3-(24*n*n+2)) == 0,
            'exact lattice shell cardinality')
    # Sum n^-p <= 1+1/(p-1), justified analytically by integral comparison.
    require(1+24*Q(4, 3)+2*Q(6, 5) < 6**2, 'H3 to supremum lattice bound')
    require(24*2+2*Q(4, 3) < 8**2, 'H3 to gradient supremum lattice bound')
    require(6+8+6 <= 32, 'one constant bounds the ordered H1 product')
    x, y, z = s.symbols('x y z', nonnegative=True)
    multi = sum(x**i*y**j*z**k for i in range(4) for j in range(4-i)
                for k in range(4-i-j))
    comparison = s.Poly(6*multi-(1+x+y+z)**3, x, y, z)
    require(all(a >= 0 for a in comparison.coeffs()),
            'Bessel H3 is at most sqrt(6), hence three, times the multi-index H3 norm')
    nu, C, W, H, E, Z = s.symbols('nu C W H E Z', positive=True)
    gamma = s.Rational(1, 100000000)
    require(s.expand(W*H+2*C*W**2*H/nu+C**2*W**3*H/nu**2
                     -W*H*(1+C*W/nu)**2) == 0,
            'all source-square derivative terms fit the complete bound')
    derivative = s.diff(gamma*E**3/nu**4, E)*(-2*nu*Z)
    require(s.simplify(derivative+6*gamma*E**2*Z/nu**3) == 0,
            'full unforced energy pays the cube with the actual viscosity power')
    require(Q(2, 100000000*243)*256**5 > 60,
            'parent amplitude at least 256nu pays the uniform receiver bound')
    require(Q(1, 2)+Q(2, 3)+Q(1, 4) == Q(17, 12),
            'original receiver norm gives the explicit initial allowance')
    require(Q(1, 2)-Q(1, 96*256) > Q(1, 3),
            'the same original perturbation cap retains the parent lower bound')
    require(8 < 3**2 and 4+Q(1, 32*256) < 5,
            'reference and full-field H3 envelopes fit the payment region')
    return {'embedding_constant': 32, 'bessel_to_multiindex_factor_upper': 3,
            'parent_amplitude_over_viscosity': 256, 'energy_cube_coefficient': str(gamma),
            'cycle_additional_conditions': ['3rho Ktheta(S)<=1', 'Delta<=nu/96',
                                            'A/nu>=max(256,2S)'],
            'original_perturbation_cap': 'Delta=sqrt(Y0)exp(M/2)',
            'clock_interval': '[0,S], including S=3/4 or prescribed finite N*P0',
            'scope': 'scalar algebra exact; lattice integral comparison and Sobolev/PDE estimates analytic'}


def full_source_checks():
    v = [mode((0, 1, 0), 1, True), mode((1, 0, 0), -1, True), {}]
    r = real_field(seed())
    generated = nonlinear(r)
    nu, C, gamma = Q(2, 7), Q(32), Q(1, 100000000)
    amplitude, epsilon = 256*nu, nu/Q(100000)
    rows = []
    for sign in (-1, 1):
        perturbation = vector_add(r, vector_scale(Q(sign, 10), generated))
        u = vector_add(vector_scale(amplitude, v), vector_scale(epsilon, perturbation))
        w = oscillation(u)
        require(any(vertical_mean(perturbation)), 'a genuinely generated mean remains in the datum')
        f.equal(f.trace(f.jac(u)), {}, 'complete datum is solenoidal')
        source = nonlinear(u)
        require(inner(u, source) == 0, 'full nonlinear work conserves energy')
        alpha = inner(u, v)
        E, Z = inner(u, u), inner(minus_laplacian(u), u)
        B, W = sqrt_upper(bessel_squared(u, 3)), sqrt_upper(bessel_squared(w, 3))
        require(alpha > amplitude/3, 'retained parent supplies a positive lower bound')
        require(E >= alpha**2 and Z >= alpha**2,
                'both resource lower bounds follow from the same parent observation')
        require(B <= 5*amplitude and C*W <= nu, 'full-data fixture satisfies the certified region')
        h = oscillation(source)
        H = sqrt_upper(bessel_squared(h, 1))
        require(H <= 3*C*B*W, 'full non-mean source includes all mean and receiver couplings')
        rhs = vector_add(h, vector_scale(-nu, minus_laplacian(w)))
        rate = storage_derivative(w, rhs, nu)+2*cubic(w)
        upper = 3*C*B*W**2*(1+C*W/nu)**2
        payment = 6*gamma*E**2*Z/nu**3
        require(rate <= upper <= 60*amplitude*nu**2 <= payment,
                'all complete rate terms are paid by the same full energy')
        rows.append({'phase': sign, 'alpha': str(alpha), 'complete_rate': str(rate),
                     'uniform_bound': str(upper), 'energy_cube_loss': str(payment),
                     'corrected_rate': str(rate-payment)})
    return rows


if __name__ == '__main__':
    print(json.dumps({'constants_and_identities': scalar_checks(),
                      'full_source_fixtures': full_source_checks()}, indent=2))
