#!/usr/bin/env python3
"""Rational certificate that the generated mean seed couples to growth.

This checks finite Gaussian integrals and a spectral-residual inequality.
The operator argument concerns the inviscid linearization about a fixed
swirl, as explained in papers/ns_symmetry_defect.tex. It does not certify
amplification in the evolving nonlinear Navier--Stokes solution.
Only the Python standard library is required. Checks also run with -O.
"""
from fractions import Fraction as Q
from math import factorial
import json

COEFFICIENTS = [
    129288, -103710, 405, 2339, 11058, 4912, 3067, 42,
    -645, -1238, -1012, -844, -499, -285, -77, 28,
    104, 123, 128, 110, 91, 65, 46, 25, 14, 0,
    -3, -13, -8, -18, -6, -19,
]


def add(p, q):
    result = [Q(0)] * max(len(p), len(q))
    for j, v in enumerate(p):
        result[j] += v
    for j, v in enumerate(q):
        result[j] += v
    return result


def scale(p, c):
    return [c * v for v in p]


def multiply(p, q):
    result = [Q(0)] * (len(p) + len(q) - 1)
    for i, u in enumerate(p):
        for j, v in enumerate(q):
            result[i + j] += u * v
    return result


def shift(p, n=1):
    return [Q(0)] * n + p


def derivative(p):
    return [j * v for j, v in enumerate(p) if j]


def gaussian_integral(p, rate):
    """Integral_0^infinity p(a) exp(-rate*a) da, for positive rate."""
    if rate <= 0:
        raise ArithmeticError('nonpositive Gaussian rate')
    return sum(v * Q(factorial(j)) / rate ** (j + 1)
               for j, v in enumerate(p))


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


# f(r)=r exp(-r^2) P(r^2), in the angular-one radial form domain.
# P(a)=sum c_j L_j^1(2a)/100000. Construct every coefficient exactly.
P = [Q(0)]
for j, c in enumerate(COEFFICIENTS):
    laguerre = [Q((-1) ** k * factorial(j + 1) * 2 ** k,
                   factorial(j - k) * factorial(k + 1) * factorial(k))
                for k in range(j + 1)]
    P = add(P, scale(laguerre, Q(c, 100000)))

# L_1 f/[r exp(-a)]=4[aP''+(2-2a)P'+(a-2)P].
# A=I-L_1/4; Phi=16(1-a)exp(-2a); R=-Phi*f-mu*A*f.
LP = scale(add(add(shift(derivative(derivative(P))),
                   multiply([Q(2), Q(-2)], derivative(P))),
               multiply([Q(-2), Q(1)], P)), Q(4))
AP = add(P, scale(LP, Q(-1, 4)))
VP = scale(multiply([Q(1), Q(-1)], P), Q(-16))
mu = Q(21, 200)
rho = Q(1, 20)
residual_squared = (
    gaussian_integral(shift(multiply(VP, VP)), Q(6))
    + mu * mu * gaussian_integral(shift(multiply(AP, AP)), Q(2))
    - 2 * mu * gaussian_integral(shift(multiply(VP, AP)), Q(4))
) / 2
form_norm_squared = gaussian_integral(shift(multiply(P, AP)), Q(2)) / 2

# Independently compute the same form from f and its radial derivative.
# f'/exp(-a)=(1-2a)P+2aP'. Boundary terms vanish at zero and infinity.
DP = add(multiply([Q(1), Q(-2)], P), scale(shift(derivative(P)), Q(2)))
direct_form = (gaussian_integral(shift(multiply(P, P)), Q(2)) / 2
               + gaussian_integral(add(multiply(DP, DP), multiply(P, P)), Q(2)) / 8)
require(direct_form == form_norm_squared, 'radial form agrees with differential operator')

# The generated azimuthal coefficient is C_Gamma/r from the mixed-parent
# calculation. h=2Omega*C_theta=(32/5)r^3 Q4(r^2)exp(-4r^2).
Q4 = [Q(27), Q(-275), Q(346), Q(-110), Q(8)]
overlap = Q(16, 5) * gaussian_integral(shift(multiply(Q4, P), 2), Q(5))
source_norm_squared = Q(512, 25) * gaussian_integral(shift(multiply(Q4, Q4), 3), Q(8))
require(0 < form_norm_squared < Q(101, 100), 'form norm squared below 101/100')
require(overlap > Q(27, 100), 'source overlap above 27/100')
require(0 < source_norm_squared < 28, 'source norm squared below 28')
require(0 < residual_squared < Q(1, 160000), 'residual norm squared below 1/160000')

# Spectral projection estimate, using ||A^-1/2||<=1:
# ||h||<16/3, ||R||<1/400, ||A^1/2 f||<101/100.
# The part of A^1/2 f below rho is at most ||R||/(mu-rho).
require(mu - rho == Q(11, 200), 'positive spectral separation')
error_bound = Q(16, 3) * Q(1, 400) / (mu - rho)
require(error_bound == Q(8, 33), 'discarded spectral overlap bound')
require(Q(27, 100) - error_bound > Q(101, 100) * Q(1, 40),
        'spectral projection of A^-1/2 h has norm above 1/40')

print(json.dumps({
    'status': 'all exact rational checks passed',
    'laguerre_coefficients': len(COEFFICIENTS),
    'mu': str(mu), 'positive_spectral_threshold': str(rho),
    'form_norm_squared': '<101/100', 'source_overlap': '>27/100',
    'source_norm_squared': '<28', 'residual_norm_squared': '<1/160000',
    'positive_spectral_projection_norm': '>1/40',
    'scope': 'generated seed in the fixed inviscid linearization; nonlinear history remains open'
}, indent=2))
