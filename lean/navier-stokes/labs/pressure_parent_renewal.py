#!/usr/bin/env python3
"""A depleting old pressure parent can generate a growing complete reserve.

Symbolic phase operators retain every Fourier output for all positive integer
frequencies. Actual viscous intervals and their quantifiers are analytic in
README.md. The calculation constructs no singular flow or truncated dynamics.
"""

import json
from itertools import product
from math import comb
from fractions import Fraction as Q

import sympy as s
import pressure_history_source as f
from cyclic_pressure_history import seed, velocity_time_jets
from retained_energy_alignment import product_jets, pressure_defect
from pressure_impulse_return import RING, NU, viscosity_jets


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def velocity_square_jets(velocity, order):
    return [f.add(*(f.scale(comb(n, j), f.dot(velocity[j], velocity[n-j]))
                    for j in range(n+1))) for n in range(order+1)]


def symbolic_frequency():
    domain = f.QQ_I.frac_field('k')
    k = domain.gens[0]

    # The third phase is k*z. Integer phase labels stay distinct, while
    # EVERY physical derivative and inverse Laplacian uses its actual k.
    def derivative(field, j):
        return f.clean({n: f.II*n[j]*(k if j == 2 else 1)*a
                        for n, a in field.items()})

    def advect(u, field):
        return f.add(*(f.mul(u[j], derivative(field, j)) for j in range(3)))

    def pressure(u, v):
        source = f.add(*(derivative(derivative(f.mul(u[i], v[j]), i), j)
                         for i in range(3) for j in range(3)))
        require(not source.get(f.ORIGIN, 0), 'Canonical pressure source has zero mean')
        return {n: a/(n[0]**2+n[1]**2+k*k*n[2]**2)
                for n, a in source.items() if n != f.ORIGIN}

    velocity = [[{n: domain.convert(a) for n, a in row.items()} for row in seed(1)]]
    pressures = []
    for n in range(4):
        p = f.add(*(f.scale(comb(n, j), pressure(velocity[j], velocity[n-j]))
                    for j in range(n+1)))
        pressures.append(p)
        tangent = [f.add(f.scale(-1, derivative(p, i)), *(
            f.scale(-comb(n, j), advect(velocity[j], velocity[n-j][i]))
            for j in range(n+1))) for i in range(3)]
        f.equal(f.add(*(derivative(tangent[i], i) for i in range(3))), {},
                'Complete symbolic-frequency Euler tangent is divergence free')
        velocity.append(tangent)

    def mean(field):
        return s.factor(domain.to_sympy(domain.convert(field.get(f.ORIGIN, 0))))

    e = velocity_square_jets(velocity, 4)
    f.equal(pressures[1], {n: -3*k/(4*(k*k+2)) for n in product((-1, 1), repeat=3)},
            'Literal first pressure derivative for the entire frequency family')
    J = [mean(a) for a in product_jets(e, e)]
    H = [mean(a) for a in product_jets(pressures[1:], pressures[1:])]
    generated = mean(f.mul(pressures[2], pressures[2]))
    old_return = mean(f.mul(pressures[1], pressures[3]))
    require(not (set(pressures[1]) & set(pressures[2])),
            'The first newly generated parent occupies distinct physical Fourier modes')
    require(mean(f.mul(pressures[1], pressures[2])) == 0,
            'The new parent is orthogonal to the original pressure-generating field')
    require(J[:4] == [s.Rational(21, 8), 0, 0, 0], 'Lower concentration returns vanish')
    require(H[1] == 0, 'The first pressure-parent energy return vanishes')
    require(s.factor(H[2]-2*(generated+old_return)) == 0,
            'The complete second return retains the newly generated square')

    # Check the entire symbolic velocity and pressure, not just the final
    # scalar signs, against the established rational physical recurrence.
    variable = domain.symbols[0]
    for scale in (4, 6, 8):
        initial = [{(n[0], n[1], scale*n[2]): a for n, a in row.items()}
                   for row in seed(1)]
        literal_v, literal_p = velocity_time_jets(initial, Q(0), 4)

        def specialize(field):
            result = {}
            for n, a in field.items():
                value = domain.to_sympy(domain.convert(a)).subs(variable, scale)
                real, imag = s.expand_complex(value).as_real_imag()
                result[(n[0], n[1], scale*n[2])] = f.QQ_I(real, imag)
            return f.clean(result)

        for actual, expected in zip(velocity, literal_v):
            for a, b in zip(actual, expected):
                f.equal(specialize(a), b, ('Independent physical velocity recurrence', scale))
        for a, b in zip(pressures, literal_p):
            f.equal(specialize(a), b, ('Independent physical pressure recurrence', scale))

    z, w = s.symbols('z w', nonnegative=True)
    PJ = 112*z**4-1158*z**3-6845*z**2-2259*z-200
    PH = 4*z**6-100*z**5-859*z**4-2370*z**3-3185*z**2-1508*z-82
    K = variable
    expected_J = 3*K**2*PJ.subs(z, K**2)/(5*(K**2+2)*(K**2+4)*(K**2+5)
                                           *(2*K**2+1)*(4*K**2+1))
    expected_H = 9*K**2*PH.subs(z, K**2)/(4*(K**2+2)**3*(K**2+5)**2*(2*K**2+1)**2)
    require(s.factor(J[4]-expected_J) == 0, 'Complete frequency law for concentration')
    require(s.factor(H[2]-expected_H) == 0, 'Complete frequency law for parent renewal')
    for polynomial, threshold in ((PJ, 16), (PH, 36)):
        require(all(c > 0 for c in s.Poly(polynomial.subs(z, w+threshold), w).all_coeffs()),
                'A positive shifted polynomial certifies the entire unbounded frequency range')
    require(all(PJ.subs(z, n*n) < 0 for n in (1, 2, 3)), 'Lower integer concentration signs')
    require(all(PH.subs(z, n*n) < 0 for n in (1, 2, 3, 4, 5)), 'Lower integer parent signs')
    for expression in (generated, -old_return):
        numerator, denominator = s.fraction(s.factor(expression))
        require(all(c >= 0 for c in s.Poly(numerator, K).all_coeffs())
                and all(c >= 0 for c in s.Poly(denominator, K).all_coeffs()),
                'Generated-square and old-direction depletion signs hold at every positive frequency')
    require(s.limit(generated, K, s.oo) == s.Rational(9, 2), 'Generated-square limit')
    require(s.limit(old_return, K, s.oo) == -s.Rational(27, 8), 'Old-direction return limit')
    require(s.limit(-old_return/generated, K, s.oo) == s.Rational(3, 4),
            'Old-direction depletion pays only three quarters of the generated square asymptotically')
    return dict(H=list(map(str, H)), J=list(map(str, J)),
                generated_square=str(generated), old_direction_return=str(old_return),
                parent_mode_counts=[len(p) for p in pressures[1:3]],
                original_direction='L2 projection onto the initial scalar pressure-generating field',
                parent_positive_for='every integer k>=6',
                concentration_positive_for='every integer k>=4',
                limiting_paid_fraction='3/4')


def viscous_fixture():
    k = 6
    initial = [{(n[0], n[1], k*n[2]): a for n, a in row.items()} for row in seed(1)]
    velocity, p = viscosity_jets(initial, 4)
    # Original retained energy, with C(0)=0, evolved without resetting it.
    e = [f.dot(initial, initial)]
    for n in range(4):
        e.append(f.add(f.scale(NU, f.lap(e[n])), *(
            f.scale(-comb(n, j), f.add(f.adv(velocity[j], e[n-j]),
                                      f.scale(2, f.adv(velocity[j], p[n-j]))))
            for j in range(n+1))))
    h = [f.add(p[j+1], f.scale(-NU, f.lap(p[j]))) for j in range(3)]
    f.equal(h[0], pressure_defect(initial, p[0], NU), 'Independent complete pressure-source formula')
    mean = lambda a: RING.to_sympy(RING.convert(a.get(f.ORIGIN, f.ZERO)))
    J = [s.expand(mean(a)) for a in product_jets(e, e)]
    H = [s.expand(mean(a)) for a in product_jets(h, h)]
    nu = RING.symbols[0]
    d = s.Rational(44670072375, 245773032364)
    require(J[0] == s.Rational(21, 8) and J[1] == -38*nu, 'Original concentration and viscous loss')
    require(H[0] == s.Rational(81, 722) and H[1] == -s.Rational(162, 19)*nu,
            'Original pressure-parent resource and viscous loss')
    require(H[2] == 648*nu**2+d, 'New parent growth retains the full viscosity polynomial')
    q = f.add(p[2], f.scale(-2*NU, f.lap(p[1])), f.scale(NU*NU, f.lap(f.lap(p[0]))))
    diffusion = mean(f.dot(f.grad(h[0]), f.grad(h[0])))
    require(s.expand(H[1]+2*nu*diffusion-2*mean(f.mul(h[0], q))) == 0,
            'The actual generating-parent balance has no inserted forcing')
    return dict(k=k, J=list(map(str, J)), H=list(map(str, H)),
                scope='Full polynomial viscosity dependence, independently specialized at 2/7')


if __name__ == '__main__':
    print(json.dumps(dict(status='all exact checks passed',
        family=symbolic_frequency(), viscosity=viscous_fixture(),
        failed_claim='J+alpha||h||_2^2 is a universal nonincreasing reserve, even with datum-dependent alpha>=0',
        scope='Actual simultaneous positive-viscosity value/rate obstruction is analytic in README.md',
        open='A larger original-data allowance or a signed joint-history reserve; no singularity is constructed'), indent=2))
