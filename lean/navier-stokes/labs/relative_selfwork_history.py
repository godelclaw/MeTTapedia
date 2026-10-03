#!/usr/bin/env python3
"""Signed self-interaction of an actual NS difference and its shear payment.

Checks full amplitude/viscosity jet polynomials, a rational Bessel enclosure,
the positive-viscosity comparison constants and the Fourier commutator.
The physical interval and all-history arguments are analytic in README.md.
"""

import json
from collections import defaultdict
from math import comb, factorial
import sympy as sp
from helicity_renewal import (
    f, pm, Q, add, scale, cross, projection, eqv, velocity_time_jets,
    zero, conjugate, coefficient, coefficient_inner, modes, sobolev_pair,
)
from helical_second_return import padd, pscale, nonlinear, certified_interval


def initial(A, B, C, D):
    """(A sin y+C cos z, D sin z, B cos x)."""
    u = [{}, {}, {}]
    for k, v in [((0, 1, 0), [-f.II*A, 0, 0]),
                 ((1, 0, 0), [0, 0, B]),
                 ((0, 0, 1), [C, -f.II*D, 0])]:
        for j in range(3):
            a = f.QQ_I.convert(v[j])/2
            u[j][k] = a
            u[j][tuple(-x for x in k)] = conjugate(a)
    return [f.clean(p) for p in u]


def diffuse(p):
    return {(*key[:-1], key[-1]+1): [f.lap(c) for c in v]
            for key, v in p.items()}


def evaluate(p, values):
    return add(*(scale(Q(sp.prod(x**n for x, n in zip(values, key))), v)
                 for key, v in p.items()))


def pair(v, w, power):
    # Expand rather than simplify each intermediate radical expression.
    weight = lambda k: (abs(k[1]) if power == 'y' else
                        sp.Integer(sum(x*x for x in k))**sp.Rational(power, 2))
    return sp.expand(sum(weight(k)
        *sp.Rational(coefficient_inner(coefficient(v, k), coefficient(w, k)))
        for k in set(modes(v)) & set(modes(w))))


def work_coefficient(d, source, order, power):
    result = defaultdict(lambda: sp.Integer(0))
    for n in range(order+1):
        for key, v in d[n].items():
            for ell, w in source[order-n].items():
                degree = tuple(x+y for x, y in zip(key, ell))
                result[degree] += pair(v, w, power)
    return {k: sp.expand(c) for k, c in result.items() if sp.expand(c) != 0}


def polynomial_return():
    # Exponents are A,B,C,D,nu. Retain the entire polynomial, not samples.
    base = {}
    for j in range(4):
        values = [Q(int(i == j)) for i in range(4)]
        key = tuple(int(i == j) for i in range(5))
        base[key] = initial(*values)
    jets = [base]
    for n in range(3):
        jets.append(padd(diffuse(jets[n]), *(pscale(comb(n, j),
            nonlinear(jets[j], jets[n-j])) for j in range(n+1))))
    # Setting C=D=0 gives the actual reference, including its later modes.
    d = [pscale(Q(1, factorial(n)), {key: v for key, v in p.items()
         if key[2] or key[3]}) for n, p in enumerate(jets)]
    source = [padd(*(nonlinear(d[j], d[n-j]) for j in range(n+1)))
              for n in range(4)]
    coefficients = {}
    for power in (0, 1, 2, 4, 6):
        for order in range(4):
            actual = work_coefficient(d, source, order, power)
            c = sp.expand((2+sp.Integer(5)**sp.Rational(power, 2)
                           -3*sp.Integer(2)**sp.Rational(power, 2))/32)
            expected = ({(2, 0, 0, 4, 0): c, (0, 2, 2, 2, 0): c}
                        if order == 3 and c != 0 else {})
            if actual != expected:
                raise ArithmeticError(('Full self-work polynomial', power, order, actual))
        coefficients[power] = c
    h3 = sp.expand(sum(comb(3, j)*coefficients[2*j] for j in range(4)))
    zero(h3-sp.Rational(151, 32), 'complete Fourier H3 work coefficient')
    lo, hi = certified_interval(32*coefficients[1])
    if not hi < 0:
        raise ArithmeticError('Initial critical self-work must be strictly negative')
    checks = []
    for values in [(Q(1), Q(2), Q(1), Q(-1), Q(3, 2)),
                   (Q(2), Q(0), Q(3), Q(3), Q(1)),
                   (Q(1), Q(1), Q(2), Q(0), Q(2))]:
        A, B, C, D, nu = values
        u = initial(A, B, C, D)
        physical, pressure = velocity_time_jets(u, nu, 3)
        reference, _ = velocity_time_jets(initial(A, B, Q(0), Q(0)), nu, 3)
        for n in range(4):
            eqv(physical[n], evaluate(jets[n], values), 'independent advective NS jets')
            eqv(scale(Q(1, factorial(n)), add(physical[n], scale(-1, reference[n]))),
                evaluate(d[n], values), 'difference retains the actual evolving reference')
        zero(sp.Rational(2*pm.mean(f.dot(u, physical[1])))
             +2*sp.Rational(nu)*sobolev_pair(u, u, 2), 'full unforced energy identity')
        if B and D and not any(pressure):
            raise ArithmeticError('Coupled history must retain nonzero pressure')
        if not B and any(pressure):
            raise ArithmeticError('Exact triangular subclass has zero pressure')
        checks.append(dict(parameters=list(map(str, values)),
            jet_modes=[len(modes(v)) for v in physical],
            pressure_modes=[len(p) for p in pressure]))
    h = initial(Q(0), Q(0), Q(1), Q(1))
    eqv(f.curl(h), scale(-1, h), 'equal-polarization perturbation is Beltrami')
    eqv(projection(cross(h, f.curl(h))), [{}, {}, {}], 'initial self-source vanishes')
    born = nonlinear(base, base)
    born_derivative = padd(nonlinear(jets[1], base), nonlinear(base, jets[1]))
    if work_coefficient(jets, [born], 0, 'y'):
        raise ArithmeticError('Initial directional work must vanish')
    if work_coefficient(jets, [born, born_derivative], 1, 'y') != {
            (2, 2, 0, 0, 0): sp.Rational(1, 4)}:
        raise ArithmeticError('Exact regenerated directional resource')
    return dict(factor='A^2 D^4+B^2 C^2 D^2',
        cubic_coefficients={str(p): str(c) for p, c in coefficients.items()},
        H3_coefficient=str(h3), critical_radical_interval=list(map(str, (lo, hi))),
        independent_checks=checks, directional_parent_work='W_y(t)=A^2 B^2 t/4+O(t^2)')


def bessel_bounds(n):
    # J_n(2)=sum_j (-1)^j/(j!(n+j)!), with decreasing terms.
    even = sum(sp.Rational((-1)**j, factorial(j)*factorial(n+j)) for j in range(13))
    odd = even-sp.Rational(1, factorial(13)*factorial(n+13))
    if not 0 < odd < even < 1:
        raise ArithmeticError(('Bessel enclosure positivity', n))
    return odd, even


def later_sign():
    J = [bessel_bounds(n) for n in range(8)]
    # First pair is negative; all remaining pairs at sigma=2 are positive.
    delta = [certified_interval(sp.sqrt(1+(n+1)**2)-sp.sqrt(1+n*n))
             for n in range(7)]
    lower = -delta[0][1]*(1-J[0][0])*J[1][1]/2
    upper_finite = -delta[0][0]*(1-J[0][1])*J[1][0]/2
    for n in range(1, 7):
        if not delta[n][0] > 0:
            raise ArithmeticError('Increasing critical frequency weight')
        lower += delta[n][0]*J[n][0]*J[n+1][0]/2
        upper_finite += delta[n][1]*J[n][1]*J[n+1][1]/2
    # For n>=1: 0<n/(n+1)!<=J_n(2)<=1/n!; omitted pairs positive.
    # Tail begins n=7 and successive factorial products have ratio <=1/72.
    tail = sp.Rational(1, 2*factorial(7)*factorial(8))*sp.Rational(72, 71)
    upper = upper_finite+tail
    if not sp.Rational(1, 100) < lower < upper < sp.Rational(3, 200):
        raise ArithmeticError('Strict later positive self-work enclosure')
    # Match the infinite-series normalization with the independent PDE jets.
    s = sp.Symbol('s')
    j = lambda n: sum((-1)**k*(s/2)**(n+2*k)
                     / (sp.factorial(k)*sp.factorial(n+k)) for k in range(3))
    expr = -(sp.sqrt(2)-1)*(1-j(0))*j(1)/2
    expr += (sp.sqrt(5)-sp.sqrt(2))*j(1)*j(2)/2
    zero(sp.expand(expr).coeff(s, 3)-(2+sp.sqrt(5)-3*sp.sqrt(2))/32,
         'Bessel history and complete NS jet normalization agree')
    # Positive-viscosity comparison in H1 on 0<=sigma<=2.
    if not (7**2+7**2+24**2 < 26**2 and 1+1+3**2 < 4**2):
        raise ArithmeticError('Explicit derivative bounds')
    zero(sp.Integer(26)+2*4-34, 'forcing <=34mu')
    zero(sp.Integer(136)+2-138, 'difference of the heat-subtracted histories')
    zero(sp.Integer(9)*138-1242, 'bilinear work continuity bound')
    mu = sp.Rational(1, 250000)
    if not (138*mu <= 1 and sp.Rational(1, 100)-1242*mu > sp.Rational(1, 200)):
        raise ArithmeticError('Strict positive-viscosity margin')
    return dict(inviscid_comparison_exact_interval=[str(lower), str(upper)],
        readable_interval=['1/100', '3/200'], mu_upper=str(mu),
        actual_positive_viscosity_work_lower='F_mu(2)>1/200',
        actual_time='2/D', condition='D>=250000nu>0',
        scope='series and error constants checked; PDE comparison analytic')


def commutator_and_payment():
    # Verify the adjacent-mode commutator formula against full real fields.
    rows = []
    for m in (1, 2, 5):
        r = {}
        for n, a in [(-3, Q(1, 3)), (-2, Q(-2, 5)), (0, Q(3, 2)), (1, Q(1, 7))]:
            k = (0, m, n)
            z = f.QQ_I.convert(a*(1+f.II))
            r[k] = z
            r[tuple(-x for x in k)] = conjugate(z)
        sinz = initial(Q(0), Q(0), Q(0), Q(1))[1]
        v = [r, sinz, {}]
        full = sobolev_pair(v, projection(cross(v, f.curl(v))))
        scalar = -sobolev_pair([r, {}, {}], [f.mul(sinz, f.diff(r, 1)), {}, {}])
        zero(full-scalar, 'full projected self-work equals scalar transport pairing')
        adjacent = sp.Integer(0)
        weighted_energy = sp.Integer(0)
        for k, a in r.items():
            _, ky, kz = k
            b = r.get((0, ky, kz+1), f.ZERO)
            w0, w1 = sp.sqrt(ky*ky+kz*kz), sp.sqrt(ky*ky+(kz+1)**2)
            adjacent -= sp.Rational(ky, 2)*(w1-w0)*sp.Rational((conjugate(a)*b).x)
            weighted_energy += abs(ky)*sp.Rational((conjugate(a)*a).x)
        zero(full-adjacent, 'all signed adjacent-mode interactions retained')
        if not certified_interval(weighted_energy/2-full)[0] > 0:
            raise ArithmeticError('Commutator bound on positive work')
        if not certified_interval(weighted_energy/2+full)[0] > 0:
            raise ArithmeticError('Commutator bound on negative work')
        rows.append(dict(y_frequency=m, self_work=str(full), bound=str(weighted_energy/2)))
    D, nu, K0, t = sp.symbols('D nu K0 t', positive=True)
    bound = 2*D*K0*sp.exp(-3*nu*t)
    allowance = 2*D*K0/(3*nu)
    zero(sp.integrate(bound, (t, 0, sp.oo))-allowance, 'all-time absolute self-work payment')
    reserve = allowance*sp.exp(-3*nu*t)
    zero(sp.diff(reserve, t)+bound, 'one decreasing reserve, no resets')
    return dict(exact_commutator_fixtures=rows, allowance=str(allowance),
        initial_resource='K0=|| |partial_y|^(1/2) w0 ||_2^2',
        scope='arbitrary smooth passive profiles in the stated triangular class; analytic PDE estimate')


if __name__ == '__main__':
    print(json.dumps(dict(status='all exact checks passed',
        full_polynomial=polynomial_return(), later_history=later_sign(),
        absolute_payment=commutator_and_payment(),
        limitation='cross work and arbitrary mutually amplifying parents remain uncontrolled',
        certification='exact algebra and rational enclosures; no new Lean theorem'), indent=2))
