#!/usr/bin/env python3
"""Phase-sensitive nonlinear return relative to a helical generation forecast.

The amplitude and viscosity identities are polynomial identities, not fitted
samples. Every generated Fourier mode and the Leray pressure projection is
retained. The positive-viscosity local PDE comparison is analytic in README.md.
"""

import json
from collections import defaultdict
from math import comb, isqrt
import sympy as sp
from helicity_renewal import (
    f, pm, Q, add, scale, cross, projection, eqv, velocity_time_jets, zero,
    parents, modes, coefficient, coefficient_inner, conjugate, sobolev_pair,
)


def minus_pair(v, w, power=1):
    """Real <Lambda^power P_minus v,P_minus w> for solenoidal real fields."""
    helicity = (sp.Rational(pm.mean(f.dot(v, f.curl(w)))) if power == 1
                else sobolev_pair(v, f.curl(w), power-1))
    return sp.expand((sobolev_pair(v, w, power)-helicity)/2)


def clean(p):
    return {key: v for key, v in p.items() if any(v)}


def padd(*ps):
    result = {}
    for p in ps:
        for key, v in p.items():
            result[key] = add(result.get(key, [{}, {}, {}]), v)
    return clean(result)


def pscale(a, p):
    return clean({key: scale(a, v) for key, v in p.items()})


def diffuse(p):
    # The three exponents count powers of the two amplitudes and viscosity.
    return clean({(a, b, n+1): [f.lap(c) for c in v]
                  for (a, b, n), v in p.items()})


def nonlinear(p, q):
    result = {}
    for key, v in p.items():
        for ell, w in q.items():
            degree = tuple(x+y for x, y in zip(key, ell))
            term = projection(cross(v, f.curl(w)))
            result[degree] = add(result.get(degree, [{}, {}, {}]), term)
    return clean(result)


def scalar_pair(p, q, power=1):
    result = defaultdict(lambda: sp.Integer(0))
    for key, v in p.items():
        for ell, w in q.items():
            degree = tuple(x+y for x, y in zip(key, ell))
            result[degree] += minus_pair(v, w, power)
    return {key: sp.expand(c) for key, c in result.items() if sp.expand(c) != 0}


def mass_derivative(jets, order, power=1):
    result = defaultdict(lambda: sp.Integer(0))
    for j in range(order+1):
        for key, c in scalar_pair(jets[j], jets[order-j], power).items():
            result[key] += comb(order, j)*c
    return {key: sp.expand(c) for key, c in result.items() if sp.expand(c) != 0}


def subtract_scalars(p, q):
    return {key: sp.expand(p.get(key, 0)-q.get(key, 0))
            for key in p.keys() | q.keys()
            if sp.expand(p.get(key, 0)-q.get(key, 0)) != 0}


def evaluate(p, a, b, nu):
    return add(*(scale(a**i*b**j*nu**n, v) for (i, j, n), v in p.items()))


def certified_interval(expr):
    """Rational enclosures of a rational linear combination of square roots."""
    lo = hi = sp.Integer(0)
    denominator = 10**8
    for term in sp.Add.make_args(sp.expand(expr)):
        c, root = term.as_coeff_Mul()
        if root == 1:
            lo += c
            hi += c
            continue
        if not (c.is_Rational and root.is_Pow and root.exp == sp.Rational(1, 2)
                and root.base.is_Integer and root.base > 0):
            raise ArithmeticError(('Unexpected radical', term))
        n = int(root.base)
        k = isqrt(n*denominator**2)
        lower, upper = sp.Rational(k, denominator), sp.Rational(k+1, denominator)
        if not (lower**2 <= n < upper**2):
            raise ArithmeticError('Invalid rational square-root enclosure')
        lo += c*(lower if c >= 0 else upper)
        hi += c*(upper if c >= 0 else lower)
    return lo, hi


def phased_parents(phase):
    base = parents('full')
    for j in range(3):
        for k in list(base[j]):
            if k == (0, 12, 16):
                base[j][k] *= phase/(-f.II)
            if k == (0, -12, -16):
                base[j][k] *= conjugate(phase/(-f.II))
    return base


def symbolic_family(phase, direction):
    base = phased_parents(phase)
    U = {(1, 0, 0): [{k: c for k, c in p.items() if sum(x*x for x in k) == 400}
                     for p in base],
         (0, 1, 0): [{k: c for k, c in p.items() if sum(x*x for x in k) == 225}
                     for p in base]}
    for key, v in U.items():
        speed = 20 if key[0] else 15
        eqv(f.curl(v), scale(speed, v), 'each original shell is positive Beltrami')
        if f.add(*(f.diff(v[j], j) for j in range(3))):
            raise ArithmeticError('Initial incompressibility')
        for k in modes(v):
            if coefficient(v, tuple(-x for x in k)) != [conjugate(c) for c in coefficient(v, k)]:
                raise ArithmeticError('Initial field must be real')
        if nonlinear({key: v}, {key: v}):
            raise ArithmeticError('One original shell alone has zero nonlinear source')
    if sp.Matrix(modes(base)).rank() != 3:
        raise ArithmeticError('The interacting fixture must span three dimensions')
    for v, E, M, D in ((U[1, 0, 0], 800, 16000, 6400000),
                        (U[0, 1, 0], 450, 6750, 1518750)):
        zero(sp.Rational(pm.mean(f.dot(v, v)))-E, 'phase-independent shell energy')
        zero(sobolev_pair(v, v)-M, 'phase-independent shell critical mass')
        zero(sobolev_pair(v, v, 3)-D, 'phase-independent shell critical dissipation')

    jets, heat, first = [U], [U], [{}]
    for n in range(3):
        jets.append(padd(diffuse(jets[n]), *(pscale(comb(n, j), nonlinear(jets[j], jets[n-j]))
                     for j in range(n+1))))
        first.append(padd(diffuse(first[n]), *(pscale(comb(n, j), nonlinear(heat[j], heat[n-j]))
                      for j in range(n+1))))
        heat.append(diffuse(heat[n]))

    # P_minus U=0, so the unknown fourth jet pairs to zero identically.
    # Thus the fourth mass derivative only needs physical jets through order 3.
    for n in range(4):
        for power in (1, 3):
            if subtract_scalars(mass_derivative(jets, n, power), mass_derivative(first, n, power)):
                raise ArithmeticError(('Mass or dissipation differs before order four', n, power))
    actual4 = defaultdict(lambda: sp.Integer(0))
    forecast4 = defaultdict(lambda: sp.Integer(0))
    for target, sequence in ((actual4, jets), (forecast4, first)):
        for j in (1, 2, 3):
            for key, c in scalar_pair(sequence[j], sequence[4-j]).items():
                target[key] += comb(4, j)*c
    difference = {key: sp.expand(c/24)
                  for key, c in subtract_scalars(actual4, forecast4).items()}
    if set(difference) != {(4, 2, 0), (2, 4, 0)}:
        raise ArithmeticError(('Unexpected amplitude or viscosity dependence', difference.keys()))
    rows = []
    for key, c in sorted(difference.items()):
        lo, hi = certified_interval(c)
        if not (hi < 0 if direction < 0 else lo > 0):
            raise ArithmeticError(('Claimed return sign', key, lo, hi))
        # Compact integer enclosures are convenient to reproduce in the derivation.
        lower_integer = int(sp.floor(lo/10**6))*10**6
        upper_integer = int(sp.ceiling(hi/10**6))*10**6
        if not lower_integer < lo <= hi < upper_integer:
            raise ArithmeticError('Strict enclosing integer bounds')
        rows.append(dict(amplitude_viscosity_degree=key, coefficient=str(c),
                         exact_interval=[str(lo), str(hi)],
                         enclosing_integers=[lower_integer, upper_integer],
                         approximate=float(c)))

    # Resolve the sign into the mixed first/third jet and the positive second-jet square.
    cubic = {key: v for key, v in jets[2].items() if key[2] == 0}
    quartic = {key: v for key, v in jets[3].items() if key[2] == 0}
    born = nonlinear(U, U)
    mixed = scalar_pair(born, quartic)
    square = scalar_pair(cubic, cubic)
    contributions = []
    for key in sorted(set(mixed) | set(square)):
        x, y = sp.expand(mixed.get(key, 0)/3), sp.expand(square.get(key, 0)/4)
        zero(x+y-difference.get(key, 0), 'complete return includes both terms')
        if x != 0 or y != 0:
            if not certified_interval(y)[0] > 0:
                raise ArithmeticError('Complete return retains the positive new square')
            if not certified_interval(x)[1] < 0:
                raise ArithmeticError('Both mixed returns must have the favorable sign')
            contributions.append(dict(degree=key, mixed=str(x), square=str(y),
                                      mixed_approx=float(x), square_approx=float(y)))
    return U, jets, heat, first, difference, rows, contributions


def independent_physical_checks(U, symbolic_jets, first, difference):
    rows = []
    for a, b, nu in ((Q(1), Q(1), Q(1)), (Q(2), Q(1), Q(3, 2)),
                     (Q(1), Q(-2), Q(2)), (Q(0), Q(1), Q(1))):
        u = evaluate(U, a, b, nu)
        jets, pressures = velocity_time_jets(u, nu, 3)
        for n in range(4):
            eqv(jets[n], evaluate(symbolic_jets[n], a, b, nu),
                'independent advective NS recurrence retains canonical pressure and all modes')
        if 2*pm.mean(f.dot(u, jets[1])) != -2*f.QQ_I(nu).x*pm.mean(f.dot(f.curl(u), f.curl(u))):
            raise ArithmeticError('Actual full energy law')
        r = [evaluate(p, a, b, nu) for p in first]
        c = sp.expand((8*minus_pair(jets[1], jets[3])+6*minus_pair(jets[2], jets[2])
                        -8*minus_pair(r[1], r[3])-6*minus_pair(r[2], r[2]))/24)
        expected = sum(sp.Rational(a)**i*sp.Rational(b)**j*sp.Rational(nu)**n*v
                       for (i, j, n), v in difference.items())
        zero(c-expected, 'physical fourth-order comparison')
        rows.append(dict(amplitudes=[str(a), str(b)], viscosity=str(nu),
                         jet_modes=[len(modes(v)) for v in jets],
                         pressure_modes=[len(p) for p in pressures], coefficient=str(c)))
    return rows


def main():
    positive_phase, negative_phase = phased_parents(f.II), phased_parents(-f.II)
    if modes(positive_phase) != modes(negative_phase):
        raise ArithmeticError('The two phases must have the same initial support')
    for k in modes(positive_phase):
        v, w = coefficient(positive_phase, k), coefficient(negative_phase, k)
        if coefficient_inner(v, v) != coefficient_inner(w, w):
            raise ArithmeticError('The full initial modal energy spectra must agree')
    p, q, rp, rq = (12, 0, 16), (-12, 0, 9), (0, 12, 16), (0, -12, 9)
    if any(p[j]+q[j]-rp[j]-rq[j] for j in range(3)):
        raise ArithmeticError('Quartet phase must be translation invariant')
    families = []
    for phase, direction in ((-f.II, -1), (f.II, 1)):
        U, jets, heat, first, difference, rows, contributions = symbolic_family(phase, direction)
        checks = independent_physical_checks(U, jets, first, difference)
        source = evaluate(nonlinear(U, U), Q(1), Q(1), Q(0))
        birth = minus_pair(source, source)
        if not certified_interval(birth)[0] > 0:
            raise ArithmeticError('Both actual negative sectors initially grow')
        families.append(dict(rotated_parent_phase=str(phase), return_direction=direction,
            polynomial_coefficients=rows, complete_return_contributions=contributions,
            first_negative_generation=str(birth), independent_NS_checks=checks))
    print(json.dumps(dict(status='all exact checks passed', families=families,
        comparison='M_minus(actual)-M_minus(first Picard)=a^2 b^2 (c42 a^2+c24 b^2)t^4+O(t^5)',
        production_comparison='J(actual)-<Lambda P_minus r1,P_minus N(heat U)>=2 C(U)t^3+O(t^4)',
        scope='opposite strict local comparisons for every fixed real a,b with ab!=0 and positive viscosity',
        limitation='later returns, arbitrary histories and a uniform continuation allowance remain open',
        certification='exact symbolic polynomial identities and rational root enclosures; no new Lean theorem'), indent=2))


if __name__ == '__main__':
    main()
