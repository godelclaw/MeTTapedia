#!/usr/bin/env python3
"""Full cyclic pressure returns and certified weighted entropy derivatives.

All Fourier products and weighted-series enclosures are exact. The uniform
positive-viscosity interval argument is analytic in README.md, not Lean-certified.
"""

import functools
import json
import math
from fractions import Fraction as Rational

import sympy as sp
from cyclic_pressure_history import time_jets
from finite_band_renewal import f, pm, Q, zero


def rational(x):
    return Rational(str(x))


def observation_coefficients(field):
    """Orbit averages for a weight depending only on sum_j sin(x_j)^2."""
    out = {}
    for k, a in field.items():
        if any(j % 2 for j in k):
            continue
        orbit = tuple(sorted(abs(j)//2 for j in k))
        out[orbit] = out.get(orbit, Rational(0))+rational(a.x)
    return {k: a for k, a in out.items() if a}


def norm_bound(field):
    return sum((abs(rational(a.x))+abs(rational(a.y)) for a in field.values()), Rational(0))


@functools.lru_cache(None)
def centered_moments(orbit, order):
    """Exact <(e0-3/4)^n exp(i k.x)> for the original cyclic datum.

    e0-3/4=-(cos(2x)+cos(2y)+cos(2z))/4. Exponential generating
    functions keep every multinomial coefficient in the three independent
    coordinate integrals. Odd k were removed by the exact symmetry above.
    """
    series = [Rational(1)]+[Rational(0)]*order
    for m in orbit:
        coordinate = [Rational(math.comb(n, (n+m)//2), 2**n*math.factorial(n))
                      if n >= m and (n+m) % 2 == 0 else Rational(0)
                      for n in range(order+1)]
        series = [sum((series[j]*coordinate[n-j] for j in range(n+1)), Rational(0))
                  for n in range(order+1)]
    return tuple(v*math.factorial(n)*Rational(-1, 4)**n for n, v in enumerate(series))


def weighted_bound(field, alpha, order=32):
    """Enclose <field (1+(e0-3/4)/(7/4))^alpha> using rational tails."""
    center = Rational(7, 4)
    moments = [Rational(0)]*(order+1)
    for orbit, coefficient in observation_coefficients(field).items():
        for n, value in enumerate(centered_moments(orbit, order)):
            moments[n] += coefficient*value
    binomial, value = Rational(1), Rational(0)
    for n in range(order+1):
        value += binomial*moments[n]/center**n
        binomial *= (alpha-n)/(n+1)
    rho = Rational(3, 7)
    # This dominates every subsequent absolute coefficient ratio.
    ratio = rho*(1+abs(alpha)/Rational(order+1))
    if not ratio < 1:
        raise ArithmeticError('Series remainder must be summable')
    tail = norm_bound(field)*abs(binomial)*rho**(order+1)/(1-ratio)
    return value-tail, value+tail


def fourth_groups(energy, pressure, tangent):
    _, e1, e2, e3, e4 = energy
    _, p1, p2, p3, p4 = pressure
    mul, add, scale = f.mul, f.add, f.scale
    e11 = mul(e1, e1)
    groups = [e4, add(scale(4, mul(e1, e3)), scale(3, mul(e2, e2))),
              scale(6, mul(e11, e2)), mul(e11, e11)]
    if tangent:
        groups[0] = add(groups[0], p4)
        groups[1] = add(groups[1], scale(4, mul(e3, p1)), scale(6, mul(e2, p2)), scale(4, mul(e1, p3)))
        groups[2] = add(groups[2], scale(12, mul(mul(e1, e2), p1)), scale(6, mul(e11, p2)))
        groups[3] = add(groups[3], scale(4, mul(mul(e11, e1), p1)))
    return groups


def fourth_bound(groups):
    lower, upper = Rational(0), Rational(0)
    factors = [Rational(3), Rational(3, 2), Rational(-3, 4), Rational(9, 8)]
    for j, field in enumerate(groups):
        lo, hi = weighted_bound(field, Rational(1, 2)-j)
        factor = factors[j]/Rational(7, 4)**j
        if factor < 0:
            lo, hi = hi, lo
        lower += factor*lo
        upper += factor*hi
    return lower, upper


def complete_return():
    jets, pressure = time_jets(1, 0, 5)
    energy = [f.scale(Q(1, 2), f.add(*(f.scale(math.comb(n, k), f.dot(jets[k], jets[n-k]))
                                     for k in range(n+1)))) for n in range(5)]
    if pressure[0]:
        raise ArithmeticError('The actual initial pressure must be zero')
    for n in range(5):
        for field in (energy[n], pressure[n]):
            if any((-1)**sum(k) != (-1)**n for k in field):
                raise ArithmeticError('Half-period translation must match Euler time reversal')
    if observation_coefficients(pressure[1]) or observation_coefficients(pressure[2]):
        raise ArithmeticError('Weighted first and second pressure jets must cancel by symmetry')
    if observation_coefficients(f.mul(energy[1], pressure[1])):
        raise ArithmeticError('Transport-pressure cross term must cancel with the joint weight retained')
    p1_square = pm.mean(f.mul(pressure[1], pressure[1]))
    if p1_square != Q(1, 2):
        raise ArithmeticError('Complete pressure variance')
    # Check moment machinery against direct Fourier multiplication.
    centered = f.add(energy[0], {(0, 0, 0): -f.QQ_I(3)/4})
    power = {(0, 0, 0): f.QQ_I(1)}
    for n in range(7):
        for orbit in ((0, 0, 0), (0, 0, 1), (0, 1, 1), (0, 0, 2)):
            coefficient = power.get(tuple(2*j for j in orbit), f.QQ_I(0))
            if rational(coefficient.x) != centered_moments(orbit, 6)[n] or coefficient.y:
                raise ArithmeticError('Independent centered Fourier moment check')
        power = f.mul(power, centered)

    velocity = fourth_bound(fourth_groups(energy, pressure, False))
    tangent = fourth_bound(fourth_groups(energy, pressure, True))
    if not Rational(-47, 100) < velocity[0] <= velocity[1] < Rational(-46, 100):
        raise ArithmeticError('Velocity entropy must have strictly depleting fourth return')
    if not Rational(9, 20) < tangent[0] <= tangent[1] < Rational(23, 50):
        raise ArithmeticError('Tangent pressure correction must have positive fourth return')
    # Both strict fourth-order margins exceed 4/5 in absolute value.
    if not Rational(7, 2)*Rational(9, 20)**2 > Rational(4, 5)**2:
        raise ArithmeticError('Positive return margin')
    if not Rational(7, 2)*Rational(46, 100)**2 > Rational(4, 5)**2:
        raise ArithmeticError('Negative return margin')
    return dict(pressure_variance='1/2', bernoulli_second_lower='3/(2*sqrt(5))',
        velocity_fourth_div_sqrt_seven_halves=['-47/100', '-46/100'],
        tangent_fourth_div_sqrt_seven_halves=['9/20', '23/50'],
        weighted_series_order=32, weighted_series_radius='3/7',
        pressure_mode_counts=[len(p) for p in pressure],
        scope='full Euler jets used only inside the analytic uniform positive-viscosity comparison')


def derivative_algebra():
    x, p = sp.symbols('x p', real=True)
    phi = 2*sp.sqrt(2)*x**sp.Rational(3, 2)
    tangent = phi+sp.diff(phi, x)*p
    # L(x)= -u.grad p -nu G, L(p)=H+u.grad p for constant h.
    advp, nu, G, H, xx, xp = sp.symbols('advp nu G H xx xp', real=True)
    actual = sp.diff(tangent, x)*(-advp-nu*G)+sp.diff(tangent, p)*(H+advp)
    actual -= nu*(sp.diff(tangent, x, 2)*xx+2*sp.diff(tangent, x, p)*xp)
    expected = sp.diff(phi, x)*H-p*sp.diff(phi, x, 2)*advp
    expected -= nu*(sp.diff(phi, x)+p*sp.diff(phi, x, 2))*G
    expected -= nu*(sp.diff(phi, x, 2)+p*sp.diff(phi, x, 3))*xx
    expected -= 2*nu*sp.diff(phi, x, 2)*xp
    zero(actual-expected, 'complete tangent entropy evolution retains mixed diffusion')
    # Independent formal differentiation verifies the fourth-order chain
    # formula for a basis spanning every scalar derivative that can occur.
    e = sp.symbols('e0:5')
    pjet = sp.symbols('p0:5')
    shift = sp.symbols('shift')
    for degree in range(5):
        F = x**degree
        expression = F.subs(x, e[0]+shift)+sp.diff(F, x).subs(x, e[0]+shift)*pjet[0]
        for _ in range(4):
            expression = sp.expand(sum(sp.diff(expression, e[j])*e[j+1]
                                       + sp.diff(expression, pjet[j])*pjet[j+1] for j in range(4)))
        groups = [e[4]+pjet[4],
            4*e[1]*e[3]+3*e[2]**2+4*e[3]*pjet[1]+6*e[2]*pjet[2]+4*e[1]*pjet[3],
            6*e[1]**2*e[2]+12*e[1]*e[2]*pjet[1]+6*e[1]**2*pjet[2],
            e[1]**4+4*e[1]**3*pjet[1]]
        formula = sum(sp.diff(F, x, j+1).subs(x, e[0]+shift)*groups[j] for j in range(4))
        zero(expression.subs(pjet[0], 0)-formula, 'independent fourth derivative chain and product rules')
    # The local comparison uses an a priori fifth-derivative bound, with
    # M*sigma<=1, and a viscosity comparison error <=sigma^4/240.
    if not Rational(4, 5)/24-Rational(1, 120) >= Rational(1, 60):
        raise ArithmeticError('Uniform Taylor margin')
    if not Rational(1, 60)-Rational(1, 240) == Rational(1, 80):
        raise ArithmeticError('Positive-viscosity comparison margin')
    return dict(tangent_coercivity='p>=-h/2 implies W>=integral |u|^3',
        retained_mixed_diffusion='-2nu integral Phi_second(e+h) grad e . grad p',
        conclusion='both pressure completions can grow while the velocity-only entropy is below its heat forecast',
        OPEN='an arbitrary-history payment of actual pressure-velocity work, without charging harmless pressure variance')


if __name__ == '__main__':
    print(json.dumps(dict(status='all exact checks passed', return_test=complete_return(),
        evolution=derivative_algebra(),
        certification='exact weighted enclosures; physical interval and inviscid comparison remain analytic'), indent=2))
