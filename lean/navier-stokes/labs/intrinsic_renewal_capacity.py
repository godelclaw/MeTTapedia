#!/usr/bin/env python3
"""Exact nonlinear return of a reserve for latent pressure work.

Complete Fourier sources, pressure Hessians and receiver variations are
retained. The same-history positive-viscosity rebound and uniform local
remainder are analytic arguments in README.md, not Lean certificates.
"""

import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path

import sympy as s
import pressure_history_source as f
import heat_work_reserve as h
from heat_remainder_pressure import plus, times, require
from generated_fourth_moment import pressure, mixed_pressure, fourth_work
from heat_work_parent_payment import heat as rational_heat
from cyclic_pressure_history import velocity_time_jets


def zero(value, label):
    require(s.expand(value) == 0, label)


def pairing(v, w):
    value = sum((a*w[j].get(tuple(-i for i in k), f.ZERO)
                 for j in range(3) for k, a in v[j].items()), f.ZERO)
    result = s.expand(h.RING.to_sympy(h.RING.convert(value)))
    require(not result.has(s.I), 'The full Fourier pairing is real')
    return result


def receiver(v):
    magnitude = f.dot(v, v)
    return [f.mul(magnitude, row) for row in v]


def receiver_change(v, w):
    magnitude, cross = f.dot(v, v), f.dot(v, w)
    return [f.add(f.mul(magnitude, w[j]), f.scale(2, f.mul(cross, v[j])))
            for j in range(3)]


def work_variation(v, w):
    return -pairing(receiver_change(v, w), f.grad(pressure(v))) \
           -pairing(receiver(v), f.grad(mixed_pressure(v, w)))


def nonlinear_change(v, w):
    gradient = f.grad(mixed_pressure(v, w))
    result = [f.scale(-1, f.add(f.adv(v, w[j]), f.adv(w, v[j]), gradient[j]))
              for j in range(3)]
    f.equal(f.trace(f.jac(result)), {}, 'The full nonlinear variation is solenoidal')
    return result


def intrinsic_change(v, b):
    """D(DP4(v)[N(v)])[b], including both second and first variations."""
    c = h.nonlinear(v)
    ab, ac, bc = f.dot(v, b), f.dot(v, c), f.dot(b, c)
    second = [f.scale(2, f.add(f.mul(ac, b[j]), f.mul(ab, c[j]), f.mul(bc, v[j])))
              for j in range(3)]
    result = -pairing(second, f.grad(pressure(v)))
    result -= pairing(receiver_change(v, b), f.grad(mixed_pressure(v, c)))
    result -= pairing(receiver_change(v, c), f.grad(mixed_pressure(v, b)))
    result -= pairing(receiver(v), f.grad(mixed_pressure(b, c)))
    result += work_variation(v, nonlinear_change(v, b))
    return s.expand(result)


def independent_intrinsic_derivative(v, b):
    """Differentiate the earlier cotangent in the exact ring eps^2=0.

    Parameter truncation commutes with every polynomial operation used
    here. Spatial Fourier modes and their pressure multipliers are kept.
    The shared arithmetic is restored before the other checks run.
    """
    original_clean = f.clean

    def linear_clean(field):
        converted = {}
        for k, value in field.items():
            polynomial = h.RING.convert(value)
            converted[k] = h.RING.ring.from_dict(
                {powers: coefficient for powers, coefficient in polynomial.items() if powers[1] <= 1})
        return original_clean(converted)

    try:
        f.clean = linear_clean
        perturbed = plus(v, times(h.EPS, b))
        value = h.variation(perturbed, h.nonlinear(perturbed))
        return s.expand(value).coeff(h.eps, 1)
    finally:
        f.clean = original_clean


ELL = s.symbols('ell')


def window_integral(polynomial, weighted=False):
    """Heat integral through log(2); ell denotes log(2) exactly."""
    result = 0
    for (rate,), coefficient in s.Poly(s.expand(polynomial), h.q).terms():
        require(rate > 0, 'Every heat mode decays')
        weight = ((1-s.Rational(1, 2)**rate*(1+rate*ELL))/rate**2
                  if weighted else (1-s.Rational(1, 2)**rate)/rate)
        result += coefficient*weight
    return s.factor(result)


def log_bounds(expression):
    """Use 2/3 < log(2) < 25/36 from the positive artanh series."""
    value = s.Poly(s.expand(expression), ELL)
    require(value.degree() <= 1, 'Weighted heat integrals are affine in log(2)')
    a, b = value.nth(0), value.nth(1)
    left, right = s.Rational(2, 3), s.Rational(25, 36)
    return ((a+b*left, a+b*right) if b >= 0 else (a+b*right, a+b*left))


def positive_window(polynomial):
    """Exact Bernstein certificates on q in [1/2,1]."""
    x, t = s.symbols('x t')
    terms = s.Poly(s.expand(polynomial), h.q).terms()
    lowest = min(power[0] for power, _ in terms)
    require(all((power[0]-lowest) % 2 == 0 for power, _ in terms),
            'The normalized heat profile is polynomial in q squared')
    p = sum(co*x**((power[0]-lowest)//2) for power, co in terms)
    degree = s.degree(p, x)
    intervals = [(s.Rational(1, 4), s.Rational(1, 2)),
                 (s.Rational(1, 2), s.Rational(3, 4)), (s.Rational(3, 4), s.Integer(1))]
    rows = []
    for left, right in intervals:
        local = s.Poly(p.subs(x, left+(right-left)*t), t)
        coefficients = [sum(local.nth(k)*s.binomial(j, k)/s.binomial(degree, k)
                            for k in range(j+1)) for j in range(degree+1)]
        reconstruction = sum(coefficients[j]*s.binomial(degree, j)*t**j*(1-t)**(degree-j)
                             for j in range(degree+1))
        zero(reconstruction-local.as_expr(), 'The Bernstein certificate reconstructs the exact polynomial')
        require(min(coefficients) > 0, 'The positive-region selector is valid on the complete window')
        rows.append(dict(left=str(left), right=str(right), minimum=str(min(coefficients))))
    return dict(q_power=lowest, bernstein=rows)


def family_repair():
    m = s.symbols('m', real=True)
    base, dm, dp = m*m+3, m*m-2*m+3, m*m+2*m+3
    intrinsic = 3*m*m/(2*base*dm*dp)
    full = m*m*(7*m**4+38*m*m+63)/(4*base*dm*dp*(base-m)*(base+m))
    zero(s.cancel(s.Rational(40, 33)-full/intrinsic
         -(m*m-3)**2/(22*(m*m-m+3)*(m*m+m+3))),
         'The whole-age ratio is uniformly at most forty over thirty-three')
    zero(s.Rational(5, 4)-s.Rational(40, 33)-s.Rational(5, 132),
         'The correction has a strict uniform family margin')
    rows = []
    for shear in (1, 2, 4):
        u = h.weighted_datum(shear, (1, 1, 1))
        change = intrinsic_change(h.heat(u), h.heat(h.nonlinear(u)))
        zero(change, 'The first nonlinear renewal of the intrinsic capacity vanishes')
        shift = ((1-shear), 1, 1)
        for component in u:
            f.equal({k: value*(-1 if sum(i*j for i, j in zip(k, shift)) % 2 else 1)
                     for k, value in component.items()}, f.scale(-1, component),
                    'A torus translation reverses all original parents together')
        rows.append(dict(shear=shear, next_renewal='0'))
    return rows


def complete_return():
    u = h.weighted_datum(2, (1, 1, 1))
    parent_change = h.nonlinear(u)
    w = plus(u, times(h.EPS, parent_change))
    z = h.heat(w)
    intrinsic = work_variation(z, h.nonlinear(z))
    response = intrinsic_change(z, h.heat(h.nonlinear(w)))
    zero(intrinsic-intrinsic.subs(h.eps, -h.eps), 'Intrinsic work is even in the generated perturbation')
    zero(response+response.subs(h.eps, -h.eps), 'Its nonlinear renewal is odd in that perturbation')
    zero(intrinsic.subs(h.eps, 0)-4*h.q**14/11, 'The complete intrinsic base profile agrees with OC4')
    heat_change = intrinsic_change(z, h.heat([f.lap(row) for row in w]))
    zero(heat_change+h.q*s.diff(intrinsic, h.q), 'The complete second variation obeys the heat shift identity')

    # This is the derivative of the full nonlinear response along N(u),
    # not an evolution that freezes the first generated modes.
    linear = s.expand(response).coeff(h.eps, 1)
    return_coefficient = window_integral(linear, weighted=True)
    expected = (s.Rational(4932628376767351521482323, 1495818281370987131830272000)
                -s.Rational(37336469241033349, 725186626391881285632)*ELL)
    zero(return_coefficient-expected, 'Exact second Euler return of the stored intrinsic capacity')
    k_lower, k_upper = log_bounds(return_coefficient)
    require(k_lower > s.Rational(1, 400), 'The second return is strictly positive without decimal logarithms')
    gamma = window_integral(h.q**10*(11+16*h.q**4-3*h.q**8)/66)
    payment = window_integral(4*h.q**14/11)
    debt = s.factor(payment-s.Rational(4, 5)*gamma)
    require(debt == s.Rational(59139, 72089600) > 0, 'The corrected reserve initially decreases')
    margin = k_lower/2-debt
    require(margin > s.Rational(1, 1500), 'The next actual return outweighs the initial viscous loss at scaled time mu')

    fixed = plus(u, times(Q(1, 16), parent_change))
    intrinsic_fixed = s.expand(intrinsic.subs(h.eps, s.Rational(1, 16)))
    response_fixed = s.expand(response.subs(h.eps, s.Rational(1, 16)))
    heat_work = h.profile(h.heat(fixed))
    intrinsic_positive = positive_window(intrinsic_fixed)
    work_positive = positive_window(heat_work)
    fixed_renewal = window_integral(response_fixed, weighted=True)
    fixed_lower, _ = log_bounds(fixed_renewal)
    require(fixed_lower > s.Rational(1, 6000), 'A nearby complete field already has positive capacity renewal')

    # Independent first-order parameter expansion uses the earlier full
    # pressure cotangent rather than this file's pressure Hessian formula.
    rz = rational_heat(fixed, Q(3, 4))
    rb = rational_heat(h.nonlinear(fixed), Q(3, 4))
    independent = independent_intrinsic_derivative(rz, rb)
    zero(independent-response_fixed.subs(h.q, s.Rational(3, 4)),
         'Independent pressure-cotangent differentiation confirms the complete second variation')

    nu = Q(2, 7)
    physical = velocity_time_jets(fixed, nu, 1)[0][1]
    physical_change = intrinsic_change(h.heat(fixed), h.heat(physical))
    zero(physical_change-(response_fixed-s.Rational(2, 7)*h.q*s.diff(intrinsic_fixed, h.q)),
         'The actual positive-viscosity tangent includes the full diffusion and nonlinear change')
    viscous_window = window_integral(-h.q*s.diff(intrinsic_fixed, h.q), weighted=True)
    boundary = ELL*intrinsic_fixed.subs(h.q, s.Rational(1, 2))
    zero(viscous_window-boundary+window_integral(intrinsic_fixed),
         'Moving the heat window at viscous speed spends intrinsic work and cancels its boundary')

    # A finite explicit initial-state obstruction, in addition to the
    # analytic same-history rebound from the unperturbed original datum.
    full = h.variation(h.heat(fixed), h.heat(h.nonlinear(fixed)))
    gamma_fixed = window_integral(full)
    i_fixed = window_integral(intrinsic_fixed)
    diffusion = s.Rational(str(fourth_work(fixed)[1]))
    ratio = 128
    initial_margin = -diffusion+ratio**2*(gamma_fixed-s.Rational(5, 4)*i_fixed) \
                     +s.Rational(5, 4)*ratio**3*fixed_lower
    require(initial_margin > 0, 'Amplitude 128nu gives positive full corrected-reserve derivative')
    base_margin = -diffusion+256**2*gamma_fixed
    capacity_margin = 256**3*fixed_lower-256**2*i_fixed
    require(base_margin > 0 and capacity_margin > 0,
            'One amplitude 256nu defeats every nonnegative constant correction weight, including datum-selected weights')
    return dict(intrinsic_profile=str(s.factor(intrinsic)), nonlinear_profile=str(s.factor(response)),
                next_return_profile=str(s.factor(linear)), second_return=str(return_coefficient),
                second_return_bounds=list(map(str, (k_lower, k_upper))),
                initial_loss=str(debt), rebound_margin_lower=str(margin),
                nearby=dict(strength='1/16', intrinsic_positive=intrinsic_positive,
                    work_positive=work_positive, nonlinear_capacity_return=str(fixed_renewal),
                    return_lower=str(fixed_lower), amplitude_over_viscosity=ratio,
                    full_derivative_margin_lower=str(initial_margin),
                    all_weights_amplitude_over_viscosity=256,
                    all_weights_base_margin=str(base_margin),
                    all_weights_capacity_margin_lower=str(capacity_margin),
                    actual_tangent_viscosity=str(nu)))


def checks():
    # log(2)=2 sum_{j>=0}(1/3)^(2j+1)/(2j+1). Keep the
    # first term and bound each later denominator below by three.
    zero(s.Rational(2, 3)+s.Rational(2, 3)*s.Rational(1, 27)/(1-s.Rational(1, 9))
         -s.Rational(25, 36), 'Rational upper bound for the logarithmic heat window')
    result = dict(family=family_repair(), return_test=complete_return(),
                  scope='Exact full Fourier derivatives and rational sign certificates. Local NS rebound, uniform remainder and family interpretation are analytic, not Lean-certified.')
    root = Path(__file__).resolve().parent
    names = ['intrinsic_renewal_capacity.py', 'heat_work_reserve.py', 'heat_work_parent_payment.py',
             'pressure_history_source.py', 'heat_remainder_pressure.py', 'generated_fourth_moment.py',
             'cyclic_pressure_history.py', 'pressure_gradient_stock.py', 'pressure_quadratic_storage.py']
    result['source_sha256'] = {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in names}
    return result


if __name__ == '__main__':
    print(json.dumps(checks(), indent=2))
