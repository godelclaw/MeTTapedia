#!/usr/bin/env python3
"""Exact heat-work profiles and nonlinear replenishment of a fluid reserve.

All pressure and nonlinear outputs are retained. The heat parameter is
q=exp(-s); eps changes a fixed solenoidal datum, not the evolution equation.
The actual-solution and separated-frequency transfer arguments are analytic
in README.md. These checks are not Lean certificates or Galerkin evolution.
"""

import json
from fractions import Fraction as Q

import sympy as s
import pressure_history_source as f
from cyclic_pressure_history import velocity_time_jets
from generated_fourth_moment import pressure, mixed_pressure, fourth_work, target_field, vector_pair
from heat_remainder_pressure import plus, times, adv, solenoidal, projection, mean, require
from pressure_gradient_stock import weighted_datum
from pressure_quadratic_storage import mode


RING = f.QQ_I.poly_ring('q', 'eps')
HEAT, EPS = RING.gens
q, eps = s.symbols('q eps')


def heat(v):
    return [{k: RING.convert(a)*HEAT**sum(x*x for x in k) for k, a in row.items()}
            for row in v]


def average(a):
    value = s.expand(RING.to_sympy(RING.convert(a.get(f.ORIGIN, f.ZERO))))
    require(not value.has(s.I), 'The complete spatial integral is real')
    return value


def profile(a):
    return -average(f.mul(f.dot(a, a), f.adv(a, pressure(a))))


def variation(a, b):
    """Full canonical pressure variation, checked against its cotangent."""
    f.equal(f.trace(f.jac(b)), {}, 'The retained variation is solenoidal')
    magnitude, cross = f.dot(a, a), f.dot(a, b)
    receiver = [f.mul(magnitude, x) for x in a]
    receiver_change = [f.add(f.mul(magnitude, b[i]), f.scale(2, f.mul(cross, a[i])))
                       for i in range(3)]
    gradient = f.grad(pressure(a))
    gradient_change = f.grad(mixed_pressure(a, b))
    value = -average(f.add(f.dot(receiver_change, gradient), f.dot(receiver, gradient_change)))
    projected_receiver = projection(receiver)
    radial = f.dot(a, gradient)
    cotangent = [f.add(f.scale(-1, f.mul(magnitude, gradient[j])),
                      f.scale(-2, f.mul(radial, a[j])),
                      f.scale(2, f.add(*(f.mul(f.diff(a[i], j), projected_receiver[i])
                                         for i in range(3))))) for j in range(3)]
    require(s.expand(value-average(f.dot(cotangent, b))) == 0,
            'The cotangent retains both receiver and canonical-pressure variation')
    return value


def integrate(p, lower_square=0):
    """Integral over s with exp(-2s) ranging from lower_square to one."""
    result = 0
    for (rate, power), coefficient in s.Poly(s.expand(p), q, eps).terms():
        if not coefficient:
            continue
        require(rate > 0, 'Every retained heat profile decays')
        if lower_square:
            require(rate % 2 == 0, 'The finite positive-region endpoint has rational powers')
            factor = 1-lower_square**(rate//2)
        else:
            factor = 1
        result += coefficient*eps**power*factor/rate
    return s.factor(result)


def heat_shift(a):
    heated = heat(a)
    p = profile(heated)
    d = variation(heated, heat([f.lap(x) for x in a]))
    require(s.expand(d+q*s.diff(p, q)) == 0,
            'The complete heat direction is the semigroup shift derivative')
    require(s.expand(integrate(d)+p.subs(q, 1)) == 0,
            'The signed heat primitive spends the present signed work')
    return p


def nonlinear(a):
    return velocity_time_jets(a, Q(0), 1)[0][1]


def checks():
    initial = weighted_datum(2, (1, 1, 1))
    tangent = nonlinear(initial)
    require(heat_shift(initial) == 0, 'The original field has no heat-work capacity')
    g = variation(heat(initial), heat(tangent))
    expected = q**10*(11+16*q**4-3*q**8)/66
    certificate = q**10*(11+13*q**4+3*q**4*(1-q**4))/66
    require(s.expand(g-expected) == 0 and s.expand(g-certificate) == 0,
            'Nonlinear replenishment is strictly positive at every finite heat age')
    gamma = integrate(g)
    require(gamma == s.Rational(109, 3465), 'Exact original capacity-creation rate')
    work, diffusion, size = fourth_work(initial)
    require(work == 0 and diffusion == Q(217, 8) and size == Q(157, 8),
            'The initial fourth moment and full diffusion are fixed exactly')
    margin = 32**2*gamma-s.Rational(diffusion.numerator, diffusion.denominator)
    require(margin == s.Rational(141023, 27720) and margin > 0,
            'The complete nonnegative reserve increases at amplitude 32nu')

    actual = []
    for nu in (Q(1), Q(2, 7)):
        amplitude = 32*nu
        datum = times(amplitude, initial)
        physical = velocity_time_jets(datum, nu, 1)[0][1]
        physical_profile = variation(heat(datum), heat(physical))
        require(s.expand(physical_profile-amplitude**6*g) == 0,
                'The actual viscous tangent gives the complete positive-part right derivative')
        receiver = [f.mul(f.dot(datum, datum), x) for x in datum]
        y_rate = vector_pair(receiver, physical)
        require(y_rate == -nu*amplitude**4*diffusion,
                'Actual transport and pressure give the full initial moment rate')
        reserve_rate = integrate(physical_profile)/s.Rational(nu.numerator, nu.denominator)
        normalized = s.factor((reserve_rate+y_rate)/(nu*amplitude**4))
        require(normalized == margin, 'Independent positive-viscosity reserve derivative')
        energy_rate = 2*vector_pair(datum, physical)
        require(energy_rate == -11*nu*amplitude**2 < 0,
                'The same unforced flow loses kinetic energy while its proposed reserve increases')
        actual.append(dict(viscosity=str(nu), amplitude=str(amplitude), normalized_rate=str(normalized),
                           squared_L2_rate=str(energy_rate)))

    # The earlier adverse-work target has a favorable capacity return.
    target = target_field()
    target_profile = heat_shift(target)
    target_return = variation(heat(target), heat(nonlinear(target)))
    require(s.expand(target_profile-q**6*(275*q**2-224)/320) == 0,
            'The original target has one exact heat-work sign change')
    negative_certificate = -q**6*(
        1224914753*q**4+2466131463*q**4*(1-q**2)+70186545*q**2+1085610240)/3162931200
    require(s.expand(target_return-negative_certificate) == 0,
            'The earlier target depletes heat-work capacity at every heat age')
    target_reserve = integrate(target_profile, s.Rational(224, 275))
    target_gamma = integrate(target_return, s.Rational(224, 275))
    require(target_reserve > 0 > target_gamma, 'Positive stored capacity with negative nonlinear return')

    # Keep an entire interval of strictly positive-work, replenishing shapes.
    perturbed = plus(initial, times(EPS, tangent))
    F = heat_shift(perturbed)
    G = variation(heat(perturbed), heat(nonlinear(perturbed)))
    require(s.expand(F).coeff(eps, 0) == 0 and s.expand(F.coeff(eps, 1)-g) == 0,
            'The perturbation creates the certified leading heat-work profile')
    require(s.expand(G.coeff(eps, 0)-g) == 0, 'The replenishment starts from the same exact profile')
    loss = 0
    for (rate, power), coefficient in s.Poly(F-eps*g, q, eps).terms():
        if coefficient < 0:
            require(rate >= 10 and power >= 3, 'Every adverse correction is bounded by eps*q^10')
            loss += -coefficient*s.Rational(1, 4)**(power-1)
        elif coefficient:
            require(power >= 2 and rate > 0, 'All other corrections are favorable')
    profile_margin = s.factor(s.Rational(1, 6)-loss)
    require(profile_margin == s.Rational(7561789, 56770560) and profile_margin > 0,
            'F>=profile_margin*eps*q^10 for 0<eps<=1/4 and 0<q<=1')
    R, Gamma = integrate(F), integrate(G)
    lower = 0
    for (power,), coefficient in s.Poly(Gamma, eps).terms():
        if power == 0:
            lower += coefficient
        elif coefficient < 0:
            lower += coefficient*s.Rational(1, 4)**power
    require(lower > s.Rational(3, 100), 'Uniform strictly positive replenishment on the entire shape interval')

    # Exact source reconstruction for the separated-frequency transfer.
    W = plus(initial, times(Q(1, 4), tangent))
    direction, k0, n = (1, 2, 3), (2, -1, 0), 32
    h = f.add(mode(k0, (1, 0, 0), 1)[0], mode(tuple(2*x for x in k0), (1, 0, 0), 1)[0])
    receiver = []
    for row in W:
        coefficients = {}
        for k, a in row.items():
            pairing = sum(x*y for x, y in zip(direction, k))
            require(pairing != 0, 'Every target mode admits the retained inverse directional derivative')
            coefficients[tuple(n*x for x in k)] = f.II*a/(n*pairing)
        receiver.append(coefficients)
    shear = [f.scale(d, h) for d in direction]
    datum = plus(shear, receiver)
    fast = [{tuple(n*x for x in k): a for k, a in row.items()} for row in W]
    expected_source = solenoidal(plus([f.mul(h, x) for x in fast],
                                      times(-1, adv(receiver, shear)), times(-1, adv(receiver, receiver))))
    source = nonlinear(datum)
    for i in range(3):
        f.equal(f.adv(shear, shear[i]), {}, 'The original shear has no self-advection')
        f.equal(source[i], expected_source[i], 'The complete generated source reconstructs exactly')
    f.equal(f.trace(f.jac(datum)), {}, 'The original shear and receiver form a solenoidal datum')
    require(all(mean(x) == 0 for x in datum), 'No constant sweeping velocity supplies the geometry')
    next_source = nonlinear(source)
    slow_candidates = {tuple(j*x for x in k0) for j in range(-4, 5) if j}
    slow_outputs = set().union(*next_source).intersection(slow_candidates)
    require(bool(slow_outputs), 'The next complete source really retains nonzero slow outputs')
    h5 = h
    for _ in range(4):
        h5 = f.mul(h5, h)
    h6 = f.mul(h5, h)
    require(mean(h5) == Q(25, 8) and mean(h6) == Q(215, 32),
            'The work and replenishment transfers have positive distinct modulation factors')

    return dict(base=dict(heat_work='0', replenishment_profile=str(s.factor(g)),
                          capacity_creation=str(gamma), diffusion=str(diffusion), fourth_moment=str(size),
                          physical_cases=actual),
                depleting_target=dict(heat_profile=str(s.factor(target_profile)), reserve=str(target_reserve),
                                      nonlinear_return=str(target_gamma)),
                replenishing_family=dict(parameter_range='0<eps<=1/4',
                    heat_profile=str(s.factor(F)), nonlinear_profile=str(s.factor(G)),
                    heat_profile_margin=str(profile_margin), reserve=str(R), nonlinear_return=str(Gamma),
                    uniform_return_lower=str(s.factor(lower)),
                    quarter_return=str(Gamma.subs(eps, s.Rational(1, 4)))),
                generated_source=dict(scale=n, input_modes=len(set().union(*datum)),
                    output_modes=len(set().union(*source)), work_modulation=str(mean(h5)),
                    renewal_modulation=str(mean(h6)),
                    next_output_modes=len(set().union(*next_source)), slow_outputs=sorted(slow_outputs),
                    scope='Exact source reconstruction; large-scale heat-history limit and actual generated-prefix transfer are analytic'),
                scope='Exact full Fourier identities and rational whole-heat-history bounds; physical interval and continuation arguments analytic, not Lean-certified')


if __name__ == '__main__':
    print(json.dumps(checks(), indent=2))
