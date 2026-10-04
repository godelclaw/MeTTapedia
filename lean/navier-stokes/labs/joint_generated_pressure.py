#!/usr/bin/env python3
"""Retained mixed pressure, complete diffusion defects and observer costs.

All Fourier outputs and full viscous amplitude histories are retained.
The general identities, uniform remainders and actual-flow implications
are analytic in README.md; these checks are not Lean certificates.
"""

import json
from fractions import Fraction as Q
from math import comb

import sympy as s
import paired_stretching_history as e
import pressure_history_source as f
from cyclic_pressure_history import velocity_time_jets
from heat_remainder_pressure import plus, times, mean, require
from pressure_gradient_stock import weighted_datum, pressure_pair, fingerprint


def scalar_fields(*fields):
    result = {}
    for field in fields:
        for k, a in field.items():
            result[k] = e.add(result.get(k, {}), a)
    return {k: a for k, a in result.items() if a}


def scale_field(c, field):
    return {k: e.scale(c, a) for k, a in field.items() if c and a}


def histories(m, weights):
    initial = weighted_datum(m, weights)
    heat = {q: tuple({(sum(k*k for k in q), 0): Q(str(row[q].y))}
                     if q in row else {} for row in initial) for q in set().union(*initial)}
    velocity, _, _ = e.evolve_amplitudes(heat, 4)
    mixed = {n: e.project(e.field_add([e.advection(velocity[1], velocity[n-1]),
                    e.advection(velocity[n-1], velocity[1])]))[1] for n in (3, 4, 5)}
    selfp = {n: e.project(e.field_add(e.advection(velocity[j], velocity[n-j])
                                    for j in range(2, n-1)))[1] for n in (3, 4, 5)}
    for n in (3, 4, 5):
        total = e.project(e.field_add(e.advection(velocity[j], velocity[n-j])
                                      for j in range(1, n)))[1]
        require(scalar_fields(mixed[n], selfp[n]) == total,
                'Mixed and self parts reconstruct the full pressure coefficient')
    quadratic = e.add(pressure_pair(mixed[4], mixed[4]),
                     e.scale(2, pressure_pair(mixed[3], mixed[5])))
    linear = e.scale(2, e.add(pressure_pair(mixed[4], selfp[4]),
                              pressure_pair(mixed[3], selfp[5])))
    constant = pressure_pair(selfp[4], selfp[4])
    profiles = constant, linear, quadratic
    coefficients = [e.integral_infinity(a) for a in profiles]
    stock = e.integral_infinity(pressure_pair(mixed[3], mixed[3]))
    for theta in (Q(-2), Q(0), Q(2, 7), Q(3, 5), Q(1)):
        joint = {n: scalar_fields(scale_field(theta, mixed[n]), selfp[n]) for n in (3, 4, 5)}
        odd = e.scale(2, pressure_pair(joint[3], joint[4]))
        direct = e.add(pressure_pair(joint[4], joint[4]),
                       e.scale(2, pressure_pair(joint[3], joint[5])))
        require(not odd, 'The full odd-amplitude cost profile vanishes')
        require(direct == e.add(*(e.scale(theta**j, profile) for j, profile in enumerate(profiles))),
                'The quadratic weight law matches the full time profile at unused weights')
        require(e.integral_infinity(pressure_pair(joint[3], joint[3])) == theta**2*stock,
                'The first mixed-pressure allowance keeps its actual weight')
    for profile in profiles:
        integrated = e.heat_convolution(profile, 0)
        require(e.derivative(integrated) == profile and e.jet(integrated, 0) == 0
                and integrated.get((0, 0), Q(0)) == e.integral_infinity(profile),
                'Independent antiderivative checks every full-time coefficient')
    c, b, a = coefficients
    schedules = []
    if weights[0] == Q(1, 4):
        require(m == 4 and a < 0 and b > 0 and c > 0, 'Quarter-parent polynomial signs')
        at_half, at_start = c+b/2+a/4, c+Q(3, 5)*b+Q(9, 25)*a
        require(at_half > 0 > at_start and b+Q(6, 5)*a < 0,
                'Half retention fails; the full interval [3/5,1] has a negative correction')
        certificate = dict(paid_weight_interval=['3/5', '1'],
                           negative_margin=str(-at_start), half_retention_correction=str(at_half))
    else:
        determinant, trace = c*a-b*b/4, c+a
        require(a > 0 and c > 0 and determinant > 0, 'Positive definite complete weight form')
        eta = determinant/trace
        theta = s.Symbol('theta', real=True)
        lift = lambda x: s.Rational(x.numerator, x.denominator)
        poly = lift(c)+lift(b)*theta+lift(a)*theta**2
        squares = (lift(c)+lift(b/2)*theta)**2+(lift(b/2)+lift(a)*theta)**2
        require(s.expand(lift(trace)*poly-lift(determinant)*(1+theta**2)-squares) == 0,
                'Exact sum of squares proves the uniform all-real-weight coercivity')
        certificate = dict(all_real_weights_fail=True, eta=str(eta), eta_approximate=float(eta),
                           inequality='B(theta)>=eta*(1+theta^2)')
        for rho in (1, 2, 4, 8):
            for kind in ('decay', 'rise'):
                theta = {(rho, 0): Q(1)} if kind == 'decay' else {(0, 0): Q(1), (rho, 0): Q(-1)}
                square = e.multiply(theta, theta)
                leading = e.multiply(square, pressure_pair(mixed[3], mixed[3]))
                correction = e.add(constant, e.multiply(theta, linear), e.multiply(square, quadratic))
                values = e.integral_infinity(leading), e.integral_infinity(correction)
                require(values[0] > 0 and values[1] > 0,
                        'The bounded prescribed-schedule family also exceeds its own leading allowance')
                derivative = e.derivative(theta)
                variation = e.integral_infinity(e.multiply({(2, 0): Q(1)},
                                                          e.multiply(derivative, derivative)))
                require(variation == Q(rho**2, 2*(1+rho)),
                        'Observer variation has an explicit full-heat-data payment at viscosity one')
                schedules.append(dict(kind=kind, rho=rho, leading_stock=str(values[0]),
                                      next_correction=str(values[1]), correction_approximate=float(values[1]),
                                      weighted_variation_per_AW_squared=str(variation)))
    return dict(m=m, weights=list(map(str, weights)), leading_mixed_stock=str(stock),
                weight_polynomial=list(map(str, coefficients)),
                polynomial_approximate=list(map(float, coefficients)),
                profile_sha256=list(map(fingerprint, profiles)), certificate=certificate,
                prescribed_schedules=schedules)


def polarized(a, b):
    return f.tensor_pressure([[f.add(f.mul(a[i], b[j]), f.mul(b[i], a[j]))
                               for j in range(3)] for i in range(3)])


def scalar_pair(a, b):
    return mean(f.mul(a, b))


def gradient_pair(a, b):
    return mean(f.dot(f.grad(a), f.grad(b)))


def source_checks(m, weights, nu):
    initial = weighted_datum(m, weights)
    actual, pressure = velocity_time_jets(initial, nu, 4)
    heat = [initial]
    for _ in range(4):
        heat.append([f.scale(nu, f.lap(a)) for a in heat[-1]])
    remainder = [plus(a, times(-1, b)) for a, b in zip(actual, heat)]
    nonlinear = [[f.add(f.diff(pressure[n], i), *(f.scale(comb(n, j),
                    f.adv(actual[j], actual[n-j][i])) for j in range(n+1)))
                  for i in range(3)] for n in range(4)]
    selfp, mixed = [], []
    for n in range(5):
        selfp.append(f.tensor_pressure([[f.add(*(f.scale(comb(n, j),
            f.mul(remainder[j][i], remainder[n-j][k])) for j in range(n+1)))
                                       for k in range(3)] for i in range(3)]))
        mixed.append(f.add(*(f.scale(comb(n, j), polarized(heat[j], remainder[n-j]))
                             for j in range(n+1))))
    sources, thermal = [[], []], [[], []]
    for n in range(4):
        self_diffusion = f.tensor_pressure([[f.add(*(f.scale(-2*nu*comb(n, j),
            f.mul(f.diff(remainder[j][i], d), f.diff(remainder[n-j][k], d)))
            for j in range(n+1) for d in range(3))) for k in range(3)] for i in range(3)])
        mixed_diffusion = f.add(*(f.scale(-2*nu*comb(n, j), polarized(
            [f.diff(a, d) for a in heat[j]], [f.diff(a, d) for a in remainder[n-j]]))
            for j in range(n+1) for d in range(3)))
        for index, (parent, diffusion) in enumerate(((remainder, self_diffusion), (heat, mixed_diffusion))):
            forcing = f.add(*(f.scale(-comb(n, j), polarized(parent[j], nonlinear[n-j]))
                              for j in range(n+1)))
            sources[index].append(f.add(forcing, diffusion))
            thermal[index].append(diffusion)
    theta, rho = Q(3, 5), Q(1, 7)
    rows = []
    for rate in (Q(0), rho):
        joint = [f.add(selfp[n], f.scale(theta, mixed[n]),
                       f.scale(n*rate, mixed[n-1]) if n else {}) for n in range(5)]
        source = [f.add(sources[0][n], f.scale(theta, sources[1][n]),
                        f.scale(n*rate, sources[1][n-1]) if n else {},
                        f.scale(rate, mixed[n])) for n in range(4)]
        for n in range(4):
            literal = f.add(joint[n+1], f.scale(-nu, f.lap(joint[n])))
            f.equal(literal, source[n], 'Complete pressure evolution retains nonlinear, thermal and weight terms')
        work, dissipation, observer = [], [], []
        for n in range(3):
            derivative = sum((Q(comb(n+1, j))*scalar_pair(joint[j], joint[n+1-j])
                              for j in range(n+2)), Q(0))/2
            diffusion = sum((Q(comb(n, j))*gradient_pair(joint[j], joint[n-j])
                             for j in range(n+1)), Q(0))
            rhs = sum((Q(comb(n, j))*scalar_pair(joint[j], source[n-j])
                       for j in range(n+1)), Q(0))
            change = sum((rate*comb(n, j)*scalar_pair(joint[j], mixed[n-j])
                          for j in range(n+1)), Q(0))
            require(derivative+nu*diffusion == rhs,
                    'Exact pressure-energy identity includes the full physical dissipation')
            work.append(str(rhs)); dissipation.append(str(diffusion)); observer.append(str(change))
        require(Q(dissipation[2]) > 0, 'The diffusion check is nonzero')
        if rate:
            require(Q(observer[2]) > 0, 'Changing the observer has a nonzero actual initial-history cost')
        rows.append(dict(theta0=str(theta), theta_rate=str(rate),
                         work_derivatives=work, dissipation_derivatives=dissipation,
                         observer_work_derivatives=observer))
    require(any(thermal[0]) and any(thermal[1]), 'Both self and mixed thermal defects are retained')
    return dict(m=m, viscosity=str(nu), cases=rows)


def checks():
    shapes = [(4, (Q(1, 4), Q(1), Q(1))), (2, (Q(1),)*3), (4, (Q(1),)*3)]
    return dict(histories=[histories(m, weights) for m, weights in shapes],
                evolution=[source_checks(m, weights, nu) for (m, weights), nu in
                           zip(shapes[:2], (Q(2, 7), Q(1)))],
                scope='Exact complete histories and PDE jets; uniform small-data and arbitrary-flow comparison arguments are analytic')


if __name__ == '__main__':
    print(json.dumps(checks(), indent=2))
