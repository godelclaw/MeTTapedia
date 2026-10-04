#!/usr/bin/env python3
"""A later actual NS return defeats adaptive heat-window reserve controls.

The datum is specified by an isolated positive algebraic polarization.
All identities below are polynomial identities before specializing it.
Every pressure and velocity time-jet output is retained. The uniform
local PDE remainder and all-policy conclusion are analytic in README.md,
not Lean certificates or a closed-mode evolution.
"""

import hashlib
import json
import math
from fractions import Fraction as Q
from pathlib import Path

import sympy as s
import pressure_history_source as f
import heat_work_reserve as h
from cyclic_pressure_history import velocity_time_jets
from heat_remainder_pressure import require
from pressure_quadratic_storage import mode


def zero(value, label):
    require(s.expand(value) == 0, label)


def datum():
    waves = [mode((0, 1, 1), (2, 1, -1), 1),
             mode((0, 1, -1), (-2, -1, -1), 1),
             mode((1, -1, 0), (1, 1, 0), 1)]
    waves[-1][2] = {k: h.EPS*a for k, a in mode((1, -1, 0), (0, 0, 1), 1)[2].items()}
    return [f.add(*(v[j] for v in waves)) for j in range(3)]


def pairing(a, b):
    require(len(a) == len(b), 'The full pairing has matching component counts')
    value = sum((x*b[j].get(tuple(-z for z in k), f.ZERO)
                 for j in range(len(a)) for k, x in a[j].items()), f.ZERO)
    return h.average({f.ORIGIN: value})


def magnitude_jets(jets, order):
    return [f.add(*(f.scale(math.comb(n, j), f.dot(jets[j], jets[n-j]))
                    for j in range(n+1))) for n in range(order+1)]


def moment_derivative(jets, order):
    magnitudes = magnitude_jets(jets, order)
    return s.factor(sum(math.comb(order, j)*pairing([magnitudes[j]], [magnitudes[order-j]])
                        for j in range(order+1))/4)


def work_jets(jets, order):
    """Derivatives of -integral |u|^2 u.grad(p), with evolving pressure."""
    pressures, magnitudes, receivers, values = [], [], [], []
    for n in range(order+1):
        tensor = [[f.add(*(f.scale(math.comb(n, j), f.mul(jets[j][a], jets[n-j][b]))
                           for j in range(n+1))) for b in range(3)] for a in range(3)]
        pressures.append(f.tensor_pressure(tensor))
        magnitudes.append(f.add(*(tensor[j][j] for j in range(3))))
        receivers.append([f.add(*(f.scale(math.comb(n, j), f.mul(magnitudes[j], jets[n-j][a]))
                                 for j in range(n+1))) for a in range(3)])
        values.append(s.factor(-sum(math.comb(n, j)*pairing(receivers[j], f.grad(pressures[n-j]))
                                    for j in range(n+1))))
    return values


def even_polynomial(expression, variable):
    result = 0
    for (power,), coefficient in s.Poly(s.expand(expression), h.eps).terms():
        require(power % 2 == 0, 'The scalar coefficient depends polynomially on squared polarization')
        result += coefficient*variable**(power//2)
    return s.expand(result)


def bernstein(expression, variable, left, right):
    t = s.symbols('t')
    p = s.Poly(expression.subs(variable, left+(right-left)*t), t)
    degree = p.degree()
    coefficients = [s.factor(sum(p.nth(k)*s.binomial(j, k)/s.binomial(degree, k)
                                 for k in range(j+1))) for j in range(degree+1)]
    reconstructed = sum(coefficients[j]*s.binomial(degree, j)*t**j*(1-t)**(degree-j)
                        for j in range(degree+1))
    zero(reconstructed-p.as_expr(), 'The interval Bernstein coefficients reconstruct the exact polynomial')
    return coefficients


def checks():
    u = datum()
    f.equal(f.trace(f.jac(u)), {}, 'Every polarization is incompressible')
    for row in u:
        require(f.ORIGIN not in row, 'The datum has zero spatial mean')
        f.equal(f.lap(row), f.scale(-2, row), 'All input modes have squared frequency two')
        f.equal({tuple(-j for j in k): a for k, a in row.items()}, row,
                'The real cosine datum is spatially even')
    jets, _ = velocity_time_jets(u, Q(0), 4)
    P = work_jets(jets, 3)
    r = s.symbols('r', real=True)
    root_polynomial = 5*r*r-153*r+372
    expected_return = -(198450*r**3+6222475*r**2-453762911*r+1498877472)/s.Integer(793800)
    zero(P[0], 'The initial pressure work vanishes')
    zero(even_polynomial(P[1], r)-root_polynomial/18, 'Exact first complete pressure-work return')
    zero(P[2], 'The second complete pressure-work derivative vanishes')
    zero(even_polynomial(P[3], r)-expected_return, 'The third complete pressure-work derivative retains every parent')
    zero(h.variation(u, jets[1])-P[1], 'Independent canonical-pressure variation checks the first return')
    for n in range(1, 5):
        zero(moment_derivative(jets, n)-P[n-1],
             'Independent fourth-moment derivatives agree with the complete Euler work jets')

    heated = h.heat(u)
    zero(h.profile(heated), 'The initial heat-work capacity vanishes for every window')
    zero(h.variation(heated, h.nonlinear(heated))-h.q**12*P[1],
         'The intrinsic capacity vanishes at every heat age at the algebraic root')
    E = even_polynomial(pairing(u, u), r)
    Y = even_polynomial(4*moment_derivative(jets, 0), r)
    magnitude = f.dot(u, u)
    gradient_square = f.add(*(f.mul(a, a) for row in f.jac(u) for a in row))
    diffusion = h.average(f.mul(magnitude, gradient_square)) \
                +sum(h.average(f.mul(f.diff(magnitude, j), f.diff(magnitude, j)))/2 for j in range(3))
    D = even_polynomial(diffusion, r)
    zero(D-2*Y, 'The direct quartic diffusion equals twice the fourth moment on this input shell')

    require(root_polynomial.subs(r, 27) == -114 and root_polynomial.subs(r, 28) == 8,
            'The polarization root lies strictly between squared values 27 and 28')
    require(s.diff(root_polynomial, r).subs(r, 27) == 117 > 0,
            'The root polynomial is strictly increasing throughout the isolating interval')
    require(s.Poly(root_polynomial, r).count_roots(27, 28) == 1,
            'Independent exact root count confirms the unique isolated polarization')
    root = (153+s.sqrt(15969))/10
    zero(root_polynomial.subs(r, root), 'The explicit radical is the specified squared polarization')
    require(117**2 < 15969 < 127**2, 'The explicit positive radical lies in the same isolating interval')
    coefficients = bernstein(expected_return, r, 27, 28)
    require(min(coefficients) > 2400, 'The complete later return has a uniform positive margin on the root interval')
    moment_coefficients = bernstein(Y, r, 27, 28)
    diffusion_coefficients = bernstein(D, r, 27, 28)
    require(min(moment_coefficients) > 0, 'The initial fourth moment is finite and positive')
    require(max(diffusion_coefficients) == 1305, 'Uniform quartic-diffusion upper bound at the algebraic root')
    leading_gain = s.Rational(4**4*2400, 24)-4*max(diffusion_coefficients)
    remainder_coefficient = 4**2+4**5
    require(leading_gain == 20380 and remainder_coefficient == 1040
            and leading_gain-remainder_coefficient > 19000,
            'The later return beats both initial viscosity and the controlled local remainder')

    viscous = []
    for nu in (Q(1), Q(2, 7)):
        actual, _ = velocity_time_jets(u, nu, 2)
        first = even_polynomial(moment_derivative(actual, 1), r)
        second = even_polynomial(moment_derivative(actual, 2), r)
        zero(first+nu*D, 'The actual viscous fourth moment initially decreases')
        zero(second-root_polynomial/18-8*nu**2*D,
             'The complete second moment derivative includes the viscous contribution')
        kinetic_rate = even_polynomial(2*pairing(u, actual[1]), r)
        zero(kinetic_rate+4*nu*E, 'The same unforced flow loses total kinetic energy')
        viscous.append(dict(viscosity=str(nu), moment_first=str(first),
                            moment_second=str(second), squared_L2_rate=str(kinetic_rate)))

    result = dict(polarization='m=sqrt((153+sqrt(15969))/10)',
                  root_polynomial=str(root_polynomial), root_interval=[27, 28],
                  pressure_work_jets=[str(value) for value in P],
                  velocity_jet_modes=[len(set().union(*v)) for v in jets],
                  later_return_polynomial=str(s.factor(expected_return)),
                  later_return_bernstein=list(map(str, coefficients)),
                  later_return_lower='2400', squared_L2=str(E), fourth_moment=str(Y),
                  quartic_diffusion=str(D), diffusion_upper=str(max(diffusion_coefficients)),
                  rebound=dict(normalized_time='4*mu^(1/3)', leading_gain_lower=str(leading_gain),
                               remainder_coefficient=remainder_coefficient, gain_lower='19000*mu^(4/3)',
                               conditions='T0<=1, C>=1, 0<mu<=min((T0/4)^3,C^(-3))'),
                  actual_tangents=viscous,
                  scope='Exact complete Fourier time jets and algebraic-polarization sign certificates. The actual positive-viscosity rebound, uniform local remainder, and obstruction for all nonnegative heat-window and scalar-weight policies are analytic, not Lean-certified. Other initial-data reserves and global regularity are not refuted.')
    root_dir = Path(__file__).resolve().parent
    names = ['adaptive_heat_reserve.py', 'heat_work_reserve.py', 'pressure_history_source.py',
             'cyclic_pressure_history.py', 'generated_fourth_moment.py', 'heat_remainder_pressure.py',
             'pressure_quadratic_storage.py', 'pressure_gradient_stock.py']
    result['source_sha256'] = {name: hashlib.sha256((root_dir/name).read_bytes()).hexdigest() for name in names}
    return result


if __name__ == '__main__':
    print(json.dumps(checks(), indent=2))
