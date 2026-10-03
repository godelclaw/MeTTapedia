#!/usr/bin/env python3
"""Complete pressure-impulse returns and a local funding obstruction.

All Fourier convolutions are retained. Viscosity is a polynomial variable,
not a fitted parameter. Actual solution intervals and conditional stochastic
moments are justified analytically in README.md; these are algebraic checks,
not a Galerkin trajectory or a Lean certificate.
"""

import json
from fractions import Fraction as Q
from math import comb, factorial

import sympy as s
import pressure_history_source as f
from pressure_parent_bellman import trig
from cyclic_pressure_history import velocity_time_jets
from cyclic_entropy_depletion import material_jets

RING = f.QQ_I.poly_ring('nu')
NU = RING.gens[0]


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def constant(value):
    return {(0, 0, 0): f.QQ_I(value)} if value else {}


def power(field, n):
    answer = constant(1)
    for _ in range(n):
        answer = f.mul(answer, field)
    return answer


def mean(field):
    return field.get((0, 0, 0), f.ZERO)


def specialize(field, value):
    return f.clean({k: RING.convert(c).evaluate(NU, f.QQ_I(value))
                    for k, c in field.items()})


def viscosity_jets(initial, order):
    """Literal NS recurrence over QQ(i)[nu], checked against the rational API."""
    velocity, pressure = [initial], []
    for n in range(order):
        tensor = [[f.add(*(f.scale(comb(n, k),
                           f.mul(velocity[k][i], velocity[n-k][j]))
                           for k in range(n+1))) for j in range(3)] for i in range(3)]
        p = f.tensor_pressure(tensor)
        pressure.append(p)
        v = [f.add(f.scale(NU, f.lap(velocity[n][i])), f.scale(-1, f.diff(p, i)),
                   f.scale(-1, f.add(*(f.scale(comb(n, k),
                                  f.adv(velocity[k], velocity[n-k][i]))
                                  for k in range(n+1))))) for i in range(3)]
        f.equal(f.trace(f.jac(v)), {}, 'Complete viscosity-polynomial NS tangent')
        velocity.append(v)
    literal, literal_p = velocity_time_jets(initial, Q(2, 7), order)
    for v, w in zip(velocity, literal):
        for a, b in zip(v, w):
            f.equal(specialize(a, Q(2, 7)), b, 'Independent rational velocity recurrence')
    for p, q in zip(pressure, literal_p):
        f.equal(specialize(p, Q(2, 7)), q, 'Independent rational canonical pressure')
    return velocity, pressure


def product_jet(a, b, n):
    terms = []
    for k in range(n+1):
        # An uncomputed derivative is harmless only if its other factor
        # is a KNOWN zero. Never silently truncate a generated derivative.
        if (k < len(a) and not a[k]) or (n-k < len(b) and not b[n-k]):
            continue
        require(k < len(a) and n-k < len(b), 'Every nonzero product jet is available')
        terms.append(f.scale(comb(n, k), f.mul(a[k], b[n-k])))
    return f.add(*terms)


def impulse_fourth_coefficients(velocity, gradient, nu):
    """Coefficients t^8,t^9,t^10 from the full conditional moment PDEs."""
    require(all(not v for v in gradient[0]), 'This recurrence requires p_0=0')
    g = [[v[i] for v in gradient] for i in range(3)]

    def step(a, source, n):
        transport = []
        for k in range(n+1):
            if not a[n-k]:
                continue
            require(k < len(velocity), 'Every generated advecting parent is available')
            transport.append(f.scale(comb(n, k), f.adv(velocity[k], a[n-k])))
        return f.add(f.scale(nu, f.lap(a[n])), f.scale(-1, f.add(*transport)), source)

    impulse = [[{}] for _ in range(3)]
    for n in range(4):
        for i in range(3):
            impulse[i].append(step(impulse[i], g[i][n], n))
    second = [[[{}] for _ in range(3)] for _ in range(3)]
    for n in range(6):
        for i in range(3):
            for j in range(3):
                source = f.add(product_jet(impulse[i], g[j], n),
                               product_jet(impulse[j], g[i], n))
                second[i][j].append(step(second[i][j], source, n))
    trace = [f.add(*(second[i][i][n] for i in range(3))) for n in range(7)]
    third = [[{}] for _ in range(3)]
    for n in range(8):
        for i in range(3):
            source = f.add(f.scale(2, f.add(*(product_jet(second[i][j], g[j], n)
                                             for j in range(3)))),
                           product_jet(trace, g[i], n))
            third[i].append(step(third[i], source, n))
    # Spatial integration cancels BOTH transport and diffusion at the last
    # level. Those terms were retained in every preceding moment equation.
    return [RING.convert(4*mean(f.add(*(product_jet(third[i], g[i], n)
                                    for i in range(3))))/factorial(n+1))
            for n in range(7, 10)]


def material_fourth_coefficients(velocity, gradient):
    """Independent Euler material-path calculation through impulse order four."""
    v = [[specialize(a, 0) for a in row] for row in velocity]
    g = [[specialize(a, 0) for a in row] for row in gradient]
    jets = [material_jets([row[i] for row in g], v) for i in range(3)]
    a = [f.scale(Q(1, 2), row[1]) for row in jets]
    b = [f.scale(Q(1, 6), row[2]) for row in jets]
    c = [f.scale(Q(1, 24), row[3]) for row in jets]
    aa, ab = f.dot(a, a), f.dot(a, b)
    return [mean(f.mul(aa, aa)), 4*mean(f.mul(aa, ab)),
            mean(f.add(f.scale(4, f.mul(aa, f.dot(a, c))),
                       f.scale(2, f.mul(aa, f.dot(b, b))), f.scale(4, f.mul(ab, ab))))]


def complete_returns():
    rows = []
    expected = {
        1: (Q(99, 512), -Q(297, 160), Q(29203, 3200), Q(20641, 152064)),
        4: (Q(199, 72), -Q(796, 5), Q(3183262, 675),
            Q(907148604883, 196886722032))}
    for k, (a, b, c, depletion) in expected.items():
        u = [trig(1, 1, 'sin'), trig(2, k, 'sin'), trig(0, 1, 'sin')]
        velocity, pressure = viscosity_jets(u, 4)
        g = [f.grad(p) for p in pressure]
        actual = impulse_fourth_coefficients(velocity, g, NU)
        eigenvalue = 2+k*k
        generated = [[{}, {}, {}], g[1],
                     [f.scale(-2*NU*eigenvalue, a) for a in g[1]],
                     [f.scale(3*NU**2*eigenvalue**2, a) for a in g[1]]]
        forecast = impulse_fourth_coefficients([[{}, {}, {}] for _ in range(5)],
                                               generated, NU)
        wanted = [RING.convert(a), b*NU, c*NU**2-RING.convert(depletion)]
        require(actual == wanted, 'Exact complete return polynomial for every viscosity')
        require(forecast == [RING.convert(a), b*NU, c*NU**2],
                'Same-viscosity first-generated pressure forecast')
        independent = material_fourth_coefficients(velocity, g)
        require([p.evaluate(NU, f.ZERO) for p in actual] == independent,
                'Material paths and conditional moment PDEs give the same Euler coefficient')
        rows.append(dict(wave_number=k, full_coefficients=[str(p) for p in actual],
                         matched_forecast=[str(p) for p in forecast],
                         first_nonlinear_difference='-'+str(depletion)+' * t^10',
                         viscosity='polynomial identity, all nu; no interpolation'))
    return rows


def local_funding():
    def odd(axis):
        return f.mul(trig(axis, 1, 'sin'),
                     power(f.add(constant(1), f.scale(-1, trig(axis, 1, 'cos'))), 2))

    cy = trig(1, 1, 'cos')
    even = f.mul(power(f.add(constant(1), f.scale(-1, cy)), 3),
                 f.add(cy, constant(Q(3, 4))))
    u = [even, odd(2), odd(0)]
    velocity, pressure = viscosity_jets(u, 2)
    require(all(mean(v) == f.ZERO for v in u), 'The datum has zero spatial mean')
    f.equal(f.trace(f.jac(u)), {}, 'Actual divergence-free datum')
    f.equal(pressure[0], {}, 'The entire initial canonical pressure vanishes')
    product = f.mul(f.diff(u[0], 1), f.mul(f.diff(u[1], 2), f.diff(u[2], 0)))
    f.equal(pressure[1], f.scale(-6, f.green(product)),
            'Generated pressure is independent of viscosity')
    gamma = Q(1178750, 28129101)
    require([f.evaluate(specialize(a, 1)) for a in f.grad(pressure[1])]
            == [0, -gamma, 0], 'Nonzero pressure gradient at the high-order quiet point')
    for n, v in enumerate(velocity):
        wanted = [RING.zero]*3 if n < 2 else [RING.zero, RING.convert(gamma), RING.zero]
        values = [RING.convert(sum(a.values(), f.ZERO)) for a in v]
        require(values == wanted, 'Actual velocity jets at the origin, every viscosity')
    for component, axis, order, derivative in [(u[0], 1, 6, Q(315, 2)),
                                              (u[1], 2, 5, Q(30)),
                                              (u[2], 0, 5, Q(30))]:
        p = component
        for n in range(order+1):
            require(f.evaluate(p) == (derivative if n == order else 0),
                    'Exact initial vanishing order')
            p = f.diff(p, axis)
    initial_fourth = power(f.dot(u, u), 2)
    lap = initial_fourth
    for n in range(11):
        want = 5244976800*factorial(10) if n == 10 else 0
        require(f.evaluate(lap) == want, 'First nonzero passive heat principal coefficient')
        lap = f.lap(lap)
    # Independent leading homogeneous polynomial calculation.
    x, z = s.symbols('x z')
    lead = (x**10+z**10)**2/256
    coefficient = sum(s.binomial(10, j)*s.diff(lead, x, 2*j, z, 20-2*j).subs({x: 0, z: 0})
                      for j in range(11))/factorial(10)
    require(coefficient == 5244976800, 'Independent degree-twenty principal heat calculation')
    return dict(datum='((1-cos y)^3(cos y+3/4), sin z(1-cos z)^2, sin x(1-cos x)^2)',
                initial_pressure='identically zero', gamma=str(gamma),
                generated_gradient='(0,-gamma,0)',
                actual_velocity='(gamma/2)*t^2*e_y+O(t^3)',
                actual_velocity_fourth='(gamma^4/16)*t^8+O(t^9)',
                conditional_impulse_fourth='(gamma^4/16)*t^8+O(t^9)',
                passive_initial_fourth='5244976800*nu^10*t^10+O(t^11)',
                failed_claim='J4(t,x) <= C(u0,nu,H)*h4(t,x), every small t and x',
                scope='one fixed smooth 3D datum, every fixed nu>0 and every finite C')


if __name__ == '__main__':
    print(json.dumps(dict(status='all exact checks passed',
        local_funding=local_funding(), pressure_returns=complete_returns(),
        OPEN='an original-data global fourth-moment allowance for repeated interacting histories',
        certification='exact full Fourier and polynomial identities; PDE intervals analytic'), indent=2))
