#!/usr/bin/env python3
"""A complete coupled return from a non-self-interacting heat source.

The full NS amplitude recurrence, positive exponential-polynomial cascade,
and independent positive-viscosity time jets are exact. Actual local
intervals and the continuation connection are analytic in README.md.
The paid leading return does not bound the higher nonlinear remainder.
"""

import hashlib
import json
import math
from pathlib import Path
from fractions import Fraction

import sympy as sy
import paired_stretching_history as ep
import convex_parent_return as c
import helicity_renewal as h

f, Q, require = c.f, c.Q, c.require
PRICE = Fraction(415522849111, 1911826022400000000)
SEVENTH = Fraction(8393, 576)


def initial(amplitudes=(1, 1, 1), sine=True):
    u = [{}, {}, {}]
    for amplitude, k, component in zip(amplitudes, ((0, 1, 0), (0, 0, 1), (1, 0, 0)), (0, 0, 2)):
        a = -f.II*Q(amplitude)/2 if sine else Q(amplitude)/2
        u[component][k] = a
        u[component][tuple(-j for j in k)] = h.conjugate(a)
    return [f.clean(v) for v in u]


def equal(u, v, label):
    for a, b in zip(u, v):
        f.equal(a, b, label)


def triple(u, v, w):
    U, V, W = f.jac(u), f.jac(v), f.jac(w)
    VW = f.matmul(V, W)
    return -c.mean(f.add(*(f.mul(U[i][j], VW[i][j]) for i in range(3) for j in range(3))))


def cubic_jet(b, order):
    total = 0
    for i in range(1, order-1):
        for j in range(1, order-i):
            k = order-i-j
            require(max(i, j, k) < len(b), 'Complete time jets for the cubic coefficient')
            total += math.factorial(order)//(math.factorial(i)*math.factorial(j)*math.factorial(k))*triple(b[i], b[j], b[k])
    return total


def pressure_identity():
    A, B, C, nu = sy.symbols('A B C nu', real=True)
    x, y, z = sy.symbols('x y z', real=True)
    xyz = (x, y, z)
    u = sy.Matrix([A*sy.cos(y)+B*sy.cos(z), 0, C*sy.cos(x)])
    lap = lambda a: sum(sy.diff(a, q, 2) for q in xyz)
    J = u.jacobian(xyz)
    p0 = B*C*sy.sin(x)*sy.sin(z)
    tangent = nu*u.applyfunc(lap)-J*u-sy.Matrix([sy.diff(p0, q) for q in xyz])
    expected = -nu*u+sy.Matrix([0, 0, A*C*sy.sin(x)*sy.cos(y)])
    require((tangent-expected).applyfunc(sy.expand) == sy.zeros(3, 1), 'Complete initial NS tangent')
    require(sy.expand(lap(p0)+sy.trace(J*J)) == 0, 'Canonical initial pressure')
    p1 = -2*nu*p0-sy.Rational(2, 3)*A*B*C*sy.cos(x)*sy.cos(y)*sy.sin(z)
    require(sy.expand(lap(p1)+2*sy.trace(J*tangent.jacobian(xyz))) == 0, 'Complete pressure derivative')
    q2 = -sy.Rational(2, 3)*A*B*C*sy.cos(x)*sy.sin(y)*sy.sin(z)
    require(sy.expand(-sy.diff(p1, y)-q2) == 0, 'Actual delayed transverse acceleration')
    return dict(datum='(A cos y+B cos z,0,C cos x)',
                heat_source='A*C*exp(-2*nu*t)*sin(x)*cos(y)*e_z',
                pressure_initial=str(p0), pressure_derivative=str(p1),
                transverse_second_derivative=str(q2),
                transverse_gradient_energy='A^2*B^2*C^2*t^4/24+O(t^5)')


def complete_amplitudes():
    u = initial()
    heat = {k: tuple({(1, 0): Fraction(str(v.get(k, f.ZERO).y))} if v.get(k, f.ZERO) else {}
                     for v in u) for k in h.modes(u)}
    U, N, P = ep.evolve_amplitudes(heat, 6)
    b = [{}, {}]+U[2:]+[{} for _ in range(4)]
    coefficients = {}
    for degree in (6, 8, 10):
        terms = []
        for i in range(2, 7):
            m = degree-i
            if m < 4:
                continue
            source = ep.field_add(ep.advection(b[j], b[m-j])
                                  for j in range(2, 7) if 2 <= m-j <= 6)
            terms.append(ep.weighted_pair(b[i], source, 1))
        coefficients[degree] = ep.add(*terms)
    require(not coefficients[6] and not coefficients[8], 'Lower even amplitude degrees vanish for all time')
    G = coefficients[10]
    require(G == ep.literal_cubic(b, 10), 'Independent physical vorticity-stretching contraction')
    require(len(G) == 22 and ep.integral_infinity(G) == PRICE, 'Complete exact leading-history price')
    require(all(ep.jet(G, j) == 0 for j in range(7)) and ep.jet(G, 7) == SEVENTH,
            'Positive seventh-order onset with all earlier derivatives zero')

    # Each step F_next=(d/dt+lambda)F has nonnegative F(0).
    # Solving these scalar equations backward from terminal zero proves
    # nonnegativity on all t>=0; a positive initial value gives strictness.
    rates = [rate for rate in sorted({i for i, _ in G}, reverse=True)
             for _ in range(1+max(j for i, j in G if i == rate))]
    current, values = G, []
    for rate in rates:
        value = ep.jet(current, 0)
        require(value >= 0, 'Nonnegative initial datum in the positive differential cascade')
        values.append(value)
        current = ep.add(ep.derivative(current), ep.scale(rate, current))
    require(not current and any(v > 0 for v in values), 'Zero terminal function and strict positive forcing')
    tail = ep.tail_integral(G)
    require(not ep.add(ep.derivative(tail), G) and ep.jet(tail, 0) == PRICE,
            'Remaining positive tail spends the complete leading return')
    return U, dict(complete_mode_counts=[len(U[i]) for i in range(1, 7)],
                   coefficients=ep.encode(G), lower_degrees_zero=[6, 8],
                   seventh_derivative=str(SEVENTH), onset_coefficient=str(SEVENTH/Fraction(math.factorial(7))),
                   total_integral=str(PRICE), tail=ep.encode(tail),
                   positive_cascade_rates=rates, positive_cascade_initial_values=[str(v) for v in values])


def literal_jets(U):
    rows = []
    for amplitudes, nu in [((1, 1, 1), Q(1)), ((1, 1, 1), Q(2)/7), ((2, 1, 1), Q(1))]:
        u0 = initial(amplitudes)
        n0 = c.nonlinear(u0)
        equal(c.nonlinear(n0), [{}, {}, {}], 'Entire original source is non-self-interacting')
        require(triple(n0, n0, n0) == 0, 'Zero original source self-stretching')
        jets, pressures = c.velocity_time_jets(u0, nu, 5)
        b = [c.addv(v, c.scale(-(-nu)**j, u0)) for j, v in enumerate(jets)]
        equal(b[0], [{}, {}, {}], 'Generated remainder initially zero')
        onset = []
        for j in range(3, 8):
            value = cubic_jet(b, j)
            expected = Q(SEVENTH)*amplitudes[0]**4*amplitudes[1]**2*amplitudes[2]**4 if j == 7 else Q(0)
            require(Q(value) == expected, 'Full viscous PDE jet matches the joint coupled onset')
            onset.append(str(value))
        require(not jets[1][1] and bool(jets[2][1]), 'Transverse component is generated at second order')
        if amplitudes == (1, 1, 1):
            for order, observed in enumerate(jets):
                reconstructed = [{}, {}, {}]
                for degree in range(1, 7):
                    factor = nu**(order+1-degree)
                    for k, v in U[degree].items():
                        for j in range(3):
                            value = f.II*factor*Q(ep.jet(v[j], order))
                            reconstructed[j][k] = reconstructed[j].get(k, f.ZERO)+value
                equal(observed, [f.clean(v) for v in reconstructed], 'Independent complete time/amplitude jet reconstruction')
        rows.append(dict(amplitudes=amplitudes, nu=str(nu),
                         complete_velocity_mode_counts=[len(h.modes(v)) for v in jets],
                         complete_pressure_mode_counts=[len(v) for v in pressures],
                         remainder_stretching_derivatives_3_to_7=onset))
    return rows


def reserve_check():
    chi, chi0, lead, eta, nu, D = sy.symbols('chi chi0 lead eta nu D', real=True)
    # Existing parent reserve derivative + (3nu/2)chi D <=2chi(lead+eta).
    parent_rate = 2*chi*(lead+eta)-3*nu*chi*D/2
    leading_tail_rate = -2*chi0*lead
    require(sy.expand(parent_rate+leading_tail_rate+3*nu*chi*D/2
                      -2*chi*eta+2*(chi0-chi)*lead) == 0,
            'Joint reserve retains the exact higher-return defect and overpayment')
    return dict(leading_history='A^4*B^2*C^4*nu^(-7)*G10(nu*t)',
                leading_reserve='2*chi0*A^4*B^2*C^4*nu^(-8)*tail_G10(nu*t)',
                original_price='2*chi0*A^4*B^2*C^4*nu^(-8)*'+str(PRICE),
                exact_remaining='eta(t)=g(u(t)-exp(nu*t*Delta)u0)-A^4*B^2*C^4*nu^(-7)*G10(nu*t)',
                OPEN='2 integral chi*eta <= nu integral chi*D_b + K(original full datum,nu,H)')


if __name__ == '__main__':
    U, amplitudes = complete_amplitudes()
    report = dict(physical_family=pressure_identity(), full_leading_history=amplitudes,
                  independent_actual_jets=literal_jets(U), physical_reserve=reserve_check(),
                  scope='Exact full amplitude coefficient and physical jets; PDE intervals analytic; arbitrary-amplitude higher-return budget open; no new Lean theorem')
    report['source_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(report, indent=2, sort_keys=True))
