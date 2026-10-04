#!/usr/bin/env python3
"""Complete NS jets for escape from an energy-priced spectral enclosure.

The actual interval estimates and the reserve comparison are analytic in
README.md. Every Fourier output in these time jets is retained.
"""

import ast
import hashlib
import itertools
import json
import math
from fractions import Fraction as Q
from pathlib import Path

import sympy as s
import pressure_history_source as f
import generated_mean_enstrophy as m
import pancake_concentration_threshold as pc
from pancake_band_parent import band, outside, trilinear
from cyclic_pressure_history import velocity_time_jets
from reciprocal_pattern_cycles import inner, mode, require, vector_add, vector_scale


def zero(expression, label):
    require(s.simplify(expression) == 0, label)


def seed():
    return [mode((0, 16, 1), 1),
            f.add(mode((16, 0, 1), 1), mode((-16, 0, 1), 1)), {}]


def exact_history():
    u = seed()
    N, record = pc.full_source(u)
    require(s.Matrix([[16, 0, 1], [0, 16, 1], [-16, 0, 1]]).det() == 512,
            'three independent input directions')
    require(not any(outside(u)), 'the initial band complement is empty')
    m.equal_vectors(m.minus_laplacian(u), vector_scale(257, u), 'the entire seed has one Laplacian eigenvalue')
    require(record['energy'] == '3/2' and record['enstrophy'] == '771/2'
            and record['dissipation'] == '198147/2', 'initial physical resources')
    require(m.cubic(u) == 0 and m.linear_cubic_term(u, N) == Q(33152, 129),
            'complete first stretching return')
    expected = {(16, 16, 2): [-4, -4, 64], (-16, 16, 2): [-4, 4, -64]}
    require(len(pc.support(N)) == 4 and not any(band(N)), 'the complete first source consists of high-band daughters')
    for q, v in expected.items():
        require([row.get(q, f.ZERO) for row in N] == [f.II*Q(x, 129) for x in v],
                'specified daughter survives canonical pressure projection')
    require(inner(N, N) == Q(128, 129), 'full generated source energy')
    c5 = Q(1098907648, 49923)
    samples, records = [], []
    for mu in (Q(0), Q(1, 7), Q(1), Q(2), Q(3), Q(4)):
        jets, pressures = velocity_time_jets(u, mu, 3)
        first = vector_add(N, vector_scale(-257*mu, u))
        m.equal_vectors(jets[1], first, 'independent complete first NS tangent')
        for n in range(1, 4):
            energy_rate = sum((math.comb(n, r)*inner(jets[r], jets[n-r]) for r in range(n+1)), Q(0))
            gradient_rate = sum((math.comb(n-1, r)*m.derivative_pair(jets[r], jets[n-1-r])
                                 for r in range(n)), Q(0))
            require(energy_rate == -2*mu*gradient_rate, ('complete kinetic time derivative', n))
        w = [[{}, {}, {}]]+[vector_scale(Q(1, math.factorial(n)), outside(jets[n])) for n in range(1, 4)]
        coefficients = {}
        for degree in (3, 4, 5):
            coefficients[degree] = sum((trilinear(w[i], w[j], w[k])
                                       for i, j, k in itertools.product(range(1, 4), repeat=3)
                                       if i+j+k == degree), Q(0))
        require(coefficients == {3: Q(0), 4: Q(0), 5: c5}, 'the first high-band self-stretching is positive at degree five')
        samples.append((s.Rational(mu.numerator, mu.denominator), s.Rational(c5.numerator, c5.denominator)))
        if mu == 0:
            daughter_return = outside(vector_scale(Q(1, 3), m.nonlinear(N)))
            parent_return = outside(vector_scale(Q(1, 6), vector_add(m.bilinear(jets[2], u), m.bilinear(u, jets[2]))))
            m.equal_vectors(vector_add(daughter_return, parent_return), w[3],
                            'complete third high-band tangent retains old and new parents')
            own_work, parent_work = m.linear_cubic_term(N, daughter_return), m.linear_cubic_term(N, parent_return)
            require(own_work == Q(1098907648, 3244995) and parent_work == 64*own_work,
                    'existing parents supply sixty-four times the isolated daughter return')
            require(own_work+parent_work == c5, 'both sources reconstruct the complete fifth-order coefficient')
        records.append(dict(viscosity=str(mu), time_jet_modes=[len(pc.support(x)) for x in jets],
                            coefficients={str(k): str(v) for k, v in coefficients.items()},
                            pressure_jet_modes=[len(p) for p in pressures]))
    mu_symbol = s.symbols('mu')
    zero(s.interpolate(samples, mu_symbol)-s.Rational(c5.numerator, c5.denominator),
         'degree-at-most-five viscosity polynomial is identified by six exact samples')
    return dict(initial=record, first_source_squared='128/129', samples=records,
                degree_five=str(c5), daughter_self_share='1/65', existing_parent_share='64/65',
                polynomial_argument='The nth full time derivative has viscosity degree at most n; a cubic coefficient of time degree five has degree at most five. Six distinct rational samples determine it.')


def geometry_and_price():
    q1, q2 = s.Matrix([16, 16, 2]), s.Matrix([-16, 16, 2])
    require(q1.dot(q1) == q2.dot(q2) == 516 and q1.cross(q2).dot(q1.cross(q2)) == 266240,
            'two surviving daughters cannot share the prescribed narrow core')
    require(516 < 23**2 and 23 < 5**2 and 2*23*5 < 500 and 266240 > 500**2,
            'rational cross-product separation works for every unit core axis')
    require(all(abs(int(x)) > 1 for x in list(q1)+list(q2)),
            'both daughters escape every coordinate band of width at most one')
    c = s.symbols('c', positive=True)
    single = lambda J: c*(2*J+1)
    union = lambda J: 3*single(J)
    require(single(1) == union(0) == 3*c and single(2) == 5*c and union(1) == 9*c,
            'the next admissible width needs a fixed increase of the price')
    zero(Q(2)*Q(771, 2)/Q(3, 2)-514, 'initial fractional kinetic dissipation rate')
    return dict(core='B=R=1, gamma=1/2, arbitrary single unit axis',
                price='beta0=3c; if E/E0>3/5 and 0<=p<1, beta0(E0/E)^p<5c',
                available='single coordinate bands J<=1, or three-coordinate union J=0',
                scope='Larger original-data prices or different geometric constants remain possible.')


def reserve_comparison():
    A, nu = s.symbols('A nu', positive=True)
    E0 = 3*A*A/2
    geometric = 48*s.sqrt(E0)
    lower_L = 64*geometric**4/nu**3
    zero(lower_L-764411904*A**4/nu**3, 'retained original-data linear allowance')
    C, L, Zw, Dw, gap = s.symbols('C L Zw Dw gap', nonnegative=True)
    g = C*A*Zw-gap
    residual = 2*g-nu*Dw-2*L*Zw
    zero(residual+nu*Dw+2*(L-C*A)*Zw+2*gap, 'local full-data control pays the actual signed residual')
    Z, V, beta, cap, alpha, phi, loss, b, g0, d, D = s.symbols(
        'Z V beta cap alpha phi loss b g0 d D', real=True)
    # The residual d is signed. Geometry is not assumed at this point.
    Zd = (alpha+beta*V)*Z-nu*D/2+d-loss
    Sd = (-alpha-cap*Z)*phi*Z+phi*Zd
    Rd = 2*Sd-Zd-2*b
    cost = Zd+nu*D-2*g0
    zero(Rd+cost-2*phi*d+nu*(phi-1)*D+2*phi*(cap*(Z-V)+(cap-beta)*V)*Z+2*phi*loss+2*(b+g0),
         'a nonpositive actual residual suffices even when the geometric enclosure fails')
    gw, Dv, slack = s.symbols('g_w D_V slack', real=True)
    from_physics = 2*gw-3*nu*D/2+(beta*V+nu/2)*Z-slack
    signed = 2*gw-nu*(D-Dv)-2*L*(Z-V)
    retained = (2*L+nu/2+beta*V)*Z-nu*D/2+signed-(nu*Dv+2*L*V+slack)
    zero(from_physics-retained, 'the signed residual retains the favorable parent diffusion and linear terms')
    return dict(linear_allowance_lower=str(lower_L),
                actual_scope='Uniform smooth local NS control gives ||grad w||infinity<=C_seed A for every spectral band complement. For A sufficiently large, L(A)>=C_seed A and the signed residual is nonpositive on the common local interval.',
                limitation='No iteration beyond that local interval or arbitrary-history estimate is asserted.')


def source_hashes():
    root = Path(__file__).resolve().parent
    pending, seen = [Path(__file__).resolve()], set()
    while pending:
        path = pending.pop()
        if path in seen:
            continue
        seen.add(path)
        for node in ast.walk(ast.parse(path.read_text())):
            names = ([a.name for a in node.names] if isinstance(node, ast.Import)
                     else [node.module] if isinstance(node, ast.ImportFrom) and node.level == 0 else [])
            for name in names:
                if name:
                    other = root / (name.split('.')[0]+'.py')
                    if other.is_file():
                        pending.append(other)
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(seen)}


if __name__ == '__main__':
    print(json.dumps(dict(history=exact_history(), geometry=geometry_and_price(),
                          reserve=reserve_comparison(), source_sha256=source_hashes(),
                          scope='Exact complete source and time coefficients. Local PDE persistence, uniform remainders and inequalities are analytic, not Lean-certified.'), indent=2))
