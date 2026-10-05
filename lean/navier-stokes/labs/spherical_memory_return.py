#!/usr/bin/env python3
"""Amplifying first memory through a complete spherical Fourier cutoff.

Symbolic full convolution proves the parameter identities. Independent
Gaussian-rational NS jets retain canonical pressure and all generated modes.
Actual intervals and the triangular all-time bound are analytic in README.md,
not Lean certificates or an arbitrary-data regularity theorem.
"""

from collections import defaultdict
import hashlib
import json
from pathlib import Path

import sympy as sy
import convex_parent_return as c
import helicity_renewal as h

f, Q, require = c.f, c.Q, c.require


def cutoff(v, radius_squared=4, inside=True):
    return [f.clean({k: a for k, a in row.items()
                    if (sum(j*j for j in k) <= radius_squared) == inside})
            for row in v]


def equal(v, w, label):
    for a, b in zip(v, w):
        f.equal(a, b, label)


def datum(delta=Q(1)/10, contrast=Q(3)/2, epsilon=Q(1)):
    v = {(0, 1, 0): Q(1)/2, (0, -1, 0): Q(1)/2,
         (0, 2, 0): delta/2, (0, -2, 0): delta/2,
         (0, 0, 1): epsilon/2, (0, 0, -1): epsilon/2}
    w = {(x, y, 0): Q(1)/2 if y == 0 else -contrast*delta/4
         for x in (-1, 1) for y in (-1, 0, 1)}
    return [f.clean(v), {}, w]


def symbolic_family():
    d, a, e = sy.symbols('delta c epsilon', real=True)
    zero = sy.zeros(3, 1)

    def mode(k, v):
        return {k: sy.Matrix(v)/2, tuple(-j for j in k): sy.Matrix(v)/2}

    def add(*fields):
        result = defaultdict(lambda: sy.zeros(3, 1))
        for field in fields:
            for k, v in field.items():
                result[k] += v
        return {k: v.applyfunc(sy.expand) for k, v in result.items()
                if v.applyfunc(sy.expand) != zero}

    def advect(u, v):
        result = defaultdict(lambda: sy.zeros(3, 1))
        for p, A in u.items():
            for q, B in v.items():
                k = tuple(x+y for x, y in zip(p, q))
                result[k] += sy.I*A.dot(sy.Matrix(q))*B
        return dict(result)

    def negative_leray(v):
        result = {}
        for k, A in v.items():
            r2, q = sum(j*j for j in k), sy.Matrix(k)
            result[k] = (-A+q.dot(A)*q/r2 if r2 else -A).applyfunc(sy.expand)
        return {k: v for k, v in result.items() if v != zero}

    u = add(mode((0, 1, 0), (1, 0, 0)), mode((0, 2, 0), (d, 0, 0)),
            mode((0, 0, 1), (e, 0, 0)), mode((1, 0, 0), (0, 0, 1)),
            mode((1, 1, 0), (0, 0, -a*d/2)), mode((1, -1, 0), (0, 0, -a*d/2)))
    n = negative_leray(advect(u, u))
    b = {k: v for k, v in n.items() if sum(j*j for j in k) > 4}
    expected_b = {}
    for x in (-1, 1):
        for y in (-3, -2, 2, 3):
            amplitude = d*(1-a/2) if abs(y) == 2 else -a*d*d/2
            expected_b[(x, y, 0)] = sy.Matrix([0, 0, -sy.I*x*amplitude/4])
    require(set(b) == set(expected_b), 'Every symbolic hidden output retained')
    for k in b:
        require((b[k]-expected_b[k]).applyfunc(sy.expand) == zero, 'Literal hidden source')
    L = negative_leray(add(advect(u, b), advect(b, u)))
    L = {k: v for k, v in L.items() if sum(j*j for j in k) <= 4}
    l0, l1 = -d*d*(1-a/2)/2, -d*(1-a/2-a*d*d/2)/2
    expected_L = add(mode((1, 0, 0), (0, 0, l0)),
                     mode((1, 1, 0), (0, 0, l1/2)),
                     mode((1, -1, 0), (0, 0, l1/2)))
    require(set(L) == set(expected_L), 'Every symbolic retained return retained')
    for k in L:
        require((L[k]-expected_L[k]).applyfunc(sy.expand) == zero, 'Literal retained return')
    shell = {}
    for r2 in (1, 2, 4):
        shell[r2] = sy.factor(2*sum((sy.conjugate(v).dot(L.get(k, zero))
                                   for k, v in u.items() if sum(j*j for j in k) == r2), sy.S.Zero))
    require(sy.expand(shell[1]+d*d*(1-a/2)/2) == 0, 'Radius-one exchange')
    require(sy.expand(shell[2]-a*d*d*(1-a/2-a*d*d/2)/4) == 0, 'Radius-root-two exchange')
    require(shell[4] == 0, 'No return to the radius-two parent')
    energy = sy.expand(sum((sy.conjugate(v).dot(v) for v in b.values()), sy.S.Zero))
    require(sy.expand(sum(shell.values())+2*energy) == 0, 'Classical kinetic cancellation')

    m1, m2, r = sy.symbols('m1 m2 r', positive=True)
    work = sy.expand(m1*shell[1]+m2*shell[2])
    repaired = work.subs({m1: r*m2, a: 1+r})
    desired = d*d*m2*((1-r)**2-(1+r)**2*d*d)/8
    require(sy.simplify(repaired-desired) == 0, 'General increasing radial-weight obstruction')
    dstar = (1-r)/(2*(1+r))
    require(sy.factor(desired.subs(d, dstar)-3*m2*(1-r)**4/(128*(1+r)**2)) == 0,
            'Strict positive coefficient for every 0<r<1')

    x, y, z = sy.symbols('x y z', real=True)
    pressure = e*sy.sin(x)*sy.sin(z)*(1-2*a*d*sy.cos(y)/3)
    trace_square = 2*e*sy.sin(x)*sy.sin(z)*(1-a*d*sy.cos(y))
    require(sy.expand_trig(sum(sy.diff(pressure, j, 2) for j in (x, y, z))+trace_square).expand() == 0,
            'Canonical pressure solves the complete Poisson equation')
    require(sy.expand(-sy.diff(pressure, y)+2*e*a*d*sy.sin(x)*sy.sin(y)*sy.sin(z)/3) == 0,
            'Generated transverse velocity is a physical pressure response')
    return dict(hidden_source='e_z sin(x)[delta(1-c/2)cos(2y)-c delta^2 cos(3y)/2]',
                shell_coefficients={str(k): str(v) for k, v in shell.items()},
                weighted_coefficient=str(work),
                positive_choice='r=m(1)/m(sqrt(2)) in (0,1), c=1+r, delta=(1-r)/(2(1+r))',
                positive_work='3*m(sqrt(2))*(1-r)^4/(128*(1+r)^2)',
                pressure=str(pressure), generated_transverse='-2*epsilon*c*delta*sin(x)*sin(y)*sin(z)/3')


def exact_jets():
    rows = []
    for epsilon in (Q(0), Q(1), Q(5)):
        w = datum(epsilon=epsilon)
        equal(w, cutoff(w), 'Initial support lies inside the full ball')
        f.equal(f.trace(f.jac(w)), {}, 'Literal incompressibility')
        require(all(f.ORIGIN not in row for row in w), 'Zero spatial mean')
        for row in w:
            for k, a in row.items():
                require(row[tuple(-j for j in k)] == h.conjugate(a), 'Real initial field')
        n = c.nonlinear(w)
        b = cutoff(n, inside=False)
        L = cutoff(c.linearized(w, b))
        kinetic, critical, gradient = 2*c.pairing(w, L), 2*h.sobolev_pair(w, L, 1), 2*c.pairing(w, L, True)
        require(Q(kinetic) == -Q(109)/320000, 'Negative kinetic first return')
        require(sy.simplify(critical-(291*sy.sqrt(2)-400)/320000) == 0, 'Positive critical first return')
        require(2*291**2-400**2 == 9362, 'Exact strict radical comparison')
        require(Q(gradient) == Q(91)/160000, 'Positive gradient first return')
        require(kinetic == -2*c.pairing(b, b), 'Full kinetic cancellation')
        rank = sy.Matrix(h.modes(w)).rank()
        require(rank == (2 if not epsilon else 3), 'Actual spatial dimension')
        if epsilon:
            require(bool(n[1]), 'Pressure creates the initially absent component')
        jets_rows = []
        for nu in (Q(1), Q(2)/7):
            full, pressures = c.velocity_time_jets(w, nu, 2)
            p1 = cutoff(full[1])
            observed = cutoff(c.addv(full[2], c.scale(-nu, [f.lap(v) for v in p1]),
                                     c.scale(-1, c.linearized(w, p1))))
            equal(observed, L, 'Complete viscous NS jets identify the memory derivative')
            # A Galerkin reference has the same datum and retained first jet.
            # It is not substituted for the full equation.
            closed2 = cutoff(c.addv(c.scale(nu, [f.lap(v) for v in p1]), c.linearized(w, p1)))
            difference = 2*c.pairing(w, c.addv(cutoff(full[2]), c.scale(-1, closed2)), True)
            require(difference == gradient, 'Retained gradient gap from the explicit reference')
            jets_rows.append(dict(nu=str(nu), complete_mode_counts=[len(h.modes(v)) for v in full],
                                  pressure_mode_counts=[len(p) for p in pressures]))
        cutoff_rows = []
        for radius_squared in (4, 5, 10):
            tail = cutoff(n, radius_squared, False)
            returned = cutoff(c.linearized(w, tail), radius_squared)
            d0, d1 = 2*c.pairing(w, returned), 2*c.pairing(w, returned, True)
            expected = {4: (Q(-109)/320000, Q(91)/160000),
                        5: (Q(-9)/320000, Q(-9)/160000), 10: (Q(0), Q(0))}
            require((Q(d0), Q(d1)) == expected[radius_squared], 'Complete nested-cutoff comparison')
            cutoff_rows.append(dict(radius_squared=radius_squared, hidden_modes=len(h.modes(tail)),
                                    kinetic=str(d0), gradient=str(d1)))
        rows.append(dict(epsilon=str(epsilon), spatial_rank=rank, initial_energy=str(c.pairing(w, w)),
                         initial_gradient_energy=str(c.pairing(w, w, True)), kinetic=str(kinetic),
                         critical=str(critical), gradient=str(gradient), actual_jets=jets_rows,
                         nested_cutoffs=cutoff_rows))
    return rows


def triangular_clock():
    a, d, nu, t, Z, D = sy.symbols('a delta nu t Z D', positive=True)
    kappa = a*(sy.exp(-nu*t)+2*d*sy.exp(-4*nu*t))
    remaining = a*(sy.exp(-nu*t)+d*sy.exp(-4*nu*t)/2)/nu
    require(sy.simplify(sy.diff(remaining, t)+kappa) == 0, 'Remaining parent shear is datum-fixed')
    # Z_W'+2nu D_W<=kappa Z_W. No lower bound on future smoothness is assumed.
    envelope_derivative = sy.exp(remaining)*(kappa*Z-2*nu*D+sy.diff(remaining, t)*Z)
    require(sy.simplify(envelope_derivative+2*nu*sy.exp(remaining)*D) == 0,
            'Joint evolving gradient clock pays every available triangular prefix')
    return dict(reserve='exp(a*(exp(-nu*t)+delta*exp(-4nu*t)/2)/nu)*Z_W(t)',
                initial_allowance='exp(a*(1+delta/2)/nu)*a^2*(1+c^2*delta^2)/2',
                scope='epsilon=0 exact triangular NS, every a>0 and nu>0; no all-time assertion for epsilon!=0')


if __name__ == '__main__':
    report = dict(symbolic_family=symbolic_family(), exact_fixtures=exact_jets(),
                  triangular_all_prefix_payment=triangular_clock(),
                  scope='Full Fourier identities exact; actual local intervals and all-time triangular estimate analytic, not Lean-certified')
    report['source_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(report, indent=2, sort_keys=True))
