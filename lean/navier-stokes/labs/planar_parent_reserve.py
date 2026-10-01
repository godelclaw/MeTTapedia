#!/usr/bin/env python3
"""A strain-paying planar reserve and its actual three-dimensional defect.

The torus has period 2*pi and normalized volume. Gaussian-rational checks
retain every Fourier output and the canonical NS pressure. The analytic
Sobolev inequalities and continuous PDE passage are given in README.md;
scalar reserve inequalities are certified in PlanarParentReserve.lean.
No finite-mode evolution or arbitrary-data regularity claim is made.
"""

import json
from fractions import Fraction as Q

import sympy as s
import pressure_history_source as f
from cyclic_pressure_history import velocity_time_jets


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def mean(a):
    value = a.get(f.ORIGIN, f.ZERO)
    require(not value.y, 'real spatial mean')
    return Q(str(value.x))


def average(a):
    return {k: v for k, v in a.items() if k[2] == 0}


def inner(a, b):
    return mean(f.mul(a, b))


def gradient_inner(a, b):
    return mean(f.dot(f.grad(a), f.grad(b)))


def mode(k, a, sine=False):
    value = -f.II*f.QQ_I(a)/2 if sine else f.QQ_I(a)/2
    return {k: value, tuple(-j for j in k): f.QQ_I(value.x, -value.y)}


def feedback_datum(eps, phase, matched_receiver=False):
    p, k, ell = (1, 2, 0), (1, 1, 1), (0, -1, 1)
    u = [mode(p, Q(2, 5), True), mode(p, Q(-1, 5), True),
         mode((1, 0, 0), 2, True)]
    if matched_receiver:
        u[2] = f.add(u[2], mode(p, 2, True))
    for i, (v, w) in enumerate(zip((1, -1, 0), (1, 1, 1))):
        if v:
            u[i] = f.add(u[i], mode(k, eps*v))
        if w:
            u[i] = f.add(u[i], mode(ell, phase*eps*w))
    return u


def nonlinear_planar_datum():
    psi = f.add(mode((1, 0, 0), 1), mode((0, 2, 0), Q(1, 2)),
                mode((1, 2, 0), Q(1, 3)))
    return [f.scale(-1, f.diff(psi, 1)), f.diff(psi, 0),
            f.add(mode((1, 0, 0), 1), mode((0, 1, 0), 2))]


def check_split(u, nu, name):
    f.equal(f.trace(f.jac(u)), {}, 'initial solenoidality')
    for field in u:
        for k, value in field.items():
            require(field.get(tuple(-j for j in k), f.ZERO) ==
                    f.QQ_I(value.x, -value.y), 'initial reality')
    U, P = velocity_time_jets(u, nu, 1)
    v = [average(u[0]), average(u[1]), {}]
    theta = average(u[2])
    fluct = [f.add(q, f.scale(-1, average(q))) for q in u]
    reynolds = [[average(f.mul(fluct[i], fluct[j])) for j in range(3)]
                for i in range(3)]
    force = [f.scale(-1, f.add(*(f.diff(reynolds[i][j], j) for j in (0, 1))))
             for i in range(3)]
    # Keep the averaged physical pressure, including the Reynolds source.
    for i in range(3):
        expected = f.add(f.scale(f.QQ_I(nu), f.lap(average(u[i]))),
                         f.scale(-1, f.adv(v, average(u[i]))),
                         f.scale(-1, f.diff(average(P[0]), i)), force[i])
        f.equal(average(U[1][i]), expected, ('complete mean equation', name, i))
    omega = f.curl(v)[2]
    forcing = f.curl(force)[2]
    omega1 = f.add(f.diff(average(U[1][1]), 0),
                   f.scale(-1, f.diff(average(U[1][0]), 1)))
    f.equal(omega1, f.add(f.scale(f.QQ_I(nu), f.lap(omega)),
                           f.scale(-1, f.adv(v, omega)), forcing),
            'pressure-free parent curl retains the Reynolds curl')
    Z, Y, W = inner(omega, omega), gradient_inner(omega, omega), inner(f.lap(omega), f.lap(omega))
    A, B = inner(omega, forcing), gradient_inner(omega, forcing)
    C = gradient_inner(theta, force[2])
    T = -mean(f.add(*(f.mul(f.mul(f.diff(omega, i), f.diff(v[j], i)),
                             f.diff(omega, j)) for i in (0, 1) for j in (0, 1))))
    require(inner(omega, omega1) == -nu*Y+A, 'signed parent enstrophy ledger')
    require(gradient_inner(omega, omega1) == -nu*W+T+B, 'signed parent gradient ledger')
    E, D = gradient_inner(theta, theta), inner(f.lap(theta), f.lap(theta))
    G = -mean(f.add(*(f.mul(f.mul(f.diff(theta, i), f.diff(v[j], i)),
                              f.diff(theta, j)) for i in (0, 1) for j in (0, 1))))
    require(gradient_inner(theta, average(U[1][2])) == G-nu*D+C,
            'signed mean receiver ledger')
    # Full physical curl stretching: the unresolved field is not discarded.
    curl_u = f.curl(u)
    Gfull = mean(f.dot(curl_u, f.matvec(f.jac(u), curl_u)))
    full_Z_rate = mean(f.dot(curl_u, f.curl(U[1])))
    full_D = sum(gradient_inner(q, q) for q in curl_u)
    require(full_Z_rate == Gfull-nu*full_D, 'full physical enstrophy ledger')
    fluct1 = [f.add(q, f.scale(-1, average(q))) for q in U[1]]
    fluct_Z_rate = sum(gradient_inner(q, r) for q, r in zip(fluct, fluct1))
    fluct_D = sum(inner(f.lap(q), f.lap(q)) for q in fluct)
    require(fluct_Z_rate+nu*fluct_D == Gfull-G-A-C,
            'complete fluctuation ledger retains all exchanged work')
    mean_force_work = sum(inner(average(q), r) for q, r in zip(u, force))
    fluct_kinetic_work = sum(inner(q, r)+nu*gradient_inner(q, q)
                            for q, r in zip(fluct, fluct1))
    require(fluct_kinetic_work == -mean_force_work,
            'kinetic transfer is internal and signed, not an external force')
    return {'fixture': name, 'nu': str(nu), 'Z': str(Z), 'Y': str(Y), 'W': str(W),
            'A': str(A), 'B': str(B), 'C': str(C), 'receiver_E': str(E),
            'G_receiver': str(G), 'G_full': str(Gfull), 'parent_transport_T': str(T),
            'parent_gradient_rate': str(2*(-nu*W+T+B)),
            'actual_parent_reserve_rate_over_reserve': str((-nu*W+T+B)/Y+128*(-nu*Y+A)/nu**2),
            'mean_force_kinetic_work': str(mean_force_work),
            'parent_advection_nonzero': bool(f.adv(v, omega)),
            'feedback_over_reserve': str(B/Y+128*A/(nu*nu))}


def algebra_checks():
    nu, Z, Y, W = s.symbols('nu Z Y W', positive=True)
    A, B, C, G, E, D, q, r, rp = s.symbols('A B C G E D q r rp', real=True)
    R = 8*s.sqrt(Y)*s.exp(64*Z/nu**2)/nu
    J = R*(B/Y+128*A/nu**2)
    Zp, Yp = -2*nu*Y+2*A, -nu*W+256*Z*Y/nu+2*B
    rate = s.diff(R, Z)*Zp+s.diff(R, Y)*Yp
    expected = J-4*s.exp(64*Z/nu**2)*W/s.sqrt(Y)-128*R*(Y-Z)/nu
    require(s.simplify(rate-expected) == 0, 'complete parent reserve derivative')
    V = E*(s.exp(2*r)-1)
    Vp = s.diff(V, E)*(2*G-2*nu*D+2*C)+s.diff(V, r)*rp
    residual = 2*(s.exp(2*r)-1)*C+2*E*s.exp(2*r)*(rp+q)
    # The difference is nonpositive when |G| <= q E and r >= 0.
    identity = Vp+2*s.Abs(G)+2*nu*(s.exp(2*r)-1)*D-residual
    require(s.simplify(identity-2*((s.exp(2*r)-1)*G+s.Abs(G)-E*s.exp(2*r)*q)) == 0,
            'receiver reserve retains both signed replenishment sources')
    return {'parent_reserve': str(R), 'feedback': str(J),
            'receiver_reserve': str(V), 'symbolic_differentiation': 'PASS'}


def main():
    rows = []
    for nu in (Q(1, 100), Q(1, 5), Q(1), Q(3)):
        planar = check_split(nonlinear_planar_datum(), nu, 'interacting planar profiles')
        require(planar['parent_advection_nonzero'], 'parent is not an autonomous heat solution')
        require(all(planar[k] == '0' for k in ('A', 'B', 'C')), 'no omitted planar feedback')
        require(planar['parent_transport_T'] == '1', 'nonzero nonlinear gradient production')
        if nu == Q(1, 100):
            require(Q(planar['parent_gradient_rate']) > 0, 'actual parent gradient grows initially')
        rows.append(planar)
        for eps in (Q(1, 2), Q(1), Q(2)):
            for phase in (-1, 1):
                row = check_split(feedback_datum(eps, phase), nu, 'three-dimensional feedback')
                require(Q(row['Z']) == Q(1, 2) and Q(row['Y']) == Q(5, 2), 'original parent norms')
                require(Q(row['A']) == 2*phase*eps**2 and Q(row['B']) == 10*phase*eps**2,
                        'exact signed parent replenishment')
                require(row['C'] == '0' and row['receiver_E'] == '2', 'unchanged receiver resource')
                require(Q(row['feedback_over_reserve']) == phase*eps**2*(4+256/nu**2),
                        'explicit signed reserve defect')
                if nu == Q(1, 5) and eps == 1:
                    require(Q(row['actual_parent_reserve_rate_over_reserve']) ==
                            (4803 if phase == 1 else -8005),
                            'actual unforced parent reserve can increase')
                rows.append(dict(row, epsilon=str(eps), phase=phase))
        for phase in (-1, 1):
            row = check_split(feedback_datum(Q(1), phase, True), nu, 'nonzero receiver forcing')
            require(Q(row['C']) == -Q(5, 2)*phase and row['receiver_E'] == '12',
                    'retained nonzero receiver forcing work')
            rows.append(dict(row, epsilon='1', phase=phase))
    print(json.dumps({'algebra': algebra_checks(), 'fixtures': rows,
                      'scope': 'exact initial PDE identities and scalar algebra; continuous history analysis in README'}, indent=2))


if __name__ == '__main__':
    main()
