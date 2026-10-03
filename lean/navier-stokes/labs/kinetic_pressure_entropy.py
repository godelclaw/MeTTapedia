#!/usr/bin/env python3
"""Exact moments for the actual pressure-history kinetic representation.

The density construction, entropy balances and viscous interval comparison
are analytic in README.md. These checks retain the complete NS Fourier jets
and the pressure coupling in the finite raw-moment equations.
"""

import json
import math
from fractions import Fraction as Q

import sympy as s
import pressure_history_source as f
from cyclic_pressure_history import seed, velocity_time_jets
from cyclic_entropy_depletion import energy_jets, material_jets


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def gaussian_mean(expression, variables, eta):
    polynomial = s.Poly(s.expand(expression), *variables)
    result = 0
    for powers, coefficient in polynomial.terms():
        if any(n % 2 for n in powers):
            continue
        moment = s.prod(eta**(n//2)*s.factorial2(n-1) if n else 1 for n in powers)
        result += coefficient*moment
    return s.expand(result)


def gaussian_checks():
    u = s.symbols('u0:3', real=True)
    z = s.symbols('z0:3', real=True)
    eta = s.symbols('eta', positive=True)
    v = [a+b for a, b in zip(u, z)]
    square = sum(a*a for a in v)
    u2 = sum(a*a for a in u)
    require(gaussian_mean(square**2, z, eta) == s.expand(u2**2+10*eta*u2+15*eta**2),
            'Complete Gaussian fourth moment')
    for j in range(3):
        require(gaussian_mean(square*v[j], z, eta) == s.expand((u2+5*eta)*u[j]),
                'Complete Gaussian third vector moment')
    # The conservative velocity drift is -grad p, independent of v.
    y = s.symbols('v0:3', real=True)
    g = s.symbols('g0:3', real=True)
    norm2 = sum(a*a for a in y)
    for j in range(3):
        derivative = -sum(g[k]*s.diff(norm2*y[j], y[k]) for k in range(3))
        expected = -2*y[j]*sum(g[k]*y[k] for k in range(3))-norm2*g[j]
        require(s.expand(derivative-expected) == 0, 'Third raw moment retains full stress')
    require(s.expand(-sum(g[k]*s.diff(norm2**2, y[k]) for k in range(3))
                     +4*norm2*sum(g[k]*y[k] for k in range(3))) == 0,
            'Quartic pressure source')
    # Gaussian spatial Fisher information of a shifted component.
    B = s.Matrix(3, 3, s.symbols('b0:9', real=True))
    score = B.T*s.Matrix(z)/eta
    require(s.expand(gaussian_mean(score.dot(score), z, eta)
                     -sum(a*a for a in B)/eta) == 0, 'Shifted Gaussian Fisher cost')
    return dict(second='|u|^2+3eta', third='(|u|^2+5eta)u',
                fourth='|u|^4+10eta|u|^2+15eta^2', fisher='|grad z|_F^2/eta')


def constant(q):
    return {(0, 0, 0): f.QQ_I(q)} if q else {}


def moment_jets(velocity, pressure, nu, eta):
    """Raw moment equations of the identified kinetic density, through order4."""
    u = velocity[0]
    e2 = f.dot(u, u)
    L = [[[f.add(f.mul(u[i], u[j]), constant(eta) if i == j else {})
           for j in range(3)] for i in range(3)]]
    T = [[f.mul(f.add(e2, constant(5*eta)), v) for v in u]]
    K = [f.add(f.mul(e2, e2), f.scale(10*eta, e2), constant(15*eta*eta))]
    gradients = [f.grad(p) for p in pressure]
    for n in range(4):
        def passive(fields):
            return f.add(f.scale(nu, f.lap(fields[n])),
                         *(f.scale(-math.comb(n, j), f.adv(velocity[j], fields[n-j]))
                           for j in range(n+1)))
        Lnext = [[f.add(passive([tensor[i][j] for tensor in L]), *(
            f.scale(-math.comb(n, k), f.add(f.mul(velocity[k][i], gradients[n-k][j]),
                                          f.mul(gradients[n-k][i], velocity[k][j])))
            for k in range(n+1))) for j in range(3)] for i in range(3)]
        Tnext = [f.add(passive([v[i] for v in T]), *(
            f.scale(-math.comb(n, k), f.add(
                f.scale(2, f.dot(L[k][i], gradients[n-k])),
                f.mul(f.trace(L[k]), gradients[n-k][i]))) for k in range(n+1)))
            for i in range(3)]
        Knext = f.add(passive(K), *(f.scale(-4*math.comb(n, k),
                                           f.dot(gradients[k], T[n-k])) for k in range(n+1)))
        L.append(Lnext)
        T.append(Tnext)
        K.append(Knext)
    return L, T, K


def complete_checks():
    rows = []
    for scales, target in [((1, 1, 1), Q(-23, 5)), ((1, 1, 4), Q(7184, 15015))]:
        initial = [{tuple(i*j for i, j in zip(k, scales)): value
                    for k, value in field.items()} for field in seed(1)]
        for nu in [Q(0), Q(2, 7)]:
            velocity, pressure = velocity_time_jets(initial, nu, 4)
            L, T, K = moment_jets(velocity, pressure, nu, Q(1))
            # The augmented second moment has conserved global trace.
            require(all(not f.trace(tensor).get((0, 0, 0), f.ZERO) for tensor in L[1:]),
                    'Total augmented kinetic energy is conserved through all checked orders')
            if not nu:
                e = energy_jets(velocity)
                material = material_jets(e, velocity)
                physical = f.add(f.scale(8, f.mul(e[0], material[4])),
                                 f.scale(24, f.mul(material[2], material[2])))
                require(physical.get((0, 0, 0), f.ZERO) == f.QQ_I(target),
                        'Independent physical fourth-order return')
                require(K[4].get((0, 0, 0), f.ZERO) == f.QQ_I(target),
                        'Complete kinetic fourth moment has the same Euler return')
                require(all(not field.get((0, 0, 0), f.ZERO) for field in K[1:4]),
                        'First three integrated Euler returns vanish')
            rows.append(dict(scales=scales, nu=str(nu),
                             quartic_jets=[str(field.get((0, 0, 0), f.ZERO)) for field in K],
                             pressure_modes=[len(p) for p in pressure]))
    require(Q(7184, 15015) > Q(1, 3), 'Strict positive Euler margin')
    require(Q(1, 24)-Q(5, 2)/120 == Q(1, 48), 'Taylor margin')
    require(Q(1, 48)-Q(1, 192)-Q(1, 192) == Q(1, 96),
            'Both stochastic comparison and full Fisher dissipation are retained')
    return rows


def central_history():
    u = s.symbols('u0:3', real=True)
    ux = s.symbols('ux0:3', real=True)
    g = s.symbols('g0:3', real=True)
    nu = s.symbols('nu', positive=True)
    L = s.Matrix(3, 3, s.symbols('L0:9', real=True))
    Cx = s.Matrix(3, 3, s.symbols('Cx0:9', real=True))
    # Symmetrize without imposing any Gaussian closure.
    L, Cx = L+L.T, Cx+Cx.T
    Lx = Cx+s.Matrix(ux)*s.Matrix(u).T+s.Matrix(u)*s.Matrix(ux).T
    for i in range(3):
        for j in range(3):
            for k in range(3):
                cyclic = [(i, j, k), (j, i, k), (k, i, j)]
                DK = -sum(g[a]*L[b, c] for a, b, c in cyclic)
                Dproduct = sum(-g[a]*L[b, c]-u[a]*(g[b]*u[c]+u[b]*g[c])
                               -2*nu*ux[a]*Lx[b, c] for a, b, c in cyclic)
                Dtriple = -sum(g[a]*u[b]*u[c] for a, b, c in cyclic)
                Dtriple -= 2*nu*(ux[i]*ux[j]*u[k]+ux[i]*u[j]*ux[k]+u[i]*ux[j]*ux[k])
                expected = 2*nu*sum(ux[a]*Cx[b, c] for a, b, c in cyclic)
                require(s.expand(DK-Dproduct+2*Dtriple-expected) == 0,
                        'Complete central third-moment production')
    # Exact globally regular shear, theta=k*y=pi/6 and age nu*k^2*t=log2.
    q = s.symbols('q', positive=True)
    m1 = q/2
    m2 = (1-q**4/2)/2
    m3 = (3*q/2-q**9)/4
    skew = s.expand(m3-3*m1*m2+2*m1**3)
    require(skew.subs(q, s.Rational(1, 2)) == -s.Rational(297, 2048),
            'Actual shear becomes non-Gaussian at an exact positive time')
    eta = s.symbols('eta', positive=True)
    require(s.expand((m3+3*eta*m1)-3*m1*(m2+eta)+2*m1**3-skew) == 0,
            'Independent original Gaussian spread does not erase the third moment')
    return dict(source='D C_ijk=2nu sum_l[(partial_l u_i)(partial_l Sigma_jk)+cyclic]',
        shear='u=A exp(-nu*k^2*t) sin(k*y) e1',
        evaluation='k*y=pi/6, nu*k^2*t=log2',
        third_central='-297*A^3/2048, for every initial Gaussian variance eta>0')


if __name__ == '__main__':
    print(json.dumps(dict(status='all exact checks passed', gaussian=gaussian_checks(),
        histories=complete_checks(), central_history=central_history(),
        gaussian_entropy='D_G(t)+nu integral I_x=||u0||_2^2/(2eta)',
        quartic_entropy='D_kappa_prime=-nu I_x-4kappa integral grad p . T',
        consumer='sup D_kappa gives sup ||u||_4 and periodic enstrophy continuation',
        OPEN='a finite original-data payment for the signed quartic pressure history',
        certification='exact moment and Fourier algebra; density, entropy and actual interval arguments are analytic'), indent=2))
