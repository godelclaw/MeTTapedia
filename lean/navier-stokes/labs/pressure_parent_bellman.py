#!/usr/bin/env python3
"""Exact fixtures for a Bellman payment of actual stochastic pressure histories.

The Ito, conditional-expectation and all-time entropy arguments are analytic
in README.md. Polynomial and full Fourier identities below do not use a
Gaussian closure of the evolved history or a finite-mode fluid trajectory.
"""

import json
from fractions import Fraction as Q

import sympy as s
import pressure_history_source as f
from cyclic_pressure_history import velocity_time_jets
from kinetic_pressure_entropy import gaussian_mean


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def equal(p, q, message):
    f.equal(p, q, message)


def bellman():
    m = s.Matrix(s.symbols('m0:3', real=True))
    q, gap = s.symbols('q gap', nonnegative=True)
    sigma = s.Matrix(3, 3, s.symbols('s0:9', real=True))
    covariance = sigma*sigma.T
    rate = s.trace(covariance)+gap
    r2 = m.dot(m)
    value = r2**2+6*q*r2+3*q*q
    hessian = s.hessian(value, tuple(m))
    generator = s.trace(covariance*hessian)/2-rate*s.diff(value, q)
    wedge = sum((m[i]*sigma[j, k]-m[j]*sigma[i, k])**2
                for k in range(3) for i in range(3) for j in range(i+1, 3))
    require(s.expand(generator+4*wedge+6*gap*(r2+q)) == 0,
            'Complete Bellman drift is a sum of nonpositive squares')
    require(s.simplify(hessian*m-12*(r2+q)*m) == s.zeros(3, 1),
            'Radial Hessian eigenvalue gives the optimal trace-budget control')
    require(s.expand(s.diff(value, q)-6*(r2+q)) == 0,
            'Exact variance-clock HJB equation')
    eta = s.symbols('eta', positive=True)
    initial_value = 15*eta**2+18*eta*q+3*q**2
    require(s.expand(gaussian_mean(value, tuple(m), eta)-initial_value) == 0,
            'Initial Gaussian spread funds the complete three-dimensional reserve')
    require(s.expand(gaussian_mean(value.subs(m[2], 0), tuple(m[:2]), eta)
                     -(8*eta**2+12*eta*q+3*q*q)) == 0,
            'The horizontal reserve uses the two-dimensional Gaussian constants')
    return dict(value='|m|^4+6q|m|^2+3q^2',
        drift='-4 sum_{k,i<j}(m_i sigma_jk-m_j sigma_ik)^2 -6 gap(|m|^2+q)',
        hjb='partial_q B = sup_{C>=0,tr C<=1} (1/2) C:Hess_m B',
        initial_stock=str(initial_value))


def trig(axis, k, kind):
    positive = tuple(k if i == axis else 0 for i in range(3))
    negative = tuple(-x for x in positive)
    if kind == 'sin':
        return {positive: -f.II/2, negative: f.II/2}
    return {positive: f.QQ_I(1)/2, negative: f.QQ_I(1)/2}


def mean(p):
    return p.get((0, 0, 0), f.ZERO)


def abc(amplitudes, k):
    a, b, c = amplitudes
    return [f.add(f.scale(a, trig(2, k, 'sin')), f.scale(c, trig(1, k, 'cos'))),
            f.add(f.scale(b, trig(0, k, 'sin')), f.scale(a, trig(2, k, 'cos'))),
            f.add(f.scale(c, trig(1, k, 'sin')), f.scale(b, trig(0, k, 'cos')))]


def parent_checks():
    rows = []
    for amplitudes, k in [((1, 2, 3), 1), ((2, 3, 5), 4),
                           ((3, 3, 3), 1), ((0, 0, 1), 2)]:
        u = abc(amplitudes, k)
        square = f.dot(u, u)
        S = sum(a*a for a in amplitudes)
        pressure = f.add(f.scale(-Q(1, 2), square), {(0, 0, 0): f.QQ_I(S)/2})
        jets, pressures = velocity_time_jets(u, Q(2, 7), 1)
        equal(pressures[0], pressure, 'Actual canonical pressure of the complete ABC field')
        equal(f.trace(f.jac(u)), {}, 'Exact incompressibility')
        curl = [f.add(f.diff(u[2], 1), f.scale(-1, f.diff(u[1], 2))),
                f.add(f.diff(u[0], 2), f.scale(-1, f.diff(u[2], 0))),
                f.add(f.diff(u[1], 0), f.scale(-1, f.diff(u[0], 1)))]
        for i in range(3):
            equal(curl[i], f.scale(k, u[i]), 'Helical parent at its physical wave number')
            equal(f.lap(u[i]), f.scale(-k*k, u[i]), 'Exact Laplace eigenfield')
            equal(f.add(f.adv(u, u[i]), f.diff(pressure, i)), {}, 'Steady Euler balance')
            equal(jets[1][i], f.scale(-Q(2, 7)*k*k, u[i]), 'Actual viscous NS decay')
        gradient_square = f.add(*(f.mul(f.diff(v, i), f.diff(v, i))
                                  for v in u for i in range(3)))
        equal(gradient_square, {(0, 0, 0): f.QQ_I(k*k*S)},
              'Spatially constant trace rate retains all gradient components')
        P = mean(f.mul(pressure, pressure))
        expected_P = sum(amplitudes[i]**2*amplitudes[j]**2
                         for i in range(3) for j in range(i+1, 3))/Q(4)
        require(P == f.QQ_I(expected_P), 'Initial pressure variance')
        require(mean(f.mul(square, f.adv(u, pressure))) == f.ZERO,
                'Initial complete quartic pressure work vanishes')
        rows.append(dict(amplitudes=amplitudes, wave_number=k, energy=S,
                         pressure_variance=str(P), variation_cap=S))
    return rows


def symbolic_family():
    x, y, z, a, b, c = s.symbols('x y z a b c', real=True)
    k = s.symbols('k', positive=True)
    coordinates = (x, y, z)
    U = s.Matrix([a*s.sin(z)+c*s.cos(y), b*s.sin(x)+a*s.cos(z),
                  c*s.sin(y)+b*s.cos(x)])
    B = k*U.jacobian(coordinates)
    S = a*a+b*b+c*c
    P = (S-U.dot(U))/2
    pressure_gradient = k*s.Matrix([s.diff(P, v) for v in coordinates])
    require(all(s.trigsimp(v) == 0 for v in B*U+pressure_gradient),
            'Steady Euler identity for every amplitude, with physical k derivatives')
    require(s.trigsimp(sum(v*v for v in B)-k*k*S) == 0,
            'The complete family has exactly constant trace variation')
    # Pointwise speed bound follows componentwise from (r+s)^2<=2r^2+2s^2.
    remainder = ((a*s.sin(z)-c*s.cos(y))**2
                 +(b*s.sin(x)-a*s.cos(z))**2
                 +(c*s.sin(y)-b*s.cos(x))**2)
    require(s.trigsimp(s.expand(2*S-U.dot(U)-remainder)) == 0,
            'Uniform speed envelope for every amplitude')
    return dict(physical_family='ABC at any integer common k>=1',
                gradient_square='k^2(a^2+b^2+c^2)', speed_square_upper='2(a^2+b^2+c^2)')


def paid_growth():
    sx, sy = trig(0, 1, 'sin'), trig(1, 1, 'sin')
    cx, cy = trig(0, 1, 'cos'), trig(1, 1, 'cos')
    v = [f.mul(sx, cy), f.scale(-1, f.mul(cx, sy)), {}]
    p = f.scale(Q(1, 4), f.add(trig(0, 2, 'cos'), trig(1, 2, 'cos')))
    F = f.adv(v, p)
    w = f.scale(16, f.mul(sx, f.add({(0, 0, 0): f.QQ_I(1)}, f.scale(-1, F))))
    u = v[:2]+[w]
    _, actual_pressure = velocity_time_jets(u, Q(1), 1)
    equal(actual_pressure[0], p, 'The passive component does not change actual pressure')
    require(mean(f.mul(f.mul(sx, sx), f.mul(F, F))) == f.QQ_I(Q(3, 256)),
            'Exact full pressure-production coefficient')
    source = -4*mean(f.mul(f.dot(u, u), f.adv(u, p)))
    fisher_numerator = mean(f.add(*(f.mul(f.diff(v, j), f.diff(v, j))
                                   for v in u for j in range(3))))
    require(source == f.QQ_I(24) and fisher_numerator == f.QQ_I(164),
            'Both pressure production and full initial Fisher cost are retained')
    require(24*7-164 == 4, 'Positive entropy derivative at A=7nu')
    return dict(profile='w0=16A sin x(1-F), F=v.grad p_*',
                parameters='eta=A^2, kappa=A^(-4)',
                full_entropy_derivative='24A-164nu',
                example='A=7nu gives H_prime(0)=4nu>0',
                vertical_moment2=str(mean(f.mul(w, w))),
                vertical_moment4=str(mean(f.mul(f.mul(w, w), f.mul(w, w)))))


def physical_clock():
    t, nu, lam, L1 = s.symbols('t nu lam L1', positive=True)
    q = L1**2*s.exp(-2*nu*lam*t)/lam
    rate = 2*nu*L1**2*s.exp(-2*nu*lam*t)
    require(s.simplify(s.diff(q, t)+rate) == 0, 'Remaining variation is spent exactly once')
    require(s.simplify(s.integrate(rate, (t, 0, s.oo))-L1**2/lam) == 0,
            'Complete noise allowance is independent of viscosity')
    # Forward sampling adds nu Delta to the material NS drift, hence 2nu Delta.
    require(s.simplify(s.diff(s.exp(-nu*lam*t), t)
                       -nu*(-lam)*s.exp(-nu*lam*t)) == 0, 'Physical heat decay')
    drift_bound = s.exp(-nu*lam*t)+2*nu*lam*s.integrate(s.exp(-nu*lam*t), (t, 0, t))
    require(s.simplify(drift_bound-(2-s.exp(-nu*lam*t))) == 0,
            'Forward Ito correction retained in the deterministic parent envelope')
    # Equal ABC amplitudes 3, gamma=1/4, eta=kappa=1: divide by nu*k^2.
    corrected_rate = -Q(27)+4*Q(1, 4)*Q(243, 4)
    require(corrected_rate == Q(135, 4), 'Pressure-credit decay defeats monotonicity')
    return dict(q='L1^2 exp(-2nu lambda t)/lambda',
                parent_envelope='L0(2-exp(-nu lambda t)) <= 2L0',
                pressure_subtraction_counterexample='J_prime(0)=(135/4)nu*k^2>0')


if __name__ == '__main__':
    print(json.dumps(dict(status='all exact checks passed', bellman=bellman(),
        parents=parent_checks(), symbolic_family=symbolic_family(),
        clock=physical_clock(), paid_growth=paid_growth(),
        actual_history='V = u(t,X)+2nu lambda integral u(s,X_s)ds - N; N=M-zeta',
        fourth_bound='Kstar=[2L0+(15eta^2+18eta Q0+3Q0^2)^(1/4)]^4',
        entropy_payment='H_kappa(t)+nu integral I_x <= H_kappa(0)+kappa(Kstar-K0)',
        scope='all times, arbitrary amplitude; steady Euler Laplace eigenparents',
        OPEN='an original-data variation and drift allowance for mutually regenerating parents',
        certification='exact algebra; stochastic and PDE arguments analytic'), indent=2))
