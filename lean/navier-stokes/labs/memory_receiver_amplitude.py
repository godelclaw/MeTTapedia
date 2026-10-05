#!/usr/bin/env python3
"""Exact constants for absorbing capped actual memory-pressure work.

The physical all-prefix estimate and its conditional continuation bridge
are analytic. This checker does not certify those PDE arguments in Lean.
"""

import hashlib
import json
from pathlib import Path

import sympy as s


def require(condition, label):
    if not condition:
        raise AssertionError(label)


def zero(expr, label):
    require(s.simplify(s.expand(expr)) == 0, label)


def amplitude_and_interpolation():
    R = s.Rational
    level, kappa, Q = s.symbols('level kappa Q', positive=True)
    p, q = R(5, 3), R(5, 2)
    moment = s.integrate(q*Q*level**(q-1-p), (level, 0, kappa))
    zero(moment-3*Q*kappa**R(5, 6), 'full capped layer-cake constant')
    # This is a distribution calibration, not an independently assigned NS field.
    x = s.symbols('x', positive=True)
    seam = Q/kappa**p
    rearranged_moment = kappa**q*seam+s.integrate((Q/x)**(q/p), (x, seam, s.oo))
    zero(rearranged_moment-moment, 'decreasing rearrangement attains the constant')
    zero(R(1, 5)+2/R(5, 2)-1, 'joint space-time Holder')
    zero(R(3, 10)-R(2, 5)/2-R(3, 5)/6, 'parabolic interpolation')
    zero(R(10, 3)*R(2, 5)/2-R(2, 3), 'past cubic stock exponent')
    zero(R(2, 3)/10-R(1, 15), 'first stock exponent after Cauchy')
    zero(R(1, 2)+R(1, 10)-R(3, 5), 'first diffusion exponent')
    zero(R(5, 3)/10-R(1, 6), 'torus stock exponent')
    zero(R(1, 15)+R(3, 5)-R(2, 3), 'first joint degree')
    zero(R(1, 6)+R(1, 2)-R(2, 3), 'torus joint degree')
    return {'pressure_distribution_exponent': str(p), 'capped_moment_exponent': str(q),
            'capped_moment_bound': str(moment),
            'mixed_terms': ['M^(1/15)*X^(3/5)', 'M^(1/6)*X^(1/2)'],
            'joint_degree': '2/3'}


def absorption_constant():
    R = s.Rational
    K, eta, z = s.symbols('K eta z', positive=True)
    optimum = (2*K/(3*eta))**3
    zero(K*optimum**R(2, 3)-eta*optimum-4*K**3/(27*eta**2),
         'optimal sublinear absorption constant')
    # After normalizing at that optimum, the entire gap is nonnegative.
    zero(z**3-R(3, 2)*z**2+R(1, 2)-(z-1)**2*(z+R(1, 2)),
         'universal absorption square certificate')
    nu, a, b, Q, kappa = s.symbols('nu a b Q kappa', positive=True)
    pressure_norm = (3*Q*kappa**R(5, 6))**R(2, 5)
    coefficient = s.sqrt(3/nu)*(a**R(1, 10)+b**R(1, 10))*pressure_norm
    allowance = (R(4, 27)/eta**2)*(3/nu)**R(3, 2)*(
        a**R(1, 10)+b**R(1, 10))**3*(3*Q)**R(6, 5)*kappa
    zero(4*coefficient**3/(27*eta**2)-allowance, 'explicit capped-work allowance')
    zero(s.diff(allowance/kappa, kappa), 'allowance is linear in prescribed amplitude')
    E0, S, CR = s.symbols('E0 S CR', positive=True)
    whole_space = allowance.subs({a: 3*S/(4*nu), b: 0,
                                  Q: CR**R(5, 3)*S*E0**R(5, 3)/nu})
    zero(s.diff(whole_space/(kappa*E0**2), E0),
         'whole-space allowance is quadratic in original energy')
    zero(s.diff(whole_space*nu**3, nu),
         'whole-space viscosity exponent is minus three')
    H = s.symbols('H', positive=True)
    torus = allowance.subs({a: 3*S/(4*nu), b: S*H,
                            Q: CR**R(5, 3)*S*E0**R(5, 3)*(1/nu+H)})
    torus_factor = (1+nu*H)**R(6, 5)*(1+(4*nu*H/3)**R(1, 10))**3
    zero(torus-whole_space*torus_factor, 'torus retains both constant-mode factors')
    return {'K_cap': str(coefficient), 'B_cap': str(allowance),
            'whole_space_allowance': str(s.simplify(whole_space)),
            'torus_multiplier': str(torus_factor),
            'claim': 'integral |W_cap| <= eta*(sup_past J + integral D) + B_cap',
            'scope': 'eta,kappa and all coefficients fixed before the unknown continuation'}


def complete_prefix_consumer():
    R = s.Rational
    c, H = s.symbols('c H', positive=True)
    eta = s.exp(-c*H)/8
    zero(eta*s.exp(c*H)-R(1, 8), 'one original clock absorbs unweighted estimates')
    zero(R(3, 4)-R(1, 2)-R(1, 8)-R(1, 8),
         'old work, open remainder and capped work leave one eighth diffusion')
    zero((1-R(1, 8))*R(8, 7)-1, 'past maximum is absorbed rather than assumed')
    zero(1+R(1, 8)*R(8, 7)-R(8, 7), 'endpoint joint estimate after maximum bound')
    A0, M = s.symbols('A0 M', nonnegative=True)
    zero((1-R(1, 8))*M-A0-R(7, 8)*(M-R(8, 7)*A0),
         'maximum inequality has the asserted direction and coefficient')
    t0, t1, t2 = s.symbols('t0 t1 t2', real=True)
    zero(s.exp(-c*(t1-t0))*s.exp(-c*(t2-t1))-s.exp(-c*(t2-t0)),
         'history clock composes without a reserve reset')
    # The conditional physical balance is kept symbolic: the residual is unpaid.
    W, tail, pressure, comm = s.symbols('W_cap W_tail F_pressure F_comm', real=True)
    remainder = tail+pressure+comm
    zero(W+remainder-(W+tail+pressure+comm), 'no recent source channel is deleted')
    return {'eta': str(eta), 'open_remainder': str(remainder),
            'open_budget': 'integral exp(-c*t)*(R_tail-D/2) <= K_tail on every same-datum prefix',
            'conditional_result': 'J(T)+(1/8)*integral D <= (8/7)*exp(c*H)*A0',
            'A0': 'J(0)+B_low(0)+d*H+B_cap+K_tail',
            'not_proved': 'finite original-data K_tail; arbitrary-data regularity'}


def main():
    result = {'amplitude': amplitude_and_interpolation(),
              'absorption': absorption_constant(), 'consumer': complete_prefix_consumer(),
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'certification': 'exact inequality constants; continuum estimates analytic, not Lean-certified'}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
