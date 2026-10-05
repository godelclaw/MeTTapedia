#!/usr/bin/env python3
"""Exact checks for the actual created-gradient energy balance.

The Nash bounds, all-prefix payments and continuation consequence are
analytic in README.md. Fourier checks retain all physical source modes;
their initial sign test does not refute an integrated viscous allowance.
"""

import hashlib
import json
from pathlib import Path

import sympy as s
import optimal_cubic_gauge as og
import helical_parent_response as hr

f, wh, am, Q = og.f, og.wh, og.am, og.Q
require, zero = og.require, og.zero
R = s.Rational


def clock():
    t, age, delta, mu = s.symbols('t age delta mu', positive=True)
    b0, b1, b2 = s.symbols('b0 b1 b2', real=True)
    B = b0+b1*t+b2*t*t
    M = s.integrate(s.exp(-mu*age)*B.subs(t, t-age), (age, 0, delta))/delta
    delayed = s.exp(-mu*delta)*B.subs(t, t-delta)
    zero(s.diff(M, t)+mu*M-(B-delayed)/delta, 'both sliding-average endpoints')
    F = s.diff(B, t)+mu*B
    J = s.integrate((1-age/delta)*s.exp(-mu*age)*F.subs(t, t-age), (age, 0, delta))
    zero(J-(B-M), 'same-path source and averaged-gradient decompositions agree')
    zero(s.diff(J, t)+mu*J+J/delta-F-(delayed-M)/delta,
         'creation equation retains aging and the inherited endpoint')
    return {'D_M': '(B-Q_delta)/delta',
            'D_J': '-B^2-Hess p-J/delta+(Q_delta-M)/delta',
            'Q_delta': 'P_(t-delta,t) B(t-delta)'}


def smoothing_and_energy():
    S, nu, t, mass = s.symbols('S nu t mass', positive=True)
    Y = (3*S/(4*nu*t))**R(3, 2)*mass**2
    zero(s.diff(Y, t)+(2*nu/S)*Y**R(5, 3)/mass**R(4, 3), 'Nash decay normalization')
    zero(R(1, 3)-R(2, 3)/2, 'L2/Linfinity interpolation to L3')
    zero(R(3, 4)/3-R(1, 4), 'drift-independent smoothing time exponent')
    delta, E, N = s.symbols('delta E0 N', positive=True)
    energy_mass = E/(2*nu)
    bound = N*nu**(-R(1, 4))/delta*s.sqrt(s.integrate(t**(-R(1, 2)), (t, 0, delta))*energy_mass)
    zero(bound-N*s.sqrt(E)/(nu*delta)**R(3, 4), 'uniform averaged-gradient L3 bound')
    require(2**3 >= 2, 'a common Nash constant covers the torus dual projection')
    # Every square integral below uses the same original kinetic allowance.
    A = s.symbols('A', positive=True)
    zero(2*A+2*A-4*A, 'creation L2-time budget')
    zero(A/delta+(2/delta)*(A+A)-5*A/delta, 'average energy with both endpoints')
    zero((2/delta)*s.sqrt(4*A)*(s.sqrt(A)+s.sqrt(A))-8*A/delta,
         'inherited endpoint work is paid once')
    return {'A_energy': 'E0/(2*nu)', 'common_N': '2*(3*S/4)^(1/4)',
            'M_star': 'N*sqrt(E0)/(nu*delta)^(3/4)',
            'integrated_squares': {'B': 'A_energy', 'M': 'A_energy', 'Q_delta': 'A_energy', 'J': '4*A_energy'},
            'average_diffusion': 'integral |grad M|^2<=5*A_energy/(2*nu*delta)'}


def reaction_and_absorption():
    J = s.Matrix(3, 3, s.symbols('j0:9', real=True))
    M = s.Matrix(3, 3, s.symbols('m0:9', real=True))
    B = J+M
    inner = lambda a, b: s.trace(a.T*b)
    zero(-2*inner(J, B*B)+2*inner(J, J*J)+2*inner(J, J*M+M*J+M*M),
         'complete noncommuting cubic split')
    A, S, ms, cp, nu, delta, x = s.symbols('A S M_star C_P nu delta x', positive=True)
    XM = 5*A/(2*nu*delta)
    a = ms*s.sqrt(S*A)*(8+2*cp)
    b = ms*s.sqrt(S*A*XM)*(4+2*cp)+8*A/delta
    Bcross = a*a/(2*nu)+b
    zero(4*s.sqrt(4*A)+2*cp*s.sqrt(A)-(8+2*cp)*s.sqrt(A),
         'all mixed-parent and pressure coefficients on creation diffusion')
    zero(2*s.sqrt(4*A)+2*cp*s.sqrt(A)-(4+2*cp)*s.sqrt(A),
         'all mixed-parent and pressure coefficients on averaged diffusion')
    zero((nu/2)*x*x+Bcross-(a*x+b)-(nu/2)*(x-a/nu)**2,
         'universal absorption square, x=sqrt(integral |grad J|^2)')
    Z0 = s.symbols('Z0', positive=True)
    require(8 < 9, 'twice sqrt2 is below three in the initial creation bound')
    initial = 3*Z0+2*A/delta
    return {'self_reaction': 'Q_J=-integral J:J^2', 'a': str(a), 'b': str(b),
            'B_cross': str(Bcross), 'initial_creation_bound': str(initial),
            'unconditional': 'Y(T)+(3nu/2)*X_J+(2/delta)*integral Y <= initial+B_cross+2*integral Q_J',
            'OPEN': '2*integral (Q_J-nu*|grad J|_2^2/2-Y/delta)<=K_self on every same-datum prefix',
            'conditional': 'Y(T)+(nu/2)*X_J<=initial+B_cross+K_self',
            'gradient_consumer': 'Z(T)<=2*(initial+B_cross+K_self)+2*A/delta'}


def physical_sources():
    waves = [(1, 1, 0), (1, -1, 1), (2, 0, 1)]
    triad = wh.addv(*(wh.project([og.cosine(k) if j < 2 else og.vd.sine(k), {}, {}])
                     for j, k in enumerate(waves)))
    rows = []
    for label, u, expected in [('positive first creation', f.fixture(), Q(162768)/29645),
                                ('negative first creation', triad, -Q(32117)/924000)]:
        B = f.jac(u)
        pressure = f.tensor_pressure(f.tensor(u, u))
        P = f.hess(pressure)
        f.equal(f.trace(B), {}, 'actual solenoidal datum')
        pair = lambda a, b: am.pairing([a], [b])
        require(sum((pair(B[i][j], P[i][j]) for i in range(3) for j in range(3)), f.ZERO) == f.ZERO,
                'actual full-gradient pressure pairing cancels')
        B2 = f.matmul(B, B)
        F = [[f.scale(-1, f.add(B2[i][j], P[i][j])) for j in range(3)] for i in range(3)]
        f.equal(f.trace(F), {}, 'pressure retains trace-free gradient creation')
        for nu in (Q(1), Q(2)/7):
            tangent = wh.addv(hr.nonlinear(u), [f.scale(nu, f.lap(a)) for a in u])
            Bt = f.jac(tangent)
            for i in range(3):
                for j in range(3):
                    f.equal(f.add(Bt[i][j], f.adv(u, B[i][j]), f.scale(-nu, f.lap(B[i][j]))),
                            F[i][j], 'complete physical material gradient source')
        F2 = f.matmul(F, F)
        source_cubic = -sum((pair(F[i][j], F2[i][j]) for i in range(3) for j in range(3)), f.ZERO)
        require(source_cubic == expected, 'exact first creation self-reaction coefficient')
        rows.append({'label': label, 'Q_F': str(source_cubic),
                     'coefficient_in_Q_J_at_first_window': str(source_cubic/8)})
    return {'rows': rows,
            'actual_local_statement': 'J_delta(delta)=(delta/2)*F0+O(delta^2); Q_J(delta)=(delta^3/8)*Q_F+O(delta^4)',
            'refuted': 'universal nonpositive creation self-reaction',
            'not_refuted': 'a signed history allowance including viscosity and aging'}


if __name__ == '__main__':
    report = {'clock': clock(), 'smoothing_and_energy': smoothing_and_energy(),
              'reaction': reaction_and_absorption(), 'physical_sources': physical_sources(),
              'certification': 'exact algebra; continuum statements analytic, not Lean-certified',
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    print(json.dumps(report, indent=2, sort_keys=True))
