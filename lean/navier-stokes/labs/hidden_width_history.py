#!/usr/bin/env python3
"""Matched local fluid observations with different physical pressure rates.

The compact-data realization and actual short-time comparisons are analytic
in README.md. These exact checks retain the established radial-swirl pressure
law, its viscous scaling, and the full initial NS jets. They do not evolve
an invariant packet model or certify the continuum argument in Lean.
"""

import hashlib
import itertools
import json
from pathlib import Path

import sympy as s


def zero(expr, label):
    value = s.factor(s.together(expr))
    if value != 0:
        value = s.simplify(value)
    if value != 0:
        raise ArithmeticError((label, value))


def matrix_zero(matrix, label):
    for index, value in enumerate(matrix):
        zero(value, (label, index))


def radial_checks():
    r, a, nu = s.symbols('r a nu', positive=True)
    chi = s.Function('chi')(r)
    # After angular integration, the gradient norm differs from the radial
    # dissipation moment only by this compactly supported total derivative.
    gradient_integrand = 3*r**2*chi**2+2*r**3*chi*s.diff(chi, r)+r**4*s.diff(chi, r)**2
    zero(gradient_integrand-r**4*s.diff(chi, r)**2-s.diff(r**3*chi**2, r),
         'full gradient dissipation reduces to the radial moment')
    zero(r**4*chi*(s.diff(chi, r, 2)+4*s.diff(chi, r)/r)
         -s.diff(r**4*chi*s.diff(chi, r), r)+r**4*s.diff(chi, r)**2,
         'radial heat energy dissipation')
    amplitude, i0, i1 = s.symbols('amplitude I0 I1', positive=True)
    energy = amplitude**2*a**5*i0
    dissipation = amplitude**2*a**3*i1
    zero(2*nu*dissipation/energy-2*nu*i1/(a*a*i0),
         'width-dependent decay rate')
    k = s.symbols('k', integer=True, nonnegative=True)
    zero((amplitude**2*a**(5-2*k))/energy-a**(-2*k)/i0,
         'integer derivative norm at fixed energy')
    return {'pair_energy': 'E', 'pair_Hk_squared': 'E (Ck/C0) a^(-2k)',
            'decay_rate': '2nu I1/(a^2 I0)',
            'pair_dissipation': 'gamma E = 2nu ||grad u_pair||2^2'}


def exterior_response():
    x, y, z = s.symbols('x y z', real=True)
    L, E = s.symbols('L E', positive=True)
    variables = (x, y, z)
    potential = 0
    for sign in (-1, 1):
        displacement = s.Matrix([x-sign*L, y, z])
        rr = displacement.dot(displacement)
        # Every packet has energy E/2. Its exterior pressure depends on this
        # energy, axis and centre, and contains no profile-width parameter.
        potential -= E*(3*displacement[0]**2-rr)/(16*s.pi*rr**s.Rational(5, 2))
    response = s.hessian(potential, variables).subs({x: 0, y: 0, z: 0})
    matrix_zero(response-3*E*s.diag(-2, 1, 1)/(2*s.pi*L**5),
                'exact counter-rotating pair Hessian')
    return {'pair_constant': 'c=3/(2pi L^5)',
            'profile_independence': 'entire exterior pressure at fixed energy, axis and centre',
            'x_axis_response': [str(v) for v in response.diagonal()]}


def matched_jets():
    b, c, E, gamma = s.symbols('b c E gamma', positive=True)
    identity = s.eye(3)
    R = s.Matrix([[0, -1, 0], [1, 0, 0], [0, 0, 0]])
    zaxis = identity[:, 2]
    packets = [c*E*(identity-3*identity[:, i]*identity[:, i].T) for i in range(3)]
    H = sum(packets, s.zeros(3))
    matrix_zero(H, 'identical vanishing observed remote Hessian')
    Pcore = b*b*s.diag(s.Rational(4, 5), s.Rational(4, 5), s.Rational(2, 5))
    B0 = b*R
    B1 = -B0*B0-Pcore-H
    matrix_zero(B1-b*b*s.diag(1, 1, -2)/5, 'same full initial gradient rate')
    omega0 = 2*b*zaxis
    omega1 = B0*omega0
    omega2 = B1*omega0+B0*omega1
    matrix_zero(omega1, 'vorticity first derivative vanishes in the plateau')
    zero(2*omega0.dot(omega2)+s.Rational(16, 5)*b**4,
         'common negative vorticity-square second derivative')
    rows = []
    for rates in itertools.permutations((1, 2, 3)):
        P1 = -sum((gamma*rates[i]*packets[i] for i in range(3)), s.zeros(3))
        P1 += 2*b*(H*R-R*H)/5
        expected = c*E*gamma*s.diag(*(3*v-6 for v in rates))
        matrix_zero(P1-expected, 'complete first pressure rate')
        B2 = -B1*B0-B0*B1-P1
        omega3 = B2*omega0+2*B1*omega1+B0*omega2
        vorticity_third = 2*omega0.dot(omega3)+6*omega1.dot(omega2)
        zero(vorticity_third+8*b*b*P1[2, 2], 'full third vorticity-square derivative')
        row = {'relative_decay_rates': list(rates),
               'pressure_rate_over_c_E_gamma': [str(s.factor(v/(c*E*gamma))) for v in P1.diagonal()],
               'vorticity_square_third_over_b2_c_E_gamma': str(s.factor(vorticity_third/(b*b*c*E*gamma)))}
        rows.append(row)
        for k in range(4):
            zero(sum(v**k for v in rates)-sum(v**k for v in (1, 2, 3)),
                 ('matched scalar derivative moments', rates, k))
    for sigma in (-1, 1):
        rates = (2+sigma, 2, 2-sigma)
        row = next(item for item in rows if item['relative_decay_rates'] == list(rates))
        zero(s.sympify(row['vorticity_square_third_over_b2_c_E_gamma'])-24*sigma,
             'opposite third derivatives in the matched twins')
    return {'initial_remote_Hessian': '0', 'same_total_parent_energy': '3E',
            'same_parent_dissipation': '6 E gamma',
            'same_core_vorticity_square_second': '-16 b^4/5',
            'twin_relative_to_isolated_core': '4 sigma b^2 c E gamma t^3 + o(t^3)',
            'six_width_assignments': rows}


def decay_tensor_payment():
    q0, q1, q2, c = s.symbols('q0 q1 q2 c', nonnegative=True)
    nu = s.symbols('nu', positive=True)
    D = s.diag(q0, q1, q2)
    Q = s.trace(D)
    rate = c*(3*D-Q*s.eye(3))
    direct = -sum((c*q*(s.eye(3)-3*s.eye(3)[:, i]*s.eye(3)[:, i].T)
                   for i, q in enumerate((q0, q1, q2))), s.zeros(3))
    matrix_zero(rate-direct, 'positive decay tensor is the retained joint state')
    G = (Q*s.eye(3)-D)/(4*nu)
    zero(s.trace(G)-Q/(2*nu), 'trace is the full parent gradient norm')
    matrix_zero(rate-4*c*nu*(s.trace(G)*s.eye(3)-3*G),
                'the hidden state is oriented physical gradient dissipation')
    # In the eigenbasis of a positive tensor D, the two spectral bounds
    # reduce exactly to these nonnegative sums. This also proves op norm <=2cQ.
    for i, q in enumerate((q0, q1, q2)):
        zero(rate[i, i]+c*Q-3*c*q, 'lower spectral bound')
        zero(2*c*Q-rate[i, i]-3*c*(Q-q), 'upper spectral bound')
    zero(rate[0, 0].subs({q1: 0, q2: 0})-2*c*q0, 'sharp single-pair upper bound')
    return {'retained_tensor': 'D=sum_i gamma_i E_i n_i n_i^T >=0',
            'trace': 'Q=2nu ||grad u_parents||2^2',
            'physical_gradient_tensor': 'G=int grad u_parents (grad u_parents)^T=(QI-D)/(4nu)',
            'physical_tensor_response': '4c nu [(tr G)I-3G]',
            'pressure_rate_minus_core_commutator': 'c(3D-QI)',
            'spectral_bounds': '-c Q I <= rate <= 2c Q I',
            'operator_norm_payment': '6nu ||grad u_parents||2^2/(pi L^5)',
            'scope': 'exact initial compatible pressure rate; geometry evolution is retained as an open later defect'}


if __name__ == '__main__':
    report = {'radial_scaling': radial_checks(), 'exterior_pressure': exterior_response(),
              'actual_initial_jets': matched_jets(), 'initial_rate_payment': decay_tensor_payment(),
              'failed_closure': 'local initial velocity and pressure plus all scalar integer isotropic Sobolev norms do not determine the next pressure rate',
              'not_excluded': 'upper bounds from initial norms, compatible histories, or a finite full-datum allowance',
              'certification': 'exact algebra; physical realization and interval comparison analytic, not Lean-certified',
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    print(json.dumps(report, indent=2, sort_keys=True))
