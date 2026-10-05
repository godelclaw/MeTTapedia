#!/usr/bin/env python3
"""Pressure homogeneity cancellation with the actual inherited history retained.

The classical pressure identity is attributed in README.md. These exact
checks cover its complete Fourier flux, the created-tensor correction,
absorption constants and a physical first-window sign test. The continuum
history estimate and short-time NS identification remain analytic.
"""

import hashlib
import json
from pathlib import Path

import sympy as s
import pressure_history_source as f

Q = f.QQ_I


def require(test, label):
    if not test:
        raise ArithmeticError(label)


def zero(expr, label):
    value = s.factor(s.together(expr))
    if value != 0:
        raise ArithmeticError((label, value))


def traceless(prefix):
    a = s.symbols(prefix+'0:8', real=True)
    return s.Matrix([[a[0], a[1], a[2]], [a[3], a[4], a[5]],
                     [a[6], a[7], -a[0]-a[4]]])


def algebra():
    J, M = traceless('j'), traceless('m')
    pressure = traceless('p')
    A = (pressure+pressure.T)/2
    B = J+M
    inherited = J*M+M*J+M*M
    zero(s.trace(B*B*A)-s.trace(J*J*A)-s.trace(inherited*A),
         'all noncommuting inherited pressure terms')
    Sigma, Omega = (J+J.T)/2, (J-J.T)/2
    axial = s.Matrix([Omega[2, 1], Omega[0, 2], Omega[1, 0]])
    zero(s.trace(J*J*A)-s.trace(Sigma*Sigma*A)-axial.dot(A*axial),
         'pressure couples the created strain and rotation')
    zero(-4*Sigma.det()-4*axial.dot(Sigma*axial)+s.Rational(4, 3)*s.trace(J**3),
         'the pressure-cancelling cubic is the trace-cube correction')
    epsilon = s.symbols('epsilon', real=True)
    pressure_rate = s.diff(-s.Rational(4, 3)*s.trace((J-epsilon*A)**3), epsilon).subs(epsilon, 0)
    zero(pressure_rate-4*s.trace(J*J*A), 'complete cubic pressure variation')
    q = s.trace(B*B)
    zero(s.trace(B**4)-q*q/2, 'three-dimensional trace-free quartic identity')
    zero(4*(s.trace(B**4)-q*q/3)-s.Rational(2, 3)*q*q,
         'self-reaction exactly balances the full-gradient pressure integral')
    return {'correction': 'C=JM+MJ+M^2',
            'strain_rotation_split': 'tr(J^2 A)=tr(Sigma^2 A)+a^T A a',
            'null_functional_warning': '-4det Sigma-4a^T Sigma a=-(4/3)tr(J^3)',
            'full_gradient': 'its spatial integral vanishes by Betchov when J=grad u'}


def absorption():
    z, x, y, m, S = s.symbols('z x y m S', nonnegative=True)
    b = m*s.sqrt(S)*(2*x+y)
    zero(z*z/2+8*b*b-4*z*b-(z-4*b)**2/2,
         'half of the joint pressure square pays the parent correction')
    zero(40*S*m*m*(x*x+y*y)-8*b*b-8*S*m*m*(x-2*y)**2,
         'exact Sobolev allocation between created and inherited derivatives')
    return {'pointwise_in_time':
                '4 int tr(J^2 A)+(1/2)||A||2^2 <=40 S Mstar^2(D_J+D_M)',
            'integrated':
                '4 int_time int_space tr(J^2 A)+(1/2)int_time ||A||2^2 <=40 S Mstar^2(X_J+X_M_star)',
            'paid_parent': 'X_M_star=5 A_E/(2nu delta), Mstar=N sqrt(E0)/(nu delta)^(3/4)',
            'OPEN': 'created-rotation alignment and the complete coercive geometric history budget'}


def mean(field):
    value = field.get(f.ORIGIN, f.ZERO)
    require(value.y == 0, 'real spatial mean')
    return value.x


def pair(B, C):
    return f.trace(f.matmul(B, C))


def symmetric(B, sign=1):
    return [[f.scale(Q(1)/2, f.add(B[i][j], f.scale(sign, B[j][i])))
             for j in range(3)] for i in range(3)]


def physical_fixture():
    u = f.fixture()
    B = f.jac(u)
    f.equal(f.trace(B), {}, 'actual solenoidal datum')
    B2 = f.matmul(B, B)
    q = f.trace(B2)
    p = f.green(q)
    f.equal(p, f.tensor_pressure(f.tensor(u, u)), 'canonical physical pressure')
    P = f.hess(p)
    A = [[f.add(P[i][j], f.scale(Q(1)/3, q) if i == j else {})
          for j in range(3)] for i in range(3)]
    f.equal(f.trace(A), {}, 'deviatoric pressure is trace-free')
    for i in range(3):
        f.equal(f.add(*(f.diff(B2[j][i], j) for j in range(3))),
                f.scale(Q(1)/2, f.diff(q, i)), 'full gradient-square column divergence')
    require(mean(pair(P, P)) == mean(f.mul(q, q)), 'full Hessian-source L2 identity')
    A2 = pair(A, A)
    joint = f.scale(4, pair(B2, A))
    require(mean(f.add(joint, A2)) == 0, 'classical complete pressure cancellation')

    # The local cancellation has a nonzero flux, even for actual gradients.
    flux_matrix = [[f.add(f.scale(4, B2[i][j]), P[i][j],
                         f.scale(-1, q) if i == j else {}) for j in range(3)] for i in range(3)]
    flux = f.matvec(flux_matrix, f.grad(p))
    density = f.add(joint, A2)
    f.equal(f.add(*(f.diff(flux[i], i) for i in range(3))), density,
            'complete pointwise pressure-cancellation flux')
    wave, coefficient = next((k, v) for k, v in sorted(density.items())
                             if k != f.ORIGIN and v.x != 0)
    sign = 1 if coefficient.x > 0 else -1
    selector = {f.ORIGIN: Q(1), wave: Q(sign)/4,
                tuple(-a for a in wave): Q(sign)/4}
    selected = mean(f.mul(selector, density))
    boundary = mean(f.dot(f.grad(selector), flux))
    require(selected > 0 and selected+boundary == 0,
            'positive smooth selector needs its nonzero boundary flux')

    # F0 is the complete physical material gradient source. The first
    # actual created tensor is delta F0/2+O(delta^2), not a new velocity gradient.
    F = [[f.scale(-1, f.add(B2[i][j], P[i][j])) for j in range(3)] for i in range(3)]
    f.equal(f.trace(F), {}, 'physical source remains trace-free')
    for nu in (Q(1), Q(2)/7):
        ut = [f.add(f.scale(nu, f.lap(u[i])), f.scale(-1, f.adv(u, u[i])),
                    f.scale(-1, f.diff(p, i))) for i in range(3)]
        Bt = f.jac(ut)
        for i in range(3):
            for j in range(3):
                f.equal(f.add(Bt[i][j], f.adv(u, B[i][j]), f.scale(-nu, f.lap(B[i][j]))),
                        F[i][j], 'complete positive-viscosity NS source')
    Sigma, Omega = symmetric(F), symmetric(F, -1)
    geometry = mean(pair(f.matmul(Sigma, Sigma), A))
    rotation = mean(pair(f.matmul(Omega, Omega), A))
    created = mean(pair(f.matmul(F, F), A))
    require(Q(geometry) == Q(5378704)/800415, 'positive physical created-strain pressure')
    require(Q(rotation) == -Q(91904)/38115, 'negative but insufficient rotation pressure')
    require(Q(created) == Q(62704)/14553 and created == geometry+rotation,
            'positive joint created pressure needs its inherited correction')
    require(mean(pair(f.matmul(B, B), B)) == 0, 'full-gradient trace cube is a null integral')
    return {'datum': 'pressure_history_source.fixture()', 'viscosities_checked': ['1', '2/7'],
            'deviatoric_pressure_square': str(mean(A2)),
            'full_gradient_joint_pressure': str(mean(joint)),
            'selected_flux': {'wave': list(wave), 'cosine_amplitude': str(s.Rational(sign, 2)),
                              'weight_range': '[1/2,3/2]', 'positive_selected_density': str(selected),
                              'boundary_flux': str(boundary)},
            'actual_first_window_coefficients_over_delta_squared':
                {'created_strain_pressure': str(geometry), 'created_rotation_pressure': str(rotation),
                 'joint_created_pressure': str(created)},
            'scope': 'actual initial NS source and analytic first-window interval; no autonomous pressure model'}


if __name__ == '__main__':
    report = {'algebra': algebra(), 'absorption': absorption(), 'physical_fixture': physical_fixture(),
              'classical_source': 'Carbone and Wilczek (2022), section 5, doi:10.1017/jfm.2022.680',
              'certification': 'exact checks; integrated PDE estimates and history intervals analytic, not Lean-certified',
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    print(json.dumps(report, indent=2, sort_keys=True))
