#!/usr/bin/env python3
"""Exact geometry checks for the actual created-gradient history.

The continuum correction estimate and conditional continuation argument
are analytic in README.md. The cyclic fixture is an actual NS initial
field, with all source modes retained, not a closed matrix evolution.
"""

import hashlib
import json
from pathlib import Path

import sympy as s
import optimal_cubic_gauge as og
import helical_parent_response as hr

f, wh, Q = og.f, og.wh, og.Q
require, zero = og.require, og.zero
R = s.Rational


def traceless(prefix):
    a = s.symbols(prefix + '0:8', real=True)
    return s.Matrix([[a[0], a[1], a[2]], [a[3], a[4], a[5]],
                     [a[6], a[7], -a[0]-a[4]]])


def sym(a):
    return (a+a.T)/2


def dev(a):
    return a-s.trace(a)*s.eye(3)/3


def algebra():
    J, M = traceless('j'), traceless('m')
    B, strain = J+M, sym(J)
    q = -s.trace(J.T*J*J)
    zero(q+4*strain.det()-s.trace(J**3)/3,
         'created cubic equals strain determinant plus non-gradient correction')
    zero(s.trace(B**3)-s.trace(J**3)-3*s.trace(J*J*M)
         -3*s.trace(J*M*M)-s.trace(M**3),
         'all noncommuting inherited terms in the Betchov correction')
    # Embed an arbitrary trace-free two-dimensional matrix, without an
    # assumption of symmetry or rank one.
    a, b, c = s.symbols('a b c', real=True)
    planar = s.Matrix([[a, b, 0], [c, -a, 0], [0, 0, 0]])
    zero(s.trace(planar.T*planar**2), 'planar created cubic vanishes')
    zero(sym(planar).det(), 'planar created strain determinant vanishes')
    # Ordered trace-free eigenvalues with positive middle eigenvalue b.
    b, c = s.symbols('b c', nonnegative=True)
    vals = (-b-c, b, c)
    norm = sum(x*x for x in vals)
    zero(2*b*norm+4*vals[0]*vals[1]*vals[2]-4*b**3,
         'middle-eigenvalue upper bound with exact nonnegative remainder')
    return {'pointwise': '-J:J^2=-4*det(sym J)+tr(J^3)/3',
            'integrated_correction': '-integral tr(J^2 M+J M^2+M^3/3)',
            'planar_cubic': '0', 'spectral_remainder_when_lambda2_nonnegative': '4*lambda2^3'}


def evolution():
    x, y, z, h, k = s.symbols('x y z h k', real=True)
    strain = s.Matrix([[x, z, h], [z, y, k], [h, k, -x-y]])
    a1, a2, a3 = s.symbols('a1 a2 a3', real=True)
    axial = s.Matrix([a1, a2, a3])
    omega = s.Matrix([[0, -a3, a2], [a3, 0, -a1], [-a2, a1, 0]])
    zero(s.trace(strain**4)-s.trace(strain**2)**2/2,
         'trace-free three-dimensional symmetric quartic identity')
    self_part = 4*s.trace(strain**2*dev(strain**2+omega**2))
    target = (R(2, 3)*s.trace(strain**2)**2
              +4*(strain*axial).dot(strain*axial)
              -R(4, 3)*s.trace(strain**2)*axial.dot(axial))
    zero(self_part-target, 'full strain and rotation self-production')
    delta = s.symbols('delta', positive=True)
    rho = -4*strain.det()
    zero(4*s.trace(strain**3)/delta+3*rho/delta,
         'cubic aging coefficient')
    variation = sym(traceless('v'))
    e = s.symbols('e', real=True)
    second = s.diff(-4*(strain+e*variation).det(), e, 2).subs(e, 0)
    zero(second+8*s.trace(strain*variation**2),
         'signed diffusion term in the determinant chain rule')
    J, M, endpoint = traceless('j'), traceless('m'), traceless('q')
    B = J+M
    pressure_dev = sym(traceless('p'))
    pressure = pressure_dev-s.trace(B*B)*s.eye(3)/3
    DJ = -B*B-pressure-J/delta+(endpoint-M)/delta
    sigma, om = sym(J), (J-J.T)/2
    mixed = sym(J*M+M*J+M*M)
    forcing = -dev(mixed+pressure)+sym(endpoint-M)/delta
    rhs = -dev(sigma*sigma+om*om)-sigma/delta+forcing
    for value in sym(DJ)-rhs:
        zero(value, 'actual strain equation retains trace and all parents')
    # These are algebraic sign calibrations, not separately prescribed
    # reachable NS jets.
    calibration = s.diag(-2, 1, 1)
    signed = [s.trace(calibration*t*t) for t in
              [s.diag(-2, 1, 1), s.diag(0, 1, -1)]]
    require(signed == [-6, 2], 'determinant diffusion has no universal sign')
    return {'D_sigma': '-dev(sigma^2+Omega^2)-sigma/delta+K',
            'K': '-dev(sym(JM+MJ+M^2)+Hess p)+sym(Q_delta-M)/delta',
            'D_rho_plus_3rho_over_delta':
                '2|sigma|^4/3+4|sigma a|^2-4|sigma|^2|a|^2/3'
                '-4tr(sigma^2 K)+8nu sum_k tr(sigma (partial_k sigma)^2)',
            'diffusion_algebraic_signs': [str(x) for x in signed]}


def constants():
    A, S, ms, nu, delta, z = s.symbols('A S Mstar nu delta z', positive=True)
    XM = 5*A/(2*nu*delta)
    ar = 2*ms*s.sqrt(S*A)
    br = R(7, 3)*ms*s.sqrt(S*A*XM)
    cr = 4*ar*ar/nu+2*br
    zero(2+R(1, 3)-R(7, 3), 'both mixed and pure-average cubic costs')
    zero(nu*z*z/4+cr-(2*ar*z+2*br)-nu*(z-4*ar/nu)**2/4,
         'integrated Betchov correction absorption square')
    zero(2-R(1, 2)-R(1, 4)-R(5, 4), 'remaining diffusion after inherited payments')
    zero(R(5, 4)-1-R(1, 4), 'signed determinant consumer diffusion')
    zero(4*S*(nu/(16*S))-nu/4, 'critical exceptional geometry absorption')
    zero(4/(2*delta)-2/delta, 'baseline middle strain paid by window aging')
    return {'a_R': str(ar), 'b_R': str(br), 'C_R': str(cr),
            'correction_payment': '2 integral |R_Betchov|<=nu X_J/4+C_R',
            'baseline_lambda2': '1/(2delta)', 'critical_excess_threshold': 'nu/(16S)',
            'conditional': 'Y(T)+nu X_J<=C0 exp(4 integral b)',
            'OPEN': 'control the positive middle-strain excess along every actual compatible history'}


def cyclic_source():
    u = [og.vd.sine((0, 1, 0)), og.vd.sine((0, 0, 1)), og.vd.sine((1, 0, 0))]
    B = f.jac(u)
    p = f.tensor_pressure(f.tensor(u, u))
    f.equal(p, {}, 'cyclic initial pressure is exactly zero')
    F = [[f.scale(-1, a) for a in row] for row in f.matmul(B, B)]
    f.equal(f.trace(F), {}, 'complete source remains trace-free')
    for nu in (Q(1), Q(2)/7):
        ut = wh.addv(hr.nonlinear(u), [f.scale(nu, f.lap(a)) for a in u])
        Bt = f.jac(ut)
        for i in range(3):
            for j in range(3):
                f.equal(f.add(Bt[i][j], f.adv(u, B[i][j]), f.scale(-nu, f.lap(B[i][j]))),
                        F[i][j], 'actual full material gradient source')
    strain = [[f.scale(Q(1)/2, f.add(F[i][j], F[j][i])) for j in range(3)] for i in range(3)]
    cube = f.trace(f.matmul(f.matmul(F, F), F))
    straincube = f.trace(f.matmul(f.matmul(strain, strain), strain))
    F2 = f.matmul(F, F)
    cubic = f.scale(-1, f.add(*(f.mul(F[i][j], F2[i][j])
                             for i in range(3) for j in range(3))))
    f.equal(cubic, {}, 'cyclic first self-reaction vanishes pointwise')
    f.equal(f.add(f.scale(-Q(4)/3, straincube), f.scale(Q(1)/3, cube)), cubic,
            'geometric production and non-gradient correction cancel pointwise')
    require(cube.get(f.ORIGIN, f.ZERO) == -Q(3)/8, 'nonzero integrated source trace cube')
    require(straincube.get(f.ORIGIN, f.ZERO) == -Q(3)/32, 'integrated source strain cube')
    origin = s.Matrix([[s.Rational(f.evaluate(a)) for a in row] for row in strain])
    require(origin.eigenvals() == {-s.Integer(1): 1, R(1, 2): 2}, 'created expansive middle strain')
    return {'integral_tr_F3': '-3/8', 'integral_det_sym_F': '-1/32',
            'Q_F': '0 pointwise', 'sym_F_origin_eigenvalues': ['-1', '1/2', '1/2'],
            'first_window': {'Q_geometry': 'delta^3/64+O(delta^4)',
                             'R_Betchov': '-delta^3/64+O(delta^4)',
                             'Q_J': 'O(delta^4)', 'middle_strain_at_origin': 'delta/4+O(delta^2)'},
            'refuted': 'applying the integrated zero trace-cube identity to J as if it were a Jacobian',
            'not_refuted': 'the signed created-strain history allowance or arbitrary-data regularity'}


if __name__ == '__main__':
    result = {'algebra': algebra(), 'evolution': evolution(), 'constants': constants(),
              'cyclic_source': cyclic_source(),
              'certification': 'exact identities and constants; continuum estimates analytic, not Lean-certified',
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    print(json.dumps(result, indent=2, sort_keys=True))
