#!/usr/bin/env python3
"""Actual affine cores and internal-pressure tests for local reserves.

The functional rigidity theorem and compact-data NS realization are
analytic in README.md. Exact algebra reuses the existing compact-core
pressure and disjoint-swirl boundary responses; no free forcing history
or autonomous finite-dimensional fluid evolution is assumed.
"""

import hashlib
import json
from pathlib import Path

import sympy as s
from transverse_strain_history import reference_pressure, spin, zero, matrix_zero

R = s.Rational


def affine_core():
    x = s.Matrix(s.symbols('x0:3', real=True))
    b = s.symbols('b0:8', real=True)
    B = s.Matrix([[b[0], b[1], b[2]], [b[3], b[4], b[5]],
                  [b[6], b[7], -b[0]-b[4]]])
    potential = -x.cross(B*x)/3

    def curl(v):
        return s.Matrix([s.diff(v[(j+2) % 3], x[(j+1) % 3])
                         -s.diff(v[(j+1) % 3], x[(j+2) % 3]) for j in range(3)])

    matrix_zero(curl(potential)-B*x, 'arbitrary trace-free affine core')
    cutoff = s.Function('chi')(x.dot(x))
    compact = curl(cutoff*potential)
    zero(sum(s.diff(compact[j], x[j]) for j in range(3)), 'cutoff curl stays solenoidal')
    return {'local_velocity': 'B x', 'trace_B': '0',
            'compact_extension': 'curl[-chi(|x|^2) x cross (Bx)/3]',
            'local_gradient_derivatives': 'all positive spatial orders vanish on the plateau'}


def pressure_cone():
    c = s.symbols('c', positive=True)
    cap, l1, l2 = s.symbols('cap lambda1 lambda2', real=True)
    lam = [l1, l2, -l1-l2]
    energies = [(cap-a)/(3*c) for a in lam]
    response = s.zeros(3)
    for i, energy in enumerate(energies):
        n = s.eye(3)[:, i]
        response += c*energy*(s.eye(3)-3*n*n.T)
    matrix_zero(response-s.diag(*lam), 'full trace-free pressure response')
    zero(sum(energies)-cap/c, 'one finite parent energy allocation')
    return {'nonnegative_under': 'cap>=max_i lambda_i',
            'pair_energies': [str(v) for v in energies],
            'pair_constant': 'c=3/(2pi L^5)', 'total_energy': 'cap/c'}


def strain_action():
    a = s.Matrix(s.symbols('a0:3', real=True))
    z = s.Matrix(s.symbols('z0:3', real=True))
    w, alpha = a.dot(a), a.dot(z)
    S = (z*a.T+a*z.T)/w-alpha*s.eye(3)/(2*w)-alpha*a*a.T/(2*w*w)
    matrix_zero(S-S.T, 'symmetric strain sending a to z')
    zero(s.trace(S), 'trace-free strain sending a to z')
    matrix_zero(S*a-z, 'all axial derivatives attainable for a nonzero')
    t = s.symbols('t0:5', real=True)
    strain = s.Matrix([[t[0], t[1], t[2]], [t[1], t[3], t[4]],
                       [t[2], t[4], -t[0]-t[3]]])
    omega = spin(2*a)
    matrix_zero(-(strain*omega+omega*strain)-spin(2*strain*a),
                'actual skew source has axial derivative S a')
    return {'domain': 'a dot a>0',
            'S': '(z a^T+a z^T)/w-(a dot z)I/(2w)-(a dot z)aa^T/(2w^2)',
            'w': 'a dot a', 'conclusion': 'S symmetric, tr S=0, S a=z'}


def opposite_histories():
    strain = s.diag(1, 1, -2)
    vort = s.Matrix([0, 0, 2])
    omega = spin(vort)
    B = strain+omega
    core = reference_pressure(strain, vort)
    matrix_zero(core-s.diag(-R(32, 35), -R(32, 35), -R(76, 35)),
                'existing nested compact strain/swirl pressure')
    kappa, c = s.symbols('kappa c', real=True)
    H = (R(32, 35)-kappa)*strain
    F = -B*B-core-H
    matrix_zero(F-kappa*strain+2*omega, 'complete physical gradient source')
    matrix_zero((F+F.T)/2-kappa*strain, 'opposite actual strain rates')
    matrix_zero(B*vort-s.Matrix([0, 0, -4]), 'same initial vorticity compression')
    e = s.symbols('e', real=True)
    rho = -4*(strain+e*(F+F.T)/2).det()
    zero(rho.subs(e, 0)-8, 'same initial strain determinant')
    zero(s.diff(rho, e).subs(e, 0)-24*kappa, 'actual determinant rate')
    zero(2*s.trace(strain*(F+F.T)/2)-12*kappa, 'actual strain norm rate')
    sigma = (F+F.T)/2
    geom = -4*sigma.det()
    correction = s.trace(F**3)/3
    cubic = -s.trace(F.T*F*F)
    zero(geom-8*kappa**3, 'first created geometric source')
    zero(correction+2*kappa**3+8*kappa, 'first created non-gradient correction')
    zero(cubic-6*kappa**3+8*kappa, 'first created complete cubic')
    zero(geom+correction-cubic, 'opposite signs require the retained correction')
    cap = R(67, 35)
    rows = []
    for sign in (1, -1):
        target = H.subs(kappa, sign)
        energies = [(cap-target[i, i])/(3*c) for i in range(3)]
        coefficients = [s.factor(v*c) for v in energies]
        if any(v < 0 for v in coefficients):
            raise ArithmeticError('negative physical parent energy')
        response = s.zeros(3)
        for i, energy in enumerate(energies):
            n = s.eye(3)[:, i]
            response += c*energy*(s.eye(3)-3*n*n.T)
        matrix_zero(response-target, 'actual positive packet allocation')
        zero(sum(energies)-R(67, 35)/c, 'identical total remote energy')
        rows.append({'kappa': sign, 'pair_energies_times_c': [str(v) for v in coefficients],
                     'strain_determinant_rate': 24*sign,
                     'first_created_geometry_coefficient': str(geom.subs(kappa, sign)/8),
                     'first_created_correction_coefficient': str(correction.subs(kappa, sign)/8),
                     'first_created_cubic_coefficient': str(cubic.subs(kappa, sign)/8)})
    return {'core_strain': 'diag(1,1,-2)', 'core_vorticity': '(0,0,2)',
            'core_pressure': [str(core[i, i]) for i in range(3)],
            'same_remote_energy': '67/(35c)=134pi L^5/105', 'rows': rows,
            'scope': 'actual initial jets and analytic short intervals; no prescribed later pressure'}


if __name__ == '__main__':
    report = {'affine_core': affine_core(), 'pressure_cone': pressure_cone(),
              'strain_action': strain_action(), 'opposite_histories': opposite_histories(),
              'analytic_rigidity': 'a fixed C2 function of the local trace-free velocity gradient with nonpositive generator on every unforced compact-data history is constant',
              'not_excluded': 'datum-dependent allowances, spatial or history reserves, and the created tensor J',
              'certification': 'exact algebra; compact NS realization and functional theorem analytic, not Lean-certified',
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    print(json.dumps(report, indent=2, sort_keys=True))
