#!/usr/bin/env python3
"""Exact pressure-history identities on complete finite Fourier sources.

The torus has period 2*pi. Coefficients are Gaussian rationals, and every
convolution output is retained. The velocity and its tangent are actual
smooth unforced NS initial data and their full PDE right-hand side, not a
closed Galerkin evolution. The general PDE identities and the separated
whole-space source estimate are explained in README.md.
"""

import json
import itertools
from sympy.polys.domains import QQ_I

ZERO = QQ_I.zero
II = QQ_I.imag_unit
ORIGIN = (0, 0, 0)


def clean(f):
    return {k: a for k, a in f.items() if a}


def add(*fields):
    result = {}
    for field in fields:
        for k, a in field.items():
            result[k] = result.get(k, ZERO) + a
    return clean(result)


def scale(c, f):
    return clean({k: c*a for k, a in f.items()})


def mul(f, g):
    result = {}
    for k, a in f.items():
        for ell, b in g.items():
            q = tuple(x+y for x, y in zip(k, ell))
            result[q] = result.get(q, ZERO)+a*b
    return clean(result)


def diff(f, j):
    return clean({k: II*k[j]*a for k, a in f.items()})


def lap(f):
    return clean({k: -sum(x*x for x in k)*a for k, a in f.items()})


def green(f):
    return {k: a/sum(x*x for x in k) for k, a in f.items() if k != ORIGIN}


def grad(f):
    return [diff(f, j) for j in range(3)]


def hess(f):
    return [grad(diff(f, i)) for i in range(3)]


def dot(v, w):
    return add(*(mul(a, b) for a, b in zip(v, w)))


def adv(v, f):
    return dot(v, grad(f))


def jac(v):
    return [grad(f) for f in v]


def matmul(a, b):
    return [[add(*(mul(a[i][k], b[k][j]) for k in range(3)))
             for j in range(3)] for i in range(3)]


def matvec(a, v):
    return [dot(row, v) for row in a]


def trace(a):
    return add(*(a[i][i] for i in range(3)))


def curl(v):
    return [add(diff(v[2], 1), scale(-1, diff(v[1], 2))),
            add(diff(v[0], 2), scale(-1, diff(v[2], 0))),
            add(diff(v[1], 0), scale(-1, diff(v[0], 1)))]


def tensor(v, w):
    return [[mul(a, b) for b in w] for a in v]


def tensor_pressure(a):
    return green(add(*(diff(diff(a[i][j], i), j)
                       for i in range(3) for j in range(3))))


def equal(f, g, label):
    residual = add(f, scale(-1, g))
    if residual:
        raise ArithmeticError((label, next(iter(residual.items()))))


def same_matrices(a, b, label):
    for i in range(3):
        for j in range(3):
            equal(a[i][j], b[i][j], (label, i, j))


def evaluate(f):
    value = sum(f.values(), ZERO)
    if value.y:
        raise ArithmeticError('nonreal value at the origin')
    return value.x


def value_dot(v, w):
    return sum(a*b for a, b in zip(v, w))


def value_matvec(a, v):
    return [value_dot(row, v) for row in a]


def fixture():
    # Neither odd symmetry nor a stationary receiver is imposed. Each
    # polarization is perpendicular to its mode; negative modes are conjugate.
    data = [((1, 0, 1), (1, 2, -1), QQ_I(1, 2)/3),
            ((0, 1, 1), (2, 1, -1), QQ_I(-2, 1)/5),
            ((1, 1, 0), (1, -1, 2), QQ_I(1, -1)/7),
            ((2, -1, 1), (1, 1, -1), QQ_I(2, 3)/11)]
    result = [{}, {}, {}]
    for k, v, c in data:
        for j in range(3):
            result[j][k] = c*v[j]
            result[j][tuple(-x for x in k)] = QQ_I(c.x, -c.y)*v[j]
    return [clean(f) for f in result]


def check(nu):
    u = fixture()
    B = jac(u)
    BB = matmul(B, B)
    source = trace(BB)
    equal(trace(B), {}, 'incompressible datum')
    if source.get(ORIGIN, ZERO):
        raise ArithmeticError('pressure source has nonzero mean')
    p = green(source)
    equal(p, tensor_pressure(tensor(u, u)), 'two pressure representations')
    P = hess(p)
    gp = grad(p)
    ut = [add(scale(nu, lap(u[i])), scale(-1, adv(u, u[i])), scale(-1, gp[i]))
          for i in range(3)]
    Bt = jac(ut)
    equal(trace(Bt), {}, 'full unforced RHS is solenoidal')
    st = add(trace(matmul(Bt, B)), trace(matmul(B, Bt)))
    if st.get(ORIGIN, ZERO):
        raise ArithmeticError('pressure-time source has nonzero mean')
    pt = green(st)
    pt_tensor = [[add(mul(ut[i], u[j]), mul(u[i], ut[j]))
                  for j in range(3)] for i in range(3)]
    equal(pt, tensor_pressure(pt_tensor), 'independent actual pressure time derivative')
    Dp = add(pt, adv(u, p), scale(-nu, lap(p)))
    Ds = add(st, adv(u, source), scale(-nu, lap(source)))
    viscous_gradient = add(*(trace(matmul(
        [[diff(B[i][j], k) for j in range(3)] for i in range(3)],
        [[diff(B[i][j], k) for j in range(3)] for i in range(3)])) for k in range(3)))
    expected_Ds = scale(-2, add(trace(matmul(BB, B)), trace(matmul(B, P)),
                               scale(nu, viscous_gradient)))
    equal(Ds, expected_Ds, 'actual material-parabolic pressure source')
    comm = add(adv(u, p), scale(-1, green(adv(u, source))))
    equal(Dp, add(green(expected_Ds), comm), 'inverse-Laplacian transport commutator')

    # The velocity-tensor version isolates the dissipation-paid channel.
    stress = tensor(u, u)
    transport_stress = [[adv(u, stress[i][j]) for j in range(3)] for i in range(3)]
    transport_comm = add(adv(u, p), scale(-1, tensor_pressure(transport_stress)))
    reaction = tensor_pressure([[add(mul(gp[i], u[j]), mul(u[i], gp[j]))
                                 for j in range(3)] for i in range(3)])
    gradient_stress = [[add(*(mul(diff(u[i], k), diff(u[j], k)) for k in range(3)))
                        for j in range(3)] for i in range(3)]
    viscous = scale(-2*nu, tensor_pressure(gradient_stress))
    equal(Dp, add(transport_comm, scale(-1, reaction), viscous),
          'complete tensor pressure history')

    # Moving directions and the advected Hessian must be differentiated together.
    curvature = [[dot(gp, [diff(diff(u[k], i), j) for k in range(3)])
                  for j in range(3)] for i in range(3)]
    PH = hess(Dp)
    BtP = matmul([list(row) for row in zip(*B)], P)
    PB = matmul(P, B)
    DP = [[add(diff(diff(pt, i), j), adv(u, P[i][j]), scale(-nu, lap(P[i][j])))
           for j in range(3)] for i in range(3)]
    same_matrices(DP, [[add(PH[i][j], scale(-1, BtP[i][j]), scale(-1, PB[i][j]),
                           scale(-1, curvature[i][j])) for j in range(3)] for i in range(3)],
                  'Hessian transport and velocity curvature')

    omega = curl(u)
    omt = curl(ut)
    om_material = [add(omt[i], adv(u, omega[i])) for i in range(3)]
    bw = matvec(B, omega)
    for i in range(3):
        equal(om_material[i], add(bw[i], scale(nu, lap(omega[i]))), 'vorticity material law')
    v = list(map(evaluate, omega))
    vt = list(map(evaluate, om_material))
    dv = [evaluate(lap(f)) for f in omega]
    pvalue = [[evaluate(f) for f in row] for row in P]
    prate = [[evaluate(add(diff(diff(pt, i), j), adv(u, P[i][j])))
              for j in range(3)] for i in range(3)]
    v2 = value_dot(v, v)
    if not v2:
        raise ArithmeticError('fixture needs nonzero vorticity')
    sigma = value_dot(v, list(map(evaluate, bw)))/v2
    pdir = value_dot(v, value_matvec(pvalue, v))/v2
    direct = (2*value_dot(vt, value_matvec(pvalue, v))
              +value_dot(v, value_matvec(prate, v))-2*pdir*value_dot(v, vt))/v2
    J = evaluate(dot(omega, matvec([[add(PH[i][j], scale(-1, curvature[i][j]))
                                    for j in range(3)] for i in range(3)], omega)))/v2
    Vp = (evaluate(dot(omega, matvec([[lap(f) for f in row] for row in P], omega)))
          +2*value_dot(dv, value_matvec(pvalue, v))-2*pdir*value_dot(v, dv))/v2
    if direct-(-2*sigma*pdir+J+nu*Vp):
        raise ArithmeticError('normalized directional-pressure cancellation')

    bvalue = [[evaluate(f) for f in row] for row in B]
    bmaterial = [[evaluate(add(Bt[i][j], adv(u, B[i][j]))) for j in range(3)]
                 for i in range(3)]
    stretch = value_matvec(bvalue, v)
    stretch_rate = [a+b for a, b in zip(value_matvec(bmaterial, v), value_matvec(bvalue, vt))]
    sigma_rate = (value_dot(vt, stretch)+value_dot(v, stretch_rate)
                  -2*sigma*value_dot(v, vt))/v2
    G = sum((a-sigma*b)**2 for a, b in zip(stretch, v))/v2
    blap = [[evaluate(lap(f)) for f in row] for row in B]
    visc_stretch = [a+b for a, b in zip(value_matvec(blap, v), value_matvec(bvalue, dv))]
    Vs = nu*(value_dot(dv, stretch)+value_dot(v, visc_stretch)
             -2*sigma*value_dot(v, dv))/v2
    if sigma_rate-(-sigma*sigma-pdir+G+Vs):
        raise ArithmeticError('actual directional strain rate')
    h = -pdir-QQ_I(9)/14*sigma*sigma+QQ_I(1)/10*v2
    h_rate = -direct-QQ_I(9)/7*sigma*sigma_rate+QQ_I(1)/5*value_dot(v, vt)
    predicted_h = (-QQ_I(23)/7*sigma*h-QQ_I(81)/98*sigma**3+QQ_I(37)/70*sigma*v2
                   -QQ_I(9)/7*sigma*(G+Vs)-J-nu*Vp+nu/5*value_dot(v, dv))
    if h_rate-predicted_h:
        raise ArithmeticError('complete instantaneous pressure-input defect')

    viscous_zz = hess(viscous)[2][2]
    sampled = []
    for corner in itertools.product((0, 1), repeat=3):
        value = evaluate({k: (-1 if sum(a*b for a, b in zip(k, corner)) % 2 else 1)*c
                          for k, c in viscous_zz.items()})
        sampled.append((value, corner))
    if nu and not (min(sampled)[0] < 0 < max(sampled)[0]):
        raise ArithmeticError('fixture must exhibit both signs of the viscous pressure source')

    # The integrated kinetic loss is checked independently by Parseval.
    energy_rate = 2*dot(u, ut).get(ORIGIN, ZERO)
    gradient_energy = add(*(dot(grad(f), grad(f)) for f in u)).get(ORIGIN, ZERO)
    if energy_rate != -2*nu*gradient_energy:
        raise ArithmeticError('actual kinetic production')

    # A solenoidal force can alter pressure history without doing kinetic
    # work at this instant. This is a forcing diagnostic, not an unforced
    # realization of such a force or a singularity construction.
    force = omega
    equal(trace(jac(force)), {}, 'solenoidal diagnostic force')
    force_work = dot(u, force).get(ORIGIN, ZERO)
    if force_work:
        raise ArithmeticError('diagnostic force should have zero instantaneous global work')
    force_pressure = tensor_pressure([[add(mul(u[i], force[j]), mul(force[i], u[j]))
                                      for j in range(3)] for i in range(3)])
    forced_ut = [add(a, b) for a, b in zip(ut, force)]
    forced_pt = green(scale(2, trace(matmul(B, jac(forced_ut)))))
    equal(forced_pt, add(pt, force_pressure), 'exact external force entry in pressure history')
    if not force_pressure:
        raise ArithmeticError('diagnostic force must change pressure history')

    # Rigid advection of the entire datum changes pt but not Dp.
    c = [QQ_I(2), QQ_I(-1), QQ_I(3)]
    shifted_u = [add(f, {ORIGIN: cj}) for f, cj in zip(u, c)]
    shifted_ut = [add(ut[i], scale(-1, dot([{ORIGIN: cj} for cj in c], grad(u[i]))))
                  for i in range(3)]
    shifted_pt = green(scale(2, trace(matmul(B, jac(shifted_ut)))))
    equal(add(shifted_pt, adv(shifted_u, p), scale(-nu, lap(p))), Dp,
          'Galilean covariance of the full pressure history')
    return {'viscosity': str(nu), 'input_modes': len(set().union(*[set(f) for f in u])),
            'pressure_modes': len(p), 'pressure_rate_modes': len(pt),
            'directional_pressure': str(pdir), 'directional_pressure_rate': str(direct),
            'material_pressure_Hessian_and_curvature': str(J),
            'viscous_direction_correction': str(nu*Vp),
            'instantaneous_pressure_input': str(h), 'instantaneous_input_rate': str(h_rate),
            'tensor_viscous_source_zz': str(evaluate(viscous_zz)),
            'viscous_source_minimum': str(min(sampled)[0]),
            'viscous_source_minimum_point_over_pi': min(sampled)[1],
            'viscous_source_maximum': str(max(sampled)[0]),
            'viscous_source_maximum_point_over_pi': max(sampled)[1],
            'diagnostic_force_instantaneous_work': str(force_work),
            'diagnostic_force_pressure_modes': len(force_pressure),
            'gradient_energy': str(gradient_energy)}


if __name__ == '__main__':
    print(json.dumps({'status': 'all exact coefficient checks passed',
                      'cases': [check(QQ_I(0)), check(QQ_I(2)/7)],
                      'scope': 'actual unforced initial tangents; no recurrent-growth claim'}, indent=2))
