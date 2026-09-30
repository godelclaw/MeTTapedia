#!/usr/bin/env python3
"""Signed viscous pressure flux on complete unforced NS initial fields.

Exact Gaussian-rational Fourier checks retain every parent and output on
the normalized 2*pi torus. The optional spatial quadrature uses the actual
soft selector and complete initial velocity/memory tangent. It certifies
neither a continuum history nor an arbitrary-flow nonlinear allowance.
"""

import argparse
import json
from fractions import Fraction
import pressure_history_source as f
import pressure_memory_diffusion as pm


def interacting_datum():
    """A genuine resonant child breaks the base fixture's sign symmetry."""
    u = f.fixture()
    k, v, c = (1, 1, 2), (2, 0, -1), f.QQ_I(2, -3)/13
    for i in range(3):
        u[i][k] = c*v[i]
        u[i][tuple(-q for q in k)] = f.QQ_I(c.x, -c.y)*v[i]
    return u


def exact_case(amplitude, phase):
    u = [f.scale(amplitude*phase, q) for q in interacting_datum()]
    B = f.jac(u)
    f.equal(f.trace(B), {}, 'solenoidal datum')
    E = [pm.matrix_diff(B, k) for k in range(3)]
    r = pm.pair(B, B)
    source = f.trace(f.matmul(B, B))
    p = f.green(source)
    P = f.hess(p)
    G = f.matmul(B, pm.transpose(B))
    divG = pm.tensor_divergence(G)
    parent_advection = [f.add(*(f.adv([B[j][k] for j in range(3)], B[i][k])
                               for k in range(3))) for i in range(3)]
    for i in range(3):
        f.equal(divG[i], parent_advection[i], 'complete derivative-parent advection')
    g = f.add(*(f.trace(f.matmul(Ek, Ek)) for Ek in E))
    f.equal(pm.divergence(divG), g, 'actual memory-source Poisson data')
    q = f.tensor_pressure(G)
    f.equal(q, f.green(g), 'actual source pressure')
    q_parents = f.add(*(f.green(f.trace(f.matmul(Ek, Ek))) for Ek in E))
    f.equal(q, q_parents, 'all derivative parents retained in source pressure')
    Q = f.hess(q)
    gp = f.grad(q)
    divergence_cost = pm.mean(f.dot(divG, divG))
    parent_cost = pm.mean(f.mul(r, f.add(*(pm.pair(Ek, Ek) for Ek in E))))
    source_cost = pm.mean(f.dot(gp, gp))
    if not 0 <= source_cost <= divergence_cost <= parent_cost:
        raise ArithmeticError('unweighted source projection/parent payment')

    # This positive smooth weight tests the exact flux identity. It is
    # not substituted for the nonlinear observable's soft selector.
    PI = pm.matrix_add(P, [[source if i == j else {} for j in range(3)]
                           for i in range(3)])
    f.equal(pm.pair(PI, PI), f.add(pm.pair(P, P), f.mul(source, source)),
            'actual canonical pressure flux matrix square')
    flux = f.matvec(PI, gp)
    residual = f.add(pm.pair(P, Q), f.scale(-1, f.mul(source, g)))
    f.equal(pm.divergence(flux), residual,
            'pointwise bilinear Hessian localization flux')
    # Choose one informative low moment of this fixed polynomial field.
    k = next((k for k in sorted(residual) if k != f.ORIGIN), None)
    if k is None:
        raise ArithmeticError('nonzero localization defect required')
    opposite = tuple(-i for i in k)
    wave = ({k: f.QQ_I(1)/8, opposite: f.QQ_I(1)/8} if residual[k].x
            else {k: -f.II/8, opposite: f.II/8})
    a = f.add({f.ORIGIN: f.QQ_I(1)/2}, wave)
    selected = pm.mean(f.mul(a, pm.pair(P, Q)))
    local = pm.mean(f.mul(a, f.mul(source, g)))
    boundary = pm.mean(f.dot(f.grad(a), flux))
    if selected != local-boundary or not boundary:
        raise ArithmeticError('nonzero exact selected pressure/source flux')

    nu = f.QQ_I(1)/10
    gp0 = f.grad(p)
    nl = [f.add(f.scale(-1, f.adv(u, q0)), f.scale(-1, gp0[i]))
          for i, q0 in enumerate(u)]
    ut = [f.add(q0, f.scale(nu, f.lap(ui))) for q0, ui in zip(nl, u)]
    Pt = pm.observe(pm.symmetric_product(u, ut))
    Ct = pm.matrix_scale(2*nu, G)
    DP = pm.matrix_add(Pt, pm.matrix_adv(u, P),
                       pm.matrix_scale(-nu, [[f.lap(q0) for q0 in row] for row in P]))
    nonlinear_pressure = pm.matrix_add(pm.pressure_commutator(u, f.tensor(u, u)),
        pm.matrix_scale(-1, pm.observe(pm.symmetric_product(u, gp0))))
    pm_expected = pm.matrix_add(nonlinear_pressure, pm.matrix_scale(-2*nu, Q))
    f.same_matrices(DP, pm_expected, 'complete canonical material pressure law')
    f.same_matrices(pm.matrix_add(DP, pm.observe(Ct)), nonlinear_pressure,
                    'actual positive memory source cancels observer viscosity')
    # A diagnostic solenoidal force changes the pressure generator even
    # with zero instantaneous kinetic work. It is not an internal realization.
    force = f.curl(u)
    f.equal(pm.divergence(force), {}, 'solenoidal diagnostic forcing')
    force_work = pm.mean(f.dot(u, force))
    forced_pressure = pm.observe(pm.symmetric_product(u, force))
    if force_work or all(not q0 for row in forced_pressure for q0 in row):
        raise ArithmeticError('informative zero-work forcing diagnostic')
    forced_Pt = pm.observe(pm.symmetric_product(u, [f.add(v, w) for v, w in zip(ut, force)]))
    f.same_matrices(forced_Pt, pm.matrix_add(Pt, forced_pressure),
                    'literal extra force leg in pressure evolution')
    return {'amplitude': amplitude, 'velocity_sign': phase,
            'source_gradient_square': str(source_cost),
            'source_divergence_square': str(divergence_cost),
            'local_derivative_parent_cost': str(parent_cost),
            'selected_pressure_pairing': str(selected),
            'selected_local_source_pairing': str(local),
            'nonzero_boundary_flux': str(boundary),
            'smooth_test_weight_mode': list(k),
            'diagnostic_force_kinetic_work': str(force_work),
            'diagnostic_force_pressure_modes': len(set().union(*(q0.keys()
                                                   for row in forced_pressure for q0 in row))),
            'scope': 'actual unforced initial fields; smooth test weight, not a history'}


def coefficients():
    # Signed flux: f^2 <=32 J G gives |f| <=J/2+16G.
    from sympy import symbols, Rational, expand
    J, G, D, S = symbols('J G D S')
    if expand((J/2+16*G)**2-32*J*G-(J/2-16*G)**2) != 0:
        raise ArithmeticError('boundary Young square')
    source_upper = S/2+J/2+2*D+8*(D/2)
    native = S+J+8*D
    if expand(Rational(3, 4)*native-source_upper-(S+J)/4) != 0:
        raise ArithmeticError('quarter of complete diffusion survives')
    if not (5*2+Rational(63, 95)*4 < 13 and
            5*2+Rational(4, 7)*2+Rational(10, 21)*2+Rational(44, 95)*4 < 14):
        raise ArithmeticError('full initial branch upper coefficients')
    if not (221 <= 256 and 196 <= 256 and 194 <= 256):
        raise ArithmeticError('finite full initial resource coefficients')
    return {'source_gradient_payment': 'nu ||grad q_G||_2^2 <= integral D_Phi/8',
            'selected_flux_payment': '|4nu integral grad a.(P+sI)grad q_G| <= J/2+2D',
            'augmentation': 'F_b+8(Phi-Phi_infinity)',
            'remaining_diffusion_fraction': '1/4',
            'nonlinear_compatible_history_allowance': 'OPEN'}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--quadrature', action='store_true')
    args = parser.parse_args()
    report = {'coefficients': coefficients(),
              'exact_cases': [exact_case(A, sign) for A in (1, 2) for sign in (-1, 1)]}
    if args.quadrature:
        from signed_viscous_pressure_quadrature import diagnose
        report['quadrature'] = diagnose()
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
