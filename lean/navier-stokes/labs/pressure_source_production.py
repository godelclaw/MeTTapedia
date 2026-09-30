#!/usr/bin/env python3
"""Complete signed canonical-pressure-square production on actual NS tangents.

Gaussian rational coefficients retain every Fourier output on the normalized
2*pi torus. These are smooth initial states and their full PDE tangents,
not a closed Galerkin evolution or a finite-history bound. The spatial
weight test retains the localization flux; it is not an excess selector.
"""

import json
from fractions import Fraction
import pressure_history_source as f
import pressure_memory_diffusion as pm
import reciprocal_parent_history as reciprocal


def trace_product(A, B):
    return f.trace(f.matmul(A, B))


def matrix_laplacian(A):
    return [[f.lap(q) for q in row] for row in A]


def vector_add(*vectors):
    return [f.add(*(v[i] for v in vectors)) for i in range(3)]


def vector_scale(c, v):
    return [f.scale(c, q) for q in v]


def resonant_datum(sign=1):
    u = f.fixture()
    # This fourth-order resonance prevents the crossed viscous mean from
    # disappearing through pairwise opposite-mode cancellation.
    for k in ((0, 0, 2), (0, 0, -2)):
        u[0] = f.add(u[0], {k: f.QQ_I(sign)/4})
        u[1] = f.add(u[1], {k: -f.QQ_I(sign)/4})
    return u


def check(u, nu, label, forcing=None):
    f.equal(pm.divergence(u), {}, (label, 'solenoidal actual velocity'))
    B = f.jac(u)
    B2 = f.matmul(B, B)
    s = f.trace(B2)
    nonlinear, p = reciprocal.nonlinear_source(u)
    P = f.hess(p)
    f.equal(p, f.tensor_pressure(f.tensor(u, u)), 'canonical pressure')
    nu = f.QQ_I(nu)
    ut = vector_add(nonlinear, [f.scale(nu, f.lap(q)) for q in u])
    force_source = {}
    if forcing is not None:
        f.equal(pm.divergence(forcing), {}, 'solenoidal external force')
        ut = vector_add(ut, forcing)
        force_source = f.scale(2, trace_product(B, f.jac(forcing)))
    f.equal(pm.divergence(ut), {}, 'full actual solenoidal PDE tangent')
    Bt = f.jac(ut)
    st = f.scale(2, trace_product(B, Bt))
    Ds = f.add(st, f.adv(u, s), f.scale(-nu, f.lap(s)))
    cubic = f.trace(f.matmul(B2, B))
    pressure = trace_product(B, P)
    crossed = f.add(*(trace_product(pm.matrix_diff(B, j), pm.matrix_diff(B, j))
                      for j in range(3)))
    strain_square = pm.pair(B, B)
    strain_gradient_square = f.add(*(pm.pair(pm.matrix_diff(B, j), pm.matrix_diff(B, j))
                                     for j in range(3)))
    for A in [B]+[pm.matrix_diff(B, j) for j in range(3)]:
        for sign in (-1, 1):
            gap = pm.matrix_add(A, pm.matrix_scale(sign, pm.transpose(A)))
            f.equal(f.add(pm.pair(A, A), f.scale(sign, trace_product(A, A))),
                    f.scale(f.QQ_I.one/2, pm.pair(gap, gap)),
                    (label, 'actual crossed trace sum of squares', sign))
    native_mass = 8*nu.x*pm.mean(f.mul(strain_square, strain_gradient_square))
    crossed_mass = pm.mean(f.scale(-4*nu, f.mul(s, crossed)))
    if abs(crossed_mass) > native_mass/2:
        raise ArithmeticError((label, 'half strain-gradient diffusion pays crossed viscosity'))
    source_reaction = f.add(f.scale(-2, cubic), f.scale(-2, pressure),
                            f.scale(-2*nu, crossed), force_source)
    f.equal(Ds, source_reaction, (label, 'complete local source evolution'))
    s2 = f.mul(s, s)
    source_gradient_square = f.dot(f.grad(s), f.grad(s))
    square_tangent = f.scale(2, f.mul(s, st))
    square_material = f.add(square_tangent, f.adv(u, s2),
                            f.scale(-nu, f.lap(s2)))
    local_production = f.scale(2, f.mul(s, source_reaction))
    f.equal(square_material, f.add(local_production,
                                    f.scale(-2*nu, source_gradient_square)),
            (label, 'complete source-square evolution'))

    Pt = pm.observe(pm.symmetric_product(u, ut))
    DP = pm.matrix_add(Pt, pm.matrix_adv(u, P),
                       pm.matrix_scale(-nu, matrix_laplacian(P)))
    pressure_production = f.scale(2, pm.pair(P, DP))
    p2 = pm.pair(P, P)
    p2t = f.scale(2, pm.pair(P, Pt))
    pressure_gradient_square = f.add(*(pm.pair(pm.matrix_diff(P, j),
                                              pm.matrix_diff(P, j))
                                       for j in range(3)))
    f.equal(f.add(p2t, f.adv(u, p2), f.scale(-nu, f.lap(p2))),
            f.add(pressure_production, f.scale(-2*nu, pressure_gradient_square)),
            (label, 'complete pressure-square evolution'))
    quantities = [('mass', p2, s2),
                  ('mass derivative', p2t, square_tangent),
                  ('signed production', pressure_production, local_production),
                  ('square diffusion', pressure_gradient_square, source_gradient_square)]
    for name, lhs, rhs in quantities:
        if pm.mean(lhs) != pm.mean(rhs):
            raise ArithmeticError((label, 'canonical pressure/source '+name))

    # The two pressure-square cotangents differ by a genuine gradient.
    # Its work vanishes against the actual solenoidal velocity tangent.
    dual = vector_scale(4, f.matvec(f.hess(s), u))
    local_dual = vector_scale(-4, f.matvec(pm.transpose(B), f.grad(s)))
    potential = f.scale(4, f.dot(u, f.grad(s)))
    for lhs, rhs in zip(vector_add(dual, vector_scale(-1, local_dual)),
                        f.grad(potential)):
        f.equal(lhs, rhs, (label, 'pressure cotangent modulo gradients'))
    if pm.mean(f.dot(dual, ut)) != pm.mean(p2t):
        raise ArithmeticError((label, 'actual canonical-pressure first variation'))
    if pm.mean(f.dot(local_dual, ut)) != pm.mean(p2t):
        raise ArithmeticError((label, 'actual local-source first variation'))

    # A variable weight does not inherit the unweighted mass identity.
    # Keep its full spatial flux, and differentiate that flux as well.
    d = f.lap(p)
    gp, gpt = f.grad(p), f.grad(f.tensor_pressure(pm.symmetric_product(u, ut)))
    dt = f.lap(f.tensor_pressure(pm.symmetric_product(u, ut)))
    identity = [[{f.ORIGIN: f.QQ_I.one} if i == j else {}
                 for j in range(3)] for i in range(3)]
    Q = pm.matrix_add(P, pm.matrix_scalar(f.scale(-1, d), identity))
    Qt = pm.matrix_add(Pt, pm.matrix_scalar(f.scale(-1, dt), identity))
    flux = f.matvec(Q, gp)
    flux_t = vector_add(f.matvec(Qt, gp), f.matvec(Q, gpt))
    residual = f.add(p2, f.scale(-1, s2))
    residual_t = f.add(p2t, f.scale(-1, square_tangent))
    f.equal(residual, pm.divergence(flux), 'pressure/source localization flux')
    f.equal(residual_t, pm.divergence(flux_t), 'full localization flux derivative')
    mode = next((k for k in sorted(residual_t) if k != f.ORIGIN), None)
    weighted = None
    if mode is not None:
        coefficient = residual_t[mode]
        opposite = tuple(-x for x in mode)
        if coefficient.x:
            a = {f.ORIGIN: f.QQ_I.one, mode: f.QQ_I.one/4, opposite: f.QQ_I.one/4}
            description = '1+cos(k.x)/2'
        else:
            a = {f.ORIGIN: f.QQ_I.one, mode: -f.II/4, opposite: f.II/4}
            description = '1+sin(k.x)/2'
        defect = pm.mean(f.mul(a, residual_t))
        retained_flux = -pm.mean(f.dot(f.grad(a), flux_t))
        if defect != retained_flux or not defect:
            raise ArithmeticError((label, 'nonzero weighted time-flux correction'))
        weighted = {'smooth_positive_fixed_weight': description, 'mode': list(mode),
                    'pressure_vs_source_derivative_defect': str(defect),
                    'retained_flux_correction': str(retained_flux)}
    production_components = [pm.mean(f.scale(-4, f.mul(s, cubic))),
                             pm.mean(f.scale(-4, f.mul(s, pressure))),
                             pm.mean(f.scale(-4*nu, f.mul(s, crossed))),
                             pm.mean(f.scale(2, f.mul(s, force_source)))]
    return {'case': label, 'viscosity': str(nu.x),
            'pressure_square_mass': str(pm.mean(p2)),
            'complete_signed_production': str(pm.mean(pressure_production)),
            'local_cubic_component': str(production_components[0]),
            'local_pressure_component': str(production_components[1]),
            'crossed_viscous_component': str(production_components[2]),
            'native_strain_gradient_diffusion_mass': str(native_mass),
            'crossed_viscosity_vs_native_mass': str(abs(crossed_mass)/native_mass)
                if native_mass else None,
            'external_force_component': str(production_components[3]),
            'pressure_square_mass_derivative': str(pm.mean(p2t)),
            'nonnegative_square_diffusion': str(2*nu.x*pm.mean(pressure_gradient_square)),
            'weighted_flux_test': weighted,
            'scope': 'exact actual smooth NS state and full tangent; no finite-history allowance'}


def main():
    cases = [check(resonant_datum(), Fraction(1, 10), 'resonant 3D datum')]
    reversed_resonance = check(resonant_datum(-1), Fraction(1, 10),
                               'reversed resonance in 3D datum')
    if cases[0]['crossed_viscous_component'] != '48/175' or \
            reversed_resonance['crossed_viscous_component'] != '-48/175':
        raise ArithmeticError('crossed viscosity must retain both actual signs')
    cases.append(reversed_resonance)
    for phase in (-1, 1):
        u = reciprocal.seed(Fraction(1, 5), phase)
        cases.append(check(u, Fraction(1, 100), 'interacting parents phase '+str(phase)))
    boosted = resonant_datum()
    for j, speed in enumerate((2, -3, 5)):
        boosted[j] = f.add(boosted[j], {f.ORIGIN: f.QQ_I(speed)})
    boost = check(boosted, Fraction(1, 10), 'resonant 3D datum with constant drift')
    for key in ('pressure_square_mass', 'complete_signed_production',
                'pressure_square_mass_derivative', 'crossed_viscous_component'):
        if boost[key] != cases[0][key]:
            raise ArithmeticError(('complete pressure production is boost invariant', key))
    cases.append(boost)
    cases.append(check(resonant_datum(), Fraction(1, 10), 'externally forced tangent',
                       forcing=resonant_datum()))
    if not any(q['crossed_viscous_component'] != '0' for q in cases):
        raise ArithmeticError('fixtures must retain a nonzero crossed viscous term')
    if cases[-1]['external_force_component'] == '0':
        raise ArithmeticError('forced comparison must retain actual forcing work')
    print(json.dumps({'checks': cases, 'full_fourier_outputs': True,
                      'time_history_estimate': False}, indent=2))


if __name__ == '__main__':
    main()
