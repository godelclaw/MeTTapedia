#!/usr/bin/env python3
"""Selected pressure-square first variation on complete smooth NS tangents.

Every Fourier output on the normalized 2*pi torus is retained, with exact
Gaussian rational coefficients. The nonconstant smooth test selector is
bounded between 1/4 and 3/4. It tests the pressure adjoint and its gradient
gauge, not the identification of the candidate's physical excess ratio.
The complete nonlinear and viscous tangent is used. No time-history
payment or closed Galerkin evolution is asserted.
"""

import json
from fractions import Fraction
import pressure_history_source as f
import pressure_memory_diffusion as pm
import pressure_source_production as production
import reciprocal_parent_history as reciprocal


def vector_equal(a, b, label):
    for j in range(3):
        f.equal(a[j], b[j], (label, j))


def selector(mode, sine=False):
    opposite = tuple(-q for q in mode)
    c = -f.II/8 if sine else f.QQ_I.one/8
    return {f.ORIGIN: f.QQ_I.one/2, mode: c,
            opposite: f.QQ_I(c.x, -c.y)}


def negative_gradient_projection(v):
    return f.grad(f.green(pm.divergence(v)))


def pressure_variation(u, tangent):
    return pm.observe(pm.symmetric_product(u, tangent))


def informative_selector(P, drift):
    p2 = pm.pair(P, P)
    for k in sorted(p2, key=lambda q: (sum(j*j for j in q), q)):
        if k == f.ORIGIN or not sum(q*c for q, c in zip(k, drift)):
            continue
        # The quadrature relative to a nonzero pressure-square coefficient
        # makes the drift transport visible in the spatial mean.
        return k, bool(p2[k].x)
    raise ArithmeticError('fixture needs a nonzero drift-selection interaction')


def check(u, nu, label, fixed_selector=None):
    f.equal(pm.divergence(u), {}, (label, 'actual solenoidal velocity'))
    B = f.jac(u)
    s = f.trace(f.matmul(B, B))
    nonlinear, p = reciprocal.nonlinear_source(u)
    P = f.hess(p)
    ut = production.vector_add(nonlinear,
                              [f.scale(f.QQ_I(nu), f.lap(q)) for q in u])
    f.equal(pm.divergence(ut), {}, (label, 'complete NS tangent'))
    Pt = pressure_variation(u, ut)
    source_tangent = f.scale(2, f.trace(f.matmul(B, f.jac(ut))))
    f.same_matrices(Pt, f.hess(f.green(source_tangent)),
                    (label, 'actual differentiated Poisson source'))

    drift = (2, -3, 5)
    mode, sine = fixed_selector or informative_selector(P, drift)
    a = selector(mode, sine)
    aP = pm.matrix_scalar(a, P)
    chi = f.tensor_pressure(aP)
    vN = production.vector_scale(2, f.grad(chi))
    N = pm.matrix_scale(2, aP)
    vector_equal(vN, negative_gradient_projection(pm.tensor_divergence(N)),
                 (label, 'literal negative Helmholtz gradient projection'))

    stress_dual = production.vector_scale(4, f.matvec(f.hess(chi), u))
    local_dual = production.vector_scale(-2, f.matvec(pm.transpose(B), vN))
    gauge = f.scale(4, f.dot(u, f.grad(chi)))
    vector_equal(production.vector_add(stress_dual,
                                      production.vector_scale(-1, local_dual)),
                 f.grad(gauge), (label, 'full cotangent gradient gauge'))
    selected_tangent = f.scale(2, f.mul(a, pm.pair(P, Pt)))
    first_variation = pm.mean(selected_tangent)
    for name, v in [('stress', stress_dual), ('local', local_dual)]:
        if pm.mean(f.dot(v, ut)) != first_variation:
            raise ArithmeticError((label, name, 'actual selected first variation'))
    if pm.mean(f.dot(f.grad(gauge), ut)):
        raise ArithmeticError((label, 'gradient does work on a solenoidal tangent'))

    # A selected pressure adjoint retains nonlocal weight derivatives.
    # Replacing it by a times the local Poisson source loses physical work.
    naive_chi = f.mul(a, s)
    naive_dual = production.vector_scale(-4,
                                        f.matvec(pm.transpose(B), f.grad(naive_chi)))
    naive_work = pm.mean(f.dot(naive_dual, ut))
    naive_defect = naive_work-first_variation
    if not naive_defect:
        raise ArithmeticError((label, 'fixture must expose lost selector response'))

    # Pointwise Cauchy has an exact sum-of-squares witness, independent
    # of the sign, orientation, scale or phase of the parents.
    r, v2, ell2 = pm.pair(B, B), f.dot(vN, vN), f.dot(local_dual, local_dual)
    gap = f.add(f.scale(4, f.mul(r, v2)), f.scale(-1, ell2))
    minors = []
    for j in range(3):
        for i in range(3):
            for k in range(i+1, 3):
                q = f.add(f.mul(B[i][j], vN[k]), f.scale(-1, f.mul(B[k][j], vN[i])))
                minors.append(f.mul(q, q))
    f.equal(gap, f.scale(4, f.add(*minors)),
            (label, 'normalized dual diffusion sum-of-squares'))

    # A constant drift changes a fixed Eulerian selected derivative.
    # The complete material pressure production retains its transport.
    boosted = [f.add(q, {f.ORIGIN: f.QQ_I(c)}) for q, c in zip(u, drift)]
    boosted_nonlinear, boosted_p = reciprocal.nonlinear_source(boosted)
    f.equal(boosted_p, p, (label, 'canonical pressure under constant drift'))
    boosted_ut = production.vector_add(boosted_nonlinear,
                                      [f.scale(f.QQ_I(nu), f.lap(q)) for q in boosted])
    boosted_Pt = pressure_variation(boosted, boosted_ut)
    material = pm.matrix_add(Pt, pm.matrix_adv(u, P))
    boosted_material = pm.matrix_add(boosted_Pt, pm.matrix_adv(boosted, P))
    f.same_matrices(material, boosted_material,
                    (label, 'full material pressure is drift invariant'))
    boosted_selected = pm.mean(f.scale(2, f.mul(a, pm.pair(P, boosted_Pt))))
    transport_shift = pm.mean(f.scale(2, f.mul(a, pm.pair(P,
                            pm.matrix_add(pm.matrix_adv(boosted, P),
                                          pm.matrix_scale(-1, pm.matrix_adv(u, P)))))))
    if boosted_selected-first_variation != -transport_shift:
        raise ArithmeticError((label, 'Eulerian selected work retains drift compensation'))
    boosted_local_work = pm.mean(f.dot(local_dual, boosted_ut))
    if boosted_local_work != boosted_selected:
        raise ArithmeticError((label, 'same local cotangent on boosted actual tangent'))

    # For an auxiliary advected-diffused test selector, a_t is a separate
    # first-variation leg. This is not the law of the reserve's ratio.
    at = f.add(f.scale(f.QQ_I(nu), f.lap(a)), f.scale(-1, f.adv(u, a)))
    p2 = pm.pair(P, P)
    selector_work = pm.mean(f.mul(at, p2))
    material_work = pm.mean(f.scale(2, f.mul(a, pm.pair(P, material))))
    diffusion_work = pm.mean(f.scale(f.QQ_I(nu), f.mul(f.lap(a), p2)))
    if first_variation+selector_work != material_work+diffusion_work:
        raise ArithmeticError((label, 'full varying-weight chain rule'))

    return {'datum': label, 'viscosity': str(nu),
            'selector': '1/2+'+('sin' if sine else 'cos')+'(k.x)/4',
            'selector_mode': list(mode), 'selector_range': ['1/4', '3/4'],
            'selected_pressure_velocity_variation': str(first_variation),
            'naive_local_source_work': str(naive_work),
            'lost_selector_response': str(naive_defect),
            'receiver_square': str(pm.mean(v2)),
            'cotangent_cauchy_gap': str(pm.mean(gap)),
            'drift_eulerian_work_change': str(boosted_selected-first_variation),
            'compensating_drift_transport': str(transport_shift),
            'auxiliary_selector_tangent_work': str(selector_work),
            'scope': 'complete initial-state NS tangent; no arbitrary-history bound'}


def main():
    cases = [check(production.resonant_datum(sign), Fraction(1, 10),
                   'resonant 3D datum sign '+str(sign))
             for sign in (-1, 1)]
    cases += [check(reciprocal.seed(Fraction(1, 5), phase), Fraction(1, 100),
                    'interacting parents phase '+str(phase), ((1, 0, 0), False))
              for phase in (-1, 1)]
    if not any(c['drift_eulerian_work_change'] != '0' for c in cases):
        raise ArithmeticError('fixtures must expose nonzero drift transport')
    print(json.dumps({'checks': cases, 'full_fourier_outputs': True,
                      'time_history_estimate': False}, indent=2))


if __name__ == '__main__':
    main()
