#!/usr/bin/env python3
"""Exact evolving covariance/velocity identities and released-parent tests.

Every Fourier output and the full pressure are retained. Physical local
intervals and the original-parent release are analytic in README.md.
"""

import json
from functools import reduce

import sympy as sy

import joint_parent_boundary as j
import oscillatory_parent_release as release
from reciprocal_pattern_cycles import mode, mean

s, f, Q = j.s, j.f, j.Q


def tadd(*tensors):
    return reduce(j.tensor_add, tensors)


def transpose(A):
    return [list(row) for row in zip(*A)]


def tlap(A):
    return [[f.lap(a) for a in row] for row in A]


def tadv(u, A):
    return [[f.adv(u, a) for a in row] for row in A]


def vadv(u, v):
    return [f.adv(u, a) for a in v]


def tequal(A, B, label):
    for i, (a, b) in enumerate(zip(A, B)):
        j.vector_equal(a, b, (label, i))


def matrix_identity():
    return [[{f.ORIGIN: f.QQ_I(int(i == k))} if i == k else {}
             for k in range(3)] for i in range(3)]


def deformation(u, A):
    B = f.jac(u)
    return tadd(j.tensor_scale(-1, tadv(u, A)), f.matmul(B, A), f.matmul(A, transpose(B)))


def hessian_contract(A, u):
    return [f.add(*(f.mul(A[k][l], f.diff(f.diff(u[i], k), l))
                    for k in range(3) for l in range(3))) for i in range(3)]


def pressure(u):
    return f.green(f.trace(f.jac(vadv(u, u))))


def simple_parent():
    cx, cy, cz = (mode(tuple(int(i == k) for i in range(3)), 1) for k in range(3))
    return [f.mul(cz, cy), f.scale(-1, f.mul(cz, cx)), {}]


def resonant_parent(eps=Q(1, 10)):
    v = [{}, {}, {}]
    for k, a in [((2, 1, 0), Q(1)), ((1, 2, 0), Q(1)),
                 ((1, 0, 1), -eps), ((0, 1, 1), eps)]:
        for i, b in enumerate((-k[1], k[0], 0)):
            v[i] = f.add(v[i], mode(k, a*b))
    return v


def general_identity_checks():
    v = simple_parent()
    u = s.vector_add(s.nonlinear(v), s.vector_scale(Q(1, 3), v))
    nu = Q(2, 3)
    e3 = [{}, {}, {f.ORIGIN: f.QQ_I(1)}]
    F = tadd(matrix_identity(), j.tensor_scale(Q(1, 4), j.tensor(v, e3)))
    Sigma = j.tensor(v, v)
    M = tadd(f.matmul(F, transpose(F)), Sigma)
    B = f.jac(u)
    F_rate = tadd(j.tensor_scale(nu, tlap(F)), j.tensor_scale(-1, tadv(u, F)), f.matmul(B, F))
    M_rate = tadd(j.tensor_scale(nu, tlap(M)), deformation(u, M))
    Sigma_rate = tadd(M_rate, j.tensor_scale(-1, f.matmul(F_rate, transpose(F))),
                     j.tensor_scale(-1, f.matmul(F, transpose(F_rate))))
    gradients = [[[f.diff(a, k) for a in row] for row in F] for k in range(3)]
    K = tadd(*(f.matmul(dF, transpose(dF)) for dF in gradients))
    tequal(Sigma_rate, tadd(j.tensor_scale(nu, tlap(Sigma)), deformation(u, Sigma),
                           j.tensor_scale(2*nu, K)), 'actual covariance chain rule')
    div = j.tensor_div(Sigma)
    compact = s.vector_add(s.vector_scale(-1, vadv(u, div)),
                           s.vector_add(f.matvec(B, div), hessian_contract(Sigma, u)))
    j.vector_equal(j.tensor_div(deformation(u, Sigma)), compact,
                   'all divergence/stretching commutators cancel as stated')
    u_rate = s.vector_add(s.vector_scale(-nu, s.minus_laplacian(u)), s.nonlinear(u))
    C = s.vector_add(u, s.vector_scale(nu, j.project(div)))
    C_rate = s.vector_add(u_rate, s.vector_scale(nu, j.project(j.tensor_div(Sigma_rate))))
    raw_rhs = s.vector_add(s.vector_scale(-nu, s.minus_laplacian(C)),
                           s.vector_add(s.nonlinear(u), s.vector_scale(nu, j.project(
                               j.tensor_div(tadd(deformation(u, Sigma), j.tensor_scale(2*nu, K)))))))
    j.vector_equal(C_rate, raw_rhs, 'complete physical discrepancy equation')
    grad_chi = s.vector_add(div, s.vector_scale(-1, j.project(div)))
    stretch = s.vector_add(f.matvec(B, C), s.vector_scale(-1, vadv(u, C)))
    hess = hessian_contract(Sigma, u)
    pressure_part = f.matvec(tadd(B, transpose(B)), grad_chi)
    source = s.vector_add(s.nonlinear(u), s.vector_add(
        s.vector_scale(nu, j.project(s.vector_add(hess, pressure_part))),
        s.vector_scale(2*nu*nu, j.project(j.tensor_div(K)))))
    j.vector_equal(C_rate, s.vector_add(s.vector_scale(-nu, s.minus_laplacian(C)),
                                       s.vector_add(j.project(stretch), source)),
                   'projected transport form retains the gradient part of divergence')
    anisotropic = [f.add(*(f.diff(f.add(*(f.mul(Sigma[k][l], f.diff(u[i], l))
                                         for l in range(3))), k) for k in range(3)))
                   for i in range(3)]
    passive_rhs = s.vector_add(s.vector_scale(-nu, s.minus_laplacian(C)),
        j.project(s.vector_add(s.vector_scale(-1, vadv(u, C)),
            s.vector_add(s.vector_scale(nu, s.vector_add(anisotropic,
                                                       s.vector_scale(-1, vadv(u, grad_chi)))),
                         s.vector_scale(2*nu*nu, j.tensor_div(K))))))
    j.vector_equal(C_rate, passive_rhs,
                   'self-advection and defect stretching cancel into anisotropic diffusion')
    s.require(any(j.project(j.tensor_div(K))), 'the mean-frame diffusion source is genuinely present')
    energy_rate = s.inner(C, C_rate)+nu*s.inner(C, s.minus_laplacian(C))
    s.require(energy_rate == s.inner(C, f.matvec(B, C))+s.inner(C, source),
              'discrepancy energy cancels only incompressible transport')
    cross_rate = s.inner(u_rate, C)+s.inner(u, C_rate)
    cross_gradient = s.inner(u, s.minus_laplacian(C))
    anisotropic_energy = -s.inner(u, anisotropic)
    chi_work = s.inner(u, vadv(u, grad_chi))
    frame_work = -s.inner(u, j.tensor_div(K))
    s.require(cross_rate == -2*nu*cross_gradient-nu*anisotropic_energy
              -nu*chi_work-2*nu*nu*frame_work,
              'full signed cross-work identity retains pressure and mean-frame work')
    s.require(anisotropic_energy >= 0, 'positive covariance gives a favorable diffusion contribution')
    return dict(covariance_diffusion_source_squared=str(s.inner(j.project(j.tensor_div(K)),
                                                                 j.project(j.tensor_div(K)))),
                all_actual_PDE_identities=True,
                signed_cross_rate=str(cross_rate), covariance_diffusion=str(anisotropic_energy),
                pressure_gradient_work=str(chi_work), mean_frame_work=str(frame_work))


def released_checks(v, label):
    w, T = s.nonlinear(v), j.tensor(v, v)
    p = pressure(v)
    j.vector_equal(w, s.vector_scale(-1, s.vector_add(vadv(v, v), f.grad(p))),
                   'original envelope pressure and complete source')
    j.vector_equal(s.vector_add(w, j.project(j.tensor_div(T))), [{}, {}, {}],
                   'single-release compatibility starts exactly matched in the limit')
    Z = s.vector_add(s.nonlinear(w), j.project(j.tensor_div(deformation(w, T))))
    # Independent differentiation keeps viscosity on BOTH original fields.
    wt = s.vector_add(s.vector_scale(-1, s.minus_laplacian(w)), s.nonlinear(w))
    Tt = tadd(tlap(T), deformation(w, T))
    j.vector_equal(s.vector_add(wt, j.project(j.tensor_div(Tt))), Z,
                   'diffusion cancels from first discrepancy production')
    direction = s.vector_add(vadv(v, w), s.vector_scale(-1, vadv(w, v)))
    DN = s.vector_scale(-1, j.project(s.vector_add(vadv(v, direction), vadv(direction, v))))
    j.vector_equal(Z, s.vector_add(s.nonlinear(w), s.vector_scale(-1, DN)),
                   'independent deformation of the parent source')
    along = vadv(v, w)
    pressure_hessian = f.matvec(f.hess(p), w)
    j.vector_equal(Z, j.project(s.vector_add(vadv(v, along), pressure_hessian)),
                   'complete leading defect is directional diffusion plus pressure Hessian')
    L, P = s.inner(along, along), s.inner(w, pressure_hessian)
    work = s.inner(w, Z)
    s.require(work == -L+P, 'integrated directional diffusion and retained signed pressure work')
    norm = s.inner(Z, Z)
    s.require(norm > 0, 'the actual nonlinear evolution regenerates the discrepancy')
    if label == 'simple':
        s.require((norm, L, P, work) == (Q(26221, 967680), Q(5, 288), 0, Q(-5, 288)),
                  'exact simple physical fixture')
    if label == 'adverse':
        s.require(work == Q(-7065571, 1764), 'adverse parent still has a favorable first comparison')
    if label == 'resonant':
        s.require(P > L > 0, 'the pressure Hessian defeats the proposed universal directional payment')
    return dict(label=label, defect_squared=str(norm), directional_dissipation=str(L),
                pressure_work=str(P), signed_work=str(work),
                ordinary_source_energy=str(s.inner(w, w)), source_stretching=str(s.cubic(w)))


def polynomial_checks():
    # Both expressions have degree <=6, vanish to order2 at the stationary
    # base, and are even under epsilon -> -epsilon (translation z -> z+pi).
    # Three nonzero squared parameter values determine them exactly.
    for eps in (Q(1), Q(2), Q(3)):
        v = resonant_parent(eps)
        w = s.nonlinear(v)
        along = vadv(v, w)
        L = s.inner(along, along)
        P = s.inner(w, f.matvec(f.hess(pressure(v)), w))
        s.require(L == eps**2*(55*eps**4+20482*eps**2+11601)/330,
                  'exact directional-diffusion polynomial coefficient check')
        s.require(P == 6*eps**2*(507-55*eps**2)/55,
                  'exact pressure-Hessian polynomial coefficient check')
    s.require(not any(s.nonlinear(resonant_parent(0))), 'the unperturbed envelope is stationary')
    e = sy.symbols('e', real=True)
    L = e**2*(55*e**4+20482*e**2+11601)/330
    P = 6*e**2*(507-55*e**2)/55
    j.zero(P-L-e**2*(6651-22462*e**2-55*e**4)/330,
           'the exact failed pressure-absorption margin')
    lower = Q(6651)-Q(22462, 4)-Q(55, 16)
    s.require(lower == Q(16513, 16) > 0, 'uniform positive margin for 0<|epsilon|<=1/2')
    return dict(directional=str(L), pressure=str(P), excess=str(sy.factor(P-L)),
                positive_interval='0 < |epsilon| <= 1/2')


def growing_background_check():
    # The background belongs to the original datum. The joint release law
    # leaves the same covariance while changing W+J from alpha*w to -alpha*w.
    v = resonant_parent()
    w = s.nonlinear(v)
    alpha = Q(10000)
    dissipation = s.inner(s.minus_laplacian(w), s.minus_laplacian(w))
    stretching = s.cubic(w)
    enstrophy_rate = 2*alpha**2*(-alpha*stretching-dissipation)
    s.require(enstrophy_rate > 0 and stretching < 0,
              'a retained original background puts the same pressure defect in a growing flow')
    return dict(alpha=str(alpha), viscosity=1, original_background='-2 alpha w',
                released_velocity='-alpha w', inherited_covariance='alpha V tensor V',
                unit_source_dissipation=str(dissipation),
                actual_enstrophy_rate=str(enstrophy_rate),
                scope='strict actual rate in the limiting released state; finite-parent interval transfer analytic')


def main():
    result = dict(status='all exact checks passed', general=general_identity_checks(),
                  released=[released_checks(simple_parent(), 'simple'),
                            released_checks(release.horizontal_seed(), 'adverse'),
                            released_checks(resonant_parent(), 'resonant')],
                  parameter_family=polynomial_checks(),
                  growing_background=growing_background_check(),
                  scope='exact PDE chain rules and initial derivatives; actual intervals and parent realization analytic')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
