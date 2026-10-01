#!/usr/bin/env python3
"""Nonnegative pressure-endpoint completion on full unforced coframe jets.

Z=grad u+(grad I)^T cancels pressure but retains impulse deformation.
Every Gaussian-rational Fourier output is retained on the 2*pi torus.
The actual local stochastic/time realization is analytic. These checks
do not prove a finite signed allowance or a positive total-production
time window and do not refute unforced regularity.
"""

import json
import pressure_history_source as f
import pressure_memory_diffusion as pm
from pressure_impulse_history import matrix_transport, vector_transport
from signed_viscous_pressure import interacting_datum
from joint_coframe_pressure import require, identity, metric_pair, quadratic_jets


def matrix_subtract(V, W):
    return pm.matrix_add(V, pm.matrix_scale(-1, W))


def receiver(B, Q):
    return [f.add(*(f.mul(B[i][k], f.diff(Q[k][j], i))
                    for i in range(3) for k in range(3))) for j in range(3)]


def check():
    u, nu = interacting_datum(), f.QQ_I(1)/10
    B = f.jac(u)
    gp = f.grad(f.tensor_pressure(f.tensor(u, u)))
    P = f.jac(gp)
    H1 = vector_transport(u, u, nu)
    u1 = [f.add(v, f.scale(-1, w)) for v, w in zip(H1, gp)]
    B1 = f.jac(u1)
    gp1 = f.grad(f.tensor_pressure(pm.symmetric_product(u, u1)))
    u2 = [f.add(v, f.scale(-1, f.adv(u1, q)), f.scale(-1, w))
          for v, q, w in zip(vector_transport(u, u1, nu), u, gp1)]
    f.equal(pm.divergence(u1), {}, 'full first unforced NS tangent')
    f.equal(pm.divergence(u2), {}, 'full second unforced NS tangent')
    B2 = f.jac(u2)
    H2 = [f.add(v, f.scale(-1, f.adv(u1, q)))
          for v, q in zip(vector_transport(u, H1, nu), u)]
    I2 = [f.add(v, f.scale(-1, w)) for v, w in zip(H2, u2)]
    A2 = f.jac(I2)
    Q0, Q1 = identity(), pm.matrix_add(B, pm.transpose(B))
    N1 = pm.matrix_scale(-1, Q1)
    N2 = pm.matrix_add(matrix_transport(u, N1, nu),
        pm.matrix_scale(-1, pm.transpose(B1)), pm.matrix_scale(-1, B1),
        pm.matrix_scale(-1, f.matmul(pm.transpose(B), N1)),
        pm.matrix_scale(-1, f.matmul(N1, B)))
    Q2 = pm.matrix_add(pm.matrix_scale(-1, N2), pm.matrix_scale(2, f.matmul(N1, N1)))
    A0 = [[{} for _ in range(3)] for _ in range(3)]
    Bj, Aj, Hj, Qj = [B, B1, B2], [A0, P, A2], [B, f.jac(H1), f.jac(H2)], [Q0, Q1, Q2]
    ATj = list(map(pm.transpose, Aj))
    Zj = [pm.matrix_add(V, W) for V, W in zip(Bj, ATj)]
    for n in range(3):
        f.same_matrices(matrix_subtract(Zj[n], pm.transpose(Zj[n])),
            matrix_subtract(pm.matrix_scale(2, matrix_subtract(Bj[n], pm.transpose(Bj[n]))),
                            matrix_subtract(Hj[n], pm.transpose(Hj[n]))),
            ('actual physical antisymmetric gradient reconstructed with both parents', n))
    source1 = matrix_subtract(f.matmul(P, B), f.matmul(pm.transpose(B), P))
    f.same_matrices(source1, pm.matrix_scale(-1, pm.transpose(source1)),
                    'first pressure-generated completion source is antisymmetric')
    f.same_matrices(pm.matrix_add(Zj[1], pm.matrix_adv(u, B),
        pm.matrix_scale(-nu, [[f.lap(v) for v in row] for row in B])),
        pm.matrix_scale(-1, f.matmul(B, B)), 'actual initial completed gradient rate has no Hessian')
    f.same_matrices(pm.matrix_add(Zj[2], pm.matrix_adv(u1, B), pm.matrix_adv(u, Zj[1]),
        pm.matrix_scale(-nu, [[f.lap(v) for v in row] for row in Zj[1]])),
        pm.matrix_add(pm.matrix_scale(-1, f.matmul(Zj[1], B)),
                      pm.matrix_scale(-1, f.matmul(B, B1)), source1),
        'actual completed gradient first rate derivative retains all impulse deformation')

    qZ = quadratic_jets(Zj, Qj, Zj)
    qB = quadratic_jets(Bj, Qj, Bj)
    qAT = quadratic_jets(ATj, Qj, ATj)
    cross = quadratic_jets(Bj, Qj, ATj)
    for n in range(3):
        f.equal(qZ[n], f.add(qB[n], f.scale(2, cross[n]), qAT[n]),
                ('nonnegative pressure-endpoint completion with all joint time jets', n))
    T1 = receiver(B, Q1)
    T2 = [f.add(f.scale(2, v), w) for v, w in zip(receiver(B1, Q1), receiver(B, Q2))]
    endpoint2 = 2*pm.mean(f.dot(T1, gp))
    require(endpoint2 == -pm.mean(cross[2]), 'endpoint integration by parts retains transpose of impulse')
    adjoint1 = [f.add(v, f.adv(u, q), f.scale(nu, f.lap(q))) for v, q in zip(T2, T1)]
    endpoint3 = 3*pm.mean(f.add(f.dot(T1, I2), f.dot(T2, gp)))
    response2 = pm.mean(f.add(f.dot(I2, T1), f.scale(2, f.dot(gp, adjoint1))))
    comm2 = pm.mean(f.add(f.dot(T2, gp), f.scale(2, f.dot(T1, gp1))))
    require(endpoint3-response2 == comm2, 'full adjoint history test retains plus diffusion and endpoints')

    cost0 = f.add(*(pm.pair(pm.matrix_diff(B, j), pm.matrix_diff(B, j)) for j in range(3)))
    cost1 = f.add(*(f.add(f.scale(2, pm.pair(pm.matrix_diff(B, j),
        pm.matrix_add(pm.matrix_diff(Zj[1], j), f.matmul(B, pm.matrix_diff(Q1, j))))),
        metric_pair(pm.matrix_diff(B, j), Q1, pm.matrix_diff(B, j))) for j in range(3)))
    source_work1 = pm.pair(B, source1)
    f.equal(f.add(qZ[1], f.adv(u, qZ[0]), f.scale(-nu, f.lap(qZ[0]))),
            f.scale(-2*nu, cost0), 'full initial completed metric generator')
    f.equal(f.add(qZ[2], f.adv(u1, qZ[0]), f.adv(u, qZ[1]), f.scale(-nu, f.lap(qZ[1]))),
            f.add(f.scale(2, source_work1), f.scale(-2*nu, cost1)),
            'full evolving completed metric generator with retained source and diffusion')
    work = pm.mean(source_work1)
    require(work == f.QQ_I(296646304).x/10405395 and work > 0,
            'strict adverse source first jet on actual unforced data')
    require(pm.mean(qZ[1]) == -2*nu.x*pm.mean(cost0), 'actual total initial dissipation remains')
    require(pm.mean(qZ[2]) == 2*work-2*nu.x*pm.mean(cost1), 'complete integrated second production')
    # A solenoidal force can have zero instantaneous kinetic work while
    # retaining nonzero rotational work in the completed gradient.
    alpha = pm.mean(pm.pair(B, B))/pm.mean(f.dot(u, u))
    force = [f.add(f.scale(-1, f.lap(v)), f.scale(-f.QQ_I(alpha), v)) for v in u]
    f.equal(pm.divergence(force), {}, 'forced filter retains solenoidal canonical pressure')
    require(pm.mean(f.dot(u, force)) == 0, 'zero initial kinetic force work')
    Jf = f.jac(force)
    rotational_force = matrix_subtract(Jf, pm.transpose(Jf))
    forced_u1 = [f.add(v, w) for v, w in zip(u1, force)]
    forced_I1 = [f.add(v, f.scale(-1, w)) for v, w in zip(gp, force)]
    forced_Z1 = pm.matrix_add(f.jac(forced_u1), pm.transpose(f.jac(forced_I1)))
    f.same_matrices(forced_Z1, pm.matrix_add(Zj[1], rotational_force),
                    'literal forced velocity and impulse retain exactly antisymmetric force gradient')
    forced_square1 = f.add(f.scale(2, pm.pair(B, forced_Z1)), metric_pair(B, Q1, B))
    f.equal(f.add(forced_square1, f.adv(u, qZ[0]), f.scale(-nu, f.lap(qZ[0]))),
            f.add(f.scale(2, pm.pair(B, rotational_force)), f.scale(-2*nu, cost0)),
            'full forced completion generator retains force curl despite zero kinetic work')
    force_work = pm.mean(pm.pair(B, rotational_force))
    require(force_work > 0, 'strict positive rotational force work at zero initial kinetic force work')
    return {'viscosity': str(nu.x), 'source_work_initial': '0', 'source_work_first_jet': str(work),
            'actual_completed_metric_first_jet': str(pm.mean(qZ[1])),
            'actual_completed_metric_second_jet': str(pm.mean(qZ[2])),
            'full_diffusion_initial': str(pm.mean(cost0)), 'full_diffusion_first_jet': str(pm.mean(cost1)),
            'endpoint_second_jet': str(endpoint2), 'endpoint_third_jet': str(endpoint3),
            'adjoint_response_second_jet': str(response2),
            'forced_filter_kinetic_work_initial': '0',
            'forced_filter_rotational_work_initial': str(force_work),
            'forced_filter_scope': 'explicit fixed solenoidal force at initial time; not the imported singular construction',
            'failed_claim': 'the completed pressure-free source always has nonpositive integrated work',
            'scope': 'all actual unforced/coframe initial jets retained; smooth local stochastic realization analytic',
            'not_refuted': 'finite signed full-datum allowance, complete production monotonicity or unforced regularity'}


if __name__ == '__main__':
    print(json.dumps(check(), indent=2))
