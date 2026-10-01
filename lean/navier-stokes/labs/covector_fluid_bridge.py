#!/usr/bin/env python3
"""Actual covector reconstruction and its retained curl-conversion channel.

Every Gaussian-rational Fourier output is retained on the 2*pi torus.
The covector starts at the original velocity and uses the same complete
unforced NS drift and inverse-flow coframe jets. These are full initial
PDE tangents, not a closed Galerkin evolution or a regularity theorem.
The stochastic construction and positive-time realization are analytic.
"""

import json
import math
import pressure_history_source as f
import pressure_memory_diffusion as pm
from pressure_impulse_history import matrix_transport, vector_transport, vectors_equal
from signed_viscous_pressure import interacting_datum
from joint_coframe_pressure import require, identity


def vector_add(*vectors):
    return [f.add(*(v[i] for v in vectors)) for i in range(3)]


def vector_scale(c, v):
    return [f.scale(c, q) for q in v]


def projection(v):
    # P v=v+grad((-Delta)^-1 div v), retaining the zero mode.
    return vector_add(v, f.grad(f.green(pm.divergence(v))))


def metric_pair(v, Q, w):
    return f.dot(v, f.matvec(Q, w))


def square_jets(v, Q):
    return [f.add(*(f.scale(f.QQ_I(math.factorial(n)//
            (math.factorial(a)*math.factorial(b)*math.factorial(n-a-b))),
            metric_pair(v[a], Q[b], v[n-a-b]))
            for a in range(n+1) for b in range(n-a+1))) for n in range(3)]


def covector_rhs(nu, u, B, m):
    return vector_add(vector_transport(u, m, nu),
                      vector_scale(-1, f.matvec(pm.transpose(B), m)))


def connection_curl(derivatives):
    return [f.add(derivatives[(i+1) % 3][(i+2) % 3],
                  f.scale(-1, derivatives[(i+2) % 3][(i+1) % 3])) for i in range(3)]


def check():
    u, nu = interacting_datum(), f.QQ_I(1)/10
    B = f.jac(u)
    p = f.tensor_pressure(f.tensor(u, u))
    gp = f.grad(p)
    u1 = vector_add(vector_transport(u, u, nu), vector_scale(-1, gp))
    B1 = f.jac(u1)
    gp1 = f.grad(f.tensor_pressure(pm.symmetric_product(u, u1)))
    u2 = vector_add(vector_transport(u, u1, nu),
                   vector_scale(-1, [f.adv(u1, q) for q in u]), vector_scale(-1, gp1))
    m1 = covector_rhs(nu, u, B, u)
    m2 = vector_add(covector_rhs(nu, u, B, m1),
                   vector_scale(-1, [f.adv(u1, q) for q in u]),
                   vector_scale(-1, f.matvec(pm.transpose(B1), u)))
    f.equal(pm.divergence(u), {}, 'actual solenoidal 3D initial velocity')
    f.equal(pm.divergence(u1), {}, 'complete first NS tangent')
    f.equal(pm.divergence(u2), {}, 'complete second NS tangent')
    kinetic = f.scale(f.QQ_I(1)/2, f.dot(u, u))
    vectors_equal(vector_add(m1, vector_scale(-1, u1)),
                  f.grad(f.add(p, f.scale(-1, kinetic))),
                  'actual first retained gradient is grad(p-|u|^2/2)')
    for n, (m, v) in enumerate(zip((u, m1, m2), (u, u1, u2))):
        vectors_equal(projection(m), v, ('literal Helmholtz reconstruction of full NS jet', n))
        vectors_equal(f.curl(m), f.curl(v), ('actual physical curl reconstruction', n))

    # Test a nonzero gradient difference independently of canonical initialization.
    gamma = f.grad(p)
    gauged = vector_add(u, gamma)
    require(pm.mean(f.dot(gamma, gamma)) > 0, 'nonzero gradient fixture')
    vectors_equal(projection(covector_rhs(nu, u, B, gauged)), u1,
                  'retained gradient Lie transport projects to the same nonlinear NS RHS')
    vectors_equal(f.curl(gauged), f.curl(u), 'gradient difference preserves actual curl')
    require(pm.mean(f.dot(gauged, gauged)) != pm.mean(f.dot(u, u)),
            'projection equality does not authorize a covector-reserve reset')

    Q0, Q1 = identity(), pm.matrix_add(B, pm.transpose(B))
    N1 = pm.matrix_scale(-1, Q1)
    N2 = pm.matrix_add(matrix_transport(u, N1, nu),
        pm.matrix_scale(-1, pm.transpose(B1)), pm.matrix_scale(-1, B1),
        pm.matrix_scale(-1, f.matmul(pm.transpose(B), N1)),
        pm.matrix_scale(-1, f.matmul(N1, B)))
    Q2 = pm.matrix_add(pm.matrix_scale(-1, N2), pm.matrix_scale(2, f.matmul(N1, N1)))
    q = square_jets((u, m1, m2), (Q0, Q1, Q2))
    gradients = [f.grad(v) for v in u]
    m1gradients = [f.grad(v) for v in m1]
    residual0 = [[gradients[i][j] for i in range(3)] for j in range(3)]
    connection1 = [f.matvec(pm.matrix_diff(N1, j), u) for j in range(3)]
    residual1 = [vector_add([m1gradients[i][j] for i in range(3)],
                           vector_scale(-1, connection1[j])) for j in range(3)]
    cost0 = f.add(*(f.dot(v, v) for v in residual0))
    cost1 = f.add(*(f.add(f.scale(2, f.dot(v, w)), metric_pair(v, Q1, v))
                   for v, w in zip(residual0, residual1)))
    f.equal(f.add(q[1], f.adv(u, q[0]), f.scale(-nu, f.lap(q[0]))),
            f.scale(-2*nu, cost0), 'complete initial covector/coframe generator')
    f.equal(f.add(q[2], f.adv(u1, q[0]), f.adv(u, q[1]), f.scale(-nu, f.lap(q[1]))),
            f.scale(-2*nu, cost1), 'complete evolving covector/coframe generator')
    require(pm.mean(q[1]) == -2*nu.x*pm.mean(cost0), 'initial integrated diffusion payment')
    require(pm.mean(q[2]) == -2*nu.x*pm.mean(cost1), 'second integrated generator retains metric derivatives')

    omega, omega1 = f.curl(u), f.curl(u1)
    curl_connection1 = connection_curl(connection1)
    vectors_equal(curl_connection1, vector_scale(-1, [f.adv(u, q) for q in omega]),
                  'first connection curl is actual vorticity transport, not a removable zero')
    vectors_equal(f.curl(m1), vector_add(connection_curl(residual1), curl_connection1),
                  'full first ordinary-curl conversion retains connection')
    connection2 = [vector_add(f.matvec(pm.matrix_diff(N2, j), u),
        vector_scale(2, f.matvec(pm.matrix_diff(N1, j), f.matvec(Q1, u))),
        vector_scale(2, f.matvec(pm.matrix_diff(N1, j), m1))) for j in range(3)]
    curl_connection2 = connection_curl(connection2)
    vectors_equal(f.curl(m2), vector_add(connection_curl([
        vector_add([f.diff(v, j) for v in m2], vector_scale(-1, connection2[j]))
        for j in range(3)]), curl_connection2),
        'complete second ordinary-curl conversion retains metric/drift history')
    connection_square = pm.mean(f.dot(curl_connection1, curl_connection1))
    first_work = pm.mean(f.dot(omega, curl_connection1))
    second_work = pm.mean(f.add(f.dot(omega, curl_connection2),
                              f.scale(2, f.dot(omega1, curl_connection1))))
    require(connection_square > 0, 'strict nonzero physical connection curl')
    require(first_work == 0, 'signed initial transport does no integrated vorticity work')
    require(second_work == f.QQ_I(64).x/33 and second_work > 0,
            'later connection work is not universally zero or nonpositive')

    # An auxiliary gradient source is removed by P; a physical solenoidal
    # force remains in both the reconstructed NS equation and its curl.
    force = f.curl(u)
    f.equal(pm.divergence(force), {}, 'literal solenoidal physical force')
    vectors_equal(projection(vector_add(m1, gamma)), u1,
                  'auxiliary gradient source has zero projected fluid force')
    vectors_equal(projection(vector_add(m1, force)), vector_add(u1, force),
                  'physical solenoidal forcing survives projection')
    force_curl = f.curl(force)
    require(pm.mean(f.dot(force_curl, force_curl)) > 0, 'physical force curl survives')
    return {'viscosity': str(nu.x), 'original_velocity_energy': str(pm.mean(f.dot(u, u))),
            'canonical_covector_metric_first_jet': str(pm.mean(q[1])),
            'canonical_covector_metric_second_jet': str(pm.mean(q[2])),
            'complete_diffusion_initial': str(pm.mean(cost0)),
            'complete_diffusion_first_jet': str(pm.mean(cost1)),
            'connection_curl_first_jet_square': str(connection_square),
            'signed_connection_work_first_jet': str(first_work),
            'signed_connection_work_second_jet': str(second_work),
            'failed_claim': 'connection curl always does nonpositive integrated vorticity work',
            'gradient_fixture_energy_change': str(pm.mean(f.dot(gamma, gamma))),
            'force_scope': 'explicit initial source filter, not an imported singular trajectory',
            'certified_by_exact_checker': 'full original-data NS/covector/coframe jets through second time order',
            'remaining': 'stochastic/time construction and full-datum ordinary-curl conversion on arbitrary histories',
            'not_asserted': 'a Schrodinger optimizer, uniform curl payment, or unforced global regularity'}


if __name__ == '__main__':
    print(json.dumps(check(), indent=2))
