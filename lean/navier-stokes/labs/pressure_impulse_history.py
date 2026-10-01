#!/usr/bin/env python3
"""Pressure-compensated stochastic histories on complete NS time jets.

The exact checks retain the advected initial velocity, accumulated pressure
impulse, its second moment and their cross moment. Every Fourier output is
retained. The PDE energy payment is certified for a literal passive history;
its construction and stochastic identification remain analytic. These finite
jets neither construct a continuum history nor supply a regularity estimate.
"""

import argparse
import json
import pressure_history_source as f
import pressure_memory_diffusion as pm
from signed_viscous_pressure import interacting_datum


def matrix_transport(u, A, nu):
    return [[f.add(f.scale(nu, f.lap(q)), f.scale(-1, f.adv(u, q)))
             for q in row] for row in A]


def vector_transport(u, v, nu):
    return [f.add(f.scale(nu, f.lap(q)), f.scale(-1, f.adv(u, q))) for q in v]


def vectors_equal(v, w, label):
    for i in range(3):
        f.equal(v[i], w[i], label)


def check_case(amplitude, sign, forced=False):
    u = [f.scale(amplitude*sign, q) for q in interacting_datum()]
    nu = f.QQ_I(1)/10
    B = f.jac(u)
    T = f.tensor(u, u)
    gp = f.grad(f.tensor_pressure(T))
    # The force is fixed in Eulerian time, and has zero kinetic work
    # only at the tested initial state. Its impulse is retained separately.
    force = f.curl(u) if forced else [{}, {}, {}]
    source = [f.add(v, f.scale(-1, w)) for v, w in zip(gp, force)]
    H1 = vector_transport(u, u, nu)
    u1 = [f.add(v, f.scale(-1, w)) for v, w in zip(H1, source)]
    f.equal(pm.divergence(u1), {}, 'actual first NS tangent')
    T1 = pm.symmetric_product(u, u1)
    gp1 = f.grad(f.tensor_pressure(T1))
    H2 = [f.add(v, f.scale(-1, f.adv(u1, q)))
          for v, q in zip(vector_transport(u, H1, nu), u)]
    u2 = [f.add(v, f.scale(-1, w)) for v, w in zip(H2, gp1)]
    # H2 above retains the time derivative of the actual drift, but NS
    # also transports u1 instead of H1 at the second derivative.
    u2 = [f.add(q, f.adv(u, g), f.scale(-nu, f.lap(g)))
          for q, g in zip(u2, source)]
    f.equal(pm.divergence(u2), {}, 'actual second NS tangent')
    I1 = [f.add(v, f.scale(-1, w)) for v, w in zip(H1, u1)]
    I2 = [f.add(v, f.scale(-1, w)) for v, w in zip(H2, u2)]
    vectors_equal(I1, source, 'pressure-minus-force impulse mean law')
    vectors_equal(I2, [f.add(v, w) for v, w in
                      zip(vector_transport(u, source, nu), gp1)],
                  'impulse law retains evolving pressure and drift')
    J1 = f.jac(source)
    expected_J2 = pm.matrix_add(matrix_transport(u, J1, nu),
        pm.matrix_scale(-1, f.matmul(J1, B)), f.jac(gp1))
    f.same_matrices(f.jac(I2), expected_J2,
                    'gradient impulse retains the pressure Hessian and parent deformation')
    mean_work = pm.mean(f.dot(u, H1))
    expected_loss = -nu.x*pm.mean(pm.pair(B, B))
    if mean_work != expected_loss:
        raise ArithmeticError('literal passive energy rate')
    passive_energy2 = 2*pm.mean(f.add(f.dot(H1, H1), f.dot(u, H2)))
    if passive_energy2 != -4*nu.x*pm.mean(pm.pair(B, f.jac(H1))):
        raise ArithmeticError('passive energy second derivative')
    if not forced:
        energy2 = 2*pm.mean(f.add(f.dot(u1, u1), f.dot(u, u2)))
        if energy2 != -4*nu.x*pm.mean(pm.pair(B, f.jac(u1))):
            raise ArithmeticError('unforced energy second derivative')

    # Q=E[impulse tensor impulse], K=E[initial velocity tensor impulse].
    # These are zero initially; their cross moment cannot be discarded.
    L1 = matrix_transport(u, T, nu)
    L2 = pm.matrix_add(matrix_transport(u, L1, nu),
                       pm.matrix_scale(-1, pm.matrix_adv(u1, T)))
    K1 = f.tensor(u, source)
    K2 = pm.matrix_add(matrix_transport(u, K1, nu),
                       f.tensor(H1, source), f.tensor(u, gp1))
    Q2 = pm.matrix_scale(2, f.tensor(source, source))
    A1 = pm.matrix_add(L1, pm.matrix_scale(-1, K1),
                       pm.matrix_scale(-1, pm.transpose(K1)))
    A2 = pm.matrix_add(L2, pm.matrix_scale(-1, K2),
                       pm.matrix_scale(-1, pm.transpose(K2)), Q2)

    G = f.matmul(B, pm.transpose(B))
    B1 = f.jac(u1)
    G1 = pm.matrix_add(f.matmul(B1, pm.transpose(B)),
                       f.matmul(B, pm.transpose(B1)))
    C1 = pm.matrix_scale(2*nu, G)
    C2 = pm.matrix_add(matrix_transport(u, C1, nu), pm.matrix_scale(2*nu, G1))
    T2 = pm.matrix_add(pm.symmetric_product(u, u2),
                       pm.matrix_scale(2, f.tensor(u1, u1)))
    f.same_matrices(A1, pm.matrix_add(T1, C1),
                    'compensated second moment equals actual augmented stress')
    f.same_matrices(A2, pm.matrix_add(T2, C2),
                    'second derivative retains all joint parent moments')
    dropped = pm.symmetric_product(u, source)
    if all(not q for row in dropped for q in row):
        raise ArithmeticError('cross moment must have a nonzero physical consumer')

    # Variance of the impulse is itself positive diffusion memory.
    Q3 = pm.matrix_add(matrix_transport(u, Q2, nu),
                       pm.matrix_scale(2, pm.symmetric_product(gp1, source)),
                       pm.symmetric_product(source, I2))
    variance3 = pm.matrix_add(Q3,
                   pm.matrix_scale(-3, pm.symmetric_product(I1, I2)))
    f.same_matrices(variance3, pm.matrix_scale(4*nu, f.matmul(J1, pm.transpose(J1))),
                    'pressure impulse variance has a genuine positive source')

    # The usual terminal velocity covariance has a different source once
    # pressure/force drift changes the sampled velocity.
    raw2 = pm.matrix_add(L2, pm.matrix_scale(-1, pm.symmetric_product(u, H2)),
                         pm.matrix_scale(-2, f.tensor(H1, H1)))
    difference = pm.matrix_add(C2, pm.matrix_scale(-1, raw2))
    expected = pm.matrix_scale(-2*nu,
        pm.matrix_add(f.matmul(B, pm.transpose(J1)), f.matmul(J1, pm.transpose(B))))
    f.same_matrices(difference, expected, 'raw velocity covariance is not viscous memory')
    if all(not q for row in difference for q in row):
        raise ArithmeticError('nonzero covariance distinction required')
    return {'amplitude': amplitude, 'velocity_sign': sign, 'forced': forced,
            'initial_energy': str(pm.mean(f.dot(u, u))),
            'impulse_second_moment_second_derivative': str(pm.mean(f.trace(Q2))),
            'impulse_variance_third_derivative': str(pm.mean(f.trace(variance3))),
            'cross_moment_modes': len(set().union(*(q.keys() for row in K1 for q in row))),
            'kinetic_force_work_at_initial_state': str(pm.mean(f.dot(u, force))),
            'covariance_distinction': 'nonzero, exact',
            'scope': 'full initial PDE jets, not a continuum evolution'}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--initialized-quadrature', action='store_true')
    args = parser.parse_args()
    result = {'cases': [check_case(A, sign) for A in (1, 2) for sign in (-1, 1)],
              'forced_contrast': check_case(1, -1, True),
              'conditional_PDE_history_bound': '||I(t)||_2^2+2nu integral ||grad I||_2^2<=4E0',
              'history_scope': 'passive PDE construction and stochastic identification are analytic',
              'weighted_deformation_history': 'OPEN'}
    if args.initialized_quadrature:
        from signed_viscous_pressure_quadrature import diagnose
        result['initialized_quadrature'] = diagnose(initialized=True)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
