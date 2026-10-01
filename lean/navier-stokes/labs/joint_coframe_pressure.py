#!/usr/bin/env python3
"""Joint-parent pressure cancellation and complete unforced coframe jets.

Gaussian rational Fourier coefficients use the 2*pi torus. Every nonlinear
output is retained. The initial data, canonical pressure and NS tangents
are literal spatial fields; the coframe jets start at the identity and use
the same full drift. They are not a closed finite-mode time evolution.
The stochastic construction and smooth short-time realization are analytic.
No finite arbitrary-history allowance or regularity theorem is asserted.
"""

import json
import sympy as s
import pressure_history_source as f
import pressure_memory_diffusion as pm
from pressure_impulse_history import matrix_transport, vector_transport
from signed_viscous_pressure import interacting_datum


def require(value, label):
    if not value:
        raise ArithmeticError(label)


def zero(value, label):
    require(s.simplify(value) == 0, (label, value))


def metric_pair(V, Q, W):
    return pm.pair(f.matmul(V, Q), W)


def commutator(B, Q, gp):
    return f.add(*(f.mul(f.mul(B[i][k], f.diff(Q[k][j], i)), gp[j])
                   for i in range(3) for k in range(3) for j in range(3)))


def flux(B, Q, gp):
    return f.matvec(f.matmul(B, Q), gp)


def identity():
    return [[{f.ORIGIN: f.QQ_I(int(i == j))} if i == j else {}
             for j in range(3)] for i in range(3)]


def quadratic_jets(V, Q, W):
    """The full first three time derivatives of tr(V Q W^T)."""
    out = []
    for n in range(3):
        out.append(f.add(*(f.scale(f.QQ_I(s.factorial(n)//
            (s.factorial(a)*s.factorial(b)*s.factorial(n-a-b))),
            metric_pair(V[a], Q[b], W[n-a-b]))
            for a in range(n+1) for b in range(n-a+1))))
    return out


def rational_joint_generator():
    nu, t, x = s.Rational(1, 10), s.Symbol('t'), s.Symbol('x')
    B = s.Matrix([[1, 2, 3], [-3, 0, 1], [2, -1, -1]])
    H = s.Matrix([[2, 1, -3], [4, -1, 0], [1, 2, -1]])
    A = H-B
    N = s.Matrix([[2, 1, 0], [1, 3, 1], [0, 1, 2]])
    Q = N.inv()
    P = s.Matrix([[2, 1, -1], [1, -3, 2], [-1, 2, 1]])
    Nj = [s.diag(1, -2, 3), s.ones(3), s.diag(-1, 2, 0)]
    Hj = [s.Matrix([[1, 3, -1], [2, 0, 1], [-1, 2, 2]]),
          s.Matrix([[2, -1, 3], [0, 1, 4], [3, -2, 0]]), s.eye(3)]
    Aj = [s.diag(2, -1, 3), s.ones(3), s.diag(0, 2, -1)]
    Bj = [E-F for E, F in zip(Hj, Aj)]
    Njj = [s.eye(3), s.diag(2, -1, 3), s.ones(3)]
    Vjj = [s.diag(1, 2, -1), s.eye(3), s.zeros(3)]
    require(all(N[:k, :k].det() > 0 for k in range(1, 4)), 'positive rational coframe')
    Nt = -B.T*N-N*B+nu*sum(Njj, s.zeros(3))
    Bt = -B*B-P+nu*sum(Vjj, s.zeros(3))
    timed = s.trace((B+t*Bt)*(N+t*Nt).inv()*(B+t*Bt).T)
    generator = s.diff(timed, t).subs(t, 0)
    cost = s.Integer(0)
    for E, K, T, U in zip(Bj, Nj, Njj, Vjj):
        vx, nx = B+x*E+x*x*U/2, N+x*K+x*x*T/2
        generator -= nu*s.diff(s.trace(vx*nx.inv()*vx.T), x, 2).subs(x, 0)
        covariant = E-B*Q*K
        cost += s.trace(covariant*Q*covariant.T)
    work = s.trace(B*Q*P.T)
    zero(generator+2*work+2*nu*cost, 'joint actual generator with full inverse differentiation')
    cross = s.trace(H*Q*A.T)
    zero(s.trace(B*Q*B.T)-s.trace(H*Q*H.T)-s.trace(A*Q*A.T)+2*cross,
         'joint cross moment reconstructs the actual fluid gradient')
    covariant_cross = sum((s.trace((E-H*Q*K)*Q*(F-A*Q*K).T)
        for E, F, K in zip(Hj, Aj, Nj)), s.Integer(0))
    passive_cost = sum((s.trace((E-H*Q*K)*Q*(E-H*Q*K).T)
        for E, K in zip(Hj, Nj)), s.Integer(0))
    impulse_cost = sum((s.trace((E-A*Q*K)*Q*(E-A*Q*K).T)
        for E, K in zip(Aj, Nj)), s.Integer(0))
    zero(cost-passive_cost-impulse_cost+2*covariant_cross,
         'joint covariant diffusion retains the same cross moment')
    return {'actual_pressure_work': str(work), 'full_diffusion_cost': str(cost),
            'complete_parabolic_generator': str(s.factor(generator)),
            'parent_cross_moment': str(cross),
            'scope': 'exact local rate algebra; no independently selected matrix is an actual flow history'}


def actual_fourier_history():
    u, nu = interacting_datum(), f.QQ_I(1)/10
    B = f.jac(u)
    p = f.tensor_pressure(f.tensor(u, u))
    gp, P = f.grad(p), f.hess(p)
    f.equal(pm.divergence(u), {}, 'genuine solenoidal 3D datum')
    f.equal(p, f.green(f.trace(f.matmul(B, B))), 'canonical pressure from full solenoidal source')
    H1 = vector_transport(u, u, nu)
    u1 = [f.add(v, f.scale(-1, w)) for v, w in zip(H1, gp)]
    f.equal(pm.divergence(u1), {}, 'complete first unforced tangent')
    B1 = f.jac(u1)
    gp1 = f.grad(f.tensor_pressure(pm.symmetric_product(u, u1)))
    u2 = [f.add(v, f.scale(-1, f.adv(u1, q)), f.scale(-1, w))
          for v, q, w in zip(vector_transport(u, u1, nu), u, gp1)]
    f.equal(pm.divergence(u2), {}, 'complete second unforced tangent')
    B2 = f.jac(u2)
    H2 = [f.add(v, f.scale(-1, f.adv(u1, q)))
          for v, q in zip(vector_transport(u, H1, nu), u)]
    I2 = [f.add(v, f.scale(-1, w)) for v, w in zip(H2, u2)]
    pressure2 = f.tensor_pressure(pm.matrix_add(pm.symmetric_product(u, u2),
                                                pm.matrix_scale(2, f.tensor(u1, u1))))
    P1, P2 = f.jac(gp1), f.hess(pressure2)
    Q0 = identity()
    Q1 = pm.matrix_add(B, pm.transpose(B))
    N1 = pm.matrix_scale(-1, Q1)
    N2 = pm.matrix_add(matrix_transport(u, N1, nu),
        pm.matrix_scale(-1, pm.transpose(B1)), pm.matrix_scale(-1, B1),
        pm.matrix_scale(-1, f.matmul(pm.transpose(B), N1)),
        pm.matrix_scale(-1, f.matmul(N1, B)))
    Q2 = pm.matrix_add(pm.matrix_scale(-1, N2), pm.matrix_scale(2, f.matmul(N1, N1)))
    f.same_matrices(Q2, pm.matrix_add(matrix_transport(u, Q1, nu),
        B1, pm.transpose(B1), f.matmul(B, Q1), f.matmul(Q1, pm.transpose(B))),
        'inverse common-flow coframe has its full second time jet')

    # Constant anisotropic metrics cancel even though they are not I.
    anisotropic = [[{f.ORIGIN: f.QQ_I(v)} for v in row]
                   for row in ((3, 1, -1), (1, 4, 2), (-1, 2, 5))]
    require(pm.mean(metric_pair(B, anisotropic, P)) == 0, 'constant anisotropic pressure cancellation')
    Qtest = pm.matrix_add(Q0, pm.matrix_scale(f.QQ_I(1)/100, Q1))
    # A rational absolute-coefficient row bound certifies positive Qtest.
    row_bound = max(sum(sum(abs(c.x)+abs(c.y) for c in Q1[i][j].values())
                        for j in range(3)) for i in range(3))/100
    require(row_bound < 1, 'uniform positive metric fixture via coefficient row bound')
    work = metric_pair(B, Qtest, P)
    defect = commutator(B, Qtest, gp)
    f.equal(pm.divergence(flux(B, Qtest, gp)), f.add(work, defect),
            'literal full pressure flux divergence, without discarded metric derivatives')
    require(pm.mean(work) == -pm.mean(defect), 'full spatial commutator integration by parts')

    work0 = pm.pair(B, P)
    work1 = f.add(pm.pair(B1, P), pm.pair(B, P1), metric_pair(B, Q1, P))
    work2 = f.add(pm.pair(B2, P), pm.pair(B, P2),
        f.scale(2, pm.pair(B1, P1)), f.scale(2, metric_pair(B1, Q1, P)),
        f.scale(2, metric_pair(B, Q1, P1)), metric_pair(B, Q2, P))
    comm1 = commutator(B, Q1, gp)
    comm2 = f.add(f.scale(2, commutator(B1, Q1, gp)),
                 f.scale(2, commutator(B, Q1, gp1)), commutator(B, Q2, gp))
    mean0, mean1, mean2 = map(pm.mean, (work0, work1, work2))
    require(mean0 == 0, 'actual initial identity-metric pressure cancellation')
    require(mean1 == -pm.mean(comm1), 'complete first pressure/coframe jet commutator')
    require(mean2 == -pm.mean(comm2), 'complete second pressure/coframe jet commutator')
    require(mean1 == -f.QQ_I(156013232).x/10405395, 'negative actual first pressure-work jet')

    # Preserve joint parent choices at every tested time order.
    Hj = [B, f.jac(H1), f.jac(H2)]
    Aj = [[[{} for _ in range(3)] for _ in range(3)], P, f.jac(I2)]
    Bj, Qj = [B, B1, B2], [Q0, Q1, Q2]
    qB = quadratic_jets(Bj, Qj, Bj)
    qH = quadratic_jets(Hj, Qj, Hj)
    qI = quadratic_jets(Aj, Qj, Aj)
    cross = quadratic_jets(Hj, Qj, Aj)
    for n in range(3):
        f.equal(qB[n], f.add(qH[n], qI[n], f.scale(-2, cross[n])),
                ('actual gradient reconstruction with complete cross-moment time jet', n))
    FB0 = f.add(*(pm.pair(pm.matrix_diff(B, j), pm.matrix_diff(B, j)) for j in range(3)))
    FB1 = f.add(*(f.add(f.scale(2, pm.pair(pm.matrix_diff(B, j),
        pm.matrix_add(pm.matrix_diff(B1, j), f.matmul(B, pm.matrix_diff(Q1, j))))),
        metric_pair(pm.matrix_diff(B, j), Q1, pm.matrix_diff(B, j))) for j in range(3)))
    f.equal(f.add(qB[1], f.adv(u, qB[0]), f.scale(-nu, f.lap(qB[0]))),
            f.add(f.scale(-2, work0), f.scale(-2*nu, FB0)),
            'full pointwise actual metric generator at initial time')
    f.equal(f.add(qB[2], f.adv(u1, qB[0]), f.adv(u, qB[1]), f.scale(-nu, f.lap(qB[1]))),
            f.add(f.scale(-2, work1), f.scale(-2*nu, FB1)),
            'full pointwise time derivative including viscosity and drift_t')
    require(pm.mean(qB[1]) == -2*nu.x*pm.mean(FB0), 'actual initial integrated negative diffusion')
    require(pm.mean(qB[2]) == -2*mean1-2*nu.x*pm.mean(FB1),
            'integrated actual second derivative with full pressure and diffusion')
    require(nu.x > 0 and mean1 < 0, 'positive viscosity and strict pressure injection jet')
    return {'viscosity': str(nu.x), 'pressure_work_initial': str(mean0),
            'pressure_work_first_jet': str(mean1), 'pressure_work_second_jet': str(mean2),
            'metric_test_uniform_lower_bound': str(1-row_bound),
            'metric_test_pressure_work': str(pm.mean(work)),
            'full_metric_square_first_jet': str(pm.mean(qB[1])),
            'full_metric_square_second_jet': str(pm.mean(qB[2])),
            'full_covariant_diffusion_initial': str(pm.mean(FB0)),
            'full_covariant_diffusion_first_jet': str(pm.mean(FB1)),
            'scope': 'complete canonical unforced PDE/coframe time jets; actual short-prefix construction is analytic',
            'failed_claim': 'every actual coframe history has nonnegative integrated pressure work',
            'not_refuted': 'finite signed full-datum history payment, full metric-production monotonicity or unforced regularity'}


def main():
    print(json.dumps({'rational_joint_generator': rational_joint_generator(),
                     'actual_fourier_history': actual_fourier_history(),
                     'remaining': 'signed evolving metric commutator payment and physical continuation conversion',
                     'global_regularity': 'OPEN'}, indent=2))


if __name__ == '__main__':
    main()
