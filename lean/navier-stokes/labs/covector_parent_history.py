#!/usr/bin/env python3
"""Covector parent payments and pressure-generated frame diffusion.

The rational derivatives retain every spatial direction and the pressure
receiver. A whole-space central/remote construction gives actual initial
NS and auxiliary time jets. Its short-time realization and Taylor argument
are analytic, not Lean-certified. No arbitrary-data renewal bound is proved.
"""

import json
import sympy as s
import pressure_history_source as f
import pressure_memory_diffusion as pm
from pressure_impulse_history import matrix_transport, vector_transport
from signed_viscous_pressure import interacting_datum


def zero(value, label):
    if s.simplify(s.factor(value)) != 0:
        raise ArithmeticError((label, value))


def matrix_zero(value, label):
    for i, entry in enumerate(value):
        zero(entry, (label, i))


def square(value):
    return s.trace(value*value.T)


def rational_generators():
    t, x = s.symbols('t x', real=True)
    nu = s.Rational(1, 10)
    B = s.Matrix([[1, 2, 3], [-3, 0, 1], [2, -1, -1]])
    H = s.Matrix([[2, 1, -3], [4, -1, 0], [1, 2, -1]])
    A = H-B
    N = s.Matrix([[2, 1, 0], [1, 3, 1], [0, 1, 2]])
    Q = N.inv()
    M = s.Matrix([[3, 0, 1], [0, 2, 1], [1, 1, 3]])
    P = s.Matrix([[2, 1, -1], [1, -3, 2], [-1, 2, 1]])
    Nj = [s.diag(1, -2, 3), s.ones(3), s.diag(-1, 2, 0)]
    Mj = [s.Matrix([[1, 2, 0], [2, -1, 1], [0, 1, 3]]),
          s.Matrix([[0, 1, -1], [1, 2, 0], [-1, 0, -2]]),
          s.Matrix([[2, 0, 1], [0, 1, -2], [1, -2, 0]])]
    Ej = [s.Matrix([[1, 3, -1], [2, 0, 1], [-1, 2, 2]]),
          s.Matrix([[2, -1, 3], [0, 1, 4], [3, -2, 0]]), s.eye(3)]
    Aj = [s.diag(2, -1, 3), s.ones(3), s.diag(0, 2, -1)]
    Tj = [s.eye(3), s.diag(2, -1, 3), s.ones(3)]
    Uj = [s.diag(1, 2, -1), s.eye(3), s.zeros(3)]
    for matrix in (N, M):
        if any(matrix[:k, :k].det() <= 0 for k in range(1, 4)):
            raise ArithmeticError('positive definite rational frame')

    Nt = -B.T*N-N*B+nu*sum(Tj, s.zeros(3))
    Mt = B*M+M*B.T+nu*sum(Tj, s.zeros(3))

    def inverse_parent(V, Vj, source):
        Vt = -V*B+source+nu*sum(Uj, s.zeros(3))
        timed = s.trace((V+t*Vt)*(N+t*Nt).inv()*(V+t*Vt).T)
        qt = s.diff(timed, t).subs(t, 0)
        lap, cost = 0, 0
        for E, K, T, U in zip(Vj, Nj, Tj, Uj):
            vx, nx = V+x*E+x*x*U/2, N+x*K+x*x*T/2
            lap += s.diff(s.trace(vx*nx.inv()*vx.T), x, 2).subs(x, 0)
            residual = E-V*Q*K
            cost += s.trace(residual*Q*residual.T)
        work = s.trace(V*Q*source.T)
        zero(qt-nu*lap-2*work+2*nu*cost,
             'inverse coframe full generator from independent derivatives')
        return cost, work

    FH, _ = inverse_parent(H, Ej, s.zeros(3))
    FI, work = inverse_parent(A, Aj, P)
    pressure_force = s.Matrix([2, -3, 1])
    receiver, covariant_receiver = s.zeros(3, 1), s.zeros(3, 1)
    young_squares = 0
    for j, (E, K) in enumerate(zip(Aj, Nj)):
        basis = s.eye(3)[:, j]
        aq = (A+x*E)*(N+x*K).inv()
        receiver += aq.diff(x).subs(x, 0)[:, j]
        covariant = E-A*Q*K
        covariant_receiver += covariant*Q*basis
        square_row = nu*covariant-pressure_force*basis.T
        young_squares += s.trace(square_row*Q*square_row.T)/nu
    matrix_zero(receiver-covariant_receiver,
                'actual metric derivative retained in the pressure receiver')
    gradient_cost = s.trace(Q)*pressure_force.dot(pressure_force)/nu
    residual = nu*FI+gradient_cost-2*receiver.dot(pressure_force)
    zero(residual-young_squares, 'full weighted pressure receiver Young squares')
    if residual < 0:
        raise ArithmeticError('nonnegative pressure receiver transfer')
    Ht = -H*B+nu*sum(Uj, s.zeros(3))
    timed = s.trace((H+t*Ht)*(M+t*Mt)*(H+t*Ht).T)
    qt, lap, native, cross = s.diff(timed, t).subs(t, 0), 0, 0, 0
    for E, K, T, U in zip(Ej, Mj, Tj, Uj):
        hx, mx = H+x*E+x*x*U/2, M+x*K+x*x*T/2
        lap += s.diff(s.trace(hx*mx*hx.T), x, 2).subs(x, 0)
        native += s.trace(E*M*E.T)
        cross += s.trace(H*K*E.T)
    zero(qt-nu*lap+2*nu*native+4*nu*cross,
         'forward frame retains indefinite diffusion cross term')
    if FH < 0 or FI < 0:
        raise ArithmeticError('positive covector diffusion squares')
    return {'passive_covariant_cost': str(FH), 'impulse_covariant_cost': str(FI),
            'weighted_pressure_work': str(work),
            'pressure_receiver_young_square_residual': str(residual),
            'scope': 'independent rational parabolic jets; no fluid realization of these arbitrary matrices'}


def physical_remote_history():
    t, x, y, z = s.symbols('t x y z', real=True)
    b, energy, L, nu = s.symbols('b E L nu', positive=True)
    coords, origin = (x, y, z), {x: 0, y: 0, z: 0}
    spin = s.Matrix([[0, -1, 0], [1, 0, 0], [0, 0, 0]])
    B = b*spin
    u0 = B*s.Matrix(coords)
    displacement = s.Matrix([x, y, z-L])
    r2 = displacement.dot(displacement)
    remote = -energy*(3*(z-L)**2-r2)/(8*s.pi*r2**s.Rational(5, 2))
    central = b*b*(2*x*x+2*y*y+z*z)/5
    pressure = central+remote
    gp, P = s.Matrix([s.diff(pressure, c) for c in coords]), s.hessian(pressure, coords)
    lap = lambda expr: sum(s.diff(expr, c, 2) for c in coords)
    zero(lap(remote), 'remote canonical exterior pressure is harmonic')
    zero(lap(pressure)+s.trace(B*B), 'central canonical NS pressure equation')
    H1 = nu*u0.applyfunc(lap)-u0.jacobian(coords)*u0
    u1 = H1-gp
    zero(s.trace(u1.jacobian(coords)), 'complete local unforced velocity tangent is solenoidal')
    H2 = nu*H1.applyfunc(lap)-H1.jacobian(coords)*u0-u0.jacobian(coords)*u1
    BH1, BH2 = H1.jacobian(coords), H2.jacobian(coords)
    matrix_zero(BH1+B*B, 'first passive gradient jet in the flat core')
    matrix_zero(BH2-2*B**3-B*P, 'second passive gradient retains the actual pressure')
    B1 = u1.jacobian(coords)
    M1, N1 = B+B.T, -B.T-B
    matrix_zero(M1, 'first forward frame jet vanishes in the rigid core')
    matrix_zero(N1, 'first coframe jet vanishes in the rigid core')
    M2, N2 = B1+B1.T, -B1.T-B1
    c = 15*energy/(2*s.pi*L**6)
    expected = [s.Matrix([[0, 0, c], [0, 0, 0], [c, 0, 0]]),
                s.Matrix([[0, 0, 0], [0, 0, c], [0, c, 0]]), s.diag(c, c, -2*c)]
    EH, forward, covector = [], [], []
    for j, coord in enumerate(coords):
        Pj = s.simplify(P.diff(coord).subs(origin))
        matrix_zero(Pj-expected[j], 'complete third tensor of canonical remote pressure')
        matrix_zero(BH1.diff(coord), 'first parent-gradient spatial jet vanishes')
        E2 = s.simplify(BH2.diff(coord).subs(origin))
        Mj2 = s.simplify(M2.diff(coord).subs(origin))
        Nj2 = s.simplify(N2.diff(coord).subs(origin))
        matrix_zero(E2-B*Pj, 'actual second parent-gradient spatial jet')
        matrix_zero(Mj2+2*Pj, 'actual second forward-frame spatial jet')
        matrix_zero(Nj2-2*Pj, 'actual second coframe spatial jet')
        EH.append(t*t*E2/2)
        forward.append(t*t*Mj2/2)
        covector.append(t*t*Nj2/2)
    P0 = s.simplify(P.subs(origin))
    Ht = B+t*BH1+t*t*s.simplify(BH2.subs(origin))/2
    Mt, Nt = s.eye(3)+t*t*M2.subs(origin)/2, s.eye(3)+t*t*N2.subs(origin)/2
    Qt = Nt.inv()
    wrong = -2*nu*sum(s.trace(E*Mt*E.T) for E in EH)
    wrong -= 4*nu*sum(s.trace(Ht*K*E.T) for K, E in zip(forward, EH))
    wrong4 = s.expand(wrong).coeff(t, 4)
    right = -2*nu*sum(s.trace((E-Ht*Qt*K)*Qt*(E-Ht*Qt*K).T)
                        for E, K in zip(EH, covector))
    right4 = s.simplify(s.limit(right/t**4, t, 0))
    zero(wrong4-6*nu*b*b*c*c, 'strict positive wrong-frame fourth-order history coefficient')
    zero(right4+2*nu*b*b*c*c, 'correct inverse coframe fourth-order negative square')
    zero(sum(square(B*K) for K in expected)-4*b*b*c*c, 'all remote pressure directions retained')
    gap5 = 2*nu*sum((K*K for K in expected), s.zeros(3))/5
    gap_parent5 = s.trace(B*gap5*B.T)
    zero(gap_parent5-8*nu*b*b*c*c/5, 'pressure-generated reciprocal-frame gap coefficient')
    if not (wrong4 > 0 and right4 < 0 and gap_parent5 > 0):
        raise ArithmeticError('positive viscosity and nonzero physical packet required')
    return {'remote_third_pressure_scale': str(c), 'canonical_initial_hessian': str(P0),
            'forward_parent_generator_t4': str(s.factor(wrong4)),
            'inverse_covector_parent_generator_t4': str(s.factor(right4)),
            'forward_minus_inverse_parent_metric_t5': str(s.factor(gap_parent5)),
            'scope': 'actual local canonical NS/passive/frame jets; compact global realization and short-time Taylor argument are analytic',
            'failed_claim': 'nonpositive parabolic production with the forward frame M',
            'not_refuted': 'correct inverse covector payment, finite full-datum history allowances or unforced regularity'}


def fourier_frame_jets():
    u, nu = interacting_datum(), f.QQ_I(1)/10
    B = f.jac(u)
    gp = f.grad(f.tensor_pressure(f.tensor(u, u)))
    H1 = vector_transport(u, u, nu)
    u1 = [f.add(v, f.scale(-1, p)) for v, p in zip(H1, gp)]
    f.equal(pm.divergence(u1), {}, 'actual full unforced Fourier tangent')
    Bt = f.jac(u1)
    S = pm.matrix_add(B, pm.transpose(B))
    M1, N1 = S, pm.matrix_scale(-1, S)
    M2 = pm.matrix_add(matrix_transport(u, M1, nu), Bt, pm.transpose(Bt),
                       f.matmul(B, M1), f.matmul(M1, pm.transpose(B)))
    N2 = pm.matrix_add(matrix_transport(u, N1, nu),
                       pm.matrix_scale(-1, pm.transpose(Bt)), pm.matrix_scale(-1, Bt),
                       pm.matrix_scale(-1, f.matmul(pm.transpose(B), N1)),
                       pm.matrix_scale(-1, f.matmul(N1, B)))
    f.same_matrices(pm.matrix_add(M2, N2), pm.matrix_scale(2, f.matmul(S, S)),
                    'mean coframe and inverse forward frame agree through second jets only')
    # G=M-N^-1 has zero zeroth/first/second jets. Its actual equation has
    # source 2nu sum Q N_j Q N_j Q. N_j starts at t partial_j N1, so
    # G'''(0)=4nu sum (partial_j N1)^2. No pressure jet is suppressed.
    G3 = pm.matrix_scale(4*nu, pm.matrix_add(
        *(f.matmul(pm.matrix_diff(S, j), pm.matrix_diff(S, j)) for j in range(3))))
    gp1 = f.grad(f.tensor_pressure(pm.symmetric_product(u, u1)))
    u2 = [f.add(v, f.scale(-1, f.adv(u1, old)), f.scale(-1, p))
          for v, old, p in zip(vector_transport(u, u1, nu), u, gp1)]
    f.equal(pm.divergence(u2), {}, 'actual second unforced NS tangent')
    H2 = [f.add(v, f.scale(-1, f.adv(u1, old)))
          for v, old in zip(vector_transport(u, H1, nu), u)]
    I2 = [f.add(v, f.scale(-1, w)) for v, w in zip(H2, u2)]
    for v, expected in zip(I2, [f.add(v, w) for v, w in
                               zip(vector_transport(u, gp, nu), gp1)]):
        f.equal(v, expected, 'complete second impulse tangent for the pressure receiver')
    P, P1, A2 = f.jac(gp), f.jac(gp1), f.jac(I2)
    AQ2 = pm.matrix_add(A2, pm.matrix_scale(2, f.matmul(P, S)))
    receiver1, receiver2 = pm.tensor_divergence(P), pm.tensor_divergence(AQ2)
    work1 = pm.mean(pm.pair(P, P))
    work2 = pm.mean(f.add(pm.pair(AQ2, P), f.scale(2, pm.pair(P, P1))))
    transferred1 = -pm.mean(f.dot(receiver1, gp))
    transferred2 = -pm.mean(f.add(f.dot(receiver2, gp),
                                    f.scale(2, f.dot(receiver1, gp1))))
    if work1 != transferred1 or work2 != transferred2:
        raise ArithmeticError('actual changing-coframe pressure work integration by parts')
    Btt = f.jac(u2)
    M3 = pm.matrix_add(matrix_transport(u, M2, nu),
        pm.matrix_scale(-2, pm.matrix_adv(u1, M1)), Btt, pm.transpose(Btt),
        pm.matrix_scale(2, f.matmul(Bt, M1)),
        pm.matrix_scale(2, f.matmul(M1, pm.transpose(Bt))),
        f.matmul(B, M2), f.matmul(M2, pm.transpose(B)))
    N3 = pm.matrix_add(matrix_transport(u, N2, nu),
        pm.matrix_scale(-2, pm.matrix_adv(u1, N1)),
        pm.matrix_scale(-1, pm.transpose(Btt)), pm.matrix_scale(-1, Btt),
        pm.matrix_scale(-2, f.matmul(pm.transpose(Bt), N1)),
        pm.matrix_scale(-2, f.matmul(N1, Bt)),
        pm.matrix_scale(-1, f.matmul(pm.transpose(B), N2)),
        pm.matrix_scale(-1, f.matmul(N2, B)))
    independent_gap3 = pm.matrix_add(M3, N3,
        pm.matrix_scale(-3, f.matmul(N1, N2)),
        pm.matrix_scale(-3, f.matmul(N2, N1)),
        pm.matrix_scale(6, f.matmul(f.matmul(N1, N1), N1)))
    f.same_matrices(independent_gap3, G3,
                    'independent full NS/frame third jets retain the reciprocal diffusion gap')
    trace3 = pm.mean(f.trace(G3))
    if trace3 <= 0:
        raise ArithmeticError('nonzero reciprocal-frame diffusion gap')
    return {'mean_gap_trace_third_jet': str(trace3),
            'weighted_pressure_work_first_jet': str(work1),
            'weighted_pressure_work_second_jet': str(work2),
            'pressure_receiver_transfer': 'both full time jets agree; canonical pressure_t and coframe_t retained',
            'canonical_pressure_and_complete_drift_tangent': 'retained',
            'scope': 'complete rational Fourier frame jets; no closed finite-mode time evolution'}


def main():
    report = {'rational_generators': rational_generators(),
              'actual_remote_history': physical_remote_history(),
              'fourier_frame_jets': fourier_frame_jets(),
              'paid_channel': 'normalized passive parent gradient and its covariant diffusion, from original gradient data',
              'unpaid': 'weighted impulse-pressure history and conversion to actual vorticity',
              'global_regularity': 'OPEN'}
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
