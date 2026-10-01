#!/usr/bin/env python3
"""Joint two-index metric, original-gradient payment and physical curl.

Fourier checks retain every output on the 2*pi torus and the full
canonical pressure/drift. Rational joint frames test metric production,
original-label variance and the area channel. Polynomial-core localization and
short-time stochastic realization are analytic, not certified by this
script. No source history allowance or global regularity is asserted.
"""

import json
import sympy as s
import pressure_history_source as f
import pressure_memory_diffusion as pm
from signed_viscous_pressure import interacting_datum
from pressure_impulse_history import vector_transport, matrix_transport
from covector_fluid_bridge import vector_add, vector_scale, covector_rhs
from covector_receiver_geometry import matrix_sub, columns, matrix_from_columns, adjugate
from joint_coframe_pressure import identity, require


def add(*arrays):
    return [[f.add(*(a[i][j] for a in arrays)) for j in range(len(arrays[0][0]))]
             for i in range(len(arrays[0]))]


def scale(c, a):
    return [[f.scale(c, v) for v in row] for row in a]


def subtract(a, b):
    return add(a, scale(-1, b))


def multiply(a, b):
    return [[f.add(*(f.mul(a[i][k], b[k][j]) for k in range(len(b))))
             for j in range(len(b[0]))] for i in range(len(a))]


def kronecker(a, b):
    return [[f.mul(a[i][j], b[k][l]) for j in range(len(a[0])) for l in range(len(b[0]))]
             for i in range(len(a)) for k in range(len(b))]


def equal(a, b, label):
    require(len(a) == len(b) and len(a[0]) == len(b[0]), (label, 'matrix dimensions'))
    for i in range(len(a)):
        for j in range(len(a[0])):
            f.equal(a[i][j], b[i][j], (label, i, j))


def flatten(a):
    return [v for row in a for v in row]


def metric(v, Q, w):
    require(len(v) == len(Q) and all(len(row) == len(w) for row in Q),
            'metric retains every tensor coordinate')
    return f.dot(v, f.matvec(Q, w))


def actual_rates():
    u, nu = interacting_datum(), f.QQ_I(1)/10
    B = f.jac(u)
    p = f.tensor_pressure(f.tensor(u, u))
    H1 = vector_transport(u, u, nu)
    u1 = vector_add(H1, vector_scale(-1, f.grad(p)))
    B1 = f.jac(u1)
    p1 = f.tensor_pressure(pm.symmetric_product(u, u1))
    u2 = vector_add(vector_transport(u, u1, nu),
        vector_scale(-1, [f.adv(u1, v) for v in u]), vector_scale(-1, f.grad(p1)))
    B2 = f.jac(u2)
    for n, v in enumerate((u, u1, u2)):
        f.equal(pm.divergence(v), {}, ('full canonical solenoidal velocity jet', n))
    I = identity()
    N1 = scale(-1, add(B, pm.transpose(B)))
    N2 = add(matrix_transport(u, N1, nu), scale(-1, add(pm.transpose(B1), B1)),
        scale(-1, multiply(pm.transpose(B), N1)), scale(-1, multiply(N1, B)))
    N3 = add(matrix_transport(u, N2, nu), scale(-2, pm.matrix_adv(u1, N1)),
        scale(-1, add(pm.transpose(B2), B2)), scale(-2, multiply(pm.transpose(B1), N1)),
        scale(-2, multiply(N1, B1)), scale(-1, multiply(pm.transpose(B), N2)),
        scale(-1, multiply(N2, B)))
    L = [scale(-1, add(kronecker(pm.transpose(b), I), kronecker(I, pm.transpose(b))))
         for b in (B, B1, B2)]
    C1 = add(L[0], pm.transpose(L[0]))
    C2 = add(matrix_transport(u, C1, nu), L[1], pm.transpose(L[1]),
             multiply(L[0], C1), multiply(C1, pm.transpose(L[0])))
    C3 = add(matrix_transport(u, C2, nu),
        scale(-2, [[f.adv(u1, q) for q in row] for row in C1]), L[2], pm.transpose(L[2]),
        scale(2, multiply(L[1], C1)), scale(2, multiply(C1, pm.transpose(L[1]))),
        multiply(L[0], C2), multiply(C2, pm.transpose(L[0])))
    independent1 = add(kronecker(N1, I), kronecker(I, N1))
    independent2 = add(kronecker(N2, I), kronecker(I, N2), scale(2, kronecker(N1, N1)))
    independent3 = add(kronecker(N3, I), kronecker(I, N3),
                       scale(3, kronecker(N1, N2)), scale(3, kronecker(N2, N1)))
    equal(C1, independent1, 'joint and independent moment first jets match')
    equal(C2, independent2, 'joint and independent moment second jets match')
    tensor_gap3 = subtract(C3, independent3)
    source = scale(4*nu, add(*(kronecker(pm.matrix_diff(N1, k), pm.matrix_diff(N1, k))
                               for k in range(3))))
    equal(tensor_gap3, source, 'complete joint tensor gap retains the shared-noise diffusion')
    # A skew tensor sees exactly the area-moment difference. This
    # probes also retain the same original path copies.
    for v in ((1, 0, 0), (0, 1, 0), (0, 0, 1), (1, -2, 3)):
        z = [f.scale(q, {f.ORIGIN: f.QQ_I.one}) for q in v]
        skew = [[{}, f.scale(-1, z[2]), z[1]], [z[2], {}, f.scale(-1, z[0])],
                [f.scale(-1, z[1]), z[0], {}]]
        gap_area3 = scale(4*nu, add(*(adjugate(pm.matrix_diff(N1, k)) for k in range(3))))
        f.equal(metric(flatten(skew), tensor_gap3, flatten(skew)),
                f.scale(2, metric(z, gap_area3, z)), 'joint tensor gap keeps the actual area channel')

    m1 = covector_rhs(nu, u, B, u)
    m2 = vector_add(covector_rhs(nu, u, B, m1),
        vector_scale(-1, [f.adv(u1, v) for v in u]),
        vector_scale(-1, f.matvec(pm.transpose(B1), u)))

    # This source-free packet retains the original label gradient and
    # both frame copies. It differs from the generated defect Y below.
    A1 = add(matrix_transport(u, B, nu), scale(-1, multiply(pm.transpose(B), B)),
             scale(-1, multiply(B, B)))
    A2 = add(matrix_transport(u, A1, nu), scale(-1, pm.matrix_adv(u1, B)),
        scale(-1, multiply(pm.transpose(B1), B)), scale(-1, multiply(pm.transpose(B), A1)),
        scale(-1, multiply(A1, B)), scale(-1, multiply(B, B1)))
    for n, (a, m, v) in enumerate(zip((B, A1, A2), (u, m1, m2), (u, u1, u2))):
        curvature = subtract(f.jac(m), a)
        equal(curvature, pm.transpose(curvature), ('actual flow-curvature jet stays symmetric', n))
        skew = [f.add(a[2][1], f.scale(-1, a[1][2])),
                f.add(a[0][2], f.scale(-1, a[2][0])), f.add(a[1][0], f.scale(-1, a[0][1]))]
        for i in range(3):
            f.equal(f.curl(v)[i], skew[i], ('original transported tensor retains actual curl', n, i))

    W1 = scale(-1, C1)
    W2 = add(scale(-1, C2), scale(2, multiply(C1, C1)))
    a0, a1, a2 = map(flatten, (B, A1, A2))
    original_q0 = f.dot(a0, a0)
    original_q1 = f.add(f.scale(2, f.dot(a0, a1)), metric(a0, W1, a0))
    original_q2 = f.add(f.scale(2, f.dot(a1, a1)), f.scale(2, f.dot(a0, a2)),
                        f.scale(4, metric(a0, W1, a1)), metric(a0, W2, a0))
    original_cost0, original_cost1 = {}, {}
    for k in range(3):
        da0 = flatten(pm.matrix_diff(B, k))
        da1 = flatten(pm.matrix_diff(A1, k))
        Kjoint1 = pm.matrix_diff(C1, k)
        connection1 = f.matvec(Kjoint1, a0)
        require(len(da0) == len(da1) == len(connection1) == 9,
                'original tensor diffusion retains all nine coordinates')
        residual1 = [f.add(da1[i], f.scale(-1, connection1[i])) for i in range(9)]
        original_cost0 = f.add(original_cost0, f.dot(da0, da0))
        original_cost1 = f.add(original_cost1, f.scale(2, f.dot(da0, residual1)),
                              metric(da0, W1, da0))
    f.equal(f.add(original_q1, f.adv(u, original_q0), f.scale(-nu, f.lap(original_q0))),
            f.scale(-2*nu, original_cost0), 'original tensor full diffusion has no internal source')
    f.equal(f.add(original_q2, f.adv(u1, original_q0), f.adv(u, original_q1),
                  f.scale(-nu, f.lap(original_q1))), f.scale(-2*nu, original_cost1),
            'original tensor diffusion keeps changing drift, pressure and joint metric derivatives')
    require(pm.mean(original_q1) == pm.mean(f.scale(-2*nu, original_cost0)),
            'original normalized gradient energy pays initial full diffusion')
    Q1 = scale(-1, N1)
    K1 = [pm.matrix_diff(N1, j) for j in range(3)]
    K2 = [add(pm.matrix_diff(N2, j), scale(2, multiply(K1[j], Q1))) for j in range(3)]
    R1 = matrix_from_columns([vector_add([f.diff(v, j) for v in m1],
            vector_scale(-1, f.matvec(K1[j], u))) for j in range(3)])
    R2 = matrix_from_columns([vector_add([f.diff(v, j) for v in m2],
        vector_scale(-1, f.matvec(K2[j], u)), vector_scale(-2, f.matvec(K1[j], m1)))
        for j in range(3)])
    H2 = vector_add(vector_transport(u, H1, nu),
                    vector_scale(-1, [f.adv(u1, v) for v in u]))
    BH1 = f.jac(H1)
    Y1, Y2 = subtract(R1, BH1), subtract(R2, f.jac(H2))
    T0 = subtract(pm.matrix_adv(u, B), multiply(pm.transpose(B), B))
    equal(Y1, T0, 'actual pressure-completed tensor begins at its retained source')
    a1 = [f.scale(nu, f.lap(v)) for v in u]
    S1 = matrix_from_columns([vector_add(
        f.matvec(N1, f.matvec(pm.matrix_diff(B, j), u)),
        f.matvec(pm.matrix_diff(B1, j), u), f.matvec(pm.matrix_diff(B, j), a1),
        vector_scale(2*nu, vector_add(*(f.matvec(pm.matrix_diff(K1[j], k), columns(B)[k])
                                        for k in range(3))))) for j in range(3)])
    T1 = subtract(subtract(S1, multiply(pm.transpose(B1), B)), multiply(pm.transpose(B), BH1))
    lhs = add(Y2, pm.matrix_adv(u, Y1), scale(-nu, [[f.lap(v) for v in row] for row in Y1]))
    equal(lhs, add(scale(-1, multiply(pm.transpose(B), Y1)), scale(-1, multiply(Y1, B)), T1),
          'actual tensor source law retains all physical Hessian and diffusion terms')

    # Q_joint=C_joint^-1. Y(0)=0, so third scalar order needs
    # precisely its actual first metric jet -C1, not a frozen metric.
    Qjoint1 = scale(-1, C1)
    y1, y2, t0, t1 = map(flatten, (Y1, Y2, T0, T1))
    q2 = f.scale(2, f.dot(y1, y1))
    q3 = f.scale(6, f.add(f.dot(y1, y2), metric(y1, Qjoint1, y1)))
    work1 = f.dot(y1, t0)
    work2 = f.add(f.dot(y2, t0), f.scale(2, f.dot(y1, t1)),
                 f.scale(2, metric(y1, Qjoint1, t0)))
    cost2 = f.scale(2, f.add(*(f.dot(flatten(pm.matrix_diff(Y1, k)),
                                    flatten(pm.matrix_diff(Y1, k))) for k in range(3))))
    f.equal(q2, f.scale(2, work1), 'actual initial generated tensor work is retained')
    f.equal(f.add(q3, f.adv(u, q2), f.scale(-nu, f.lap(q2))),
        f.add(f.scale(2, work2), f.scale(-2*nu, cost2)),
        'complete joint tensor production keeps source, metric derivatives and diffusion')
    require(pm.mean(work1) > 0, 'unforced internal source is not set to zero')
    alpha = pm.mean(pm.pair(B, B))/pm.mean(f.dot(u, u))
    force = [f.add(f.scale(-1, f.lap(v)), f.scale(-f.QQ_I(alpha), v)) for v in u]
    f.equal(pm.divergence(force), {}, 'physical forcing filter stays solenoidal')
    require(pm.mean(f.dot(u, force)) == 0, 'physical filter has zero initial kinetic work')
    forced_Y1 = add(Y1, f.jac(force))
    equal(forced_Y1, subtract(add(R1, f.jac(force)), BH1),
          'original passive parent retains the full force gradient in the tensor source')
    force_gradient_square = pm.mean(pm.pair(f.jac(force), f.jac(force)))
    require(force_gradient_square > 0, 'zero kinetic force work does not remove the tensor source')
    forced_curl1 = f.curl(vector_add(u1, force))
    original_skew1 = [f.add(A1[2][1], f.scale(-1, A1[1][2])),
                     f.add(A1[0][2], f.scale(-1, A1[2][0])),
                     f.add(A1[1][0], f.scale(-1, A1[0][1]))]
    curl_force = f.curl(force)
    for i in range(3):
        f.equal(f.add(forced_curl1[i], f.scale(-1, original_skew1[i])), curl_force[i],
                'physical force adds a curl channel absent from the original source-free tensor')
    force_curl_square = pm.mean(f.dot(curl_force, curl_force))
    require(force_curl_square > 0, 'forced curl reconstruction cannot use the original gradient packet alone')
    return {'viscosity': str(nu.x), 'joint_moment_gap_first_and_second_jets': '0',
        'joint_moment_gap_third_jet': '4nu sum_k N1_k tensor N1_k, all entries checked',
        'generated_source_work_first_jet_mean': str(pm.mean(work1)),
        'normalized_tensor_square_second_jet_mean': str(pm.mean(q2)),
        'normalized_tensor_square_third_jet_mean': str(pm.mean(q3)),
        'full_joint_diffusion_second_jet_mean': str(pm.mean(cost2)),
        'original_tensor_curl_and_symmetric_curvature_jets': 'orders 0, 1 and 2, all outputs',
        'original_gradient_energy': str(pm.mean(original_q0)),
        'original_normalized_square_first_jet_mean': str(pm.mean(original_q1)),
        'original_normalized_square_second_jet_mean': str(pm.mean(original_q2)),
        'original_full_diffusion_initial_mean': str(pm.mean(original_cost0)),
        'original_full_diffusion_first_jet_mean': str(pm.mean(original_cost1)),
        'force_gradient_square': str(force_gradient_square),
        'force_curl_square': str(force_curl_square),
        'force_scope': 'initial fixed solenoidal source filter, not the imported singular trajectory',
        'scope': 'all-output canonical unforced NS and joint frame jets, not a continuum flow certificate'}


def finite_joint_metric():
    weights = [s.Rational(1, 3), s.Rational(1, 6), s.Rational(1, 2)]
    frames = [s.Matrix([[1, 2, 0], [0, 1, 1], [0, 0, 1]]),
              s.Matrix([[1, 0, 1], [-2, 1, 0], [0, 0, 1]]),
              s.Matrix([[2, 1, 0], [0, s.Rational(1, 2), 0], [0, 0, 1]])]
    G = [F.T*F for F in frames]
    C = sum((w*s.kronecker_product(g, g) for w, g in zip(weights, G)), s.zeros(9))
    gram = sum((w*s.kronecker_product(F, F).T*s.kronecker_product(F, F)
                for w, F in zip(weights, frames)), s.zeros(9))
    require(C == gram and all(F.det() == 1 for F in frames), 'same-sample determinant-one tensor Gram')
    require(all(C[:k, :k].det() > 0 for k in range(1, 10)), 'positive joint moment has an exact inverse')
    Q = C.inv()
    label_gradients = [s.Matrix([[1, -2, 3], [2, 1, -1], [0, 4, -2]]),
                       s.Matrix([[2, 0, 1], [-3, -1, 2], [1, 1, -1]]),
                       s.Matrix([[-1, 3, 2], [1, 2, 0], [-2, 1, -1]])]
    packet = sum((w*F.T*V*F for w, F, V in zip(weights, frames, label_gradients)), s.zeros(3))
    covector = sum((w*s.kronecker_product(F, F).T*s.Matrix(list(V))
                    for w, F, V in zip(weights, frames, label_gradients)), s.zeros(9, 1))
    require(s.Matrix(list(packet)) == covector, 'original tensor and joint covector are identical')
    fitted = Q*covector
    energy = sum(w*sum(v*v for v in V) for w, V in zip(weights, label_gradients))
    variance = sum(w*(s.Matrix(list(V))-s.kronecker_product(F, F)*fitted).dot(
        s.Matrix(list(V))-s.kronecker_product(F, F)*fitted)
        for w, F, V in zip(weights, frames, label_gradients))
    paid = (covector.T*Q*covector)[0]
    require(variance == energy-paid and variance > 0 and 0 < paid < energy,
            'same-label original tensor has exact nonnegative finite original-gradient payment')
    N = sum((w*g for w, g in zip(weights, G)), s.zeros(3))
    M = sum((w*g.adjugate() for w, g in zip(weights, G)), s.zeros(3))
    independent = s.kronecker_product(N, N)
    require(independent != C, 'independent averaging changes the joint metric')
    v = s.Matrix([2, -3, 1])
    skew = s.Matrix([[0, -v[2], v[1]], [v[2], 0, -v[0]], [-v[1], v[0], 0]])
    e = s.Matrix(list(skew))
    require((e.T*C*e)[0] == 2*(v.T*M*v)[0], 'joint skew metric retains actual forward area moment')
    require((e.T*(C-independent)*e)[0] == 2*(v.T*(M-N.adjugate())*v)[0],
            'independent compression loses the signed area covariance')
    B = s.Matrix([[1, 2, 3], [-3, 0, 1], [2, -1, -1]])
    L = -s.kronecker_product(B.T, s.eye(3))-s.kronecker_product(s.eye(3), B.T)
    Z = [s.Matrix([[1, 2, 0], [-1, -1, 1], [0, 1, 0]]),
         s.Matrix([[0, 1, -1], [1, 2, 0], [0, -1, -2]]),
         s.Matrix([[2, -1, 1], [0, 0, 2], [1, 2, -2]])]
    require(all(a.trace() == 0 for a in Z), 'frame spatial directions preserve volume to first order')
    Ck = []
    for k in range(3):
        dG = [Z[k].T*g+g*Z[k] for g in G]
        Ck.append(sum((w*(s.kronecker_product(d, g)+s.kronecker_product(g, d))
                       for w, d, g in zip(weights, dG, G)), s.zeros(9)))
    K = [d*Q for d in Ck]
    dQ = [-Q*d*Q for d in Ck]
    nu = s.Rational(1, 10)
    DQ = -Q*L-L.T*Q-2*nu*sum((k.T*Q*k for k in K), s.zeros(9))
    Y = s.Matrix([[1, -2, 3], [2, 0, -1], [-1, 4, 2]])
    BH = s.Matrix([[1, 0, 2], [-2, 3, 0], [1, -1, 1]])
    S = s.Matrix([[2, 1, -1], [3, -2, 1], [0, 2, 4]])
    source = S-B.T*BH
    y, T = s.Matrix(list(Y)), s.Matrix(list(source))
    DY = -B.T*Y-Y*B+source
    require(s.Matrix(list(DY)) == L*y+T, 'literal two-index defect and original-parent source')
    dy = [s.Matrix([(j+1)*(k+1)-2 for j in range(9)]) for k in range(3)]
    full = 2*(y.T*Q*s.Matrix(list(DY)))[0]+(y.T*DQ*y)[0] \
        -2*nu*sum((v.T*Q*v)[0] for v in dy)-4*nu*sum((y.T*dQ[k]*dy[k])[0] for k in range(3))
    cost = sum(((dy[k]-K[k]*y).T*Q*(dy[k]-K[k]*y))[0] for k in range(3))
    work = (y.T*Q*T)[0]
    require(full == 2*work-2*nu*cost and cost > 0,
            'joint inverse metric cancels both strains with full nonzero diffusion')
    return {'joint_skew_area_square': str((e.T*C*e)[0]),
        'lost_area_covariance': str((e.T*(C-independent)*e)[0]),
        'joint_normalized_diffusion': str(cost), 'retained_source_work': str(work),
        'complete_joint_production': str(full),
        'original_label_gradient_energy': str(energy),
        'original_joint_normalized_tensor_square': str(paid),
        'original_joint_variance': str(variance),
        'scope': 'exact same-sample finite frames and spatial variations, not an NS realization'}


def independent_product_defect():
    nu = s.Rational(1, 10)
    N = s.Matrix([[2, 1, 0], [1, 3, 1], [0, 1, 2]])
    Q = N.inv()
    Nk = [s.Matrix([[1, 2, 0], [2, -1, 1], [0, 1, 1]]),
          s.Matrix([[0, 1, -1], [1, 2, 0], [-1, 0, 1]]),
          s.Matrix([[2, -1, 1], [-1, 0, 2], [1, 2, -2]])]
    K = [a*Q for a in Nk]
    W = s.kronecker_product(Q, Q)
    K2 = [s.kronecker_product(k, s.eye(3))+s.kronecker_product(s.eye(3), k) for k in K]
    DQdiff = -2*nu*sum((k.T*Q*k for k in K), s.zeros(3))
    actual = s.kronecker_product(DQdiff, Q)+s.kronecker_product(Q, DQdiff) \
        -2*nu*sum((s.kronecker_product(Q*k, Q*k) for k in K), s.zeros(9))
    cross = 2*nu*sum((s.kronecker_product(Q*k, Q*k) for k in K), s.zeros(9))
    require(actual == -2*nu*sum((k.T*W*k for k in K2), s.zeros(9))+cross,
            'complete independent tensor metric retains its signed cross diffusion')
    # One spatial direction already allows either sign; this is an
    # algebra fixture, not an asserted fluid frame history.
    one_cross = 2*nu*s.kronecker_product(Q*K[0], Q*K[0])
    positive = s.Matrix(list(s.eye(3)))
    negative = s.Matrix(list(s.diag(1, -1, 0)))
    require((positive.T*one_cross*positive)[0] > 0 and
            (negative.T*one_cross*negative)[0] < 0, 'extra cross diffusion has no universal sign')

    # The actual compactly localizable core has a positive leading
    # correction for its own pressure-completed Y, not a chosen tensor.
    x, y, z = s.symbols('x y z')
    variables = (x, y, z)
    u = s.Matrix([x*z-y, x+y*z, (x*x+y*y)/2-z*z])
    B = u.jacobian(variables)
    actual_Y1 = -B.T*B+sum((u[k]*B.diff(variables[k]) for k in range(3)), s.zeros(3))
    point = {x: 0, y: 0, z: -1}
    Y1 = actual_Y1.subs(point)
    N1k = [-(B+B.T).diff(v) for v in variables]
    coefficient = 2*nu*sum(s.trace(Y1.T*k*Y1*k) for k in N1k)
    require(Y1 == s.diag(-3, -3, -2) and coefficient == s.Rational(232, 5),
            'actual retained gradient defect has a positive leading independent-metric correction')
    return {'supplied_positive_cross': str((positive.T*one_cross*positive)[0]),
        'supplied_negative_cross': str((negative.T*one_cross*negative)[0]),
        'localized_actual_Y_first_jet': [[str(v) for v in row] for row in Y1.tolist()],
        'actual_product_metric_extra_diffusion_leading_t4': str(coefficient),
        'actual_product_minus_joint_square_leading_t5': str(coefficient/3),
        'analytic_scope': 'localized finite-energy unforced prefix, stochastic/Taylor passage analytic',
        'not_refuted': 'joint metric production or finite full-datum source history payment'}


if __name__ == '__main__':
    print(json.dumps({'actual_rates': actual_rates(), 'finite_joint_metric': finite_joint_metric(),
        'independent_product_defect': independent_product_defect(),
        'remaining': 'continuous construction; physical coercivity/critical history conversion; retained Y source allowance',
        'global_regularity': 'OPEN'}, indent=2))
