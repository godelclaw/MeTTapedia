#!/usr/bin/env python3
"""Actual receiver cancellation, pressure completion and signed area memory.

Gaussian-rational Fourier checks retain every output on the 2*pi torus.
They test the full canonical initial NS/covector/frame equations, not a
truncated evolution. Independent local matrix jets test the parabolic
cofactor rule. A polynomial core can be localized as curl(chi*A); the
smooth cutoff, stochastic construction and short-time Taylor passage
are analytic arguments, not certificates produced by this script.
"""

import json
import sympy as s
import pressure_history_source as f
import pressure_memory_diffusion as pm
from pressure_impulse_history import vector_transport, matrix_transport, vectors_equal
from signed_viscous_pressure import interacting_datum
from joint_coframe_pressure import identity, require
from covector_fluid_bridge import vector_add, vector_scale, covector_rhs, projection


def matrix_sub(a, b):
    return pm.matrix_add(a, pm.matrix_scale(-1, b))


def matrix_lap(a):
    return [[f.lap(v) for v in row] for row in a]


def matrix_from_columns(columns):
    return [[columns[j][i] for j in range(3)] for i in range(3)]


def columns(a):
    return [[a[i][j] for i in range(3)] for j in range(3)]


def adjugate(a):
    out = []
    for i in range(3):
        row = []
        for j in range(3):
            rows = [k for k in range(3) if k != j]
            cols = [k for k in range(3) if k != i]
            minor = f.add(f.mul(a[rows[0]][cols[0]], a[rows[1]][cols[1]]),
                         f.scale(-1, f.mul(a[rows[0]][cols[1]], a[rows[1]][cols[0]])))
            row.append(f.scale((-1)**(i+j), minor))
        out.append(row)
    return out


def adjugate_linear_at_identity(a):
    return matrix_sub(pm.matrix_scalar(f.trace(a), identity()), a)


def adjugate_polar(a, b):
    return matrix_sub(matrix_sub(adjugate(pm.matrix_add(a, b)), adjugate(a)), adjugate(b))


def receiver(B, r):
    return vector_add(*(f.matvec(pm.transpose(pm.matrix_diff(B, j)), r[j])
                        for j in range(3)))


def actual_rates():
    u, nu = interacting_datum(), f.QQ_I(1)/10
    B = f.jac(u)
    p = f.tensor_pressure(f.tensor(u, u))
    gp = f.grad(p)
    u1 = vector_add(vector_transport(u, u, nu), vector_scale(-1, gp))
    B1 = f.jac(u1)
    p1 = f.tensor_pressure(pm.symmetric_product(u, u1))
    gp1 = f.grad(p1)
    u2 = vector_add(vector_transport(u, u1, nu),
        vector_scale(-1, [f.adv(u1, q) for q in u]), vector_scale(-1, gp1))
    B2 = f.jac(u2)
    for label, v in (('initial', u), ('first', u1), ('second', u2)):
        f.equal(pm.divergence(v), {}, ('full physical NS tangent is solenoidal', label))

    m1 = covector_rhs(nu, u, B, u)
    m2 = vector_add(covector_rhs(nu, u, B, m1),
        vector_scale(-1, [f.adv(u1, q) for q in u]),
        vector_scale(-1, f.matvec(pm.transpose(B1), u)))
    N1 = pm.matrix_scale(-1, pm.matrix_add(B, pm.transpose(B)))
    M1 = pm.matrix_scale(-1, N1)
    N2 = pm.matrix_add(matrix_transport(u, N1, nu),
        pm.matrix_scale(-1, pm.matrix_add(pm.transpose(B1), B1)),
        pm.matrix_scale(-1, f.matmul(pm.transpose(B), N1)),
        pm.matrix_scale(-1, f.matmul(N1, B)))
    M2 = pm.matrix_add(matrix_transport(u, M1, nu), pm.transpose(B1), B1,
        f.matmul(B, M1), f.matmul(M1, pm.transpose(B)))
    N3 = pm.matrix_add(matrix_transport(u, N2, nu),
        pm.matrix_scale(-2, pm.matrix_adv(u1, N1)),
        pm.matrix_scale(-1, pm.matrix_add(pm.transpose(B2), B2)),
        pm.matrix_scale(-2, f.matmul(pm.transpose(B1), N1)),
        pm.matrix_scale(-2, f.matmul(N1, B1)),
        pm.matrix_scale(-1, f.matmul(pm.transpose(B), N2)),
        pm.matrix_scale(-1, f.matmul(N2, B)))
    M3 = pm.matrix_add(matrix_transport(u, M2, nu),
        pm.matrix_scale(-2, pm.matrix_adv(u1, M1)), pm.transpose(B2), B2,
        pm.matrix_scale(2, f.matmul(B1, M1)),
        pm.matrix_scale(2, f.matmul(M1, pm.transpose(B1))),
        f.matmul(B, M2), f.matmul(M2, pm.transpose(B)))
    zero = [[{} for _ in range(3)] for _ in range(3)]
    f.same_matrices(M1, adjugate_linear_at_identity(N1), 'joint area gap first time jet vanishes')
    adjN2 = pm.matrix_add(adjugate_linear_at_identity(N2), pm.matrix_scale(2, adjugate(N1)))
    f.same_matrices(M2, adjN2, 'joint area gap second time jet vanishes')
    adjN3 = pm.matrix_add(adjugate_linear_at_identity(N3),
                         pm.matrix_scale(3, adjugate_polar(N1, N2)))
    gap3 = matrix_sub(M3, adjN3)
    expected_gap3 = pm.matrix_scale(4*nu,
        pm.matrix_add(*(adjugate(pm.matrix_diff(N1, j)) for j in range(3))))
    f.same_matrices(gap3, expected_gap3,
                    'full physical frame jets give the signed cofactor diffusion source')
    require(f.evaluate(gap3[0][0]) > 0, 'actual area gap has a positive direction')

    Q1 = pm.matrix_scale(-1, N1)
    K1 = [pm.matrix_diff(N1, j) for j in range(3)]
    K2 = [pm.matrix_add(pm.matrix_diff(N2, j),
                        pm.matrix_scale(2, f.matmul(K1[j], Q1))) for j in range(3)]
    r0 = columns(B)
    r1 = [vector_add([f.diff(v, j) for v in m1],
                     vector_scale(-1, f.matvec(K1[j], u))) for j in range(3)]
    r2 = [vector_add([f.diff(v, j) for v in m2],
        vector_scale(-1, f.matvec(K2[j], u)),
        vector_scale(-2, f.matvec(K1[j], m1))) for j in range(3)]
    R1, R2 = matrix_from_columns(r1), matrix_from_columns(r2)
    E1, E2 = matrix_sub(R1, B1), matrix_sub(R2, B2)
    H1 = vector_transport(u, u, nu)
    H2 = vector_add(vector_transport(u, H1, nu),
                    vector_scale(-1, [f.adv(u1, q) for q in u]))
    BH1, BH2 = f.jac(H1), f.jac(H2)
    Y1, Y2 = matrix_sub(R1, BH1), matrix_sub(R2, BH2)
    P0, P1 = f.hess(p), f.hess(p1)
    a1 = vector_add(f.matvec(Q1, u), m1)
    vectors_equal(a1, [f.scale(nu, f.lap(q)) for q in u], 'actual normalized parent first jet')
    S0 = pm.matrix_adv(u, B)
    S1 = matrix_from_columns([vector_add(
        f.matvec(N1, f.matvec(pm.matrix_diff(B, j), u)),
        f.matvec(pm.matrix_diff(B1, j), u),
        f.matvec(pm.matrix_diff(B, j), a1),
        vector_scale(2*nu, vector_add(*(f.matvec(pm.matrix_diff(K1[j], k), r0[k])
                                        for k in range(3))))) for j in range(3)])
    f.same_matrices(E1, pm.matrix_add(P0,
        pm.matrix_scale(-1, f.matmul(pm.transpose(B), B)), S0),
        'physical-gradient defect retains pressure and Hessian source')
    f.same_matrices(Y1, pm.matrix_add(
        pm.matrix_scale(-1, f.matmul(pm.transpose(B), B)), S0),
        'original passive parent removes the explicit pressure Hessian')
    # The first derivative of the full material-parabolic law keeps all
    # drift, original-parent and connection diffusion terms.
    DE1 = pm.matrix_add(E2, pm.matrix_adv(u, E1), pm.matrix_scale(-nu, matrix_lap(E1)))
    expected_E = pm.matrix_add(pm.matrix_scale(-1, f.matmul(pm.transpose(B), E1)),
        pm.matrix_scale(-1, f.matmul(E1, B)), P1,
        pm.matrix_scale(-1, f.matmul(pm.transpose(B1), B)),
        pm.matrix_scale(-1, f.matmul(pm.transpose(B), B1)), S1)
    f.same_matrices(DE1, expected_E, 'complete evolving receiver defect retains physical pressure')
    DY1 = pm.matrix_add(Y2, pm.matrix_adv(u, Y1), pm.matrix_scale(-nu, matrix_lap(Y1)))
    expected_Y = pm.matrix_add(pm.matrix_scale(-1, f.matmul(pm.transpose(B), Y1)),
        pm.matrix_scale(-1, f.matmul(Y1, B)),
        pm.matrix_scale(-1, f.matmul(pm.transpose(B1), B)),
        pm.matrix_scale(-1, f.matmul(pm.transpose(B), BH1)), S1)
    f.same_matrices(DY1, expected_Y,
        'completed receiver law retains original parent and every connection source')
    f.same_matrices(E1, pm.matrix_add(f.jac(vector_add(H1, vector_scale(-1, u1))), Y1),
                    'pressure impulse and completed receiver reconstruct the actual defect')

    z0 = receiver(B, r0)
    vectors_equal(z0, f.grad(f.scale(f.QQ_I(1)/2, pm.pair(B, B))),
                  'physical-gradient receiver is a gradient')
    vectors_equal(projection(z0), [{}, {}, {}], 'initial solenoidal receiver vanishes')
    z1 = vector_add(receiver(B1, r0), receiver(B, r1))
    d1 = receiver(B, columns(E1))
    vectors_equal(vector_add(z1, vector_scale(-1, f.grad(pm.pair(B, B1)))), d1,
                  'complete current-velocity gradient cancellation retains the defect')
    projected = projection(z1)
    vectors_equal(projected, projection(d1), 'actual projected receiver comes from retained history')
    initial_work = pm.mean(f.dot(z0, u))
    work1 = pm.mean(f.add(f.dot(z1, u), f.dot(z0, a1)))
    projected_square = pm.mean(f.dot(projected, projected))
    require(initial_work == 0 and work1 > 0 and projected_square > 0,
            'zero initial receiver is not a persistent zero parent-work theorem')

    # A fixed physical solenoidal force cannot be absorbed into free
    # sampling. Zero initial kinetic work does not remove its history.
    alpha = pm.mean(pm.pair(B, B))/pm.mean(f.dot(u, u))
    force = [f.add(f.scale(-1, f.lap(v)), f.scale(-f.QQ_I(alpha), v)) for v in u]
    f.equal(pm.divergence(force), {}, 'physical force is solenoidal')
    require(pm.mean(f.dot(u, force)) == 0, 'force has zero initial kinetic work')
    forced_R1 = f.jac(vector_add(m1, force))
    forced_R1 = matrix_sub(forced_R1, matrix_from_columns([f.matvec(K1[j], u) for j in range(3)]))
    forced_B1 = f.jac(vector_add(u1, force))
    f.same_matrices(matrix_sub(forced_R1, forced_B1), E1,
                    'initial force gradients cancel only in physical-gradient comparison')
    f.same_matrices(matrix_sub(forced_R1, BH1), pm.matrix_add(Y1, f.jac(force)),
                    'original-parent completion retains physical force gradient')
    require(pm.mean(pm.pair(f.jac(force), f.jac(force))) > 0,
            'nonzero force history survives zero initial force work')
    # Exercise zero separately; no assertion about a sampled time flow.
    f.same_matrices(matrix_sub(identity(), adjugate(identity())), zero, 'original joint area gap is zero')
    return {'viscosity': str(nu.x), 'initial_parent_work': str(initial_work),
        'parent_work_first_derivative': str(work1),
        'projected_receiver_first_jet_square': str(projected_square),
        'completed_defect_first_jet_square': str(pm.mean(pm.pair(Y1, Y1))),
        'area_gap_third_jet_at_origin': [[str(f.evaluate(v)) for v in row] for row in gap3],
        'area_gap_third_jet_trace_mean': str(pm.mean(f.trace(gap3))),
        'failed_shortcuts': ['the initially gradient receiver stays projected to zero',
                             'forward moment is bounded by the adjugate of the mean coframe'],
        'scope': 'complete canonical unforced initial PDE jets; continuum realization analytic',
        'force_scope': 'explicit initial solenoidal source filter, not an imported singular trajectory'}


def local_cofactor_rule():
    """Independent space/time matrix jets test the full diffusion rule."""
    t = s.Symbol('t')
    x = s.symbols('x:3')
    nu = s.Rational(1, 10)
    N0 = s.Matrix([[2, 1, 0], [1, 3, 1], [0, 1, 2]])
    B = s.Matrix([[1, 2, 3], [-3, 0, 1], [2, -1, -1]])
    Nj = [s.Matrix([[1, 2, 0], [2, -1, 1], [0, 1, 1]]),
          s.Matrix([[0, 1, -1], [1, 2, 0], [-1, 0, 1]]),
          s.Matrix([[2, -1, 1], [-1, 0, 2], [1, 2, -2]])]
    Njk = [(j+1)*s.Matrix([[1, 0, 1], [0, -1, 2], [1, 2, 0]]) for j in range(3)]
    DN = -B.T*N0-N0*B
    Nt = DN+nu*sum(Njk, s.zeros(3))
    N = N0+t*Nt+sum((x[j]*Nj[j]+x[j]**2*Njk[j]/2 for j in range(3)), s.zeros(3))
    origin = {t: 0, **{q: 0 for q in x}}
    area = N.adjugate()
    Darea = (area.diff(t)-nu*sum((area.diff(q, 2) for q in x), s.zeros(3))).subs(origin)
    signed_source = 2*nu*sum((a.adjugate() for a in Nj), s.zeros(3))
    require(B.trace() == 0 and N0.is_positive_definite, 'positive coframe and incompressible drift fixture')
    require(Darea == B*N0.adjugate()+N0.adjugate()*B.T-signed_source,
            'complete parabolic adjugate chain rule retains signed area source')
    require(signed_source != s.zeros(3), 'nonzero cofactor diffusion is exercised')
    return {'signed_area_source': [[str(v) for v in row] for row in signed_source.tolist()],
        'scope': 'independent complete supplied matrix jets, not a constructed NS trajectory'}


def localized_straining_core():
    x, y, z = s.symbols('x y z')
    coordinates = s.Matrix([x, y, z])
    variables = (x, y, z)
    quadratic = s.Matrix([x*z, y*z, (x*x+y*y)/2-z*z])
    rotation = s.Matrix([-y, x, 0])
    u = quadratic+rotation
    def curl(v):
        return s.Matrix([s.diff(v[(j+2) % 3], variables[(j+1) % 3])-
                         s.diff(v[(j+1) % 3], variables[(j+2) % 3]) for j in range(3)])
    potential = -coordinates.cross(quadratic)/4-coordinates.cross(rotation)/3
    require(s.simplify(curl(potential)-u) == s.zeros(3, 1),
            'homogeneous vector potential permits compact solenoidal localization')
    B = u.jacobian(variables)
    require(B.trace() == 0, 'localized core has incompressible initial jets')
    nu = s.Rational(1, 10)
    N1 = -B-B.T
    gap3 = 4*nu*sum((N1.diff(q).adjugate() for q in variables), s.zeros(3))
    expected = s.diag(-s.Rational(24, 5), -s.Rational(24, 5), s.Rational(8, 5))
    require(gap3 == expected, 'actual leading joint area covariance is signed')
    energy_density = s.trace(B.T*B)/2
    receiver0 = s.Matrix([s.diff(energy_density, q) for q in variables])
    point = {x: 0, y: 0, z: -1}
    w0 = curl(u).subs(point)
    z0 = receiver0.subs(point)
    require(w0 == s.Matrix([0, 0, 2]), 'nonzero initial vorticity survives localization')
    stretching = w0.dot(B.subs(point)*w0)
    gap_work3 = z0.dot(gap3*z0)
    require(stretching == 8 and gap_work3 == s.Rational(288, 5),
            'positive stretching core refutes the cofactor shortcut in the actual receiver direction')
    require(w0.dot(gap3*w0) > 0, 'same failure occurs in the actual vorticity direction')
    return {'viscosity': str(nu), 'core_velocity': [str(v) for v in u],
        'point': [0, 0, -1], 'initial_vorticity': [str(v) for v in w0],
        'initial_vorticity_stretching': str(stretching),
        'actual_receiver': [str(v) for v in z0],
        'area_gap_third_jet': [[str(v) for v in row] for row in gap3.tolist()],
        'receiver_gap_third_jet': str(gap_work3),
        'receiver_gap_leading_time_coefficient': str(gap_work3/6),
        'analytic_localization': 'u0=curl(chi*potential), chi=1 on |x|<=2 and zero on |x|>=3',
        'analytic_time_scope': 'some positive short interval; no explicit uniform Taylor endpoint',
        'failed_claim': 'M<=adj(N), including testing in the actual current receiver or vorticity direction',
        'not_refuted': 'full-datum signed history payment or unforced global regularity'}


if __name__ == '__main__':
    print(json.dumps({'actual_rates': actual_rates(), 'local_cofactor_rule': local_cofactor_rule(),
        'localized_core': localized_straining_core(),
        'remaining': 'joint original-parent, receiver-defect and signed area-covariance history payment',
        'global_regularity': 'OPEN'}, indent=2))
