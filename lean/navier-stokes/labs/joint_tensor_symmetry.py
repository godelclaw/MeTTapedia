#!/usr/bin/env python3
"""Same-frame tensor channels and actual NS gradient compatibility.

Exact rational frames check the inverse metric and complete supplied
diffusion. Complete Fourier jets retain every generated parent and the
canonical pressure on the period-2*pi torus. The matrix-sign failure on
an actual short solution interval uses analytic stochastic identification
and local smooth existence; no uniform interval or history allowance is
certified by this script.
"""

import json
from fractions import Fraction

import sympy as s
import pressure_history_source as f
import pressure_memory_diffusion as pm
import joint_receiver_tensor as jt
from cyclic_pressure_history import time_jets, zero
from pressure_impulse_history import matrix_transport


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def sym(A):
    return (A + A.T)/2


def skew(A):
    return (A - A.T)/2


def axial(A):
    return s.Matrix([A[2, 1]-A[1, 2], A[0, 2]-A[2, 0], A[1, 0]-A[0, 1]])


def skew_matrix(z):
    return s.Matrix([[0, -z[2], z[1]], [z[2], 0, -z[0]], [-z[1], z[0], 0]])


def vec(A):
    return s.Matrix(list(A))


def finite_channels():
    weights = [s.Rational(1, 3), s.Rational(1, 6), s.Rational(1, 2)]
    frames = [s.Matrix([[1, 2, 0], [0, 1, 1], [0, 0, 1]]),
              s.Matrix([[1, 0, 1], [-2, 1, 0], [0, 0, 1]]),
              s.Matrix([[2, 1, 0], [0, s.Rational(1, 2), 0], [0, 0, 1]])]
    labels = [s.Matrix([[1, -2, 3], [2, 1, -1], [0, 4, -2]]),
              s.Matrix([[2, 0, 1], [-3, -1, 2], [1, 1, -1]]),
              s.Matrix([[-1, 3, 2], [1, 2, 0], [-2, 1, -1]])]
    require(sum(weights) == 1 and all(F.det() == 1 for F in frames),
            'one normalized law with determinant-one frames')
    inverse = [F.inv() for F in frames]
    grams = [F.T*F for F in frames]
    C = sum((w*s.kronecker_product(G, G) for w, G in zip(weights, grams)), s.zeros(9))
    M = sum((w*J*J.T for w, J in zip(weights, inverse)), s.zeros(3))
    require(all(C[:k, :k].det() > 0 for k in range(1, 10)), 'positive exact joint moment')
    Q, H = C.inv(), M.inv()
    T = s.zeros(9)
    for i in range(3):
        for j in range(3):
            T[3*i+j, 3*j+i] = 1
    embed = s.Matrix.hstack(*(vec(skew_matrix(s.eye(3)[:, k])) for k in range(3)))
    require(embed.T*embed == 2*s.eye(3), 'two entries per axial coordinate')
    require(C*T == T*C and Q*T == T*Q, 'same-frame swap symmetry survives inversion')
    require(C*embed == embed*M and Q*embed == embed*H, 'exact inverse restriction to the area channel')
    A = sum((w*F.T*V*F for w, F, V in zip(weights, frames, labels)), s.zeros(3))
    omega = axial(A)
    quadratic = lambda v: (v.T*Q*v)[0]
    paid, symmetric, rotational = map(quadratic, (vec(A), vec(sym(A)), vec(skew(A))))
    require((vec(sym(A)).T*Q*vec(skew(A)))[0] == 0, 'no symmetric/skew cross payment')
    require(paid == symmetric+rotational and rotational == (omega.T*H*omega)[0]/2,
            'normalized original tensor equals symmetric plus inverse-area curl energy')

    B = s.Matrix([[1, 2, -1], [-2, 0, 3], [4, -1, -1]])
    generators = [s.Matrix([[1, 2, 0], [-1, 0, 1], [2, 0, -1]]),
                  s.Matrix([[0, -1, 2], [3, 1, 0], [1, -2, -1]]),
                  s.Matrix([[-1, 0, 3], [1, 2, -1], [0, 1, -1]])]
    connections, derivatives = [], []
    full_cost = symmetric_cost = skew_cost = curl_cost = 0
    for k in range(3):
        dF = [F*((k+1)*R+(j-1)*generators[(j+1) % 3].T)
              for j, (F, R) in enumerate(zip(frames, generators))]
        require(all((F.inv()*d).trace() == 0 for F, d in zip(frames, dF)),
                'spatial frame tangents preserve determinant')
        dJ = [-J*d*J for J, d in zip(inverse, dF)]
        dG = [d.T*F+F.T*d for F, d in zip(frames, dF)]
        dC = sum((w*(s.kronecker_product(d, G)+s.kronecker_product(G, d))
                  for w, G, d in zip(weights, grams, dG)), s.zeros(9))
        dM = sum((w*(d*J.T+J*d.T) for w, J, d in zip(weights, inverse, dJ)), s.zeros(3))
        dV = [(k+1)*V+(j-1)*B for j, V in enumerate(labels)]
        dA = sum((w*(d.T*V*F+F.T*dv*F+F.T*V*d)
                  for w, F, d, V, dv in zip(weights, frames, dF, labels, dV)), s.zeros(3))
        K = dC*Q
        require(dC*embed == embed*dM, 'differentiated common-frame area identity')
        require(K*T == T*K and Q*K == K.T*Q, 'complete connection preserves channels and metric')
        residual = vec(dA)-K*vec(A)
        rs = vec(sym(dA))-K*vec(sym(A))
        rk = vec(skew(dA))-K*vec(skew(A))
        rw = axial(dA)-dM*H*omega
        require(residual == rs+rk and T*rs == rs and T*rk == -rk,
                'all spatial residual coordinates retain their proper channel')
        require(rk == embed*rw/2, 'skew connection is precisely the evolving inverse-area connection')
        require(quadratic(residual) == quadratic(rs)+quadratic(rk), 'full diffusion split')
        require(quadratic(rk) == (rw.T*H*rw)[0]/2, 'full inverse-vorticity diffusion factor')
        full_cost += quadratic(residual)
        symmetric_cost += quadratic(rs)
        skew_cost += quadratic(rk)
        curl_cost += (rw.T*H*rw)[0]
        connections.append(K)
        derivatives.append(dA)
    require(full_cost == symmetric_cost+skew_cost and skew_cost == curl_cost/2,
            'complete three-direction diffusion; no dropped derivatives')
    nu = s.Rational(1, 10)
    L = -s.kronecker_product(B.T, s.eye(3))-s.kronecker_product(s.eye(3), B.T)
    DQ = -Q*L-L.T*Q-2*nu*sum((K.T*Q*K for K in connections), s.zeros(9))

    def production(Y, dY):
        v = vec(Y)
        diffusion = sum((vec(d).T*Q*vec(d))[0]
                        +2*(v.T*(-Q*K)*vec(d))[0] for K, d in zip(connections, dY))
        return 2*(v.T*Q*L*v)[0]+(v.T*DQ*v)[0]-2*nu*diffusion

    rate = production(A, derivatives)
    require(L*T == T*L, 'source-free tensor drift preserves both channels')
    require(rate == -2*nu*full_cost, 'full supplied inverse-metric production')
    require(rate == production(sym(A), list(map(sym, derivatives)))
            +production(skew(A), list(map(skew, derivatives))), 'production split includes diffusion')
    require(axial(-B.T*A-A*B) == B*omega, 'trace-free physical curl rate')
    return {'samples': 3, 'tensor_coordinates': 9, 'spatial_directions': 3,
            'same_frame_inverse_split': 'q_A=q_sym+(1/2)*omega^T M^-1 omega',
            'full_diffusion_split': 'F_A=F_sym+(1/2)*F_omega',
            'supplied_production': '-2*nu*F_A, with every spatial connection',
            'cross_pairing': '0', 'physical_history_scope': 'finite supplied frames and tangents, not a stochastic construction'}


def fourier_sym(A):
    return jt.scale(f.QQ_I(1)/2, jt.add(A, pm.transpose(A)))


def fourier_curl(A):
    return [f.add(A[2][1], f.scale(-1, A[1][2])),
            f.add(A[0][2], f.scale(-1, A[2][0])),
            f.add(A[1][0], f.scale(-1, A[0][1]))]


def quadratic_jets(A, W):
    a0, a1, a2 = map(jt.flatten, A)
    return [jt.metric(a0, W[0], a0),
            f.add(f.scale(2, jt.metric(a0, W[0], a1)), jt.metric(a0, W[1], a0)),
            f.add(f.scale(2, jt.metric(a1, W[0], a1)), f.scale(2, jt.metric(a0, W[0], a2)),
                  f.scale(4, jt.metric(a0, W[1], a1)), jt.metric(a0, W[2], a0))]


def actual_fourier():
    nu = f.QQ_I(1)/10
    jets, pressure = time_jets(Fraction(1), Fraction(1, 10), 2)
    u, u1, _ = jets
    B, B1, B2 = map(f.jac, jets)
    A1 = jt.add(matrix_transport(u, B, nu), jt.scale(-1, jt.multiply(pm.transpose(B), B)),
                jt.scale(-1, jt.multiply(B, B)))
    A2 = jt.add(matrix_transport(u, A1, nu), jt.scale(-1, pm.matrix_adv(u1, B)),
                jt.scale(-1, jt.multiply(pm.transpose(B1), B)),
                jt.scale(-1, jt.multiply(pm.transpose(B), A1)),
                jt.scale(-1, jt.multiply(A1, B)), jt.scale(-1, jt.multiply(B, B1)))
    E1, E2 = jt.subtract(A1, B1), jt.subtract(A2, B2)
    source0 = jt.subtract(f.hess(pressure[0]), jt.multiply(pm.transpose(B), B))
    source1 = jt.subtract(f.hess(pressure[1]),
                         jt.add(jt.multiply(pm.transpose(B1), B), jt.multiply(pm.transpose(B), B1)))
    jt.equal(E1, source0, 'actual original-gradient compatibility source initially')
    full_rate = jt.add(matrix_transport(u, E1, nu),
                       jt.scale(-1, jt.multiply(pm.transpose(B), E1)),
                       jt.scale(-1, jt.multiply(E1, B)), source1)
    jt.equal(E2, full_rate, 'complete time-differentiated pressure/gradient defect equation')
    for n, (A, v) in enumerate(zip((B, A1, A2), jets)):
        defect = jt.subtract(A, f.jac(v))
        jt.equal(defect, pm.transpose(defect), ('actual compatibility remains symmetric', n))
        for i, value in enumerate(fourier_curl(A)):
            f.equal(value, f.curl(v)[i], ('literal unforced curl identification', n, i))
    I = [[{f.ORIGIN: f.QQ_I.one} if i == j else {} for j in range(3)] for i in range(3)]
    L0 = jt.scale(-1, jt.add(jt.kronecker(pm.transpose(B), I), jt.kronecker(I, pm.transpose(B))))
    L1 = jt.scale(-1, jt.add(jt.kronecker(pm.transpose(B1), I), jt.kronecker(I, pm.transpose(B1))))
    C1 = jt.add(L0, pm.transpose(L0))
    C2 = jt.add(matrix_transport(u, C1, nu), L1, pm.transpose(L1),
                jt.multiply(L0, C1), jt.multiply(C1, pm.transpose(L0)))
    W0 = jt.kronecker(I, I)
    W1, W2 = jt.scale(-1, C1), jt.add(jt.scale(-1, C2), jt.scale(2, jt.multiply(C1, C1)))
    M1 = jt.add(B, pm.transpose(B))
    M2 = jt.add(matrix_transport(u, M1, nu), B1, pm.transpose(B1),
                jt.multiply(B, M1), jt.multiply(M1, pm.transpose(B)))
    H1, H2 = jt.scale(-1, M1), jt.add(jt.scale(-1, M2), jt.scale(2, jt.multiply(M1, M1)))
    A = (B, A1, A2)
    full, symmetric = quadratic_jets(A, (W0, W1, W2)), quadratic_jets(list(map(fourier_sym, A)), (W0, W1, W2))
    omega = [fourier_curl(a) for a in A]
    w0, w1, w2 = omega
    rotational = [jt.metric(w0, I, w0),
                  f.add(f.scale(2, jt.metric(w0, I, w1)), jt.metric(w0, H1, w0)),
                  f.add(f.scale(2, jt.metric(w1, I, w1)), f.scale(2, jt.metric(w0, I, w2)),
                        f.scale(4, jt.metric(w0, H1, w1)), jt.metric(w0, H2, w0))]
    for n in range(3):
        f.equal(full[n], f.add(symmetric[n], f.scale(f.QQ_I(1)/2, rotational[n])),
                ('normalized split along actual full canonical NS jets', n))

    e1, e2, s0, s1 = map(jt.flatten, (E1, E2, source0, source1))
    defect_q2 = f.scale(2, f.dot(e1, e1))
    defect_q3 = f.scale(6, f.add(f.dot(e1, e2), jt.metric(e1, W1, e1)))
    work1 = f.dot(e1, s0)
    work2 = f.add(f.dot(e2, s0), f.scale(2, f.dot(e1, s1)),
                  f.scale(2, jt.metric(e1, W1, s0)))
    cost2 = f.scale(2, f.add(*(f.dot(jt.flatten(pm.matrix_diff(E1, k)),
                                    jt.flatten(pm.matrix_diff(E1, k))) for k in range(3))))
    f.equal(defect_q2, f.scale(2, work1), 'initial pressure/gradient defect source work')
    f.equal(f.add(defect_q3, f.adv(u, defect_q2), f.scale(-nu, f.lap(defect_q2))),
            f.add(f.scale(2, work2), f.scale(-2*nu, cost2)),
            'actual defect production includes pressure, changing metric and complete diffusion')

    def evaluate(field):
        return sum((value*f.II**((k[0]+k[1]) % 4) for k, value in field.items()), f.ZERO)

    direction = (1, -1, 0)
    signed = lambda E: sum((direction[i]*direction[j]*evaluate(E[i][j])
                            for i in range(3) for j in range(3)), f.ZERO)
    require(signed(E1) == f.ZERO and signed(E2) == f.QQ_I(18)/5,
            'positive-viscosity actual defect has a positive second time derivative')
    return {'nu': '1/10', 'point': '(pi/2,pi/2,0)', 'direction': [1, -1, 0],
            'directional_defect_initial': '0', 'directional_defect_first': '0',
            'directional_defect_second': '18/5', 'positive_short_time_term': '(9/5)*t^2+o(t^2)',
            'normalized_split': 'all Fourier outputs through second time order',
            'full_defect_production': 'first nonzero time orders; full source, metric and diffusion',
            'defect_source_work_first_jet_mean': str(pm.mean(work1)),
            'defect_normalized_square_second_jet_mean': str(pm.mean(defect_q2)),
            'defect_normalized_square_third_jet_mean': str(pm.mean(defect_q3)),
            'scope': 'actual unforced PDE and supplied original-packet jets; continuous stochastic/Taylor passage analytic'}


def symbolic_defect():
    x, y, z = s.symbols('x y z', real=True)
    a, b, c, nu = s.symbols('a b c nu', positive=True)
    coordinates = (x, y, z)
    lap = lambda v: sum(s.diff(v, q, 2) for q in coordinates)
    u = s.Matrix([a*s.sin(y), c*s.sin(z), b*s.sin(x)])
    B = u.jacobian(coordinates)
    u1 = nu*u.applyfunc(lap)-B*u
    B1 = u1.jacobian(coordinates)
    p1 = -2*a*b*c*s.cos(x)*s.cos(y)*s.cos(z)
    zero(lap(p1)+2*s.trace(B*B1), 'complete canonical pressure derivative')
    E1 = -B.T*B
    advection = lambda A: A.applyfunc(lambda value: sum(u[j]*s.diff(value, coordinates[j]) for j in range(3)))
    E2 = nu*E1.applyfunc(lap)-advection(E1)-B.T*E1-E1*B+s.hessian(p1, coordinates)-B1.T*B-B.T*B1
    point = {x: s.pi/2, y: s.pi/2, z: 0}
    direction = s.Matrix([1, -1, 0])
    first = (direction.T*E1*direction)[0].subs(point)
    second = s.simplify((direction.T*E2*direction)[0].subs(point))
    zero(first, 'initial nonpositive defect tangent vanishes in the tested direction')
    zero(second-(4*a*b*c-2*nu*(a*a+b*b)), 'pressure feedback reverses the candidate matrix comparison')
    return {'datum': 'u0=(a sin y,c sin z,b sin x)', 'first_directional_derivative': '0',
            'second_directional_derivative': str(second),
            'positive_condition': '2*a*b*c>nu*(a^2+b^2)',
            'refuted_claim': 'A-grad u remains negative semidefinite',
            'surviving_target': 'a signed finite allowance depending on the full original datum and complete histories'}


if __name__ == '__main__':
    print(json.dumps({'finite_same_frame_channels': finite_channels(),
                      'actual_fourier': actual_fourier(), 'symbolic_defect': symbolic_defect()}, indent=2))
