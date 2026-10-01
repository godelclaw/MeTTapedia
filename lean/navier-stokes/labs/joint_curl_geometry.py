#!/usr/bin/env python3
"""Physical curl conversion and a finite unforced parent-history class.

Exact finite same-law frames test the joint metric and directional area
cost. Symbolic equations check the actual triangular NS reduction and
the full forward-frame comparison envelopes. Stochastic realization,
parabolic existence and time integration are analytic obligations, not
proved by this checker. The kinematic obstruction is not a finite-energy
NS counterexample or a refutation of a full-datum history allowance.
"""

import json
import sympy as s
from memory_soft_excess import check_unforced_reduction
import pressure_history_source as fourier
from signed_viscous_pressure import interacting_datum


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def zero(expression, label):
    require(s.simplify(expression) == 0, label)


def equal(a, b, label):
    require(a.shape == b.shape, (label, 'matrix dimensions'))
    for i in range(a.rows):
        for j in range(a.cols):
            zero(a[i, j]-b[i, j], (label, i, j))


def flat(matrix):
    require(matrix.shape == (3, 3), 'retain all nine original tensor entries')
    return s.Matrix([matrix[i, j] for i in range(3) for j in range(3)])


def skew(z):
    require(z.shape == (3, 1), 'curl test direction has three entries')
    return s.Matrix([[0, -z[2], z[1]], [z[2], 0, -z[0]], [-z[1], z[0], 0]])


def curl(matrix):
    require(matrix.shape == (3, 3), 'physical tensor curl uses a complete matrix')
    return s.Matrix([matrix[2, 1]-matrix[1, 2], matrix[0, 2]-matrix[2, 0],
                     matrix[1, 0]-matrix[0, 1]])


def quadratic(v, matrix):
    require(matrix.shape == (v.rows, v.rows) and v.cols == 1,
            'metric dimensions agree with every retained coordinate')
    return s.factor((v.T*matrix*v)[0])


def triangular(b, c, d):
    return s.Matrix([[1, b, 0], [0, 1, 0], [c, d, 1]])


def joint_data(Js, weights):
    require(len(Js) == len(weights) and sum(weights) == 1,
            'one normalized law for both frame copies')
    require(all(w >= 0 for w in weights), 'nonnegative sample weights')
    Fs, C, M = [], s.zeros(9), s.zeros(3)
    for J, w in zip(Js, weights):
        require(J.det() == 1, 'volume-preserving original frame')
        F = J.inv()
        Fs.append(F)
        G = F.T*F
        C += w*s.kronecker_product(G, G)
        M += w*J*J.T
    equal(C, C.T, 'symmetric retained joint metric')
    require(C.det() > 0, 'invertible retained joint metric')
    return Fs, C, M


def finite_direction_tests():
    Q = s.Rational
    entries = ((Q(1, 2), Q(-3, 4), Q(2, 3)),
               (Q(-1, 4), Q(5, 6), Q(-1, 3)),
               (Q(3, 5), Q(1, 3), Q(-7, 6)))
    Js = [triangular(*entry) for entry in entries]
    weights = [Q(1, 5), Q(1, 3), Q(7, 15)]
    Fs, C, M = joint_data(Js, weights)
    Vs = [s.Matrix([[1, 2, -1], [0, -1, 3], [2, 1, 0]]),
          s.Matrix([[0, -1, 2], [3, 1, 0], [-2, 4, -1]]),
          s.Matrix([[2, 0, 3], [-1, 0, 1], [4, -2, -2]])]
    require(all(s.trace(V) == 0 for V in Vs), 'original labels are trace free')
    A = sum((w*F.T*V*F for w, F, V in zip(weights, Fs, Vs)), s.zeros(3))
    a, W, omega = flat(A), C.inv(), curl(A)
    paid = quadratic(a, W)
    require(paid > 0 and omega.dot(omega) > 0, 'nontrivial original packet and curl')
    tests = [s.eye(3)[:, i] for i in range(3)]+[omega, s.Matrix([1, -2, 3])]
    deficits = []
    for z in tests:
        r = flat(skew(z))
        zero(z.dot(omega)-r.dot(a), 'curl is the skew tensor observation')
        zero(quadratic(r, C)-2*quadratic(z, M), 'same-law area channel')
        deficit = s.factor(2*paid*quadratic(z, M)-z.dot(omega)**2)
        require(deficit >= 0, 'directional curl Cauchy bound')
        deficits.append(str(deficit))

    coefficients = W*a
    variance, original = s.S.Zero, s.S.Zero
    for w, F, V in zip(weights, Fs, Vs):
        Phi = s.kronecker_product(F, F)
        residual = flat(V)-Phi*coefficients
        require(residual.rows == 9, 'variance retains every original tensor entry')
        variance += w*residual.dot(residual)
        original += w*flat(V).dot(flat(V))
    zero(variance-original+paid, 'one original-label payment, with no seam reset')
    require(variance >= 0, 'nonnegative original tensor variance')

    r, t = s.Integer(1), s.Integer(2)
    budget = 3+r*r+t*t+(r*t)**2
    for entry, J in zip(entries, Js):
        b, c, d = entry
        require(abs(b) <= r and abs(c) <= t and abs(d) <= r*t,
                'all triangular entries obey their retained history budget')
        require(s.trace(J*J.T) <= budget, 'complete forward-frame square is paid')
    for z in tests:
        require(quadratic(z, M) <= budget*z.dot(z), 'uniform finite frame cost')
    require(omega.dot(omega) <= 2*budget*paid, 'finite paid physical curl')
    return {'samples': len(Js), 'tensor_entries': 9, 'paid_norm': str(paid),
            'original_gradient_square': str(original), 'variance': str(variance),
            'directional_deficits': deficits, 'triangular_budget': str(budget),
            'scope': 'exact finite same-law fixture; no physical solution assigned to these samples'}


def planar_direction_test():
    Js = [s.Matrix([[1, 2, 0], [0, 1, 0], [0, 0, 1]]),
          s.diag(3, s.Rational(1, 3), 1)]
    Fs, C, M = joint_data(Js, [s.Rational(1, 2)]*2)
    n = s.Matrix([0, 0, 1])
    V = skew(n)
    for F, J in zip(Fs, Js):
        equal(J.T*n, n, 'common invariant planar normal')
        equal(F.T*V*F, V, 'area-preserving planar transport of original curl')
    paid, omega = quadratic(flat(V), C.inv()), curl(V)
    zero(quadratic(n, M)-1, 'normal area cost is one despite planar deformation')
    zero(omega.dot(omega)-2*paid, 'planar curl conversion is sharp')
    return {'paid_norm': str(paid), 'curl_square': str(omega.dot(omega)),
            'normal_area_cost': str(quadratic(n, M)),
            'scope': 'finite planar frames; nonzero z-independent fields are not finite-energy on R3'}


def mixing_history_test():
    reduction = check_unforced_reduction()
    A, B, nu = s.symbols('A B nu', positive=True)
    t = s.symbols('t', nonnegative=True)
    q = s.exp(-nu*t)
    b, c, d = s.symbols('b c d', real=True)
    a, vx, vy = s.symbols('a vx vy', real=True)
    J = triangular(b, c, d)
    velocity_gradient = s.Matrix([[0, a, 0], [0, 0, 0], [vx, vy, 0]])
    rates = s.Matrix([[0, a, 0], [0, 0, 0], [vx, vx*b+vy, 0]])
    equal(velocity_gradient*J, rates, 'complete original forward-frame ODE')
    zero(J.det()-1, 'original triangular frame retains incompressibility')
    zero(s.trace(J*J.T)-(3+b*b+c*c+d*d), 'all frame entries are counted')

    parent = A*(1-q)/nu
    vertical = B*(1-q)/nu
    cross = A*B*(1-q)**2/nu**2
    zero(parent.diff(t)-A*q, 'horizontal frame envelope')
    zero(vertical.diff(t)-B*q, 'vertical derivative frame envelope')
    zero(cross.diff(t)-(B*q*parent+A*B*q*(1-q)/nu),
         'coupled frame entry includes both parent paths')
    for envelope in (parent, vertical, cross):
        zero(envelope.subs(t, 0), 'no original frame allowance spent at time zero')
    r, tau = A/nu, B/nu
    budget = 3+r*r+tau*tau+(r*tau)**2
    original_gradient_mean = (A*A+B*B)/2
    enstrophy_allowance = 2*budget*original_gradient_mean
    zero(velocity_gradient.trace(), 'full mixing velocity is incompressible')
    omega = curl(velocity_gradient)
    strain = (velocity_gradient+velocity_gradient.T)/2
    zero(omega.dot(strain*omega)+a*vx*vy,
         'unforced mixing retains genuinely nonzero stretching')
    return {'actual_NS_reduction': reduction,
            'frame_equations': "b'=a; c'=v_x; d'=v_x*b+v_y",
            'comparison_envelopes': [str(v) for v in (parent, vertical, cross)],
            'all_time_frame_budget': str(budget),
            'initial_gradient_square_mean': str(original_gradient_mean),
            'enstrophy_allowance': str(enstrophy_allowance),
            'scope': 'exact reduction/envelope derivatives; stochastic comparisons and integrated payment are analytic',
            'open_extension': 'parents with reciprocal amplification'}


def geometry_free_obstruction():
    lam = s.symbols('lambda', positive=True)
    F, J = s.diag(1/lam, lam, 1), s.diag(lam, 1/lam, 1)
    equal(J*F, s.eye(3), 'coherent inverse frame')
    zero(F.det()-1, 'coherent frame preserves volume')
    G = F.T*F
    C, M = s.kronecker_product(G, G), J*J.T
    V = skew(s.Matrix([1, 0, 0]))
    A = F.T*V*F
    paid, omega = quadratic(flat(A), C.inv()), curl(A)
    zero(paid-2, 'original gradient payment is constant')
    zero(omega.dot(omega)-4*lam**2, 'coherent volume preservation allows amplification')
    zero(2*paid*quadratic(omega, M)-omega.dot(omega)**2,
         'directional estimate keeps the exact growing geometric cost')
    ratio = s.factor(omega.dot(omega)/paid)
    require(s.limit(ratio, lam, s.oo) == s.oo,
            'no geometry-free uniform kinematic curl conversion')
    return {'paid_norm': str(paid), 'curl_square': str(omega.dot(omega)),
            'conversion_ratio': str(ratio), 'law': 'one coherent determinant-one frame',
            'refutes': 'a universal curl conversion from volume preservation and coherence alone',
            'does_not_refute': 'a datum-fixed directional geometry bound along finite-energy unforced NS',
            'scope': 'kinematic family, not an actual periodic or finite-energy R3 NS trajectory'}


def directional_history_rate():
    # The complete parabolic product rule is checked with a generic
    # nonzero derivative of both the curl and its retained area moment.
    # This single generic derivative term applies to each spatial axis.
    B = s.Matrix(3, 3, s.symbols('b0:9'))
    m = s.symbols('m0:6')
    M = s.Matrix([[m[0], m[1], m[2]], [m[1], m[3], m[4]], [m[2], m[4], m[5]]])
    dm = s.symbols('dm0:6')
    Mk = s.Matrix([[dm[0], dm[1], dm[2]], [dm[1], dm[3], dm[4]],
                   [dm[2], dm[4], dm[5]]])
    w, dw = s.Matrix(s.symbols('w0:3')), s.Matrix(s.symbols('dw0:3'))
    nu = s.symbols('nu', positive=True)
    strain, W = (B+B.T)/2, w.dot(w)
    Omega, V = quadratic(w, M), w.dot(strain*w)
    rho = Omega/W  # Only used on the explicitly stated nonzero-curl set.
    rate = 2*w.dot(M*B*w)+w.dot((B*M+M*B.T)*w) \
        -2*nu*(quadratic(dw, M)+2*dw.dot(Mk*w))
    expected = 4*w.dot(M*strain*w)-2*nu*(quadratic(dw, M)+2*dw.dot(Mk*w))
    zero(rate-expected, 'full forward-area/curl rate retains mixed spatial derivatives')
    Wrate = 2*V-2*nu*dw.dot(dw)
    Wk = 2*w.dot(dw)
    rhok = (2*dw.dot(M*w)+quadratic(w, Mk)-rho*Wk)/W
    rhorate = (rate-rho*Wrate+2*nu*rhok*Wk)/W
    normalized = (4*w.dot(M*strain*w)-2*rho*V)/W \
        -2*nu*(quadratic(dw, M-rho*s.eye(3))+2*dw.dot(Mk*w))/W
    zero((rhorate-2*nu*rhok*Wk/W)-normalized,
         'normalized directional history retains every diffusion and drift term')

    # An actual finite periodic datum and its full canonical unforced
    # tangent reject a monotone-decrease shortcut even at positive nu.
    f = fourier
    u = [f.scale(-1, v) for v in interacting_datum()]
    B0, omega = f.jac(u), f.curl(u)
    nu0 = f.QQ_I(1)/10
    p = f.tensor_pressure(f.tensor(u, u))
    u1 = [f.add(f.scale(nu0, f.lap(u[i])), f.scale(-1, f.adv(u, u[i])),
                f.scale(-1, f.diff(p, i))) for i in range(3)]
    f.equal(f.trace(B0), {}, 'genuine three-dimensional periodic solenoidal datum')
    f.equal(f.trace(f.jac(u1)), {}, 'complete canonical unforced NS tangent')
    Domega = [f.add(f.curl(u1)[i], f.adv(u, omega[i]),
                   f.scale(-nu0, f.lap(omega[i]))) for i in range(3)]
    for i in range(3):
        f.equal(Domega[i], f.matvec(B0, omega)[i], 'actual viscous vorticity equation')
    materialB = [[f.add(f.diff(u1[i], j), f.adv(u, B0[i][j]),
                       f.scale(-nu0, f.lap(B0[i][j]))) for j in range(3)] for i in range(3)]
    squareB, Hess = f.matmul(B0, B0), f.hess(p)
    for i in range(3):
        for j in range(3):
            f.equal(materialB[i][j], f.scale(-1, f.add(squareB[i][j], Hess[i][j])),
                    'parents retain the canonical pressure Hessian')
    w0 = [f.evaluate(v) for v in omega]
    Bvalue = [[f.evaluate(v) for v in row] for row in B0]
    W0 = f.value_dot(w0, w0)
    V0 = f.value_dot(w0, f.value_matvec(Bvalue, w0))
    require(W0 > 0 and V0 > 0, 'actual initial directional geometry grows')
    return {'full_cost_rate': 'D Omega=4 omega^T M S omega-2nu sum_k '
                              '[(partial_k omega)^T M(partial_k omega)'
                              '+2(partial_k omega)^T(partial_k M)omega]',
            'normalized_domain': 'W=|omega|^2>0; rho=Omega/W',
            'initial_rho': '1', 'positive_initial_material_rate': str(2*V0/W0),
            'viscosity': str(nu0),
            'refutes': 'universal nonincrease of the actual directional geometry from its initial value',
            'does_not_refute': 'a finite full-datum allowance for directional growth over a prescribed horizon',
            'scope': 'exact generic rate algebra and full periodic NS initial tangent; stochastic time passage is analytic'}


def first_reciprocal_parent_test():
    # Add a transverse parent to the actual triangular initial datum.
    # This creates a three-way feedback loop, not an assigned force.
    x, y, z = s.symbols('x y z', real=True)
    a, b, nu = s.symbols('a b nu', positive=True)
    eps = s.symbols('epsilon', nonnegative=True)
    coords = (x, y, z)
    u = s.Matrix([a*s.sin(y), eps*s.sin(z), b*s.sin(x)])
    B = u.jacobian(coords)
    lap = lambda f: sum(s.diff(f, c, 2) for c in coords)
    zero(B.trace(), 'reciprocal periodic parents are incompressible')
    zero(s.trace(B*B), 'initial canonical pressure is zero')
    u1 = nu*u.applyfunc(lap)-B*u
    B1 = u1.jacobian(coords)
    zero(B1.trace(), 'all three actual unforced tangent components are retained')
    pressure1 = -2*a*b*eps*s.cos(x)*s.cos(y)*s.cos(z)
    zero(lap(pressure1)+2*s.trace(B*B1),
         'generated canonical pressure retains the full reciprocal loop')
    omega = curl(B)
    stretching = s.factor(omega.dot(B*omega))
    zero(stretching-3*a*b*eps*s.cos(x)*s.cos(y)*s.cos(z),
         'reciprocal parents produce actual three-dimensional stretching')
    origin = {x: 0, y: 0, z: 0}
    initial_rate = s.factor(2*stretching.subs(origin)/omega.dot(omega).subs(origin))
    zero(initial_rate-6*a*b*eps/(a*a+b*b+eps*eps),
         'reciprocal directional growth has its full datum dependence')
    require(initial_rate.subs({a: 2, b: 3, eps: s.Rational(1, 4)}) == s.Rational(144, 209),
            'small feedback fixture has a strict positive directional rate')
    return {'datum': '(a sin y, epsilon sin z, b sin x)',
            'epsilon_zero': 'the established triangular mixing datum',
            'initial_pressure': '0', 'first_pressure_derivative': str(pressure1),
            'initial_origin_directional_rate': str(initial_rate),
            'small_feedback_example_rate': '144/209 for a=2,b=3,epsilon=1/4',
            'scope': 'exact periodic initial NS/pressure jets; no continued-flow allowance or singularity claimed',
            'next_obligation': 'pay the evolving reciprocal parents and their generated pressure on actual prefixes'}


if __name__ == '__main__':
    print(json.dumps({'finite_joint_curl': finite_direction_tests(),
                      'planar_normal': planar_direction_test(),
                      'actual_mixing_history': mixing_history_test(),
                      'geometry_free_obstruction': geometry_free_obstruction(),
                      'directional_history_rate': directional_history_rate(),
                      'first_reciprocal_parents': first_reciprocal_parent_test()}, indent=2))
