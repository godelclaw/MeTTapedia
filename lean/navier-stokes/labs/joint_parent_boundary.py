#!/usr/bin/env python3
"""Exact joint carrier, pressure and inherited-frame boundary checks.

The actual release limits and successive-stage realization are analytic
in README.md. These checks retain all Fourier outputs; they are not a
time-discretized NS evolution or a Lean certificate.
"""

import json
from fractions import Fraction as Q
from math import factorial

import sympy as sy

import heat_remainder_payment as hp
from reciprocal_pattern_cycles import mode

s, f = hp.s, hp.f
tau, q = sy.symbols('tau q', real=True)
nu = sy.symbols('nu', positive=True)


def zero(expr, label):
    if sy.cancel(sy.expand(expr)) != 0:
        raise AssertionError((label, expr))


def matrix_zero(matrix, label):
    for j, value in enumerate(matrix):
        zero(value, (label, j))


def clean(field):
    return {k: sy.expand(a) for k, a in field.items() if sy.expand(a) != 0}


def product(a, b):
    result = {}
    for k, x in a.items():
        for l, y in b.items():
            result[k+l] = result.get(k+l, 0)+x*y
    return clean(result)


def dtheta(a):
    return clean({k: sy.I*k*x for k, x in a.items()})


def rate(a):
    return sy.diff(a, tau)-nu*q*sy.diff(a, q)


def solve_mode(forcing, k):
    """Zero-initial solution of y'+nu*k^2*y=forcing(tau,exp(-nu*tau))."""
    result = 0
    for (degree, decay), coefficient in sy.Poly(sy.expand(forcing), tau, q).terms():
        difference = k*k-decay
        if difference == 0:
            result += coefficient*q**(k*k)*tau**(degree+1)/(degree+1)
        else:
            primitive = sum((-1)**j*sy.Rational(factorial(degree), factorial(degree-j))
                            *tau**(degree-j)/(nu*difference)**(j+1)
                            for j in range(degree+1))
            result += coefficient*(q**decay*primitive-q**(k*k)*primitive.subs(tau, 0))
    result = sy.expand(result)
    zero(rate(result)+nu*k*k*result-forcing, ('complete coefficient ODE', k))
    zero(result.subs({tau: 0, q: 1}), ('zero initial coefficient', k))
    return result


def solve(forcing):
    return clean({k: solve_mode(a, k) for k, a in forcing.items()})


def carrier_checks(sign):
    # Different heat rates, and a nonzero correlation whose sign can change.
    carriers = [{-1: sy.Rational(1, 2), 1: sy.Rational(1, 2)},
                {-1: sign*sy.Rational(1, 2), 1: sign*sy.Rational(1, 2),
                 -2: sy.I/2, 2: -sy.I/2}]
    H = [{k: a*q**(k*k) for k, a in row.items()} for row in carriers]
    gradients = [dtheta(row) for row in H]
    a = [{k: tau*v for k, v in row.items()} for row in gradients]
    gram, frame = {}, {}
    return_channels = 0
    for i in range(2):
        for j in range(2):
            pair = product(H[i], H[j])
            gram[i, j] = solve_mode(pair.get(0, 0), 0)
            raw_oscillation = solve({k: -v for k, v in pair.items() if k})
            for v in raw_oscillation.values():
                zero(v.subs(q, 0), 'raw oscillatory source decays')
            C = solve({k: 2*tau*v for k, v in product(gradients[i], gradients[j]).items()})
            frame[i, j] = C
            zero(C.get(0, 0).subs(q, 0)-gram[i, j].subs(q, 0)/nu,
                 'joint frame memory equals joint heat Gram divided by viscosity')
            for k, v in C.items():
                if k:
                    zero(v.subs(q, 0), 'nonconstant frame channels decay')
            aa = product(a[i], a[j])
            source = product(dtheta(a[i]), dtheta(a[j]))
            for k in set(C) | set(aa) | set(source):
                covariance = C.get(k, 0)-aa.get(k, 0)
                zero(rate(covariance)+nu*k*k*covariance-2*nu*source.get(k, 0),
                     'complete covariance diffusion source')
            for l in range(2):
                # Each generated mean vertical B(V_i,V_j)_3 acts on EACH carrier.
                forcing = {k: -gram[i, j]*v for k, v in gradients[l].items()}
                returned = solve(forcing)
                for v in returned.values():
                    zero(v.subs(q, 0), 'vertical return eventually decays')
                return_channels += len(returned)
    Gamma = sy.Matrix(2, 2, lambda i, j: sy.simplify(gram[i, j].subs(q, 0)))
    expected = sy.Matrix([[sy.Rational(1, 4), sign*sy.Rational(1, 4)],
                          [sign*sy.Rational(1, 4), sy.Rational(5, 16)]])/nu
    matrix_zero(Gamma-expected, 'complete joint Gram including off-diagonal sign')
    zero(Gamma.det()-1/(64*nu**2), 'strictly positive joint Gram determinant')
    for row in gradients:
        for k, value in row.items():
            zero(solve_mode(value, k)-tau*value, 'incoming vertical background return')
    return {'sign': sign, 'Gamma': str(Gamma), 'vertical_return_coefficients': return_channels}


def incoming_frame_checks():
    v1, v2, w1, w2 = sy.symbols('v1 v2 w1 w2', real=True)
    V = [sy.Matrix([v1, v2, 0]), sy.Matrix([w1, w2, 0])]
    n = sy.Matrix([0, 0, 1])
    m11, m12, m13, m22, m23, m33 = sy.symbols('m11 m12 m13 m22 m23 m33')
    M = sy.Matrix([[m11, m12, m13], [m12, m22, m23], [m13, m23, m33]])
    E = [v*n.T for v in V]
    for i in range(2):
        for j in range(2):
            matrix_zero(E[i]*E[j], 'parallel-normal shears are nilpotent')
            matrix_zero(E[i]*M*E[j].T-m33*V[i]*V[j].T,
                        'incoming second moment weights the joint update')


def tensor(a, b):
    return [[f.mul(x, y) for y in b] for x in a]


def tensor_scale(c, A):
    return [[f.scale(f.QQ_I(c), a) for a in row] for row in A]


def tensor_add(A, B):
    return [[f.add(a, b) for a, b in zip(ar, br)] for ar, br in zip(A, B)]


def tensor_div(A):
    return [f.add(*(f.diff(A[i][j], j) for j in range(3))) for i in range(3)]


def vector_equal(a, b, label):
    for j in range(3):
        f.equal(a[j], b[j], (label, j))


def project(a):
    # green=(-Delta)^(-1) on nonzero modes; constants are retained.
    return s.vector_add(a, f.grad(f.green(f.trace(f.jac(a)))))


def pressure_checks():
    cx, cy, cz = (mode(tuple(int(i == j) for i in range(3)), 1) for j in range(3))
    V1 = [f.mul(cz, cy), {}, {}]
    V2 = [{}, f.scale(-1, f.mul(cz, cx)), {}]
    V = [V1, V2]
    cross = s.nonlinear(s.vector_add(V1, V2))
    s.require(any(cross[2]), 'cross pressure creates vertical velocity')
    for v in V:
        vector_equal(s.nonlinear(v), [{}, {}, {}], 'isolated envelope produces no descendant')
    outputs = []
    for sign in (-1, 1):
        Gamma = [[Q(1, 4), Q(sign, 4)], [Q(sign, 4), Q(5, 16)]]
        S = [[{} for _ in range(3)] for _ in range(3)]
        descendant = [{}, {}, {}]
        for i in range(2):
            for j in range(2):
                S = tensor_add(S, tensor_scale(Gamma[i][j], tensor(V[i], V[j])))
                raw = [f.adv(V[i], row) for row in V[j]]
                descendant = s.vector_add(descendant,
                                         s.vector_scale(-Gamma[i][j], project(raw)))
        vector_equal(descendant, s.vector_scale(Q(sign, 4), cross),
                     'the cross-covariance reverses the released velocity')
        vector_equal(descendant, s.vector_scale(-1, project(tensor_div(S))),
                     'the same covariance tensor determines the full pressure-projected output')
        f.equal(f.trace(f.jac(descendant)), {}, 'released output is incompressible')
        s.require(s.inner(descendant, descendant) > 0, 'the physical output is nonzero')
        # With N>=3 all relevant carrier/envelope aliases are absent.
        for N in (3, 7):
            c1 = mode((0, 0, N), 1)
            c2 = f.add(mode((0, 0, N), sign), mode((0, 0, 2*N), 1, sine=True))
            data = [f.scale(N, f.add(f.mul(c1, V1[j]), f.mul(c2, V2[j]))) for j in range(3)]
            f.equal(f.trace(f.jac(data)), {}, 'joint original datum is exactly solenoidal')
            s.require(s.inner(data, data) == Q(3*N*N, 8),
                      'opposite cross phase retains exact original energy')
        outputs.append({'sign': sign, 'descendant_squared_norm': str(s.inner(descendant, descendant)),
                        'vertical_squared_norm': str(s.inner([{}, {}, descendant[2]],
                                                            [{}, {}, descendant[2]]))})
    A = s.vector_add(V1, V2)
    B = [{}, f.mul(cx, cz), f.scale(-1, f.mul(cx, cy))]
    for N1, N2 in ((7, 3), (3, 7)):
        parent1, parent2 = mode((0, 0, N1), 2*N1), mode((N2, 0, 0), 2*N2)
        data = [f.add(f.mul(parent1, A[j]), f.mul(parent2, B[j])) for j in range(3)]
        f.equal(f.trace(f.jac(data)), {}, 'both ordered packets belong to one unforced datum')
        s.require(s.inner(data, data) == N1*N1+N2*N2,
                  'interchanging the initial frequency hierarchy preserves exact energy')
    return outputs


def ordered_release_checks():
    alpha, beta = sy.symbols('alpha beta', positive=True)
    a, b = sy.Matrix([1, -1, 0]), sy.Matrix([0, 1, -1])
    n1, n2 = sy.Matrix([0, 0, 1]), sy.Matrix([1, 0, 0])
    S1, S2 = alpha*a*a.T, beta*b*b.T
    update = lambda M, n, S: M+(n.T*M*n)[0]*S
    M12 = update(update(sy.eye(3), n1, S1), n2, S2)
    M21 = update(update(sy.eye(3), n2, S2), n1, S1)
    matrix_zero(M12-M21-alpha*beta*(b*b.T-a*a.T),
                'changing release order changes the original frame memory')
    zero(M12.trace()-3-2*alpha-2*beta-2*alpha*beta,
         'both original parents contribute to the second moment')
    zero(M21.trace()-M12.trace(), 'equal traces can conceal different geometry')
    values = [M.subs({alpha: 1, beta: 1}) for M in (M12, M21)]
    # These directions belong to full physical envelopes, not arbitrary matrices.
    x, y, z = sy.symbols('x y z', real=True)
    coords = (x, y, z)
    A = sy.Matrix([sy.cos(z)*sy.cos(y), -sy.cos(z)*sy.cos(x), 0])
    B = sy.Matrix([0, sy.cos(x)*sy.cos(z), -sy.cos(x)*sy.cos(y)])
    matrix_zero(A.subs({x: 0, y: 0, z: 0})-a, 'first envelope at the origin')
    matrix_zero(B.subs({x: 0, y: 0, z: 0})-b, 'second envelope at the origin')
    for v, n in ((A, n1), (B, n2)):
        zero(v.dot(n), 'envelope tangent to its own carrier planes')
        zero(sy.trace(v.jacobian(coords)), 'each oriented envelope is incompressible')
    raw = -A.jacobian(coords)*A-B.jacobian(coords)*B
    # curl commutes with Leray: the pressure gradient drops out exactly.
    omega = sy.Matrix([sy.diff(raw[2], y)-sy.diff(raw[1], z),
                       sy.diff(raw[0], z)-sy.diff(raw[2], x),
                       sy.diff(raw[1], x)-sy.diff(raw[0], y)])
    point = {x: 0, y: sy.pi/4, z: sy.pi/4}
    om = sy.simplify(omega.subs(point))
    matrix_zero(om-sy.Matrix([0, sy.sqrt(2)/2, 0]), 'same released physical vorticity')
    AA, BB = A.subs(point), B.subs(point)
    T1, T2 = AA*AA.T, BB*BB.T
    P12 = update(update(sy.eye(3), n1, T1), n2, T2)
    P21 = update(update(sy.eye(3), n2, T2), n1, T1)
    weighted = [sy.simplify((om.T*M.inv()*om)[0]) for M in (P12, P21)]
    zero(weighted[0]-sy.Rational(65, 232), 'first order has its own weighted vorticity')
    zero(weighted[1]-sy.Rational(33, 124), 'reversed order has different weighted vorticity')
    return {'M12_at_origin': str(values[0]), 'M21_at_origin': str(values[1]),
            'difference': str(sy.expand(M12-M21)), 'equal_trace': str(M12.trace()),
            'same_physical_vorticity_squared': str(om.dot(om)),
            'distinct_weighted_vorticities': [str(v) for v in weighted]}


def main():
    carriers = [carrier_checks(sign) for sign in (-1, 1)]
    incoming_frame_checks()
    result = dict(status='all exact checks passed', carrier_checks=carriers,
                  physical_phase_checks=pressure_checks(), ordered_releases=ordered_release_checks(),
                  scope='exact full layer coefficients and physical boundary algebra; actual release and two-stage limits analytic')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
