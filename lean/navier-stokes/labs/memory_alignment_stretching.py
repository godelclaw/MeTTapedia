#!/usr/bin/env python3
"""Exact checks for the stress-memory deficit and actual NS stretching.

Universal inequalities and the continuum continuation implication are
proved analytically in README.md. These checks are not Lean PDE proofs.
The periodic fixture uses the complete projected NS tangent, not a
closed Fourier truncation or a prescribed memory history.
"""

import hashlib
import json
from pathlib import Path

import sympy as s

import optimal_cubic_gauge as og
import helical_parent_response as hr

f, wh, am, Q = og.f, og.wh, og.am, og.Q
require, zero = og.require, og.zero
R = s.Rational


def inner(a, b):
    return s.trace(a.T*b)


def curl_matrix(b):
    return s.Matrix([b[2, 1]-b[1, 2], b[0, 2]-b[2, 0], b[1, 0]-b[0, 1]])


def shear_split():
    a, b, c, d, e, f0, g, h = s.symbols('a b c d e f g h', real=True)
    B = s.Matrix([[a, b, c], [d, e, f0], [g, h, -a-e]])
    N = s.Matrix([[0, b, c], [0, 0, 0], [0, 0, 0]])
    Q0 = B-N
    transverse = B.copy()
    transverse[0, :] = s.zeros(1, 3)
    omega, wN, rho = map(curl_matrix, (B, N, Q0))
    require(N*wN == s.zeros(3, 1) and wN.T*N == s.zeros(1, 3),
            'rank-one trace-free shear has both required curl cancellations')
    zero(inner(N, Q0), 'orthogonal shear and remainder')
    zero(inner(Q0, Q0)-inner(transverse, transverse)-a*a,
         'trace correction in the full remainder')
    zero(2*(e*e+(a+e)**2)-a*a-(a+2*e)**2,
         'trace-free constraint pays the normal component')
    zero((omega.T*B*omega)[0]-(omega.T*Q0*omega)[0]-(rho.T*N*rho)[0],
         'complete cubic stretching split')
    for M in (B, Q0):
        zero(2*inner(M, M)-curl_matrix(M).dot(curl_matrix(M))
             -inner(M+M.T, M+M.T)/2, 'curl norm bound as a square identity')
    x, y, z = s.symbols('x y z', real=True)
    zero((b*b+c*c)*(y*y+z*z)-(b*y+c*z)**2-(b*z-c*y)**2,
         'rank-one symmetric contraction bound')
    zero((x*x+y*y+z*z)**2-4*x*x*(y*y+z*z)
         -(x*x-y*y-z*z)**2, 'factor one half in shear quadratic form')
    zero(R(25, 4)*12-75, 'pointwise stretching constant')
    require(R(3, 4)**2 > R(1, 2), 'second eigenvalue is below three quarters')
    rotation = s.Matrix([[-R(1, 2), -s.sqrt(3)/2, 0],
                         [s.sqrt(3)/2, -R(1, 2), 0], [0, 0, 1]])
    require(rotation.trace() == 0 and rotation*rotation.T == s.eye(3),
            'three-dimensional isotropic-source calibration')
    w = curl_matrix(rotation)
    zero((w.T*rotation*w)[0]-3, 'isotropic source can stretch positively')
    return {'universal_bound': '|omega^T B omega|^2 <= 75*|B|^4*h',
            'hypotheses': 'trace B=0; A positive semidefinite; Frobenius norm A<=1; h=(I-A):BB^T',
            'orthogonal_remainder_bound': '|Q|^2<=12*h',
            'isotropic_source_stretching': '3'}


def smooth_norm():
    x = s.Matrix(s.symbols('x0:3', real=True))
    v = s.Matrix(s.symbols('v0:3', real=True))
    k, t, r = s.symbols('k t r', positive=True)
    C = x+t*v
    radius = s.sqrt(k*k+C.dot(C))
    a = C/radius
    s0 = radius.subs(t, 0)
    first = v/s0-x*x.dot(v)/s0**3
    second = -2*v*x.dot(v)/s0**3-x*v.dot(v)/s0**3+3*x*x.dot(v)**2/s0**5
    for i in range(3):
        zero(s.diff(a[i], t).subs(t, 0)-first[i], 'full first derivative of normalized memory')
        zero(s.diff(a[i], t, 2).subs(t, 0)-second[i], 'full second derivative of normalized memory')
    hessian = (x/s0).jacobian(x).subs({x[0]: r, x[1]: 0, x[2]: 0})
    require(s.simplify(hessian) == s.diag(k*k/(k*k+r*r)**R(3, 2),
                                          1/s.sqrt(k*k+r*r), 1/s.sqrt(k*k+r*r)),
            'positive radial and transverse diffusion costs')
    # This is a local convexity calibration, not a reachable fluid-history claim.
    c, b = s.symbols('c b', real=True)
    h = (1-c/s.sqrt(1+c*c))*b*b
    joint = s.hessian(h, (c, b)).subs({c: R(3, 4), b: 1})
    direction = s.Matrix([1, R(32, 25)])
    curvature = (direction.T*joint*direction)[0]
    zero(curvature+R(1792, 3125), 'joint memory/gradient deficit is not convex')
    return {'Phi': 'sqrt(k^2+|C|^2)-k', 'A': 'C/sqrt(k^2+|C|^2)',
            'reserve': 'E+integral Phi', 'initial_reserve': 'E0',
            'paid': '2*nu*integral H + nu*integral HessPhi[grad C,grad C] <= E0',
            'local_joint_curvature': str(curvature)}


def chain_rule():
    t = s.symbols('t', real=True)
    nu, k = R(2, 7), s.Integer(12)
    O = s.Matrix([[R(3, 5), -R(4, 5), 0], [R(4, 5), R(3, 5), 0], [0, 0, 1]])
    C = O*s.diag(3, 4, 0)*O.T
    V = s.Matrix([[2, 1, 0], [1, -1, 2], [0, 2, 3]])
    Cxx = s.Matrix([[1, 2, 3], [2, 4, 0], [3, 0, 1]])
    B = s.Matrix([[1, 2, -1], [3, -2, 1], [2, 1, 1]])
    J = s.Matrix([[2, 1, 3], [-1, 1, 2], [0, 3, -3]])
    Bxx = s.Matrix([[0, 1, -1], [2, 1, 0], [3, 2, -1]])
    P = s.Matrix([[1, 2, 0], [2, -3, 1], [0, 1, 2]])
    G = B*B.T
    require(C*G != G*C, 'chain rule retains noncommuting source and memory')
    radius = s.sqrt(k*k+inner(C, C))
    A = C/radius
    def dA(W):
        return W/radius-C*inner(C, W)/radius**3
    def ddA(W):
        return -2*W*inner(C, W)/radius**3-C*inner(W, W)/radius**3+3*C*inner(C, W)**2/radius**5
    def deficit(c, b):
        return inner(s.eye(3)-c/s.sqrt(k*k+inner(c, c)), b*b.T)
    spatial = deficit(C+t*V+t*t*Cxx/2, B+t*J+t*t*Bxx/2)
    material = deficit(C+t*(2*nu*G+nu*Cxx), B+t*(-B*B-P+nu*Bxx))
    actual = s.diff(material, t).subs(t, 0)-nu*s.diff(spatial, t, 2).subs(t, 0)
    DG = -B*G-G*B.T-P*B.T-B*P-2*nu*J*J.T
    predicted = (inner(s.eye(3)-A, DG)-2*nu*inner(dA(G), G)
                 +nu*inner(ddA(V), G)+2*nu*inner(dA(V), J*B.T+B*J.T))
    zero(actual-predicted, 'full parabolic deficit chain rule with every spatial derivative')
    return {'noncommuting_chain_value': str(predicted),
            'retained': ['strain', 'pressure Hessian', 'weighted gradient diffusion',
                         'source-square Hessian', 'memory Hessian gradient term', 'mixed source gradient']}


def periodic_datum():
    waves = [(1, 1, 0), (1, -1, 1), (2, 0, 1)]
    u = wh.addv(*(wh.project([og.cosine(k) if j < 2 else og.vd.sine(k), {}, {}])
                  for j, k in enumerate(waves)))
    B, omega = f.jac(u), f.curl(u)
    f.equal(f.trace(B), {}, 'actual datum is divergence-free')
    G = [[f.add(*(f.mul(B[i][l], B[j][l]) for l in range(3)))
          for j in range(3)] for i in range(3)]
    pair = lambda a, b: am.pairing([a], [b])
    enstrophy = am.pairing(omega, omega)
    lap = [f.lap(a) for a in u]
    dissipation = am.pairing(lap, lap)
    stretching = sum((pair(f.mul(omega[i], omega[j]), B[i][j])
                      for i in range(3) for j in range(3)), f.ZERO)
    quartic = sum((pair(a, a) for row in G for a in row), f.ZERO)
    require((enstrophy, dissipation, stretching, quartic)
            == (Q(2), Q(13)/2, Q(13)/60, Q(1217)/300), 'exact physical coefficients')
    P = f.hess(f.tensor_pressure(f.tensor(u, u)))
    nonlinear = hr.nonlinear(u)
    for viscosity in (Q(1), Q(2)/7):
        tangent = wh.addv(nonlinear, wh.scalev(viscosity, lap))
        Bt = f.jac(tangent)
        for i in range(3):
            for j in range(3):
                actual = f.add(*(f.add(f.mul(Bt[i][l], B[j][l]), f.mul(B[i][l], Bt[j][l]))
                                 for l in range(3)))
                reaction = f.add(*(f.add(f.mul(B[i][l], G[l][j]), f.mul(G[i][l], B[j][l]),
                                         f.mul(P[i][l], B[j][l]), f.mul(B[i][l], P[l][j]))
                                  for l in range(3)))
                loss = f.add(*(f.mul(f.diff(B[i][l], d), f.diff(B[j][l], d))
                               for d in range(3) for l in range(3)))
                expected = f.add(f.scale(-1, f.adv(u, G[i][j])), f.scale(viscosity, f.lap(G[i][j])),
                                 f.scale(-1, reaction), f.scale(-2*viscosity, loss))
                f.equal(actual, expected, 'complete physical source evolution')
        zprime = 2*sum((pair(B[i][j], Bt[i][j]) for i in range(3) for j in range(3)), f.ZERO)
        require(zprime == 2*stretching-2*viscosity*dissipation, 'full NS enstrophy tangent')
        hp = zprime-2*viscosity*quartic  # k=1 at unit amplitude, C(0)=0.
        require(hp == Q(13)/30-Q(3167)*viscosity/150, 'actual deficit derivative')
    amp, nu = s.symbols('amp nu', positive=True)
    hp = R(13, 30)*amp**3-R(3167, 150)*nu*amp**2
    zero(hp.subs(amp, 50*nu)-R(4150, 3)*nu**3, 'positive-viscosity increasing deficit')
    zero(hp.subs(amp, R(3167, 65)*nu), 'exact amplitude threshold for k=amp^2')
    return {'energy': str(am.pairing(u, u)), 'Z0': str(enstrophy), 'D0': str(dissipation),
            'g0': str(stretching), 'integral_G_squared': str(quartic),
            'prescribed_original_k': 'amp^2', 'H_prime_zero': str(hp),
            'at_amp_50nu': '4150*nu^3/3 > 0',
            'scope': 'actual smooth periodic NS initially increases H; no failure of a full-datum integrated allowance'}


def continuation():
    zero(R(1, 4)-R(1, 4)/2-R(3, 4)/6, 'spatial interpolation for gradient L4')
    S, nu, H, Z, x = s.symbols('S nu H Z x', positive=True)
    coefficient = s.sqrt(75)*S**R(3, 4)
    a = 2*coefficient*Z**R(1, 4)*s.sqrt(H)
    optimum = 3*a/(4*nu)  # x is D^(1/4).
    optimum_value = (a*x**3-nu*x**4).subs(x, optimum)
    target = R(151875, 16)*S**3*H**2*Z/nu**3
    zero(optimum_value-target, 'exact Young continuation coefficient')
    y = s.symbols('y', nonnegative=True)
    zero(3*y**4-4*y**3+1-(y-1)**2*(3*y**2+2*y+1),
         'universal Young nonnegative gap')
    return {'paid_time_cost': 'integral H <= E0/(2*nu)',
            'OPEN_time_cost': 'integral H^2 <= K(u0,nu,horizon,k) on every same-datum prefix',
            'conditional_gradient_bound': 'Z(t)<=Z0*exp(151875*S^3*K/(16*nu^3))',
            'domains': 'R3 and T3; periodic gradients have zero spatial mean'}


if __name__ == '__main__':
    result = {'shear_split': shear_split(), 'smooth_norm': smooth_norm(),
              'chain_rule': chain_rule(), 'actual_periodic_datum': periodic_datum(),
              'continuation': continuation(),
              'certification': 'exact algebra; continuum claims analytic, not Lean-certified',
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    print(json.dumps(result, indent=2, sort_keys=True))
