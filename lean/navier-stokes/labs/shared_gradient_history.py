#!/usr/bin/env python3
"""Exact checks for gradient creation in a shared viscous history.

The matrix Jensen argument, continuum history bound and local-time
consequences are analytic in README.md. Complete Fourier tangents are
used, not a closed Galerkin evolution or independently prescribed memory.
"""

import hashlib
import itertools
import json
from pathlib import Path

import sympy as s
import optimal_cubic_gauge as og
import helical_parent_response as hr

f, wh, am, Q = og.f, og.wh, og.am, og.Q
require, zero = og.require, og.zero
R = s.Rational


def transpose(M):
    return [list(row) for row in zip(*M)]


def matadd(*matrices):
    return [[f.add(*(M[i][j] for M in matrices)) for j in range(3)] for i in range(3)]


def matscale(a, M):
    return [[f.scale(a, v) for v in row] for row in M]


def matrix_at_origin(M):
    return s.Matrix([[f.evaluate(a) for a in row] for row in M])


def actual_cyclic_history():
    u = [og.vd.sine(k) for k in ((0, 1, 0), (0, 0, 1), (1, 0, 0))]
    B = f.jac(u)
    G = f.matmul(B, transpose(B))
    pressure = f.tensor_pressure(f.tensor(u, u))
    f.equal(pressure, {}, 'canonical initial pressure is identically zero')
    f.equal(f.trace(B), {}, 'actual cyclic datum is incompressible')
    F = matscale(-1, matadd(f.matmul(B, B), f.hess(pressure)))
    f.equal(f.trace(F), {}, 'full gradient-creation source is trace-free')
    B0, F0 = matrix_at_origin(B), matrix_at_origin(F)
    require(B0 == s.Matrix([[0, 1, 0], [0, 0, 1], [1, 0, 0]]), 'cyclic gradient')
    require(matrix_at_origin(G) == s.eye(3), 'isotropic initial gradient stress')
    require(F0 == -B0*B0, 'actual initial deformation source')
    for d in range(3):
        require(matrix_at_origin([[f.diff(v, d) for v in row] for row in B]) == s.zeros(3),
                'all first spatial derivatives of B vanish at the observation point')
    n = s.Matrix([1, -1, 0])
    reports = []
    nonlinear = hr.nonlinear(u)
    for nu in (Q(1), Q(2)/7):
        ut = wh.addv(nonlinear, [f.scale(nu, f.lap(v)) for v in u])
        Bt = f.jac(ut)
        LG = [[f.add(f.scale(nu, f.lap(v)), f.scale(-1, f.adv(u, v)))
               for v in row] for row in G]
        LB = [[f.add(f.scale(nu, f.lap(v)), f.scale(-1, f.adv(u, v)))
               for v in row] for row in B]
        f.same_matrices(Bt, matadd(LB, F), 'complete differentiated NS equation')
        Gt = matadd(f.matmul(Bt, transpose(B)), f.matmul(B, transpose(Bt)))
        # C''(0)=2nu*(G_t(0)+L G(0)); no term acts on C(0)=0.
        Ctt = matscale(2*nu, matadd(Gt, LG))
        second_coefficient = matrix_at_origin(matadd(matscale(Q(1)/2, Ctt), matscale(-2*nu, Gt)))
        require(second_coefficient == nu.x*(B0+B0.T), 'full memory-minus-current-stress second jet')
        zero((n.T*second_coefficient*n)[0]+2*nu.x, 'strict failure of heat-style matrix dominance')
        corrected = second_coefficient+nu.x*(F0*B0.T+B0*F0.T)
        require(corrected == s.zeros(3), 'retaining the half-age source cancels the failed second jet')
        reports.append({'nu': str(nu), 'unrepaired_directional_t2': str(-2*nu.x),
                        'source_corrected_t2': 'zero matrix'})
    return {'datum': '(sin y,sin z,sin x)', 'initial_energy': str(am.pairing(u, u)),
            'B_at_origin': str(B0), 'F_at_origin': str(F0),
            'all_nu_positive_failure': 'n^T[C(t)-2*nu*t*B(t)B(t)^T]n=-2*nu*t^2+o(t^2)',
            'direction': '(1,-1,0)', 'positive_viscosity_checks': reports,
            'scope': 'actual smooth periodic NS on a short interval; not a singularity construction'}


def joint_variance_and_source_clock():
    lam = s.symbols('lam', real=True)
    X = s.Matrix(2, 3, s.symbols('x0:6', real=True))
    Y = s.Matrix(2, 3, s.symbols('y0:6', real=True))
    mean = lam*X+(1-lam)*Y
    covariance = lam*X*X.T+(1-lam)*Y*Y.T-mean*mean.T
    require((covariance-lam*(1-lam)*(X-Y)*(X-Y).T).applyfunc(s.expand) == s.zeros(2),
            'joint matrix covariance, including off-diagonal terms')
    age, r, q = s.symbols('age r q', positive=True)
    c0, c1, c2 = s.symbols('c0 c1 c2', real=True)
    source = c0+c1*q+c2*q*q
    double = s.integrate(s.integrate(source, (q, r, age)), (r, 0, age))/age
    single = s.integrate((q/age)*source, (q, 0, age))
    zero(double-single, 'Duhamel average retains the increasing source-age weight')
    zero(single-(age*c0/2+age**2*c1/3+age**3*c2/4), 'source-age moments')
    a, b = s.symbols('a b', real=True)
    shear = s.Matrix([[0, a, 0], [0, 0, 0], [0, b, 0]])
    require(shear*shear == s.zeros(3), 'source-free exact unforced shear calibration')
    return {'joint_constraint': 'C_recent >= 2*nu*age*(B-J)(B-J)^T',
            'source': 'F=-B^2-Hess p',
            'J': 'integral_start^end [(r-start)/age]*P_(r,end) F(r) dr',
            'source_moments': str(single),
            'source_free_case': 'J=0 for actual decaying shears'}


def compact_localization():
    # A bounded periodic potential gives genuinely compact solenoidal data.
    potential = [f.scale(-1, og.cosine(k)) for k in ((0, 0, 1), (1, 0, 0), (0, 1, 0))]
    cyclic = [og.vd.sine(k) for k in ((0, 1, 0), (0, 0, 1), (1, 0, 0))]
    wh.same_vectors(f.curl(potential), cyclic, 'explicit periodic vector potential')
    x = s.symbols('x0:3', real=True)
    radius = s.sqrt(sum(v*v for v in x))
    delta = lambda i, j: int(i == j)
    for i, j, k, l in itertools.combinations_with_replacement(range(3), 4):
        derivative = s.diff(1/radius, x[i], x[j], x[k], x[l])
        formula = (105*x[i]*x[j]*x[k]*x[l]/radius**9
                   -15*(delta(i,j)*x[k]*x[l]+delta(i,k)*x[j]*x[l]
                        +delta(i,l)*x[j]*x[k]+delta(j,k)*x[i]*x[l]
                        +delta(j,l)*x[i]*x[k]+delta(k,l)*x[i]*x[j])/radius**7
                   +3*(delta(i,j)*delta(k,l)+delta(i,k)*delta(j,l)
                       +delta(i,l)*delta(j,k))/radius**5)
        zero((derivative-formula)*radius**9, 'fourth Newton derivative, including repeated indices')
    require(105+6*15+3*3 == 204, 'pointwise fourth derivative bound')
    require(3*9*204//2 == 2754, 'matrix pressure Hessian tail coefficient')
    r, R0 = s.symbols('r R', positive=True)
    zero(s.integrate(r**(-3), (r, R0, s.oo))-1/(2*R0**2), 'integrable far pressure tail')
    zero(-2+4*R(1, 4)+1, 'localization retains a strictly negative second jet')
    return {'potential': '-(cos z,cos x,cos y)',
            'compact_datum': 'u_R=curl(chi(x/R)*potential)',
            'pressure_bound': '||Hess p_R(0)||op <= 2754*M_chi/R^2',
            'M_chi': '3*((1+||grad chi||infinity)^2+1)',
            'radius': 'R>=max(1,2*sqrt(2754*M_chi))',
            'directional_second_coefficient': '<=-nu<0 for every nu>0',
            'scope': 'analytic compact finite-energy R3 NS localization; no singularity claim'}


def continuation_constants():
    E, Z, nu, S = s.symbols('E0 Z0 nu S', positive=True)
    c = R(151875, 16)*S**3/nu**3
    delta = 1/(4*c*Z**2)
    zero(1-2*c*Z**2*delta-R(1, 2), 'datum-fixed local time doubles at most the squared gradient energy')
    K0 = 2*delta*Z**2+2*E**2/(nu**2*delta)
    zero(K0-(8*nu**3/(151875*S**3)+151875*S**3*E**2*Z**2/(2*nu**5)),
         'explicit initial and overlapping-window allowance')
    m, L = s.symbols('m L', nonnegative=True)
    zero(2*m*m+8*L*L-(m+2*L)**2-(m-2*L)**2,
         'exact square gap for the source-aware cost split')
    # Fubini charges a dissipated-energy element for at most delta time.
    zero((E/(nu*delta))*(E/nu)-E**2/(nu**2*delta),
         'L-infinity times L1 pays the squared overlapping-window cost')
    lam = s.symbols('lambda', positive=True)
    zero(K0.subs({E: E/lam, Z: lam*Z})-K0, 'whole-space NS scaling of paid critical cost')
    return {'delta': str(s.simplify(delta)), 'paid_cost_K0': str(s.simplify(K0)),
            'unconditional_estimate': 'integral H_k^2 <= K0 + 8*integral_delta^T L_delta^2',
            'weighted_creation_cost': 'L_delta(t)=integral (I-A(C(t))):J_delta(t)J_delta(t)^T',
            'OPEN': 'bound integral L_delta^2 by a finite original-data constant on every same-datum prefix',
            'conditional_gradient_bound': 'Z(t)<=Z0*exp(c*(K0+8*K_creation))'}


if __name__ == '__main__':
    report = {'actual_history': actual_cyclic_history(),
              'joint_variance': joint_variance_and_source_clock(),
              'whole_space': compact_localization(),
              'continuation': continuation_constants(),
              'certification': 'exact algebra; PDE, covariance and all-prefix estimates analytic, not Lean-certified',
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    print(json.dumps(report, indent=2, sort_keys=True))
