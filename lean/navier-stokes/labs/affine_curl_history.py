#!/usr/bin/env python3
"""Exact algebra for affine stochastic smoothing and shared NS parents.

Gaussian kernel estimates and continuum operator bounds are analytic in
README.md. The shear calibration uses the full unforced viscous equation;
its transported initial pieces are not separate Navier--Stokes solutions.
"""

import hashlib
import itertools
import json
from pathlib import Path

import sympy as s


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def zero(value, label):
    values = list(value) if isinstance(value, s.MatrixBase) else [value]
    require(all(s.simplify(s.expand_trig(x)) == 0 for x in values), label)


def psd(matrix, label):
    require(matrix == matrix.T, label+' symmetry')
    minors = []
    for size in (1, 2, 3):
        for rows in itertools.combinations(range(3), size):
            minor = s.factor(matrix.extract(rows, rows).det())
            require(minor >= 0, label+' principal minor')
            minors.append(str(minor))
    return minors


def matrix_checks():
    a, b, x, y, z = s.symbols('a b x y z', positive=True)
    determinant = (a+b*x)*(a+b*y)*(a+b*z)
    remainder = s.Poly(s.expand(determinant-a*b*b*x*y), a, b, x, y, z)
    require(all(c > 0 for c in remainder.coeffs()),
            'the Gaussian determinant pays the product of the largest two stretches')
    rows = []
    fixtures = [s.eye(3), s.diag(16, s.Rational(1, 2), s.Rational(1, 8)),
                s.Matrix([[1, 8, 0], [0, 1, 0], [0, 0, 1]]),
                s.Matrix([[1, 0, 0], [0, 1, 5], [0, 0, 1]])
                *s.Matrix([[1, 7, 0], [0, 1, 0], [0, 0, 1]])]
    aa, bb = s.Rational(2, 3), s.Rational(5, 7)
    r = s.Matrix([1, -2, 3])
    h, v = s.Matrix([2, 3, -1]), s.Matrix([1, -4, 2])
    for J in fixtures:
        require(J.det() == 1, 'the actual matrix retains volume')
        zero(J*(J.T*h).cross(v)-h.cross(J.inv().T*v),
             'curl integration by parts retains the inverse-transpose factor')
        C = aa*s.eye(3)+bb*J*J.T+r*r.T/11
        psd(C-aa*s.eye(3)-bb*J*J.T, 'extra covariance remains nonnegative')
        certificate = psd(C.det()*s.eye(3)-aa*bb**2*(J*J.T).inv(),
                          'determinant controls every cofactor direction')
        rows.append({'J': str(J), 'covariance_determinant': str(C.det()),
                     'cofactor_certificate_minors': certificate})

    J1, J2, J3 = fixtures[2], fixtures[3], fixtures[1]
    C1, C2, C3 = s.diag(1, 2, 3), s.diag(4, 2, 1), s.diag(2, 5, 3)

    def compose(second, first):
        K, D = second
        J, C = first
        return K*J, D+K*C*K.T

    left = compose((J3, C3), compose((J2, C2), (J1, C1)))
    right = compose(compose((J3, C3), (J2, C2)), (J1, C1))
    zero(left[0]-right[0], 'composed deformation is associative')
    zero(left[1]-right[1], 'composed covariance retains transported earlier noise')
    require(J2*C1*J2.T != C1, 'resetting earlier noise changes the boundary response')
    nu, t, gamma = s.symbols('nu t gamma', positive=True)
    J = s.Matrix([[1, gamma*t, 0], [0, 1, 0], [0, 0, 1]])
    C = 2*nu*s.Matrix([[t+gamma**2*t**3/3, gamma*t*t/2, 0],
                      [gamma*t*t/2, t, 0], [0, 0, t]])
    A = s.Matrix([[0, gamma, 0], [0, 0, 0], [0, 0, 0]])
    zero(s.diff(J, t)-A*J, 'complete shear deformation rate')
    zero(s.diff(C, t)-A*C-C*A.T-2*nu*s.eye(3), 'complete stochastic covariance rate')
    zero(C.det()-(2*nu*t)**3*(1+gamma**2*t*t/12), 'shear covariance determinant')
    M, d = s.symbols('M d', positive=True)
    variance = nu*(1-s.exp(-2*M*d))/M
    zero(s.diff(variance, d)-2*nu*s.exp(-2*M*d), 'initial and terminal diffusion windows')
    return {'fixtures': rows, 'shear_covariance_determinant': str(s.factor(C.det())),
            'endpoint_variance': str(variance),
            'kernel_constant': 'exp(-1/2)/(2*pi)^(3/2)',
            'bound': '||T_(J,C) curl v||_infinity <= kernel_constant*||v||_1/(a*b)',
            'hypotheses': 'det J=1, a>0, b>0, C >= a I + b J J^T'}


def shear_checks():
    x, y, z, t = s.symbols('x y z t', real=True)
    A, B = s.symbols('A B', real=True)
    nu = s.symbols('nu', positive=True)
    xyz = (x, y, z)

    def grad(f):
        return s.Matrix([s.diff(f, q) for q in xyz])

    def lap(v):
        return v.applyfunc(lambda f: sum(s.diff(f, q, 2) for q in xyz))

    def curl(v):
        return s.Matrix([s.diff(v[2], y)-s.diff(v[1], z),
                         s.diff(v[0], z)-s.diff(v[2], x),
                         s.diff(v[1], x)-s.diff(v[0], y)])

    def adv(v, w):
        return w.jacobian(xyz)*v

    u = s.Matrix([s.exp(-nu*t)*(A*s.sin(y)+B*s.sin(z)), 0, 0])
    omega = curl(u)
    shared = A*B*t*s.exp(-2*nu*t)*s.cos(y)*s.cos(z)
    m = s.Matrix([shared, B*s.exp(-nu*t)*s.cos(z), 0])
    n = s.Matrix([-shared, 0, -A*s.exp(-nu*t)*s.cos(y)])
    zero(s.trace(u.jacobian(xyz)), 'full shear is incompressible')
    zero(s.diff(u, t)+adv(u, u)-nu*lap(u), 'actual unforced NS with canonical pressure zero')
    zero(m+n-omega, 'both original parents reconstruct the actual vorticity')
    zero(m.subs(t, 0)-curl(s.Matrix([B*s.sin(z), 0, 0])), 'first piece retains its original parent')
    zero(n.subs(t, 0)-curl(s.Matrix([A*s.sin(y), 0, 0])), 'second piece retains its original parent')
    for field in (m, n, omega):
        zero(s.trace(field.jacobian(xyz)), 'transported vorticity contribution remains solenoidal')
        zero(s.diff(field, t)+adv(u, field)-adv(field, u)-nu*lap(field),
             'all components use the same complete viscous stretching equation')
    work = lambda w: (w.T*u.jacobian(xyz)*w)[0]
    factor = A*A*B*B*t*s.exp(-4*nu*t)*s.cos(y)**2*s.cos(z)**2
    zero(work(m)-factor, 'first parent has positive individual stretching')
    zero(work(n)-factor, 'second parent has positive individual stretching')
    zero(work(omega), 'complete physical stretching vanishes')
    cross = (m.T*u.jacobian(xyz)*n+n.T*u.jacobian(xyz)*m)[0]
    zero(cross+2*factor, 'joint signed cross work cancels both positive individual costs')
    energy_m = B*B*s.exp(-2*nu*t)/2+A*A*B*B*t*t*s.exp(-4*nu*t)/4
    diffusion_m = B*B*s.exp(-2*nu*t)/2+A*A*B*B*t*t*s.exp(-4*nu*t)/2
    mean_work = A*A*B*B*t*s.exp(-4*nu*t)/4
    zero(s.diff(energy_m, t)-2*mean_work+2*nu*diffusion_m,
         'normalized component energy retains its full viscous cost')
    zero(s.integrate(mean_work, (t, 0, s.oo))-A*A*B*B/(64*nu*nu),
         'each separate stretching bill is finite and explicitly evaluated')
    amplitude_at_peak = (A*B*t*s.exp(-2*nu*t)).subs(t, 1/(2*nu))
    zero(amplitude_at_peak-A*B/(2*s.E*nu), 'exact generated component at its peak')
    full_energy = (A*A+B*B)*s.exp(-2*nu*t)/2
    zero(s.diff(full_energy, t)+2*nu*full_energy, 'one original kinetic reserve decays')

    # A prescribed affine observation leaves this exact nonlinear source.
    h = s.symbols('h0:8')
    L = s.Matrix([[h[0], h[1], h[2]], [h[3], h[4], h[5]], [h[6], h[7], -h[0]-h[4]]])
    drift = L*s.Matrix(xyz)
    defect = (u-drift).cross(omega)
    zero(s.diff(omega, t)+adv(drift, omega)-L*omega-nu*lap(omega)-curl(defect),
         'the actual physical bridge retains the complete curl source')

    amplitude, alpha, beta = s.symbols('L alpha beta', positive=True)
    J = s.Matrix([[1, amplitude*s.cos(y), 0], [0, 1, 0], [0, 0, 1]])
    require(J.det() == 1, 'the nonlinear periodic shear preserves volume')
    before_terminal_heat = J*s.exp(-beta/2)*curl(s.Matrix([s.sin(z), 0, 0]))
    zero(lap(before_terminal_heat)+s.diag(2, 1, 1)*before_terminal_heat,
         'the generated components have their exact terminal heat eigenvalues')
    split_output = s.Matrix([amplitude*s.exp(-alpha-beta/2)*s.cos(y)*s.cos(z),
                              s.exp(-(alpha+beta)/2)*s.cos(z), 0])
    zero(split_output-s.diag(s.exp(-alpha), s.exp(-alpha/2), s.exp(-alpha/2))*before_terminal_heat,
         'both heat intervals and the full volume-preserving pushforward are retained')
    zero(split_output[0].subs({y: 0, z: 0})-amplitude*s.exp(-alpha-beta/2),
         'two heat intervals cannot uniformly erase a curved shear contribution')
    return {'actual_velocity': str(u), 'actual_vorticity': str(omega),
            'shared_generated_component': str(shared),
            'individual_stretching_mean': str(A*A*B*B*t*s.exp(-4*nu*t)/4),
            'individual_stretching_integral': str(A*A*B*B/(64*nu*nu)),
            'complete_stretching': '0',
            'component_peak_amplitude': 'A*B/(2*exp(1)*nu)',
            'nonlinear_split_output': str(split_output),
            'scope': 'The full shear is actual NS. Its transported pieces and the heat/map/heat operator are auxiliary observations, not independent NS solutions.'}


if __name__ == '__main__':
    result = {'matrix_and_covariance': matrix_checks(), 'shared_shear': shear_checks(),
              'status': 'Exact matrix, covariance, full NS, component and physical-defect checks passed.',
              'scope': 'Gaussian operator estimates and continuum consequences are analytic; no new Lean certificate or arbitrary-data regularity bound.',
              'source_sha256': {Path(__file__).name: hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}}
    print(json.dumps(result, indent=2), flush=True)
