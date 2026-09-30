#!/usr/bin/env python3
"""Complete local receiver payments and an actual-parent norm obstruction.

Default checks use exact rational Fourier fields and symbolic matrix
variations. Every NS output is retained. Optional quadrature evaluates
full continuum-PDE tangents in two phase variables with the physical
anisotropic symbol; it is not a time evolution or a continuum enclosure.
The arbitrary-history allowance remains open.
"""

import argparse
import json
from fractions import Fraction
import sympy as s
import pressure_history_source as f
import pressure_memory_diffusion as pm
import pressure_diffusion_completion as completion


def coefficient_checks():
    p_first = 5*16+s.Rational(63, 95)*16+8+192
    c_first = 5*16+s.Rational(4, 7)*8+s.Rational(10, 21)*8+s.Rational(44, 95)*16+192
    p_second = 5*152+s.Rational(63, 95)*48+8+576
    c_second = 5*152+s.Rational(4, 7)*18+s.Rational(10, 21)*12+s.Rational(44, 95)*48+576
    if not (p_first < 300 and c_first < 300 and p_second < 1400 and c_second < 1400):
        raise ArithmeticError('complete B-slot coefficient bounds')
    if not (2800+s.Rational(180000, 48) < 6600
            and 192+s.Rational(19216, 48) < 600):
        raise ArithmeticError('full radial block upper bounds')
    if not (2*7500 <= 15000 and 2*6600 <= 15000
            and 2*s.Rational(20000, 24) < 1700 and 2*600 < 1700
            and 2*1700+2*16 < 3500):
        raise ArithmeticError('complete product-rule payment coefficients')
    a = 48+s.Rational(63, 95)
    b = 48+s.Rational(1399, 1995)
    rho = s.sqrt(a*a+b*b)
    kappa = (a+b)/rho
    return {'full_B_block_upper': '6600 Q',
            'B_sensitivity_square': '180000 Q^3',
            'pressure_block_upper': '600 Q/q',
            'pressure_sensitivity_square': '20000 Q^2',
            'strain_receiver_payment': 'nu |grad M|^2/Q <= 15000 (J+a D_Phi)',
            'pressure_receiver_payment': 'nu (q/Q) |grad N|^2 <= 3500 (J+a D_Phi)',
            'limiting_branch_coefficients': [str(a), str(b)],
            'limiting_radial_factor': str(rho), 'limiting_pressure_factor': str(kappa),
            'scope': 'analytic matrix bounds; scalar coefficient identities checked exactly'}


def exact_matrix_cases():
    t = s.symbols('t', real=True)
    matrices = [s.Matrix([[3, 0, 3], [4, 4, 2], [3, 1, -7]]),
                s.Matrix([[0, 1, 0], [-1, 0, -1], [0, 1, 0]]), s.zeros(3)]
    E = s.Matrix([[2, -1, 3], [4, 1, 0], [0, 2, -3]])
    P = s.Matrix([[2, 1, 0], [1, -1, 2], [0, 2, 3]])
    L = s.Matrix([[1, -2, 3], [-2, 4, 0], [3, 0, -1]])
    norm = lambda m: s.trace(m.T*m)
    cases = []
    for B in matrices:
        r = norm(B); q = s.sqrt(1+norm(P)); Q = r+q
        def value(D, R):
            p0, c0 = completion.branches(D, R, s.Rational(1, 7))
            R0 = (norm(D)+s.sqrt(1+norm(R)))**2
            A, C = p0+48*R0, c0+48*R0
            return 1+s.sqrt(A*A+C*C)
        BB = s.diff(value(B+t*E, P), t, 2).subs(t, 0)
        PP = s.diff(value(B, P+t*L), t, 2).subs(t, 0)
        bmargin = s.simplify(6600*Q*norm(E)-BB)
        pmargin = s.simplify(600*Q/q*norm(L)-PP)
        if not (bmargin > 0 and pmargin > 0):
            raise ArithmeticError('independently differentiated full block fixture')
        cases.append({'gradient_square': str(r), 'pressure_scale': str(q),
                      'complete_B_increment': str(E), 'pressure_increment': str(L),
                      'full_B_upper_margin_positive': True,
                      'pressure_upper_margin_positive': True})
    return cases


def derivative(q, j, N):
    return f.scale(N if j == 0 else 1, f.diff(q, j))


def gradient(q, N): return [derivative(q, j, N) for j in range(3)]
def jacobian(u, N): return [gradient(q, N) for q in u]
def hessian(q, N): return [gradient(derivative(q, j, N), N) for j in range(3)]

def green(q, N):
    return {k: a/(N*N*k[0]**2+k[1]**2+k[2]**2)
            for k, a in q.items() if k != f.ORIGIN}

def observe(T, N):
    source = f.add(*(derivative(derivative(T[i][j], i, N), j, N)
                     for i in range(3) for j in range(3)))
    return hessian(green(source, N), N)

def reflection(q): return {(-k[0], k[1], k[2]): a for k, a in q.items()}


def parity(q, sign, label):
    f.equal(reflection(q), f.scale(sign, q), label)


def exact_family(N, phase):
    sin = completion.d.sin
    cos = completion.d.cos
    u = [f.scale(N, sin((0, 1, 0))),
         f.scale(f.QQ_I(phase)/(N*N), sin((1, 0, 0))), {}]
    B = jacobian(u, N)
    f.equal(f.trace(B), {}, 'actual incompressible datum')
    p = f.scale(f.QQ_I(2*phase)/(N*N+1), f.mul(cos((0, 1, 0)), cos((1, 0, 0))))
    P = hessian(p, N)
    f.equal(p, green(f.trace(f.matmul(B, B)), N), 'literal canonical pressure')
    f.same_matrices(P, observe(f.tensor(u, u), N), 'canonical tensor observer')
    G = f.matmul(B, pm.transpose(B))
    nu = f.QQ_I(1)/10
    Ct = pm.matrix_scale(2*nu, G)
    f.same_matrices(observe(Ct, N), [[{} for _ in range(3)] for _ in range(3)],
                    'actual generated memory has zero pressure source at this state')
    nonlinear = [f.add(f.scale(-1, f.dot(u, gradient(q, N))),
                       f.scale(-1, derivative(p, j, N))) for j, q in enumerate(u)]
    lap = lambda q: f.add(*(derivative(derivative(q, j, N), j, N) for j in range(3)))
    ut = [f.add(v, f.scale(nu, lap(q))) for v, q in zip(nonlinear, u)]
    f.equal(f.trace(jacobian(ut, N)), {}, 'complete unforced NS tangent')
    Pt = observe(pm.symmetric_product(u, ut), N)
    St = f.scale(2, f.trace(f.matmul(B, jacobian(ut, N))))
    f.same_matrices(Pt, hessian(green(St, N), N), 'actual differentiated Poisson source')
    Pnl = observe(pm.symmetric_product(u, nonlinear), N)
    Bnl = jacobian(nonlinear, N)
    for i, j in [(0, 1), (1, 0)]:
        parity(B[i][j], 1, 'retained B slot is even in the fast phase')
        parity(Bnl[i][j], -1, 'actual nonlinear off-diagonal B tangent is odd')
    for i in range(3):
        for j in range(3):
            if i != j and {i, j} == {0, 1}:
                parity(P[i][j], -1, 'actual off-diagonal pressure parity')
                parity(Pnl[i][j], 1, 'actual off-diagonal pressure tangent parity')
            else:
                parity(P[i][j], 1, 'actual diagonal pressure parity')
                parity(Pnl[i][j], -1, 'actual diagonal pressure tangent parity')
    # On these matrices the complete B-gradient has only the xy/yx
    # entries. The pressure gradient retains the diagonal, xy/yx and zz
    # entries. The envelope and its soft selector are even in the phase.
    # Thus each nonlinear cotangent work integrand is odd; no parent is
    # discarded. Its spatial mean is zero, not an absolute-norm payment.
    energy = pm.mean(f.dot(u, u))
    if energy != f.QQ_I(Fraction(N*N, 2)+Fraction(1, 2*N**4)).x:
        raise ArithmeticError('exact full initial energy')
    return {'parent_frequency': N, 'phase': phase, 'initial_squared_L2': str(energy),
            'pressure': '2 phase cos(y) cos(n x)/(n^2+1)',
            'canonical_pressure_and_full_NS_tangent': 'exact',
            'generated_memory_pressure_source': 'zero at C=0 only',
            'full_nonlinear_work_mean': 'zero by exact phase parity',
            'scope': 'actual initial NS state; initialized history allowance not refuted'}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--quadrature', action='store_true',
                        help='also compare phase-grid continuum-PDE diagnostics')
    args = parser.parse_args()
    report = {'coefficients': coefficient_checks(), 'matrices': exact_matrix_cases(),
              'actual_family': [exact_family(N, sign) for N in (3, 5, 8) for sign in (-1, 1)],
              'arbitrary_history_bound': False}
    if args.quadrature:
        from joint_receiver_quadrature import diagnose
        report['quadrature'] = diagnose()
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
