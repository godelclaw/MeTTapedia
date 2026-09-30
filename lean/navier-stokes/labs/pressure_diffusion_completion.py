#!/usr/bin/env python3
"""Exact coupled diffusion tests and a convex pressure/geometry completion.

The counterexample uses canonical pressure and the complete unforced NS
initial tangent, including the retained-memory pressure correction. It
refutes automatic nonnegative diffusion of the preceding envelope, not a
finite history allowance. The completion's uniform estimates are analytic
in README.md; this file checks their differential algebra and coefficients.
"""
import json
import sympy as s
import pressure_history_source as f
import strain_cycle_diffusion as d
import pressure_core_envelope as envelope


def curl_matrix(B):
    return s.Matrix([B[2, 1]-B[1, 2], B[0, 2]-B[2, 0], B[1, 0]-B[0, 1]])


def branches(B, P, eta):
    S = (B+B.T)/2
    w = curl_matrix(B)
    W = w.dot(w)
    V = w.dot(S*w)
    Q = s.trace(S*S)
    Z = (S*w).dot(S*w)
    perspective = V*V/(W+eta)
    pressure = 5*perspective+s.Rational(63, 95)*W*W-2*w.dot(P*w)
    core = (5*perspective+s.Rational(4, 7)*Z
            +s.Rational(10, 21)*Q*W+s.Rational(44, 95)*W*W)
    return pressure, core


def datum(amplitude):
    sx, sy, sz = d.SINES
    sxz, syz = d.sin((1, 0, 1)), d.sin((0, 1, 1))
    base = [f.scale(3, sxz),
            f.add(f.scale(4, sx), f.scale(4, syz), f.scale(-2, sz)),
            f.add(f.scale(-3, sxz), f.scale(-4, syz), f.scale(6, sx), f.scale(5, sy))]
    wave = f.scale(amplitude, f.add(d.COSINES[2], f.scale(-1, d.ONE)))
    return [f.add(base[0], f.scale(3, wave)),
            f.add(base[1], f.scale(-3, wave)), base[2]]


def check_physical_diffusion():
    u = datum(d.MM)
    result = envelope.actual(u, d.NN, s.Integer(1))
    b = f.jac(u)
    B = d.matval(b)
    expected = s.Matrix([[3, 0, 3], [4, 4, 2], [3, 1, -7]])
    for entry in B-expected:
        d.zero(entry, 'fixed physical gradient')
    E = s.Matrix([[0, 0, 3], [0, 0, -3], [0, 0, 0]])
    d.zero(s.trace(B), 'incompressibility of the observed gradient')
    d.zero(s.trace(E), 'solenoidal rank-one perturbation')
    G = f.matmul(b, [list(row) for row in zip(*b)])
    C1 = [[f.scale(2*d.NN, q) for q in row] for row in G]
    P1 = d.matval(f.hess(f.tensor_pressure(C1)))
    w = curl_matrix(B)
    g = result['gap']
    theta = (1+g/s.sqrt(g*g+1))/2
    corrected = result['DY']-2*theta*w.dot(P1*w)
    geometric = 2*d.NU*s.trace(d.matval(G))/3
    normalized = corrected-geometric*result['Y']
    coefficient = s.expand(corrected).coeff(d.NU).coeff(d.M, 2)
    target = (s.Rational(1157059982, 53865)
              +s.Rational(1878897001588512, 24008300438700487)*s.sqrt(58564129))
    d.zero(coefficient-target, 'positive coupled viscous coefficient')
    d.zero(s.expand(normalized).coeff(d.NU).coeff(d.M, 2)-coefficient,
           'actual geometric normalization does not remove this coefficient')
    if not s.Rational(1157059982, 53865) > 20000:
        raise ArithmeticError('strict rational viscous lower certificate')

    # Independently compute the complete coupled spatial Hessian. At C=0
    # the explicit viscosity in D(P_hat) cancels with C_t=2 nu G.
    pressure = f.hess(f.green(f.trace(f.matmul(b, b))))
    P = d.matval(pressure)
    t = s.symbols('t', real=True)
    coupled_curvature = 0
    for j in range(3):
        Bj = d.matval([[f.diff(q, j) for q in row] for row in b])
        Pj = d.matval([[f.diff(q, j) for q in row] for row in pressure])
        pbranch, core = branches(B+t*Bj, P+t*Pj, s.Integer(1))
        gap = pbranch-core
        curv = (s.diff(core, t, 2).subs(t, 0)
                +theta*s.diff(gap, t, 2).subs(t, 0)
                +s.diff(gap, t).subs(t, 0)**2/(2*(g*g+1)**s.Rational(3, 2)))
        coupled_curvature += curv
    d.zero(s.expand(coupled_curvature).coeff(d.M, 2)+coefficient,
           'independent physical Hessian matches the full NS tangent')
    _, core = branches(B+t*E, P, s.Integer(1))
    core_second = s.factor(s.diff(core, t, 2).subs(t, 0))
    d.zero(core_second+s.Rational(1124556302, 53865), 'core rank-one nonconvexity')
    return {'fixed_gradient': str(B), 'canonical_pressure': str(P),
            'fixed_gap': str(g), 'core_rank_one_second_derivative': str(core_second),
            'viscous_alpha_squared_coefficient': str(coefficient),
            'strict_rational_lower': '20000',
            'memory_correction_and_normalization': 'included',
            'scope': 'initial-time diffusion obstruction; no excess-history refutation'}


def check_joint_completion():
    r, q, e2, d0, ell, L2 = s.symbols('r q e2 d ell L2', real=True)
    second = 8*d0*d0+4*(r+q)*e2+8*d0*ell+2*L2+2*r/q*(L2-ell*ell)
    certificate = (s.Rational(2, 5)*(5*d0+2*ell)**2
                   +2*(r*e2-d0*d0)+2*q*e2
                   +s.Rational(8, 5)*(L2-ell*ell)+2*r/q*(L2-ell*ell))
    d.zero(second-2*(r+q)*e2-s.Rational(2, 5)*L2-certificate,
           'joint completion Hessian lower certificate')

    # Independent matrix differentiation, with a noncommuting pressure
    # perturbation. No simultaneous eigenframe is assumed.
    B = s.Matrix([[1, 2, -1], [0, -2, 3], [4, 1, 1]])
    E = s.Matrix([[2, -1, 3], [4, 1, 0], [0, 2, -3]])
    P = s.Matrix([[2, 1, 0], [1, -1, 2], [0, 2, 3]])
    L = s.Matrix([[1, -2, 3], [-2, 4, 0], [3, 0, -1]])
    t = s.symbols('t', real=True)
    norm2 = lambda A: s.trace(A.T*A)
    rr = norm2(B); qq = s.sqrt(1+norm2(P))
    dd = s.trace(B.T*E); ll = s.trace(P.T*L)/qq
    direct = (norm2(B+t*E)+s.sqrt(1+norm2(P+t*L)))**2
    expected = second.subs({r: rr, q: qq, e2: norm2(E), d0: dd,
                           ell: ll, L2: norm2(L)})
    d.zero(s.diff(direct, t, 2).subs(t, 0)-expected,
           'independent full matrix completion derivative')

    # The universal norm estimates are derived in the README. These
    # coefficient checks retain both branches, all mixed directions,
    # and the pressure-gradient square.
    core_negative = s.Rational(1744, 21)
    lower = 48*(2*(r+q)*e2+s.Rational(2, 5)*L2)
    core_lower = lower-core_negative*r*e2
    pressure_lower = lower-(88*r+8*q)*e2-8*L2
    target = 8*(r+q)*e2+s.Rational(56, 5)*L2
    d.zero(core_lower-target-(s.Rational(104, 21)*r+88*q)*e2-8*L2,
           'completed core lower coefficient')
    d.zero(pressure_lower-target-80*q*e2, 'completed pressure lower coefficient')
    if not s.Rational(19457, 3990) < 5:
        raise ArithmeticError('core value upper coefficient')
    if not 596+601+s.Rational(212**2+217**2, 48) < 3200:
        raise ArithmeticError('radial strain-Hessian upper coefficient')
    if not 212**2+217**2 < 93000:
        raise ArithmeticError('strain-sensitivity square upper coefficient')
    return {'completion': '(||B||_F^2+sqrt(sigma^2+||P_hat||_F^2))^2',
            'coefficient': 48,
            'smooth_envelope': '1+sqrt((pressure_branch+48R)^2+(core_branch+48R)^2)',
            'full_Hessian_lower': '8Q||E||_F^2+(56/5)||L||_F^2',
            'strain_Hessian_upper': '3200Q||H||_F^2',
            'strain_sensitivity_square_upper': '93000Q^3',
            'scope': 'uniform analytic matrix estimates with exact algebra certificates'}


def check_completed_matrix_fixtures():
    # Exact independent differentiation tests a general strain, a rotating
    # background and vorticity zero, with a noncommuting pressure increment.
    backgrounds = [s.Matrix([[3, 0, 3], [4, 4, 2], [3, 1, -7]]),
                   s.Matrix([[0, 1, 0], [-1, 0, -1], [0, 1, 0]]), s.zeros(3)]
    E = s.Matrix([[0, 0, 3], [0, 0, -3], [0, 0, 0]])
    P = s.diag(1, 2, 2)
    L = s.Matrix([[1, 2, -1], [2, 0, 3], [-1, 3, -2]])
    t = s.symbols('t', real=True)
    norm2 = lambda A: s.trace(A.T*A)
    results = []
    for B in backgrounds:
        r, q, e, g = norm2(B), s.Integer(4), norm2(E), norm2(L)
        pbranch, core = branches(B+t*E, P+t*L, s.Rational(1, 7))
        completion = (norm2(B+t*E)+s.sqrt(7+norm2(P+t*L)))**2
        p2 = s.factor(s.diff(pbranch, t, 2).subs(t, 0))
        c2 = s.factor(s.diff(core, t, 2).subs(t, 0))
        R2 = s.factor(s.diff(completion, t, 2).subs(t, 0))
        target = 8*(r+q)*e+s.Rational(56, 5)*g
        margins = [p2+48*R2-target, c2+48*R2-target]
        if not (c2 >= -s.Rational(1744, 21)*r*e
                and p2 >= -(88*r+8*q)*e-8*g
                and R2 >= 2*(r+q)*e+s.Rational(2, 5)*g
                and all(margin >= 0 for margin in margins)):
            raise ArithmeticError('independent matrix fixture lower estimate')
        results.append({'gradient_norm_squared': str(r),
                        'completed_branch_margins': list(map(str, margins))})
    return results


def check_radial_switch_and_receiver():
    A, B, rho, a1, b1, a2, b2 = s.symbols('A B rho a1 b1 a2 b2', real=True)
    first = (A*a2+B*b2)/rho
    radial = first+(a1*a1+b1*b1)/rho-(A*a1+B*b1)**2/rho**3
    positive = first+(B*a1-A*b1)**2/rho**3
    d.zero((radial-positive)*rho**3
           -(rho*rho-A*A-B*B)*(a1*a1+b1*b1), 'radial switch square')
    b, z = s.symbols('b z', positive=True)
    curvature = 2*b*b/z**3
    d.zero(2-z*curvature-2*(z-b)*(z+b)/z**2,
           'full receiver weight derivative scale')
    # PSD-Hessian Cauchy--Schwarz supplies ||d T||^2 <=3200Q Hess.
    # The continuous selection weight supplies the other product term.
    d.zero(s.Rational(93000, 12)-7750, 'full threshold product coefficient')
    if not 7750 < 8000 or not 6400 < 8000:
        raise ArithmeticError('full pressure-receiver payment coefficient')
    return {'strain_receiver': 'M=a_b partial_S Psi',
            'full_gradient_payment': '(nu/(8000Q))||grad M||_F^2<=J_b+a_b D_Psi',
            'retained_defects': ['weighted nonlocal memory-pressure norm',
                                 'new completion reaction and parent-pressure source',
                                 'signed arbitrary-history allowance'],
            'scope': 'local diffusion payment; no nonlocal or recurrent-history bound'}


def check_preserved_mixing_payment():
    sigma, L, nu, t = s.symbols('sigma L nu t', positive=True)
    r = s.symbols('r', nonnegative=True)
    # Here r=||grad u||^2=|omega|^2. Actual fluid and retained-memory
    # pressure are zero throughout the triangular mixing history.
    excess_upper = 192*sigma*r+107*r*r
    d.zero(11*r*r+96*((sigma+r)**2-sigma**2)-excess_upper,
           'completed branch Lipschitz bound above the far-field offset')
    bound = excess_upper.subs(r, L*L*s.exp(-2*nu*t))
    allowance = 96*sigma*L*L/nu+107*L**4/(4*nu)
    d.zero(s.integrate(bound, (t, 0, s.oo))-allowance,
           'completed observable retains the full stochastic mixing payment')
    return {'far_field_offset': '1+48*sqrt(2)*sigma^2',
            'L_squared': 'A^2+B^2+(A*B/nu)^2',
            'all_time_allowance': '96*sigma*L^2/nu+107*L^4/(4*nu)',
            'threshold': 'fixed above the initial envelope and the far-field offset',
            'scope': 'the existing actual periodic triangular mixing class'}


if __name__ == '__main__':
    print(json.dumps({'status': 'all exact checks passed',
                      'physical_counterexample': check_physical_diffusion(),
                      'completion': check_joint_completion(),
                      'matrix_fixtures': check_completed_matrix_fixtures(),
                      'receiver': check_radial_switch_and_receiver(),
                      'mixing': check_preserved_mixing_payment()}, indent=2))
