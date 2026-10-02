#!/usr/bin/env python3
"""Complete far-parent flux and original-data spatial-moment payment.

Checks exact Cartesian and weighted identities, constants and scaling.
Optional quadrature compares the literal Riesz tail with its stress rewrite,
including the cutoff derivative. Moment propagation, convolution estimates
and the resulting physical history payment are analytic, not Lean-certified.
"""

import argparse
import json
import sympy as s
from rotational_curl_reserve import require, zero
from rotational_joint_enstrophy import r, z, grad, lap5, velocity
from critical_parent_transport import terms, moment


def stress_identity():
    x = s.symbols('x0:5', real=True)
    chi = s.Function('chi')(*x)
    g = s.Matrix([s.diff(chi, t) for t in x])
    ez = s.Matrix([0, 0, 0, 0, 1])
    Y = s.Matrix([*x[:4], 0])
    A = ez*Y.T-Y*ez.T
    v = 2*chi*ez+A*g
    h = -sum(s.diff(chi, t, 2) for t in x)
    S = g*g.T-s.eye(5)*g.dot(g)/2
    T = ez*g.dot(g)-2*g[4]*g
    F = 2*chi*g*ez.T+S*A.T  # F_ij: divergence in its first index
    H = s.Matrix([-3*g[4]*g[i] for i in range(4)]
                 + [2*sum(g[i]**2 for i in range(4))-g[4]**2])
    divF = s.Matrix([sum(s.diff(F[i, j], x[i]) for i in range(5))
                      for j in range(5)])
    zero(v*h+T+divF-H, 'complete Cartesian parent stress identity')
    gh2, gz2 = s.symbols('gh2 gz2', nonnegative=True)
    normH2 = 9*gh2*gz2+(2*gh2-gz2)**2
    zero(4*(gh2+gz2)**2-normH2-3*gz2*(gh2+gz2),
         'pointwise H norm is at most twice the gradient square')
    zero(sum(S[i, j]**2 for i in range(5) for j in range(5))
         -s.Rational(5, 4)*g.dot(g)**2, 'quadratic stress Frobenius norm')
    zero(sum(A[i, j]**2 for i in range(5) for j in range(5))-2*Y.dot(Y),
         'coordinate skew matrix Frobenius norm')
    require(s.sqrt(s.Rational(5, 2)) < 2, 'conservative quadratic F norm constant')
    return {'identity': 'v h+T=-div F+H, h=-Delta5 chi',
            'F_ij': '2 delta_jz chi chi_i + sum_k (delta_jz Y_k-Y_j delta_kz) S_ik',
            'H': '(-3 chi_z grad_h chi, 2|grad_h chi|^2-chi_z^2)',
            'bounds': '|H|<=2|grad chi|^2; |F|<=2|chi||grad chi|+2r|grad chi|^2'}


def spatial_moment():
    x = s.symbols('x0:3', real=True)
    viscosity = s.symbols('nu', positive=True)
    u = s.Matrix([s.Function('u'+str(i))(*x) for i in range(3)])
    pressure = s.Function('pressure')(*x)
    div = lambda vector: sum(s.diff(vector[i], x[i]) for i in range(3))
    lap = lambda scalar: sum(s.diff(scalar, xi, 2) for xi in x)
    du = u.jacobian(x)
    rhs = viscosity*u.applyfunc(lap)-du*u-s.Matrix([s.diff(pressure, xi) for xi in x])
    zero(2*u.dot(rhs)+div(u*(u.dot(u)+2*pressure))
         -viscosity*lap(u.dot(u))+2*viscosity*sum(entry**2 for entry in du)
         -div(u)*(u.dot(u)+2*pressure), 'full local kinetic energy including pressure work')
    rho2, length = s.symbols('rho2 length', positive=True)
    W = rho2/(1+rho2/length**2)
    dW = s.diff(W, rho2)
    lapW = 6*dW+4*rho2*s.diff(W, rho2, 2)
    zero(lapW-(6-2*rho2/length**2)/(1+rho2/length**2)**3,
         'three-dimensional bounded moment test Laplacian')
    zero(4*W-4*rho2*dW**2
         -4*rho2*((1+rho2/length**2)**3-1)/(1+rho2/length**2)**4,
         'bounded moment test obeys |grad W|^2<=4W')
    zero(6-lapW-(20*rho2/length**2+18*rho2**2/length**4
                  +6*rho2**3/length**6)/(1+rho2/length**2)**3,
         'bounded moment test obeys Delta W<=6')
    chi, weight = s.Function('chi')(r, z), s.Function('weight')(r, z)
    v = velocity(chi)
    zero(r*weight*v.dot(v)-r**3*weight*grad(chi).dot(grad(chi))
         -s.diff(2*r*r*weight*chi*chi, r)+2*r*r*s.diff(weight, r)*chi*chi,
         'physical meridional energy with every weight derivative')
    zero(1/(1-4*s.Rational(4, 25))-s.Rational(25, 9),
         'weighted gradient is controlled by physical moment')
    zero(2*s.Rational(2, 5)+2-s.Rational(14, 5),
         'integrated F bound from weighted Hardy')
    # Exact integrated check on the earlier positive-production fixture.
    profile = z/(1+r*r+z*z)**3
    gp = grad(profile)
    integral = lambda f: s.simplify(s.expand_func(sum(
        c*moment(m, k) for c, m, k in terms(f) if m % 2 == 0)))
    G0 = integral(gp.dot(gp))
    G2 = integral((r*r+z*z)*gp.dot(gp))
    C0 = integral(profile*profile)
    physical_moment_pi = G2-4*C0
    require(G0 > 0 and C0 > 0 and physical_moment_pi > 0,
            'positive finite physical resources on the rational fixture')
    require(G2 <= s.Rational(25, 9)*physical_moment_pi,
            'physical weighted-gradient estimate on the rational fixture')
    return {'actual_moment': 'sqrt(I(t))<=sqrt(I0+6nu E0 H)+3 C_S^(3/2) E0^(1/4) H^(1/4)(E0/(2nu))^(3/4)',
            'hypotheses': 'smooth unforced R3 prefix; canonical pressure; E0,I0 finite; nu>0',
            'lifted_identity': 'G0=pi E_meridional; G2=pi I_meridional+4||chi||_2^2',
            'lifted_bound': 'G2<=25pi I_meridional/9',
            'fixture': {'G0': str(G0), 'G2': str(G2), 'chi_L2_squared': str(C0),
                        'pi_I_meridional': str(physical_moment_pi)}}


def prepared_multiplier():
    k = s.Matrix(s.symbols('k0:5', real=True))
    rho2 = k.dot(k)
    m = -k[4]*k/rho2
    derivative = m.jacobian(k)
    zero(sum(entry**2 for entry in derivative)-(1+3*k[4]**2/rho2)/rho2,
         'complete vector multiplier derivative')
    zero(m.dot(m)-k[4]**2/rho2, 'prepared gradient multiplier norm')
    zero(1+2*s.Rational(2, 3)-s.Rational(7, 3),
         'Fourier Hardy gives the weighted prepared-gradient constant')
    t, H = s.symbols('t H', positive=True)
    zero(s.integrate(s.sqrt(t)+s.sqrt(H-t), (t, 0, H))
         -s.Rational(4, 3)*H**s.Rational(3, 2), 'both heat displacements are retained')
    return {'J': 'J(t)=integral_0^t heat(nu(t-s)) B(s)^2 ds; chi1=partial_z(-Delta5)^(-1)J',
            'bounds': '||grad chi1||_2<=||J||_2; ||x grad chi1||_2<=(7/3)||x J||_2',
            'original_heat': '||J||_2<=H A F; ||xJ||_2<=A[H M+(4/3)sqrt(10nu)H^(3/2)F]',
            'data': 'A=||b0||_infinity, F=||b0||_2, M=||x b0||_2, all on R5'}


def kernel_and_ledger():
    t = s.symbols('t', real=True)
    theta = 3*(t-1)**2-2*(t-1)**3
    zero(theta.subs(t, 1), 'cutoff vanishes at the inner seam')
    zero(theta.subs(t, 2)-1, 'cutoff reaches one at the outer seam')
    zero(s.diff(theta, t).subs(t, 1), 'zero inner derivative')
    zero(s.diff(theta, t).subs(t, 2), 'zero outer derivative')
    zero(s.Rational(3, 2)-s.diff(theta, t)-6*(t-s.Rational(3, 2))**2,
         'cutoff derivative bounded by 3/2')
    R, rho = s.symbols('R rho', positive=True)
    zero(s.integrate(rho**4*rho**(-10), (rho, R, s.oo))-R**(-5)/5,
         'far kernel L5/2 power')
    zero(s.integrate(rho**4*rho**(-s.Rational(25, 2)), (rho, R, s.oo))
         -s.Rational(2, 15)*R**(-s.Rational(15, 2)), 'far derivative L5/2 power')
    pp = s.Rational(5, 2)
    zero(pp*(pp-1)-s.Rational(15, 4), 'nu/4 diffusion allocation leaves 15/(4nu)')
    zero(s.Rational(15, 4)/5-s.Rational(3, 4), 'far linear clock coefficient')
    zero(s.Rational(15, 4)*s.Rational(4, 5)-3, 'far additive payment coefficient')
    zero(s.Rational(3, 4)-s.Rational(1, 4)-s.Rational(1, 2),
         'the near target retains half the original diffusion')
    # NS scaling: E:-1, I:-3, H:-2, A:2, F:-1/2, M:-3/2, R:-1.
    zero(-2+2-s.Rational(1, 2)+s.Rational(1, 2), 'prepared J norm scales as lambda^-1/2')
    zero(2-3-s.Rational(1, 2)+s.Rational(3, 2), 'prepared weighted J scales as lambda^-3/2')
    zero(3+s.Rational(-1-3, 2)-1, 'derivative kernel times F stock scales as lambda')
    zero(2-2, 'far clock times horizon is scale invariant')
    return {'kernel': 'K_R(x)=theta(|x|/R)/(2pi^3 |x|^4), theta=0 below1, 3(t-1)^2-2(t-1)^3 on[1,2], 1 above2',
            'complete_far_flux': 'J_a,far=e_z K_R*b^2 + sum_i partial_i K_R*F_ij - K_R*H',
            'far_norm': '||J_a,far||_(5/2)<=P_R, from original stocks in README',
            'pairing': '|Q_far|<=nu D_p/4+(15/(4nu))P_R^2 R_p^(1/5)',
            'clock': 'choose L0>0 from original data; c_R=3P_R^2/(4nu L0^(4/5)); d_R=4L0 c_R',
            'open_near_target': 'integral_0^T Omega exp(-c_R t)[Q_near-nu D_p/4]<=K_near(u0,nu,H,R)',
            'scope': 'fixed R5 kernel separation; no uniform bound as R tends to zero; J_b remains in Q_near'}


def full_scaling():
    E, I, nu, H, A, F, M, R, CS, cK, cD, lam = s.symbols(
        'E I nu H A F M R CS cK cD lam', positive=True)
    MH = s.sqrt(I+6*nu*E*H)+3*CS**s.Rational(3, 2)*E**s.Rational(1, 4)*H**s.Rational(1, 4)*(E/(2*nu))**s.Rational(3, 4)
    J0 = H*A*F
    Jw = A*(H*M+s.Rational(4, 3)*s.sqrt(10*nu)*H**s.Rational(3, 2)*F)
    Gbar = 2*(s.pi*E+J0**2)
    Wbar = 2*(25*s.pi*MH**2/9+49*Jw**2/9)
    P = cK*R**(-2)*(s.pi*E+2*Gbar)+cD*R**(-3)*s.Rational(14, 5)*s.sqrt(Gbar*Wbar)
    scale = {E: E/lam, I: I/lam**3, H: H/lam**2, A: A*lam**2,
             F: F/s.sqrt(lam), M: M/lam**s.Rational(3, 2), R: R/lam}
    for name, expression, power in (
            ('physical moment', MH, -s.Rational(3, 2)),
            ('prepared norm', J0, -s.Rational(1, 2)),
            ('prepared weighted norm', Jw, -s.Rational(3, 2)),
            ('residual energy', Gbar, -1), ('residual weighted energy', Wbar, -3),
            ('far flux norm', P, 1)):
        zero(s.powdenest(expression.subs(scale, simultaneous=True), force=True)
             -lam**power*expression, 'complete NS scaling of '+name)
    return {'scaling': 'u_lambda= lambda u(lambda x,lambda^2 t), R_lambda=R/lambda',
            'checked': 'M_H,J0,Jw,Gbar,Wbar,P_R transform with powers -3/2,-1/2,-3/2,-1,-3,1',
            'clock': 'c_R H is invariant when the critical starting stock L0 is invariant'}


def quadrature():
    import numpy as np
    from scipy.special import roots_legendre
    chi_profiles = {'positive_parent': z/(1+r*r+z*z)**3,
                    'nodal_parent': (1+r*r+z*z)**(-2)-s.Rational(125, 16)/(4+r*r+z*z)**2}
    profiles = {}
    for name, chi in chi_profiles.items():
        cr, cz = grad(chi)
        v = velocity(chi)
        h = -lap5(chi)
        b = (1+r*r+z*z)**(-3) if name == 'positive_parent' else s.exp(-r*r-z*z)/10
        Gamma_z = v[1]*h+cr*cr-cz*cz
        Hz = 2*cr*cr-cz*cz
        Frz = 2*chi*cr+r*(cr*cr-cz*cz)/2
        Fzz = 2*chi*cz+r*cr*cz
        profiles[name] = s.lambdify((r, z), (b*b, Gamma_z, Hz, Frz, Fzz), 'numpy')
    rows = []
    for n in (48, 96, 192):
        xx, ww = roots_legendre(n)
        cc, wc = xx[None, :], ww[None, :]
        for name, evaluate in profiles.items():
            for radius in (.5, 1., 2.):
                direct = rewritten = omitted = 0.
                for interval in ('transition', 'tail'):
                    if interval == 'transition':
                        rho = (radius*(1.5+xx/2))[:, None]
                        dr = (radius*ww/2)[:, None]
                    else:
                        angle = np.pi*(xx+1)/4
                        rho = (2*radius+np.tan(angle))[:, None]
                        dr = (np.pi*ww/(4*np.cos(angle)**2))[:, None]
                    tt = rho/radius
                    th = 3*(tt-1)**2-2*(tt-1)**3 if interval == 'transition' else np.ones_like(rho)
                    dth = 6*(tt-1)*(2-tt)/radius if interval == 'transition' else np.zeros_like(rho)
                    kr = th/(2*np.pi**3*rho**4)
                    dkr = (dth/rho**4-4*th/rho**5)/(2*np.pi**3)
                    dkr_omitted = -4*th/(2*np.pi**3*rho**5)
                    rr, zz = rho*np.sqrt(1-cc**2), .4+rho*cc
                    bb, gamma, hh, fr, fz = evaluate(rr, zz)
                    normal = -(np.sqrt(1-cc**2)*fr+cc*fz)
                    volume = 2*np.pi**2*rho**4*(1-cc**2)*dr*wc
                    direct += np.sum(volume*kr*(bb-gamma))
                    rewritten += np.sum(volume*(kr*(bb-hh)+dkr*normal))
                    omitted += np.sum(volume*(kr*(bb-hh)+dkr_omitted*normal))
                rows.append({'n': n, 'profile': name, 'R': radius,
                             'direct_far_axial': float(direct), 'stress_far_axial': float(rewritten),
                             'abs_difference': float(abs(direct-rewritten)),
                             'omitting_cutoff_derivative_error': float(abs(direct-omitted))})
    require(all(row['abs_difference'] < 1e-10 for row in rows if row['n'] == 192),
            'independent complete far-flux quadrature agreement')
    require(all(row['omitting_cutoff_derivative_error'] > 1e-7
                for row in rows if row['n'] == 192), 'cutoff derivative is detectably necessary')
    return rows


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quadrature', action='store_true')
    args = parser.parse_args()
    output = {'stress': stress_identity(), 'moment': spatial_moment(),
              'prepared': prepared_multiplier(), 'far_payment': kernel_and_ledger(),
              'scaling': full_scaling()}
    if args.quadrature:
        output['quadrature'] = quadrature()
    print(json.dumps(output, indent=2))
