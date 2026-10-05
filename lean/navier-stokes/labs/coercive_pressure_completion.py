#!/usr/bin/env python3
"""Convex pressure-cubic completion and its full unforced NS calibration.

Every Fourier output is retained. The continuum history balance, norm
inequalities and local-time consequence are analytic in README.md, not
Lean certificates. The physical test uses a periodic velocity gradient;
it is not substituted for a non-gradient created-history tensor.
"""

import hashlib
import json
from pathlib import Path

import sympy as s
import pressure_history_source as f
import signed_viscous_pressure as sp

Q = f.QQ_I


def require(test, label):
    if not test:
        raise ArithmeticError(label)


def zero(expr, label):
    value = s.factor(s.together(expr))
    if value != 0:
        raise ArithmeticError((label, value))


def traceless(prefix):
    x = s.symbols(prefix+'0:8', real=True)
    return s.Matrix([[x[0], x[1], x[2]], [x[3], x[4], x[5]],
                     [x[6], x[7], -x[0]-x[4]]])


def pairing(A, B):
    return s.trace(A.T*B)


def algebra():
    J, H = traceless('j'), traceless('h')
    k, theta, e = s.symbols('k theta e', real=True)
    r2 = pairing(J, J)

    def phi(A):
        n = pairing(A, A)
        return k*k*n+n*n-theta*k*s.trace(A**3)

    grad = (2*k*k+4*r2)*pairing(J, H)-3*theta*k*s.trace(J*J*H)
    hess = ((2*k*k+4*r2)*pairing(H, H)+8*pairing(J, H)**2
            -6*theta*k*s.trace(J*H*H))
    zero(s.diff(phi(J+e*H), e).subs(e, 0)-grad,
         'complete first variation for arbitrary trace-free directions')
    zero(s.diff(phi(J+e*H), e, 2).subs(e, 0)-hess,
         'complete convex diffusion Hessian')
    q = s.trace(J*J)
    devJ2 = J*J-q*s.eye(3)/3
    zero(3*s.trace(J*J*devJ2)-q*q/2,
         'cubic correction retains its positive deviatoric self-reaction')
    zero((2*k*k+4*r2)*r2-3*theta*k*s.trace(J**3)
         -(2*k*k*r2+4*r2*r2-3*theta*k*s.trace(J**3)),
         'full aging derivative')

    # Norm inequalities |tr J^3| <= |J|^3 and
    # |tr(J H^2)| <= |J||H|^2 are proved analytically by Cauchy--Schwarz.
    r = s.symbols('r', nonnegative=True)
    zero(k*k*r*r+r**4-k*r**3/2-s.Rational(3, 4)*(k*k*r*r+r**4)
         -r*r*(k-r)**2/4, 'coercivity at the worst theta=1/2')
    zero(2*k*k+4*r*r-3*k*r-(k*k+r*r)
         -((k-s.Rational(3, 2)*r)**2+s.Rational(3, 4)*r*r),
         'uniform positive Hessian lower bound')
    zero(2*k*k*r*r+4*r**4-s.Rational(3, 2)*k*r**3
         -(s.Rational(5, 4)*k*k*r*r+s.Rational(13, 4)*r**4)
         -s.Rational(3, 4)*r*r*(k-r)**2, 'positive window-aging lower bound')
    return {
        'Phi': 'k^2 |J|^2+|J|^4-theta*k*tr(J^3)',
        'parameters': 'k>0 and 0<=theta<=1/2, fixed from the original datum',
        'coercivity': '3/4 (k^2 |J|^2+|J|^4) <= Phi <= 5/4 (k^2 |J|^2+|J|^4)',
        'diffusion': 'Hess Phi(J)[H,H] >= (k^2+|J|^2)|H|^2',
        'aging': 'grad Phi(J):J >= 5k^2 |J|^2/4+13|J|^4/4',
        'self_reaction': '-(2k^2+4|J|^2) J:J^2+(theta*k/2)(tr J^2)^2',
        'pressure': '-(2k^2+4|J|^2) J:A+3theta*k*tr(J^2 A)',
        'inherited': '(2k^2+4|J|^2) J:K-3theta*k*tr(J^2 K)',
        'K': '-dev(JM+MJ+M^2)+(Q_delta-M)/delta',
    }


def mean(a):
    value = a.get(f.ORIGIN, f.ZERO)
    require(value.y == 0, 'real spatial integral')
    return value.x


def pair(A, B):
    return f.add(*(f.mul(A[i][j], B[i][j]) for i in range(3) for j in range(3)))


def history_exponents():
    # Exact interpolation powers, expressed using squared/quartic norms.
    rows = [(3, 2, [(2, s.Rational(1, 3)), (4, s.Rational(1, 3))]),
            (3, 1, [(2, s.Rational(1, 6)), (4, s.Rational(1, 6))]),
            (6, 4, [(4, s.Rational(1, 2)), (12, s.Rational(1, 2))]),
            (9, 3, [(4, s.Rational(1, 8)), (12, s.Rational(5, 8))]),
            (s.Rational(9, 2), 3, [(4, s.Rational(5, 8)), (12, s.Rational(1, 8))])]
    for target, power, terms in rows:
        # L12 is bounded through its fourth power, not its twelfth power.
        norm_power = lambda p: 2 if p == 2 else 4
        zero(sum(norm_power(p)*a for p, a in terms)-power, 'interpolation homogeneity')
        zero(sum(norm_power(p)*a/p for p, a in terms)-s.Rational(power)/target,
             'interpolation integrability')
    for p, a_power, eps_power in [(s.Rational(1, 2), 2, 1),
                                  (s.Rational(5, 8), s.Rational(8, 3), s.Rational(5, 3)),
                                  (s.Rational(1, 8), s.Rational(8, 7), s.Rational(1, 7))]:
        zero(a_power*(1-p)-1, 'Young source power')
        zero(eps_power*(1-p)-p, 'Young absorption power')
    zero(3*s.Rational(1, 6)-s.Rational(1, 2), 'three history absorptions spend half diffusion')
    zero(1-s.Rational(8, 7)/2-s.Rational(3, 7), 'endpoint time Holder power')
    return {
        'D4': 'integral |J|^2 |grad J|^2',
        'K3': 'integral ||Q_delta||3^2 <= N^2 A_E/sqrt(nu delta)',
        'history_payment': '|integral dPhi(J)[K]| <= nu D4/2+a(t)(1+R)',
        'coefficient': 'integral a <= explicit original-data Astar in README.md',
        'remaining': 'signed self-reaction plus weighted pressure, with aging and diffusion retained',
    }


def physical():
    # This is the negative of an existing resonant five-mode datum, with
    # all conjugate modes. The resonant child removes the odd-moment symmetry.
    u = [f.scale(-1, a) for a in sp.interacting_datum()]
    B = f.jac(u)
    f.equal(f.trace(B), {}, 'actual divergence-free periodic datum')
    require(all(f.ORIGIN not in a for a in u), 'zero mean')
    B2 = f.matmul(B, B)
    q = f.trace(B2)
    p = f.green(q)
    P = f.hess(p)
    f.equal(p, f.tensor_pressure(f.tensor(u, u)), 'complete canonical pressure')
    r2 = pair(B, B)
    derivatives = [[[f.diff(B[i][j], k) for j in range(3)] for i in range(3)]
                   for k in range(3)]
    c2 = -2*mean(pair(B, B2))
    c4self = -4*mean(f.mul(r2, pair(B, B2)))
    c4pressure = -4*mean(f.mul(r2, pair(B, P)))
    c4 = c4self+c4pressure
    d2 = 2*sum(mean(pair(H, H)) for H in derivatives)
    d4 = 4*sum(mean(f.add(f.mul(r2, pair(H, H)),
                         f.scale(2, f.mul(pair(B, H), pair(B, H))))) for H in derivatives)
    expected = {'C2': Q(768)/65, 'C4_self': Q(162790222016)/75150075,
                'C4_pressure': -Q(314203808)/20495475, 'C4': Q(96982884832)/45090045,
                'D2': Q(206084096)/1156155, 'D4': Q(21137811378269312)/1336694384025}
    values = dict(C2=c2, C4_self=c4self, C4_pressure=c4pressure, C4=c4, D2=d2, D4=d4)
    require(all(Q(value) == expected[key] for key, value in values.items()),
            'exact full nonlinear and viscous coefficients')
    require(c2 > 0 and c4 > 0 and c4pressure < 0 and d2 > 0 and d4 > 0,
            'self-amplification wins despite helpful pressure and viscosity')
    require(mean(pair(B, P)) == 0, 'full-gradient quadratic pressure cancellation')
    require(mean(f.trace(f.matmul(B2, B))) == 0, 'Betchov null integral')
    require(sum(mean(f.trace(f.matmul(B, f.matmul(H, H)))) for H in derivatives) == 0,
            'integrated cubic diffusion correction also vanishes')
    q2 = mean(f.mul(q, q))
    A = [[f.add(P[i][j], f.scale(Q(1)/3, q) if i == j else {})
          for j in range(3)] for i in range(3)]
    joint = 4*mean(f.trace(f.matmul(B2, A)))
    require(Q(joint) == -Q(2)*Q(q2)/3 and joint < 0,
            'favorable classical joint pressure sign is retained')

    # Independent full Eulerian tangents check the integrated generator,
    # including transport, at two positive viscosities and their chosen amplitudes.
    for nu in (Q(1), Q(2)/7):
        amplitude = 16*nu
        U = [f.scale(amplitude, a) for a in u]
        G = f.jac(U)
        pressure = f.tensor_pressure(f.tensor(U, U))
        Ut = [f.add(f.scale(nu, f.lap(U[i])), f.scale(-1, f.adv(U, U[i])),
                    f.scale(-1, f.diff(pressure, i))) for i in range(3)]
        Gt = f.jac(Ut)
        zrate = 2*mean(pair(G, Gt))
        wrate = 4*mean(f.mul(pair(G, G), pair(G, Gt)))
        require(Q(zrate) == amplitude**2*(amplitude*Q(c2)-nu*Q(d2)),
                'actual complete quadratic rate')
        require(Q(wrate) == amplitude**4*(amplitude*Q(c4)-nu*Q(d4)),
                'actual complete quartic rate')
        require(zrate > 0 and wrate > 0, 'simultaneous actual positive rates')
    margins = (16*c2-d2, 16*c4-d4)
    require(all(m > 0 for m in margins), 'one amplitude works for every reserve parameter')
    return {
        'datum': '-signed_viscous_pressure.interacting_datum()',
        'coefficients': {key: str(value) for key, value in values.items()},
        'q_square': str(q2), 'classical_joint_pressure': str(joint),
        'amplitude': 'a=16nu for every fixed nu>0',
        'positive_margins': [str(m) for m in margins],
        'complete_rate': 'k^2 a^2(a C2-nu D2)+a^4(a C4-nu D4)>0 for every k>0',
        'theta': 'the integrated trace-cube correction vanishes for the full gradient at every time',
        'interval_scope': 'analytic common positive interval for both moments, hence every k and theta',
        'not_refuted': 'a finite full-datum allowance or a genuinely history-dependent reserve',
    }


if __name__ == '__main__':
    report = {'algebra': algebra(), 'history_exponents': history_exponents(), 'physical': physical(),
              'certification': 'exact algebra and full NS tangents; continuum claims analytic, not Lean-certified',
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    print(json.dumps(report, indent=2, sort_keys=True))
