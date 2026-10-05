#!/usr/bin/env python3
"""Optimal cubic gradient correction on actual periodic NS initial data.

Complete Fourier coefficients check the physical nonlinear response and
explicit Wiener-algebra remainder constants. Convex optimality and the
positive-time NS consequence are proved analytically in README.md.
There is no truncated evolution or arbitrary-history regularity claim.
"""

import hashlib
import json
from pathlib import Path

import sympy as s
import pressure_history_source as f
import recent_pressure_reconstruction as wh
import aged_joint_memory_payment as am
import viscous_pressure_regeneration as vd
from rotational_curl_reserve import require, zero

Q = f.QQ_I


def cosine(k):
    return {k: Q(1)/2, tuple(-a for a in k): Q(1)/2}


def adv(u, v):
    return [f.adv(u, a) for a in v]


def scalar_vector(a, v):
    return [f.mul(a, b) for b in v]


def cross(u, v):
    return [f.add(f.mul(u[(i+1) % 3], v[(i+2) % 3]),
                  f.scale(-1, f.mul(u[(i+2) % 3], v[(i+1) % 3])))
            for i in range(3)]


def action(v, diagonal, half_shift):
    return [f.clean({tuple(diagonal[j]*k[j] for j in range(3)):
                     diagonal[i]*(-1 if half_shift and k[2] % 2 else 1)*a
                     for k, a in v[i].items()}) for i in range(3)]


def wiener(v):
    """An exact majorant for the weighted componentwise Fourier l1 norm."""
    return sum((1+sum(abs(a) for a in k))*(abs(c.x)+abs(c.y))
               for field in v for k, c in field.items())


def datum(sign):
    sx, sy, sz = [vd.sine(tuple(int(i == j) for i in range(3))) for j in range(3)]
    cx, cy, cz = [cosine(tuple(int(i == j) for i in range(3))) for j in range(3)]
    base = [cz, sz, {}]
    horizontal = f.mul(sx, sy)
    perturbation = [f.scale(2, f.mul(horizontal, sz)),
                    f.scale(2, f.mul(f.mul(cx, cy), sz)),
                    f.scale(2*sign, horizontal)]
    return base, perturbation


def expansion(sign):
    base, G = datum(sign)
    h, j = f.dot(base, G), f.dot(G, G)
    w1 = wh.addv(G, wh.scalev(-Q(1)/2, scalar_vector(h, base)))
    w2 = wh.addv(scalar_vector(f.add(f.scale(-Q(1)/4, j),
                                    f.scale(Q(5)/8, f.mul(h, h))), base),
                 wh.scalev(-Q(1)/2, scalar_vector(h, G)))
    ws = [base, w1, w2]
    us = [wh.project(w) for w in ws]
    rs = [{f.ORIGIN: Q(1)}, f.scale(Q(1)/2, h),
          f.add(f.scale(Q(1)/4, j), f.scale(-Q(3)/8, f.mul(h, h)))]
    dual = [base, G, [{}, {}, {}]]
    for n in range(3):
        wh.same_vectors(wh.addv(*(scalar_vector(rs[a], ws[n-a]) for a in range(n+1))),
                        dual[n], ('optimality flux |w|w=F', sign, n))
        f.equal(f.trace(f.jac(us[n])), {}, ('physical coefficient is solenoidal', sign, n))
        wh.same_vectors(f.curl(ws[n]), f.curl(us[n]), ('physical curl is unchanged', sign, n))
        require(all(a.get(f.ORIGIN, f.ZERO) == f.ZERO for a in ws[n]),
                'all displayed coefficients have zero mean')
    for v in (base, G):
        f.equal(f.trace(f.jac(v)), {}, 'the exact optimizing dual field is solenoidal')
        for diagonal, half_shift in (((1, -1, -1), False), ((-1, 1, -1), True)):
            wh.same_vectors(v, action(v, diagonal, half_shift),
                            'physical rotation symmetry forces the exact datum mean to zero')

    nonlinear, pressures = [], []
    P, D, gauge_work = [], [], []
    for n in range(3):
        conv = wh.addv(*(adv(us[a], us[n-a]) for a in range(n+1)))
        stress = [[f.add(*(f.mul(us[a][i], us[n-a][j]) for a in range(n+1)))
                   for j in range(3)] for i in range(3)]
        pressure = f.tensor_pressure(stress)
        rhs = wh.scalev(-1, wh.addv(conv, f.grad(pressure)))
        wh.same_vectors(rhs, wh.scalev(-1, wh.project(conv)),
                        'canonical pressure and full projected NS tangent agree')
        f.equal(f.trace(f.jac(rhs)), {}, 'every generated NS output is retained')
        pressures.append(pressure)
        nonlinear.append(rhs)
        P.append(am.pairing(base, rhs)+(am.pairing(G, nonlinear[n-1]) if n else f.ZERO))
        D.append(-am.pairing(base, [f.lap(a) for a in us[n]])
                 -(am.pairing(G, [f.lap(a) for a in us[n-1]]) if n else f.ZERO))
        transpose_work = f.ZERO
        triple_work = f.ZERO
        for a in range(min(n, 1)+1):
            for b in range(n-a+1):
                c = n-a-b
                Ut = list(map(list, zip(*f.jac(us[b]))))
                transpose_work -= am.pairing(dual[a], f.matvec(Ut, ws[c]))
                triple_work += am.pairing(dual[a], cross(us[b], f.curl(us[c])))
        require(transpose_work == P[n] and triple_work == P[n],
                'optimal gauge reaction equals the complete physical geometric feedback')
        gauge_work.append(transpose_work)
    require(P == [f.ZERO, f.ZERO, Q(sign)/12], 'opposite exact leading nonlinear feedback')
    require(D == [Q(1), f.ZERO, Q(61)/16], 'same leading viscous cost')
    # The gradient correction is genuinely nonzero, not a relabelled velocity.
    correction = wh.addv(w1, wh.scalev(-1, us[1]))
    correction_square = am.pairing(correction, correction)
    require(correction_square.x > 0 and correction_square.y == 0, 'nontrivial optimal gradient')
    for nu in (Q(1), Q(2)/7):
        for n in range(3):
            rhs = wh.addv(nonlinear[n], [f.scale(nu, f.lap(a)) for a in us[n]])
            covector = wh.addv([f.scale(nu, f.lap(a)) for a in ws[n]],
                              wh.scalev(-1, wh.addv(*(adv(us[a], ws[n-a]) for a in range(n+1)))),
                              wh.scalev(-1, wh.addv(*(f.matvec(list(map(list, zip(*f.jac(us[a])))), ws[n-a])
                                                     for a in range(n+1)))))
            wh.same_vectors(wh.project(covector), rhs,
                            'the controlled optimal lift projects to the actual NS tangent')
            expected = P[n]-nu*D[n]
            rate = am.pairing(base, rhs)
            if n:
                previous = wh.addv(nonlinear[n-1], [f.scale(nu, f.lap(a)) for a in us[n-1]])
                rate += am.pairing(G, previous)
            require(rate == expected, 'actual positive-viscosity tangent retains diffusion')
    return {'sign': sign, 'nonlinear_coefficients': list(map(str, P)),
            'diffusion_coefficients': list(map(str, D)),
            'gradient_first_coefficient_norm_squared': str(correction_square),
            'pressure_coefficient_modes': list(map(len, pressures)),
            'scope': 'Expansion of the exact smooth datum and its full NS tangent; not a time-truncated NS model.'}, (base, G, h, j, w1, us[1])


def remainder(data):
    base, G, h, j, w1, u1 = data
    a, g, b, c = wiener(base), wiener(G), wiener([h]), wiener([j])
    eps0 = 1/(8*(1+b+c+g))
    Cw = a*c/4+g*b/2+eps0*g*c/4+2*(a+eps0*g)*(2*b+eps0*c)**2
    Cu = 3*Cw
    v1 = wiener(u1)
    V = v1+eps0*Cu
    C3 = a*Cu*(V+v1)+2*g*a*Cu+g*V*V
    eps = Q(1).x/(2**28)
    require(Cw < 5700 and Cu < 17100 and v1 < 27 and V < 61,
            'simple explicit remainder majorants')
    require(C3 < 10**7 and Q(10**7).x*eps <= Q(1).x/24,
            'integer remainder constant also certifies the chosen parameter')
    require(eps <= eps0 and eps0*(2*b+eps0*c) < Q(1).x/2,
            'the complete binomial series converges in the weighted Wiener algebra')
    require(C3*eps <= Q(1).x/24, 'full nonlinear remainder is less than half the leading term')
    eta = eps*(wiener(w1)+eps0*Cw)
    require(wiener(w1)+eps0*Cw < 60, 'simple complete C1 remainder bound')
    require(eta <= Q(1).x/10, 'the complete optimizing field is C1-close to the unit shear')
    zero(s.Rational(11, 10)**3+s.Rational(21, 100)**2/s.Rational(9, 10)-s.Rational(69, 50),
         'full diffusion bound including the norm-gradient term')
    require(Q(69).x/50 < 2, 'diffusion is below the chosen uniform cost')
    amplitude_over_nu = 96/(eps*eps)
    require(amplitude_over_nu*eps*eps/24-2 == 2,
            'fixed original amplitude beats viscosity with a positive margin')
    return {'W_base': str(a), 'W_G': str(g), 'W_h': str(b), 'W_j': str(c),
            'epsilon0': str(eps0), 'C_w': str(Cw), 'C_u': str(Cu), 'W_u1': str(v1),
            'C3': str(C3), 'epsilon': str(eps), 'amplitude_over_nu': str(amplitude_over_nu),
            'rigorous_bounds': '|P_sign-sign epsilon^2/12|<=C3 epsilon^3; D<=69/50<2',
            'physical_growth': 'For A=96nu/epsilon^2 and plus datum, J(u(t))-J(u0)>=nu A^3 t for all sufficiently small positive t.',
            'scope': 'Wiener-algebra and local-PDE remainder proofs are analytic; displayed constants and exact Fourier coefficients are checked.'}


def shear_calibration():
    z = s.symbols('z', real=True)
    moment = s.integrate(s.sin(z)**3, (z, 0, s.pi))/(3*s.pi)
    diffusion = 2*s.integrate(s.sin(z)*s.cos(z)**2, (z, 0, s.pi))/s.pi
    zero(moment-4/(9*s.pi), 'the exact cubic quotient of the pressure-free shear')
    zero(diffusion-3*moment, 'optimal gradient removal leaves exactly physical shear diffusion')
    return 'For u=A exp(-nu t)sin(z)e1, w=u is optimal and J=4A^3 exp(-3nu t)/(9pi), J_prime=-nu D. The canonical covector overcharge is absent.'


def control_hessian():
    w = s.Matrix(s.symbols('w0:3', real=True))
    v = s.Matrix(s.symbols('v0:3', real=True))
    r = s.sqrt(w.dot(w))
    M = r*s.eye(3)+w*w.T/r
    zero((r*w).jacobian(w)-M, 'exact elliptic coefficient for preserving optimality')
    zero((v.T*M*v)[0]-r*v.dot(v)-w.dot(v)**2/r,
         'the gauge equation is positive definite wherever the optimizer is nonzero')
    return 'For r=|w|>0, M=r I+w tensor w/r; C=nu Delta w-u.grad w-U^T w. The optimal gauge satisfies w_t=C+grad eta, div(M grad eta)=-div(M C). This control is a gradient, not a force on the projected fluid.'


def invariance():
    base, plus = datum(1)
    _, minus = datum(-1)
    f.equal(f.dot(base, plus), f.dot(base, minus), 'same linear speed perturbation')
    f.equal(f.dot(plus, plus), f.dot(minus, minus), 'same exact quadratic speed perturbation')
    wh.same_vectors(minus, [plus[0], plus[1], f.scale(-1, plus[2])],
                    'only the vertical dual component changes sign')
    w = s.Matrix(s.symbols('w0:3', real=True))
    dw = s.Matrix(s.symbols('d0:3', real=True))
    reflection = s.diag(1, 1, -1)
    zero((reflection*w).dot(reflection*w)-w.dot(w), 'pointwise optimal stock is identical')
    zero((reflection*dw).dot(reflection*dw)-dw.dot(dw), 'gradient-square diffusion is identical')
    zero((reflection*w).dot(reflection*dw)-w.dot(dw), 'radial diffusion is identical')
    return 'The two exact optimized fields have identical pointwise magnitudes and identical complete cubic diffusion, while their nonlinear responses have opposite signs.'


if __name__ == '__main__':
    fixtures = [expansion(sign) for sign in (1, -1)]
    result = {'datum': 'F0=(cos z,sin z,0); G_sign=(2sin x sin y sin z,2cos x cos y sin z,2 sign sin x sin y); F=F0+epsilon G; w=F/(F.F)^(1/4); u=Pi w.',
              'candidate': 'J(u)=inf_{Pi w=u} integral |w|^3/3. The exact optimizer satisfies |w|w=F and div F=0.',
              'shear_calibration': shear_calibration(),
              'compatible_control': control_hessian(),
              'pair_invariance': invariance(), 'fixtures': [v[0] for v in fixtures],
              'remainders': [remainder(v[1]) for v in fixtures],
              'status': 'Exact checks passed. Convex minimization, full analytic remainders and actual positive-time histories are not Lean-certified.',
              'limitation': 'Refutes nonincrease of the optimized instantaneous cubic stock, including all gradient policies starting at its minimum. Does not refute a finite full-datum history allowance or global regularity.',
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    print(json.dumps(result, indent=2), flush=True)
