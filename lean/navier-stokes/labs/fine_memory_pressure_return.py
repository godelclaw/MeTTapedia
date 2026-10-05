#!/usr/bin/env python3
"""Opposite first memory-pressure returns on actual unforced NS histories.

Exact complete initial jets and limiting Fourier currents supplement the
analytic asymptotic/interval argument in README.md. No closed cascade,
quadrature enclosure or arbitrary-history payment is asserted.
"""

import hashlib
import json
from pathlib import Path

import sympy as s
import pressure_history_source as f
import viscous_pressure_regeneration as vd
from rotational_curl_reserve import require, zero


def average_x(field):
    return {k: a for k, a in field.items() if k[0] == 0}


def mean_free(field):
    return {k: a for k, a in field.items() if k != f.ORIGIN}


def fast_pressure(xx, xy, yy):
    source = f.add(f.diff(f.diff(xx, 0), 0),
                   f.scale(2, f.diff(f.diff(xy, 0), 1)),
                   f.diff(f.diff(yy, 1), 1))
    return {k: a/(k[0]*k[0]) for k, a in source.items() if k[0]}


def leading_fields(A, B):
    V, W, _ = vd.datum(1, A, B)
    adv = lambda field: f.add(f.mul(V, f.diff(field, 0)), f.mul(W, f.diff(field, 1)))
    p0 = f.scale(-1, mean_free(average_x(f.mul(W, W))))
    WE = f.scale(-1, f.add(adv(W), f.diff(p0, 1)))
    f.equal(average_x(WE), {}, 'Euler vertical tangent has zero fast mean')
    VE = {k: -f.QQ_I(k[1])/k[0]*a for k, a in WE.items() if k[0]}
    f.equal(f.add(f.diff(VE, 0), f.diff(WE, 1)), {}, 'leading Euler divergence')
    p2 = f.add(f.scale(f.QQ_I(A*A)/4, vd.cosine((2, 0, 0))),
               f.scale(f.QQ_I(B*B)/16, vd.cosine((4, 0, 0))),
               f.scale(f.QQ_I(A*B)/4, f.mul(vd.sine((0, 2, 0)),
                    f.add(f.scale(-9, vd.cosine((1, 0, 0))),
                          f.scale(f.QQ_I(1)/9, vd.cosine((3, 0, 0)))))))
    f.equal(VE, f.scale(-1, f.add(adv(V), f.diff(p2, 0))),
            'horizontal Euler tangent retains the full leading pressure')
    VX, WX, VEX, WEX = (f.diff(field, 0) for field in (V, W, VE, WE))
    Gxx, Gxy, Gyy = f.mul(VX, VX), f.mul(VX, WX), f.mul(WX, WX)
    P1 = fast_pressure(f.scale(2, Gxx), f.scale(2, Gxy), f.scale(2, Gyy))
    Txx = f.add(f.scale(-2, adv(Gxx)), f.scale(4, f.mul(VX, VEX)))
    Txy = f.add(f.scale(-2, adv(Gxy)), f.scale(2, f.mul(VEX, WX)),
                f.scale(2, f.mul(VX, WEX)))
    Tyy = f.add(f.scale(-2, adv(Gyy)), f.scale(4, f.mul(WX, WEX)))
    P2 = fast_pressure(Txx, Txy, Tyy)
    J1 = average_x(f.mul(W, P1))
    J1E = average_x(f.mul(WE, P1))
    J2 = average_x(f.mul(W, P2))
    pE0 = f.scale(-2, mean_free(average_x(f.mul(W, WE))))
    return V, W, VE, WE, P1, P2, J1, J1E, J2, pE0


def rational(value):
    return s.Rational(int(value.numerator), int(value.denominator))


def slow_trig(field, y, q, primitive=False, derivative=False):
    out = 0
    for (m, k, ell), a in field.items():
        require(m == 0 and ell == 0, 'slow-current support')
        if k <= 0:
            continue
        if derivative:
            a *= f.II*k
        multiplier = (1-q**(k*k))/(k*k) if primitive else 1
        out += 2*multiplier*(rational(a.x)*s.cos(k*y)-rational(a.y)*s.sin(k*y))
    return s.expand(out)


def limiting_return(A, B):
    require(A > B > 0, 'stated parent branch')
    _, _, _, _, _, _, J1, J1E, J2, pE0 = leading_fields(A, B)
    y, q = s.symbols('y q', real=True)
    b = -s.Rational(A*A-B*B, 8)*(1-q**4)*s.sin(2*y)
    bE = slow_trig(pE0, y, q, primitive=True, derivative=True)
    currents = [slow_trig(f.diff(field, 1), y, q) for field in (J1, J1E, J2)]
    pieces = [6*bE*currents[0], 6*b*currents[1], 3*b*currents[2]]
    # For 0<q<1, sign(b)=-sign(sin(2y)). Integrate each exact smooth piece.
    integrated = []
    for piece in pieces:
        total = sum((-1 if j % 2 == 0 else 1)*s.integrate(s.expand(piece),
                     (y, j*s.pi/2, (j+1)*s.pi/2)) for j in range(4))/(2*s.pi)
        integrated.append(s.factor(total))
    result = s.factor(sum(integrated))
    if (A, B) == (3, 2):
        expected = (-13851*q**9+19605*q**4+12393*q-18147)/(8*s.pi)
        half = -s.Rational(5505147, 4096)/s.pi
        zero(currents[0]+45*s.sin(y)-s.Rational(243, 2)*s.sin(3*y), 'first source current')
        zero(currents[1]-120*s.cos(2*y)-364*s.cos(4*y), 'receiver current')
        zero(currents[2]+s.Rational(1355, 2)*s.cos(2*y)-s.Rational(2465, 2)*s.cos(4*y),
             'complete second-memory current')
    else:
        require((A, B) == (11, 10), 'second stated family')
        expected = (-187770825*q**9+85033543*q**4+168005475*q-65268193)/(24*s.pi)
        half = s.Rational(4041796445, 4096)/s.pi
    zero(result-expected, 'complete limiting return polynomial')
    zero(result.subs(q, s.Rational(1, 2))-half, 'same-cutoff exact sign')
    require(half < 0 if A == 3 else half > 0, 'strict return sign')
    return {'A': A, 'B': B, 'slow_Euler_pressure': str(slow_trig(pE0, y, q)),
            'slow_beta_Euler': str(bE), 'current_derivatives': [str(v) for v in currents],
            'three_integrated_contributions': [str(v) for v in integrated],
            'limit': str(s.expand(expected)), 'at_q_half': str(half),
            'sign': 'depleting' if A == 3 else 'positive memory work'}


def rescale_fast(field, n):
    require(all(k[0] % n == 0 for k in field), 'all rescaled modes remain integral')
    return {(k[0]//n, k[1], k[2]): a for k, a in field.items()}


def l1_coefficients(field):
    return sum((abs(a.x)+abs(a.y) for a in field.values()), f.ZERO.x)


def complete_jet(n, A, B):
    u = vd.datum(n, A, B)
    p = f.tensor_pressure(f.tensor(u, u))
    f.equal(p, vd.pressure_formula(n, A, B), 'full canonical pressure')
    omega = f.curl(u)
    f.equal(omega[0], {}, 'planar vorticity has no horizontal component')
    f.equal(omega[1], {}, 'planar vorticity has no horizontal component')
    stretching = f.dot(omega, [f.adv(omega, ui) for ui in u])
    f.equal(stretching, {}, 'positive observer work is not planar vortex stretching')
    euler = [f.scale(-1, f.add(f.adv(u, ui), f.diff(p, i))) for i, ui in enumerate(u)]
    f.equal(f.trace(f.jac(euler)), {}, 'full Euler tangent is solenoidal')
    G = [[f.add(*(f.mul(f.diff(u[i], k), f.diff(u[j], k)) for k in range(3)))
          for j in range(3)] for i in range(3)]
    C1 = [[f.scale(2, gij) for gij in row] for row in G]  # nu=1
    GE = [[f.add(*(f.add(f.mul(f.diff(euler[i], k), f.diff(u[j], k)),
                        f.mul(f.diff(u[i], k), f.diff(euler[j], k))) for k in range(3)))
           for j in range(3)] for i in range(3)]
    C2E = [[f.add(f.scale(-1, f.adv(u, C1[i][j])), f.scale(2, GE[i][j]))
            for j in range(3)] for i in range(3)]
    visc = [f.lap(ui) for ui in u]
    GV = [[f.add(*(f.add(f.mul(f.diff(visc[i], k), f.diff(u[j], k)),
                        f.mul(f.diff(u[i], k), f.diff(visc[j], k))) for k in range(3)))
           for j in range(3)] for i in range(3)]
    C2V = [[f.add(f.lap(C1[i][j]), f.scale(2, GV[i][j]))
            for j in range(3)] for i in range(3)]
    p1 = f.tensor_pressure(C1)
    p2E, p2V = f.tensor_pressure(C2E), f.tensor_pressure(C2V)
    require(all(k[1] % 2 for ui in u for k in ui), 'odd velocity')
    require(all(k[1] % 2 == 0 for k in p1), 'even first memory pressure')
    require(all(k[1] % 2 for k in p2E), 'odd nonlinear second memory pressure')
    require(all(k[1] % 2 == 0 for k in p2V), 'even viscous second memory pressure')
    low_coefficient = f.QQ_I((A*A-4*B*B)*n*n-A*A+B*B)/2
    f.equal(average_x(p1), f.scale(low_coefficient, vd.cosine((0, 2, 0))),
            'exact slow first-memory pressure, including its n-squared part')
    f.equal(average_x(euler[1]), {}, 'full vertical Euler mean')
    _, _, VE, WE, P1, P2, *_ = leading_fields(A, B)
    fast = lambda field: {k: a for k, a in field.items() if k[0]}
    differences = [f.add(f.scale(n, rescale_fast(euler[0], n)), f.scale(-1, VE)),
                   f.add(rescale_fast(euler[1], n), f.scale(-1, WE)),
                   f.add(rescale_fast(fast(p1), n), f.scale(-1, P1)),
                   f.add(rescale_fast(fast(p2E), n), f.scale(-1, P2))]
    return {'n': n, 'A': A, 'B': B, 'p_C1_modes': len(p1),
            'p_C2_Euler_modes': len(p2E), 'p_C2_viscous_modes': len(p2V),
            'n_squared_coefficient_errors': [str(n*n*l1_coefficients(v)) for v in differences],
            'error_scope': 'Exact finite jet comparisons; the all-n asymptotic estimate is derived analytically from the fixed-support Fourier multiplier.'}


if __name__ == '__main__':
    result = {
        'limiting_returns': [limiting_return(A, B) for A, B in ((3, 2), (11, 10))],
        'complete_jets': [complete_jet(n, A, B) for A, B in ((3, 2), (11, 10))
                          for n in (2, 7, 16)],
        'physical_setup': 'nu=1, L^2=log(2), u0=n^3 u_n(A,B), C(0)=0; actual unforced NS and its actual stress memory',
        'jet': 'W_mem(0)=W_mem_prime(0)=0; W_mem_second=-3 integral [2(r_prime u+r u_prime).Delta K_L C1+r u.Delta K_L C2]',
        'limit': 'lim_(n->infinity) W_mem_second(0)/(sqrt(2)n^18) is the stated strict-sign coefficient',
        'physical_consequence': 'For sufficiently large finite n, the two families have opposite memory-work signs on actual positive short intervals. Both augmented observations initially decrease.',
        'planar_limit': 'The base histories have zero vortex stretching. Positive W_mem is a pressure-observer contribution, not positive stretching or growth of the full observation.',
        'OPEN': 'Payment of W_mem+F_hat-D_hat/2 over every arbitrary-data history remains open; positive local work does not refute a finite full-datum allowance.',
        'status': 'Exact Fourier and integral checks passed. The asymptotic and actual-history arguments remain analytic, not Lean-certified.',
        'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    print(json.dumps(result, indent=2), flush=True)
