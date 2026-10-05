#!/usr/bin/env python3
"""Old stress-memory absorption for the complete joint NS observation.

Exact algebra and complete Fourier fixtures support the analytic estimates
in README.md. The propagator, multiplier and PDE arguments are not Lean
certificates. The recent-memory and fine-pressure history bound stays open.
"""

import hashlib
import json
from pathlib import Path

import sympy as s
import pressure_history_source as f
import viscous_pressure_regeneration as vd
from rotational_curl_reserve import require, zero


def scalar_checks():
    R = s.Rational
    # Interpolation is with the full six-component norm, not velocity alone.
    zero(R(1, 6)-R(1, 4)/3-R(3, 4)/9, 'L6 interpolation')
    zero(R(1, 4)-R(5, 8)/3-R(3, 8)/9, 'L4 interpolation')
    zero(2*R(5, 8)/3-R(5, 12), 'L4 squared J exponent')
    zero(2*R(3, 8)/3-R(1, 4), 'L4 squared Sobolev exponent')
    zero(R(5, 12)*R(4, 3)-R(5, 9), 'sublinear Young remainder')

    x, y = s.symbols('x y', nonnegative=True)
    zero(x**4-R(4, 3)*y*x**3+y**4/3
         -(x-y)**2*(x*x+R(2, 3)*x*y+y*y/3),
         'three-quarter Young polynomial')
    zero(x**4-4*y**3*x+3*y**4
         -(x-y)**2*(x*x+2*x*y+3*y*y),
         'one-quarter Young polynomial')
    k, J, e = s.symbols('k J epsilon_positive', positive=True)
    opt = (3*k*J**R(1, 4)/(4*e))**4
    zero(k*J**R(1, 4)*opt**R(3, 4)-e*opt
         -27*k**4*J/(256*e**3), 'sharp three-quarter Young coefficient')
    opt = (k*J**R(5, 12)/(4*e))**R(4, 3)
    zero(k*J**R(5, 12)*opt**R(1, 4)-e*opt
         -3*k**R(4, 3)*J**R(5, 9)/(4**R(4, 3)*e**R(1, 3)),
         'sharp one-quarter Young coefficient')
    tangents = []
    for numerator, denominator in ((1, 3), (5, 9), (2, 3)):
        theta = R(numerator, denominator)
        gap = theta*x**denominator+1-theta-x**numerator
        quotient, remainder = s.div(gap, (x-1)**2, x)
        zero(remainder, 'affine majorant has a double contact')
        require(all(c >= 0 for c in s.Poly(quotient, x).all_coeffs()),
                'affine majorant is valid for every nonnegative stock')
        tangents.append({'theta': str(theta), 'gap_factor': str(quotient)})
    zero(1-4*R(1, 16)-R(3, 4), 'four absorption costs leave three quarters')
    zero(R(3, 4)-R(1, 2)-R(1, 4), 'conditional history leaves one quarter')

    t, c = s.symbols('t c', positive=True)
    Y = s.Function('Y')(t)
    zero(s.diff(s.exp(-c*t)*Y, t)
         -s.exp(-c*t)*(s.diff(Y, t)-c*Y), 'fixed integrating factor')
    # A scalar comparison starts at the original datum and telescopes at seams.
    d, Y0 = s.symbols('d Y0', positive=True)
    comparison = s.exp(c*t)*Y0+d*(s.exp(c*t)-1)/c
    zero(s.diff(comparison, t)-c*comparison-d, 'finite affine comparison')
    a, b = s.symbols('a b', nonnegative=True)
    zero(s.exp(-c*a)*s.exp(-c*(b-a))-s.exp(-c*b),
         'inherited clock composes without a new allowance')
    return {
        'old_norms': 'm_infinity=E0*N_delta; m2=E0*N_delta^(1/2); m3=E0*N_delta^(2/3)',
        'interpolation': ['||r||6^3<=J^(1/4)*(a*D+b*J)^(3/4)',
                          '||r||4^2<=J^(5/12)*(a*D+b*J)^(1/4)'],
        'young_coefficients': ['27*k^4/(256*epsilon^3)',
                               '3*k^(4/3)/(4^(4/3)*epsilon^(1/3))'],
        'affine_tangents': tangents,
        'diffusion_remaining': '3/4 before the open recent-source payment; 1/4 after it',
        'clock': 'exp(-c*t), c fixed from original resources, never a future norm',
        'conditional_bound': 'J(T)+(1/4)*integral_0^T D <= exp(c*H)*(J(0)+B_low(0)+d*H+K_recent)'}


def coefficients_and_symbols():
    R = s.Rational
    nu, CR, m3, a, S = s.symbols('nu C_R m3 a S', positive=True)
    s1, s2, s3, b = s.symbols('s1 s2 s3 b', nonnegative=True)
    eps = R(1, 16)
    c0 = 27*s1**4*a**3/(256*eps**3)+s1*b**R(3, 4)
    v1 = 3*CR**2*m3**2/(eps*nu)
    v2 = 3*a**R(1, 3)*(s2**R(4, 3)+s3**R(4, 3))/(4**R(4, 3)*eps**R(1, 3))
    v3 = (s2+s3)*b**R(1, 4)
    c = c0+v1*S**R(-2, 3)/3+5*v2*S**R(-4, 9)/9+2*v3*S**R(-1, 3)/3
    d = 2*v1*S**R(1, 3)/3+4*v2*S**R(5, 9)/9+v3*S**R(2, 3)/3
    zero(c*S+d-(c0*S+v1*S**R(1, 3)+v2*S**R(5, 9)+v3*S**R(2, 3)),
         'combined affine majorant touches the full cost at the prescribed scale')
    x = s.symbols('x', positive=True)
    total = c0*x+v1*x**R(1, 3)+v2*x**R(5, 9)+v3*x**R(2, 3)
    zero(s.diff(total, x).subs(x, S)-c, 'complete cost tangent has coefficient c')
    # Full Frobenius symbol norms; rank one, so these are operator norms.
    xi = s.symbols('xi0:3', real=True)
    norm2 = sum(v*v for v in xi)
    rr = sum(xi[i]**2*xi[j]**2 for i in range(3) for j in range(3))
    zero(rr-norm2**2, 'full contracted pressure symbol')
    kk = sum(xi[j]**2*xi[i]**2*xi[l]**2
             for i in range(3) for j in range(3) for l in range(3))
    zero(kk-norm2**3, 'complete K symbol norm before its denominator')
    zero(norm2*kk-norm2**4, 'gradient K and K div have the same unit bound')
    return {'epsilon': str(eps), 'c0': str(c0), 'v1': str(v1),
            'v2': str(v2), 'v3': str(v3), 'c': str(c), 'd': str(d),
            'symbols': 'L2 symbol norms: R norm 1; K norm h/|xi|; grad K and K div norm h, 0<=h<=min(1,L^2|xi|^2).'}


def matrix_add(a, b):
    return [[f.add(a[i][j], b[i][j]) for j in range(3)] for i in range(3)]


def average(field):
    return field.get(f.ORIGIN, f.ZERO)


def pairing(a, b):
    return average(f.dot(a, b))


def tensor_pairing(a, b):
    return sum((pairing(v, w) for v, w in zip(a, b)), f.ZERO)


def high(field):
    # L^2=log(2), so the heat factors at integer modes are exact rationals.
    return {k: a*(1-f.QQ_I(1)/2**sum(v*v for v in k))
            for k, a in field.items() if k != f.ORIGIN}


def primitive(tensor):
    return f.green(high(f.tensor_pressure(tensor)))


def K(tensor):
    return f.grad(primitive(tensor))


def Kstar(vector):
    minus_div = f.scale(-1, f.trace(f.jac(vector)))
    return f.hess(f.green(f.green(high(minus_div))))


def adv_tensor(u, tensor):
    return [[f.adv(u, v) for v in row] for row in tensor]


def commutator(u, tensor):
    beta, transported = K(tensor), K(adv_tensor(u, tensor))
    return [f.add(f.adv(u, beta[i]), f.scale(-1, transported[i])) for i in range(3)]


def memory_jets(u):
    p = f.tensor_pressure(f.tensor(u, u))
    ut = [f.add(f.lap(ui), f.scale(-1, f.adv(u, ui)), f.scale(-1, f.diff(p, i)))
          for i, ui in enumerate(u)]  # nu=1, full unforced NS tangent
    C1 = [[f.scale(2, f.add(*(f.mul(f.diff(u[i], k), f.diff(u[j], k))
                                  for k in range(3)))) for j in range(3)] for i in range(3)]
    Gt = [[f.add(*(f.add(f.mul(f.diff(ut[i], k), f.diff(u[j], k)),
                        f.mul(f.diff(u[i], k), f.diff(ut[j], k)))
                   for k in range(3))) for j in range(3)] for i in range(3)]
    C2 = [[f.add(f.lap(C1[i][j]), f.scale(-1, f.adv(u, C1[i][j])),
                 f.scale(2, Gt[i][j])) for j in range(3)] for i in range(3)]
    f.equal(f.trace(f.jac(ut)), {}, 'actual NS tangent remains solenoidal')
    require(average(f.trace(C1)) == -2*pairing(u, ut),
            'initial source mass equals actual kinetic-energy loss')
    return p, C1, C2


def fixture(u, name):
    f.equal(f.trace(f.jac(u)), {}, 'actual initial velocity is solenoidal')
    p, C1, C2 = memory_jets(u)
    source = [[f.scale(-1, f.add(f.mul(u[i], f.diff(p, j)),
                               f.mul(u[j], f.diff(p, i))))
               for j in range(3)] for i in range(3)]
    source_beta = K(source)
    checks = []
    for order, C in ((1, C1), (2, C2)):
        M = matrix_add(f.tensor(u, u), C)
        beta, comm = K(M), commutator(u, M)
        q = primitive(M)
        qcomm = f.add(f.adv(u, q), f.scale(-1, primitive(adv_tensor(u, M))))
        for i in range(3):
            deformation = f.add(*(f.mul(f.diff(u[j], i), beta[j]) for j in range(3)))
            f.equal(comm[i], f.add(f.diff(qcomm, i), f.scale(-1, deformation)),
                    'compact commutator retains the full receiver deformation')
        # The adjoint identity holds for every receiver. This exact polynomial
        # receiver exercises nonzero work; it is not the nonlinear entropy B.
        B = [f.add(comm[i], source_beta[i]) for i in range(3)]
        require(pairing(B, B).x > 0, 'nonzero complete receiver fixture')
        Htensor = Kstar(B)
        require(pairing(B, K(M)) == tensor_pairing(Htensor, M),
                'complete tensor-to-vector adjoint')
        weak_comm = pairing(B, [f.adv(u, v) for v in beta])
        weak_comm += tensor_pairing(adv_tensor(u, Htensor), M)
        require(pairing(B, comm) == weak_comm, 'joint weak transport identity')
        weak_pressure = 2*average(f.mul(p, f.trace(f.jac(f.matvec(Htensor, u)))))
        require(pairing(B, source_beta) == weak_pressure, 'canonical pressure weak source')
        old_comm = commutator(u, C)
        base_comm = commutator(u, f.tensor(u, u))
        for i in range(3):
            f.equal(comm[i], f.add(old_comm[i], base_comm[i]), 'complete linear memory split')
        # Move the transport derivative to u*C, with no gradient estimate on C.
        divergence_flux = [[f.add(*(f.diff(f.mul(u[k], C[i][j]), k)
                                    for k in range(3))) for j in range(3)] for i in range(3)]
        f.same_matrices(divergence_flux, adv_tensor(u, C), 'incompressible memory flux')
        KC, pressure_C = K(C), high(f.tensor_pressure(C))
        for i in range(3):
            f.equal(f.scale(-1, f.lap(KC[i])), f.diff(pressure_C, i),
                    'fine memory work keeps the full pressure multiplier')
        checks.append({'memory_jet': order, 'memory_pressure_modes': len(pressure_C),
                       'commutator_modes': sum(map(len, comm)),
                       'nonzero_joint_receiver': True})
    return {'name': name, 'checks': checks,
            'scope': 'Exact initial memory jets and unrestricted weak identities, not a finite-time truncation or entropy quadrature.'}


if __name__ == '__main__':
    result = {
        'scalar_checks': scalar_checks(),
        'coefficients_and_symbols': coefficients_and_symbols(),
        'physical_jet_fixtures': [fixture(vd.datum(n, A, B), f'A={A},B={B},n={n}')
                                 for A, B in ((3, 2), (11, 10)) for n in (2, 3)]
                               + [fixture(f.fixture(), 'genuine three-dimensional datum')],
        'analytic_result': 'For any fixed age delta>0, old-memory fine work, its full transport commutator, and coarse canonical-pressure generation are bounded by D/4+c*J+d on every available smooth unforced prefix.',
        'constants': 'c,d depend only on E0,nu,L,delta, a prescribed positive stock scale and domain constants.',
        'OPEN': 'A same-original-datum finite bound for the weighted signed recent-memory/fine-pressure remainder; old parents still influence the current velocity and newly generated stress.',
        'status': 'Exact checks passed; actual propagator estimates, PDE inequalities and conditional continuation are analytic, not Lean-certified.',
        'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    print(json.dumps(result, indent=2), flush=True)
