#!/usr/bin/env python3
"""Directional cubic renewal in complete original NS histories.

The normalized torus has period 2*pi. Exact Fourier jets retain all
outputs, the canonical pressure, the original two-index tensor, actual
curl and an independently evolved passive cubic label. Continuous
stochastic identification and fixed-datum short-time realization are
analytic, not certified by this checker. No arbitrary-history allowance,
uniform Taylor window or singularity is claimed.
"""

import json
import math
from fractions import Fraction

import sympy as s
import pressure_history_source as f
import pressure_memory_diffusion as pm
import joint_receiver_tensor as jt
from cyclic_pressure_history import velocity_time_jets
from joint_source_history import seed
from signed_viscous_pressure import interacting_datum


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def cubic(A, w):
    return f.dot(w, f.matvec(A, w))


def cubic_jet(As, ws, n):
    return f.add(*(f.scale(math.comb(n, i)*math.comb(n-i, j),
                          f.dot(ws[i], f.matvec(As[j], ws[n-i-j])))
                   for i in range(n+1) for j in range(n-i+1)))


def mixed_diffusion(A, w):
    terms = []
    for k in range(3):
        dw = [f.diff(q, k) for q in w]
        dA = pm.matrix_diff(A, k)
        terms += [cubic(A, dw), f.dot(dw, f.matvec(dA, w)),
                  f.dot(w, f.matvec(dA, dw))]
    return f.add(*terms)


def mixed_diffusion_jet(As, ws, n):
    terms = []
    for k in range(3):
        dws = [[f.diff(q, k) for q in w] for w in ws]
        dAs = [pm.matrix_diff(A, k) for A in As]
        for i in range(n+1):
            for j in range(n-i+1):
                ell = n-i-j
                coefficient = math.comb(n, i)*math.comb(n-i, j)
                terms.append(f.scale(coefficient, f.add(
                    f.dot(dws[i], f.matvec(As[j], dws[ell])),
                    f.dot(dws[i], f.matvec(dAs[j], ws[ell])),
                    f.dot(ws[i], f.matvec(dAs[j], dws[ell])))))
    return f.add(*terms)


def check_history(initial, viscosity, order, name):
    nu = f.QQ_I(viscosity)
    us, pressures = velocity_time_jets(initial, viscosity, order)
    Bs, ws = list(map(f.jac, us)), list(map(f.curl, us))
    As = [Bs[0]]
    for n in range(order):
        As.append(jt.add(jt.scale(nu, [[f.lap(q) for q in row] for row in As[n]]), *(
            jt.scale(-math.comb(n, r), jt.add(pm.matrix_adv(us[r], As[n-r]),
                jt.multiply(pm.transpose(Bs[r]), As[n-r]),
                jt.multiply(As[n-r], Bs[r]))) for r in range(n+1))))
    Es = [jt.subtract(A, B) for A, B in zip(As, Bs)]
    for n, (A, E, w) in enumerate(zip(As, Es, ws)):
        jt.equal(E, pm.transpose(E), ('actual symmetric compatibility', name, n))
        curl_A = [f.add(A[2][1], f.scale(-1, A[1][2])),
                  f.add(A[0][2], f.scale(-1, A[2][0])),
                  f.add(A[1][0], f.scale(-1, A[0][1]))]
        for i in range(3):
            f.equal(curl_A[i], w[i], ('literal physical curl', name, n, i))
    Hs = [cubic_jet(As, ws, n) for n in range(order+1)]
    hs = [Hs[0]]
    for n in range(order):
        hs.append(f.add(f.scale(nu, f.lap(hs[n])), f.scale(-1, f.add(*(
            f.scale(math.comb(n, r), f.adv(us[r], hs[n-r])) for r in range(n+1))))))
    chis = [f.add(h, f.scale(-1, H)) for h, H in zip(hs, Hs)]
    defects = [cubic_jet(Es, ws, n) for n in range(order+1)]
    stretching = [cubic_jet(Bs, ws, n) for n in range(order+1)]
    for n in range(order+1):
        f.equal(stretching[n], f.add(hs[n], f.scale(-1, chis[n]),
                                   f.scale(-1, defects[n])),
                ('physical stretching retains both original histories', name, n))
        require(pm.mean(hs[n]) == (pm.mean(hs[0]) if n == 0 else 0),
                ('passive cubic mass conservation', name, n))
    if name in ('two-parent triangular boundary', 'single-parent boundary'):
        require(not bool(hs[0]), ('initial cubic label vanishes pointwise', name))
    for n in range(order):
        def material(fields):
            return f.add(fields[n+1], f.scale(-nu, f.lap(fields[n])), *(
                f.scale(math.comb(n, r), f.adv(us[r], fields[n-r]))
                for r in range(n+1)))
        mixed = mixed_diffusion_jet(As, ws, n)
        f.equal(material(Hs), f.scale(-2*nu, mixed),
                ('full strain cancellation with every mixed derivative', name, n))
        f.equal(material(chis), f.scale(2*nu, mixed),
                ('original cubic covariance history', name, n))
        Gs = [jt.add(*(jt.scale(math.comb(j, r),
                      jt.multiply(pm.transpose(Bs[r]), Bs[j-r]))
                      for r in range(j+1))) for j in range(n+1)]
        parent_pressure = [jt.subtract(G, f.hess(p))
                           for G, p in zip(Gs, pressures)]
        f.equal(material(stretching), f.add(cubic_jet(parent_pressure, ws, n),
                    f.scale(-2*nu, mixed_diffusion_jet(Bs, ws, n))),
                ('full physical pressure-parent Riccati observation', name, n))
    Z1 = f.scale(2, f.dot(ws[0], ws[1]))
    enstrophy_loss = f.add(*(f.dot([f.diff(q, k) for q in ws[0]],
                                 [f.diff(q, k) for q in ws[0]]) for k in range(3)))
    require(pm.mean(Z1) == 2*pm.mean(stretching[0])-2*nu.x*pm.mean(enstrophy_loss),
            ('literal physical enstrophy balance', name))
    return {'name': name, 'nu': str(viscosity), 'time_order': order,
            'original_cubic_mass': str(pm.mean(hs[0])),
            'initial_passive_label_identically_zero': not bool(hs[0]),
            'original_observation_jets': list(map(lambda q: str(pm.mean(q)), Hs)),
            'cubic_covariance_jets': list(map(lambda q: str(pm.mean(q)), chis)),
            'compatibility_direction_jets': list(map(lambda q: str(pm.mean(q)), defects)),
            'physical_stretching_jets': list(map(lambda q: str(pm.mean(q)), stretching)),
            'full_pointwise_mixed_diffusion': 'PASS',
            'pressure_parent_and_history_reconstruction': 'PASS',
            'scope': 'complete exact jets; continuous physical history passage analytic'}


def cancelling_signed_mass():
    v = interacting_datum()
    B, w = f.jac(v), f.curl(v)
    require(pm.mean(cubic(B, w)) == Fraction(-384, 65), 'base original cubic mass')
    require(pm.mean(mixed_diffusion(B, w)) == Fraction(-384, 13),
            'base full mixed diffusion')
    reports = []
    for n in (5, 7, 11):
        scaled = [{tuple(n*j for j in k): -a/n for k, a in q.items()} for q in v]
        u = [f.add(a, b) for a, b in zip(v, scaled)]
        f.equal(f.trace(f.jac(u)), {}, 'real solenoidal mixed-scale initial datum')
        require(pm.mean(cubic(f.jac(u), f.curl(u))) == 0,
                'initial signed cubic mass cancels exactly')
        D = pm.mean(mixed_diffusion(f.jac(u), f.curl(u)))
        require(D == Fraction(384*(n*n-1), 13), 'exact different-scale diffusion weight')
        for sign in (-1, 1):
            signed = [f.scale(sign, q) for q in u]
            value = pm.mean(mixed_diffusion(f.jac(signed), f.curl(signed)))
            require(value == sign*D, 'opposite signed covariance production from real data')
        reports.append({'scale': n, 'initial_signed_cubic_mass': '0',
                        'covariance_derivative': 'sign * 768 nu (%d^2-1)/13' % n})
    # Retain the full actual NS tangent on one mixed-scale case, rather
    # than infer physical compatibility from a heat-only calculation.
    n = 5
    scaled = [{tuple(n*j for j in k): -a/n for k, a in q.items()} for q in v]
    u = [f.scale(-1, f.add(a, b)) for a, b in zip(v, scaled)]
    actual = check_history(u, Fraction(1, 10), 1, 'negative two-scale parents')
    require(actual['cubic_covariance_jets'][1] == str(Fraction(-9216, 65)),
            'positive-viscosity covariance renewal with zero initial signed mass')
    return {'family': reports, 'full_actual_prefix': actual,
            'refutes': 'a universal covariance sign or payment from initial signed cubic mass alone',
            'does_not_refute': 'a full-original-datum bound including unsigned labels and coupled compatibility',
            'scope': 'actual smooth periodic data and exact unforced initial tangent; no uniform time window'}


def forced_leg():
    u = interacting_datum()
    nu = f.QQ_I(Fraction(1, 10))
    us, _ = velocity_time_jets(u, Fraction(1, 10), 1)
    B, w = f.jac(u), f.curl(u)
    force = f.curl(u)
    g = f.curl(force)
    require(pm.mean(f.dot(u, force)) == 0, 'diagnostic force has zero instantaneous kinetic work')
    A1 = jt.add(jt.scale(nu, [[f.lap(q) for q in row] for row in B]),
               jt.scale(-1, pm.matrix_adv(u, B)),
               jt.scale(-1, jt.multiply(pm.transpose(B), B)),
               jt.scale(-1, jt.multiply(B, B)))
    wf1 = [f.add(a, b) for a, b in zip(f.curl(us[1]), g)]
    H1 = f.add(f.dot(wf1, f.matvec(B, w)), f.dot(w, f.matvec(A1, w)),
               f.dot(w, f.matvec(B, wf1)))
    production = f.add(H1, f.adv(u, cubic(B, w)), f.scale(-nu, f.lap(cubic(B, w))))
    supplied = f.add(f.scale(-2*nu, mixed_diffusion(B, w)),
                     f.dot(g, f.matvec(B, w)), f.dot(w, f.matvec(B, g)))
    f.equal(production, supplied, 'complete physical curl-force leg')
    extra = f.add(f.dot(g, f.matvec(B, w)), f.dot(w, f.matvec(B, g)))
    require(bool(extra), 'zero kinetic work does not erase the directional force source')
    return {'instantaneous_kinetic_work': '0', 'extra_curl_source_modes': len(extra),
            'extra_curl_source_mean': str(pm.mean(extra)),
            'scope': 'explicit diagnostic forcing, not the imported blowup construction or internal realization'}


def symbolic_reciprocal():
    x, y, z = coordinates = s.symbols('x y z', real=True)
    a, b, c, nu = s.symbols('a b c nu', real=True)
    angles = s.symbols('sx cx sy cy sz cz')
    replacements = {v: angles[2*i+j] for i, q in enumerate(coordinates)
                    for j, v in enumerate((s.sin(q), s.cos(q)))}

    def mean(expression):
        polynomial = s.Poly(s.expand_trig(s.expand(expression)).xreplace(replacements), *angles)
        result = 0
        for powers, coefficient in polynomial.terms():
            weight = s.Integer(1)
            for m, n in zip(powers[::2], powers[1::2]):
                if m % 2 or n % 2:
                    weight = 0
                    break
                r, t = m//2, n//2
                weight *= s.Rational(math.factorial(2*r)*math.factorial(2*t),
                    4**(r+t)*math.factorial(r)*math.factorial(t)*math.factorial(r+t))
            result += weight*coefficient
        return s.factor(result)

    expand = lambda A: A.applyfunc(s.expand)
    lap = lambda A: A.applyfunc(lambda v: sum(s.diff(v, q, 2) for q in coordinates))
    adv = lambda u, A: A.applyfunc(lambda v: sum(u[i]*s.diff(v, q)
                                               for i, q in enumerate(coordinates)))
    curl = lambda u: s.Matrix([s.diff(u[2], y)-s.diff(u[1], z),
                               s.diff(u[0], z)-s.diff(u[2], x),
                               s.diff(u[1], x)-s.diff(u[0], y)])
    scalar = lambda A, v, w: (v.T*A*w)[0]
    u = s.Matrix([a*s.sin(y), b*s.sin(z), c*s.sin(x)])
    B, w = u.jacobian(coordinates), curl(u)
    u1 = expand(nu*lap(u)-B*u)
    B1, w1 = u1.jacobian(coordinates), curl(u1)
    p1 = -2*a*b*c*s.cos(x)*s.cos(y)*s.cos(z)
    u2 = expand(nu*lap(u1)-B1*u-B*u1-s.Matrix([s.diff(p1, q) for q in coordinates]))
    B2, w2 = u2.jacobian(coordinates), curl(u2)
    A1 = expand(nu*lap(B)-adv(u, B)-B.T*B-B*B)
    A2 = expand(nu*lap(A1)-adv(u, A1)-adv(u1, B)-B1.T*B-B.T*A1-A1*B-B*B1)
    H2 = scalar(B, w2, w)+scalar(B, w, w2)+2*scalar(B, w1, w1) \
        +2*scalar(A1, w1, w)+2*scalar(A1, w, w1)+scalar(A2, w, w)
    E1, E2 = A1-B1, A2-B2
    Eobs1 = scalar(E1, w, w)
    Eobs2 = scalar(E2, w, w)+2*scalar(E1, w1, w)+2*scalar(E1, w, w1)
    stretch2 = scalar(B2, w, w)+2*scalar(B1, w1, w)+2*scalar(B1, w, w1) \
        +scalar(B, w2, w)+scalar(B, w, w2)+2*scalar(B, w1, w1)
    H1 = scalar(A1, w, w)+scalar(B, w1, w)+scalar(B, w, w1)
    results = {'original_cubic_mass': mean(scalar(B, w, w)),
               'observation_first': mean(H1), 'observation_second': mean(H2),
               'compatibility_first': mean(Eobs1), 'compatibility_second': mean(Eobs2),
               'physical_stretch_second': mean(stretch2)}
    S22 = a*a*b*b+a*a*c*c+b*b*c*c
    expected = {'original_cubic_mass': 0, 'observation_first': 0,
                'observation_second': -nu*S22/2, 'compatibility_first': -S22/4,
                'compatibility_second': 3*nu*S22/2, 'physical_stretch_second': -2*nu*S22}
    for name, value in results.items():
        require(s.expand(value-expected[name]) == 0, ('independent generic symbolic mean', name))
    return {'generic_mean_jets': {k: str(v) for k, v in results.items()},
            'scope': 'independent trigonometric-polynomial integration; no time remainder bound'}


def paid_calibrations():
    a, b, c, nu = s.symbols('a b c nu', positive=True)
    t = s.symbols('t', nonnegative=True)
    K = a*a*b*b/(6*nu*nu)
    remaining = K*(4*s.exp(-3*nu*t)-3*s.exp(-4*nu*t))
    rate = 2*a*a*b*b*s.exp(-3*nu*t)*(1-s.exp(-nu*t))/nu
    require(s.simplify(s.diff(remaining, t)+rate) == 0,
            'complete triangular physical stretching reserve derivative')
    require(s.simplify(remaining.subs(t, 0)-K) == 0,
            'same original triangular allowance at time zero')
    require(s.limit(remaining, t, s.oo) == 0,
            'no fresh original allowance at a late seam')
    q = s.symbols('q', nonnegative=True)
    require(s.expand(4*q**3-3*q**4-q**3-3*q**3*(1-q)) == 0,
            'remaining reserve nonnegative for q=exp(-nu t) in [0,1]')

    x, y, z = coordinates = s.symbols('x y z', real=True)
    sigma, kappa, theta = s.symbols('sigma kappa theta', real=True)
    w0 = s.sin(x-sigma*s.sin(y))
    require(s.simplify(s.diff(w0, sigma)+s.sin(y)*s.diff(w0, x)) == 0,
            'exact zero-diffusivity triangular turnover profile')
    lap0 = s.diff(w0, x, 2)+s.diff(w0, y, 2)
    residual = s.diff(w0, sigma)+s.exp(-kappa*sigma)*s.sin(y)*s.diff(w0, x)-kappa*lap0
    forcing = (1-s.exp(-kappa*sigma))*s.sin(y)*s.diff(w0, x)+kappa*lap0
    require(s.simplify(residual+forcing) == 0,
            'literal scaled viscous difference equation retains heat and decaying shear')
    omega0 = s.Matrix([s.diff(w0, y), -s.diff(w0, x), -s.cos(y)])
    gradient0 = omega0.jacobian((x, y))
    mean_shifted = lambda v: s.simplify(s.integrate(s.integrate(
        s.expand_trig(s.expand(v.subs(x, theta+sigma*s.sin(y)))),
        (theta, 0, 2*s.pi)), (y, 0, 2*s.pi))/(2*s.pi)**2)
    require(mean_shifted(omega0.dot(omega0)) == 1+sigma*sigma/4,
            'exact limiting physical enstrophy during a turnover')
    require(mean_shifted(s.trace(gradient0.T*gradient0)) ==
            1+3*sigma*sigma/4+3*sigma**4/16,
            'exact limiting complete vorticity-gradient dissipation')
    V = s.Matrix([a*s.sin(z)+c*s.cos(y), b*s.sin(x)+a*s.cos(z),
                  c*s.sin(y)+b*s.cos(x)])
    curl = lambda u: s.Matrix([s.diff(u[2], y)-s.diff(u[1], z),
                               s.diff(u[0], z)-s.diff(u[2], x),
                               s.diff(u[1], x)-s.diff(u[0], y)])
    simplify_zero = lambda A: all(s.trigsimp(s.expand(v)) == 0 for v in A)
    require(simplify_zero(curl(V)-V), 'complete three-parent Beltrami field')
    lapV = V.applyfunc(lambda v: sum(s.diff(v, q, 2) for q in coordinates))
    require(simplify_zero(lapV+V), 'complete Beltrami Laplacian eigenfield')
    u = s.exp(-nu*t)*V
    B = u.jacobian(coordinates)
    p = -u.dot(u)/2
    gradp = s.Matrix([s.diff(p, q) for q in coordinates])
    lapu = u.applyfunc(lambda v: sum(s.diff(v, q, 2) for q in coordinates))
    require(simplify_zero(s.diff(u, t)+B*u+gradp-nu*lapu),
            'actual all-time unforced NS with all pressure parents')
    require(simplify_zero(curl(u)-u), 'physical vorticity of the evolving Beltrami field')
    flux = u*(u.dot(u)/2)
    stretching = (u.T*B*u)[0]
    require(s.trigsimp(s.expand(stretching-sum(s.diff(flux[i], q)
                                              for i, q in enumerate(coordinates)))) == 0,
            'the full physical stretching is a periodic divergence')
    require(s.trigsimp(s.expand(stretching)).subs({a: 1, b: 2, c: 3, x: 0, y: 0, z: 0}) != 0,
            'the three-dimensional calibration retains pointwise stretching')
    initial = [{}, {}, {}]
    for i, axis, amplitude in ((0, 2, 1), (1, 0, 2), (2, 1, 3)):
        k = tuple(int(j == axis) for j in range(3))
        initial[i] = {k: -f.II*f.QQ_I(amplitude)/2,
                      tuple(-j for j in k): f.II*f.QQ_I(amplitude)/2}
    for i, axis, amplitude in ((0, 1, 3), (1, 2, 1), (2, 0, 2)):
        k = tuple(int(j == axis) for j in range(3))
        initial[i] = f.add(initial[i], {k: f.QQ_I(amplitude)/2,
                           tuple(-j for j in k): f.QQ_I(amplitude)/2})
    original_history = check_history(initial, Fraction(1, 10), 2, '3D Beltrami calibration')
    require(original_history['physical_stretching_jets'] == ['0']*3,
            'complete Beltrami physical mean stretching through the tested order')
    require(all(Fraction(c)+Fraction(e) == 0 for c, e in
                zip(original_history['cubic_covariance_jets'],
                    original_history['compatibility_direction_jets'])),
            'Beltrami covariance and compatibility cancel in the joined history')
    require(original_history['cubic_covariance_jets'][2] == '49/5' and
            original_history['compatibility_direction_jets'][2] == '-49/5',
            'the joined Beltrami cancellation retains two individually nonzero history legs')
    return {'triangular_mixing': {'all_time_joined_allowance': str(K),
                'remaining_original_reserve': str(remaining),
                'zero_initial_cubic_label_turnover': {
                    'data': 'u0=(A sin y,0,A sin x), h0=0 pointwise',
                    'scaled_viscosity': 'kappa=nu/A, sigma=A t',
                    'limiting_enstrophy': 'A^2(1+sigma^2/4)',
                    'fixed_sigma_viscous_convergence': 'O(kappa) in H^2 by the linear parabolic difference estimate',
                    'refutes': 'an arbitrary amplitude-uniform joined budget depending only on h0=0,nu,H',
                    'scope': 'exact limiting equations/integrals; actual positive-viscosity family and uniform fixed-turnover convergence analytic'},
                'scope': 'exact scalar identities; original stochastic derivative bounds and spatial history payment analytic'},
            'three_dimensional_Beltrami': {'velocity': str(u),
                'pressure': str(p), 'net_spatial_cubic_renewal': '0 at every time',
                'complete_original_history_jets': original_history,
                'allowance': 'K=0 for the joined physical renewal budget',
                'scope': 'exact all-time NS and divergence identities; original stochastic reconstruction analytic',
                'limitation': 'monochromatic Beltrami parents decay by heat; arbitrary mutually amplifying parents not covered'}}


if __name__ == '__main__':
    print(json.dumps({'reciprocal_parents': [check_history(seed(amplitudes), nu, 2, name)
                      for amplitudes, nu, name in (
                        ((1, 1, 1), Fraction(1, 10), 'equal reciprocal parents'),
                        ((2, -1, 3), Fraction(2, 5), 'unequal signed reciprocal parents'),
                        ((1, 2, 0), Fraction(1, 4), 'two-parent triangular boundary'),
                        ((0, 0, 2), Fraction(1, 3), 'single-parent boundary'))],
                      'independent_symbolic_reciprocal': symbolic_reciprocal(),
                      'mixed_scale_covariance': cancelling_signed_mass(),
                      'diagnostic_forcing': forced_leg(),
                      'paid_calibrations': paid_calibrations()}, indent=2))
