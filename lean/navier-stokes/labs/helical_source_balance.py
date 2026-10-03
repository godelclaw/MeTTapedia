#!/usr/bin/env python3
"""Exact full-source helicity and a paid two-coordinate calibration.

All Fourier outputs and the pressure projection are retained. Coefficients
lie in Q(i,sqrt(2),sqrt(5)). PDE intervals, whole-space localization and the
all-time calibration are analytic arguments in README.md, not Lean proofs.
"""

import json
from collections import defaultdict
from itertools import product
import sympy as s


def clean(p):
    return {k: s.expand(a) for k, a in p.items() if s.expand(a) != 0}


def add(*ps):
    result = defaultdict(lambda: 0)
    for p in ps:
        for k, a in p.items():
            result[k] += a
    return clean(result)


def scale(c, p):
    return clean({k: c*a for k, a in p.items()})


def mul(p, q):
    result = defaultdict(lambda: 0)
    for k, a in p.items():
        for ell, b in q.items():
            result[tuple(x+y for x, y in zip(k, ell))] += a*b
    return clean(result)


def diff(p, j):
    return clean({k: s.I*k[j]*a for k, a in p.items()})


def grad(p):
    return [diff(p, j) for j in range(3)]


def div(v):
    return add(*(diff(p, j) for j, p in enumerate(v)))


def vadd(*vs):
    return [add(*(v[j] for v in vs)) for j in range(3)]


def cross(v, w):
    return [add(mul(v[(j+1) % 3], w[(j+2) % 3]),
                scale(-1, mul(v[(j+2) % 3], w[(j+1) % 3]))) for j in range(3)]


def curl(v):
    return [add(diff(v[(j+2) % 3], (j+1) % 3),
                scale(-1, diff(v[(j+1) % 3], (j+2) % 3))) for j in range(3)]


def green(p):
    return {k: a/sum(x*x for x in k) for k, a in p.items() if any(k)}


def projection(v):
    return vadd(v, grad(green(div(v))))


def pair(v, w):
    return s.expand(sum(a*w[j].get(tuple(-x for x in k), 0)
                        for j, p in enumerate(v) for k, a in p.items()))


def zero(x, label):
    if s.simplify(x) != 0:
        raise ArithmeticError((label, x))


def equal(v, w, label):
    for j in range(3):
        if add(v[j], scale(-1, w[j])):
            raise ArithmeticError((label, j))


def modes(v):
    return set().union(*(p.keys() for p in v))


def fixture():
    # psi_hat is invariant under coordinate exchange and independent signs.
    data = {(0, 1): 1, (0, 2): -s.Rational(2, 7), (0, 3): s.Rational(1, 20),
            (1, 1): -s.Rational(9, 14), (2, 2): -s.Rational(1, 6),
            (1, 3): -s.Rational(3, 40)}
    psi = {}
    for (a, b), c in data.items():
        for x, y in {(a, b), (b, a)}:
            for sx, sy in product([-1, 1], repeat=2):
                psi[sx*x, sy*y, 0] = c
    u = [diff(psi, 1), scale(-1, diff(psi, 0)),
         {k: s.sqrt(sum(x*x for x in k))*a for k, a in psi.items()}]
    h = [{(0, 0, 1): s.Rational(1, 2), (0, 0, -1): s.Rational(1, 2)},
         {(0, 0, 1): s.I/2, (0, 0, -1): -s.I/2}, {}]
    return psi, u, h


def root_upper(expr):
    """An exact rational upper bound; no floating-point sign decisions."""
    result = expr
    for radicand, lower, upper in ((2, 141421356, 141421357),
                                   (10, 316227766, 316227767)):
        lo, hi = s.Rational(lower, 10**8), s.Rational(upper, 10**8)
        if not (0 < lo and lo*lo < radicand < hi*hi):
            raise ArithmeticError('Invalid root enclosure')
        c = s.expand(result).coeff(s.sqrt(radicand))
        if not c.is_Rational:
            raise ArithmeticError('Root enclosure expects a rational linear coefficient')
        result = s.expand(result-c*s.sqrt(radicand)+c*(hi if c >= 0 else lo))
    if not result.is_Rational:
        raise ArithmeticError('Unenclosed radical remains')
    return result


def full_source():
    psi, u, h = fixture()
    omega = curl(u)
    b = projection(cross(u, omega))
    q = {k: sum(x*x for x in k)*a for k, a in psi.items()}
    adv = lambda p: add(*(mul(u[j], diff(p, j)) for j in range(2)))
    w_rhs, q_rhs = scale(-1, adv(u[2])), scale(-1, adv(q))
    if add(b[2], scale(-1, w_rhs)) or add(curl(b)[2], scale(-1, q_rhs)):
        raise ArithmeticError('Full source differs from the two-coordinate equations')
    H0 = pair(b, curl(b))
    formula = -350383*s.sqrt(2)/180075+s.Rational(378244847, 864360000)
    formula += 9824477*s.sqrt(10)/13720000
    zero(H0-formula, 'complete generated helicity')
    zero(H0-2*pair([w_rhs], [q_rhs]), 'independent advected-scalar bracket identity')
    if root_upper(H0) >= -s.Rational(49, 1000):
        raise ArithmeticError('Planar complete source is not strictly negative')
    equal(projection(cross(h, curl(h))), [{}, {}, {}], 'third wave is Beltrami')
    c = projection(vadd(cross(u, curl(h)), cross(h, omega)))
    Hc = pair(c, curl(c))
    zero(Hc+s.Rational(362501, 44100)-81*s.sqrt(10)/20-6946*s.sqrt(2)/441,
         'all cross-source modes retained')
    zero(pair(b, curl(c)), 'disjoint vertical supports')
    records = []
    for epsilon in (s.Integer(0), s.Rational(1, 100)):
        v = vadd(u, [scale(epsilon, p) for p in h])
        cv = curl(v)
        equal(cv, [{k: s.sqrt(sum(x*x for x in k))*a for k, a in p.items()} for p in v],
              'initial field has only positive helicity')
        if div(v):
            raise ArithmeticError('Initial field is not incompressible')
        for p in v:
            for k, a in p.items():
                zero(p.get(tuple(-x for x in k), 0)-s.conjugate(a), 'reality')
        raw = cross(v, cv)
        source = projection(raw)
        equal(source, vadd(b, [scale(epsilon, p) for p in c]), 'complete nonlinear expansion')
        H = pair(source, curl(source))
        zero(H-H0-epsilon**2*Hc, 'exact three-dimensional source helicity')
        zero(H-pair(raw, curl(raw)), 'pressure projection preserves source helicity')
        if root_upper(H) >= -s.Rational(47, 1000):
            raise ArithmeticError('Strict complete-source helicity bound failed')
        # Independently reconstruct canonical pressure and the physical tangent.
        advection = [add(*(mul(v[j], diff(p, j)) for j in range(3))) for p in v]
        pressure = green(div(advection))
        equal(source, [scale(-1, p) for p in vadd(advection, grad(pressure))],
              'literal full NS pressure equation')
        nu = s.Rational(3, 2)
        lap = [{k: -sum(x*x for x in k)*a for k, a in p.items()} for p in v]
        tangent = vadd([scale(nu, p) for p in lap], source)
        zero(2*pair(v, tangent)+2*nu*pair(cv, cv), 'actual kinetic-energy decay')
        rank = s.Matrix(sorted(modes(v))).rank()
        if rank != (3 if epsilon else 2):
            raise ArithmeticError('Unexpected spatial dependence')
        records.append(dict(epsilon=str(epsilon), spatial_rank=rank,
            velocity_modes=len(modes(v)), source_modes=len(modes(source)), pressure_modes=len(pressure),
            full_source_helicity=str(H), rational_upper=str(root_upper(H)),
            actual_heat_remainder='H(u(t)-exp(nu t Delta)u0)=H(source)t^2+O(t^3)'))
    Eh, Zh, X0 = pair(u[:2], u[:2]), pair([q], [q]), pair(grad(u[2]), grad(u[2]))
    zero(Eh-s.Rational(221407, 22050), 'horizontal initial energy')
    zero(Zh-s.Rational(1246171, 44100), 'horizontal initial enstrophy')
    zero(X0-Zh, 'initial scalar-gradient stock')
    return dict(cases=records, planar_resources=dict(Eh0=str(Eh), Zh0=str(Zh), X0=str(X0)),
                scope='all source outputs; actual short-time and localization statements are analytic')


def paid_history():
    nu, Eh, Zh, X0, E0, kappa = s.symbols('nu Eh Zh X0 E0 kappa', positive=True)
    A = 52*s.sqrt(Eh*Zh)/nu
    Xstar = X0*s.exp(A/nu)
    Zstar, Dstar = Zh+Xstar, (Zh/2+Xstar)/nu
    B = s.sqrt(E0*Zstar)+kappa*s.sqrt(E0*(Zh+2*Xstar))
    zero((2*kappa*nu)**2*(E0/(2*nu))*Dstar-kappa**2*E0*(Zh+2*Xstar),
         'complete integrated critical dissipation allowance')
    J, L = s.symbols('J L', real=True)
    Mp = 4*J-2*nu*L
    Cp = 4*J-2*(1-kappa)*nu*L
    zero(Mp-Cp+2*kappa*nu*L, 'same reserve through all compatible seams')
    return dict(velocity_supremum_integral=str(A), scalar_gradient_upper=str(Xstar),
        enstrophy_upper=str(Zstar), integrated_order_two_upper=str(Dstar),
        signed_helicity_allowance=str(B),
        scope='all-time allowance for autonomous two-coordinate torus flows, any amplitude',
        OPEN='three-dimensional feedback into the horizontal energy and enstrophy balances')


if __name__ == '__main__':
    print(json.dumps(dict(status='all exact checks passed', full_source=full_source(),
        complete_planar_history=paid_history(),
        scope='analytic physical results with exact checks; no new Lean certificate'), indent=2))
