#!/usr/bin/env python3
"""Exact fixtures for an unforced oscillatory initial layer.

The layer profile retains its generated vertical feedback. The full PDE
realization and stability argument are analytic in README.md; this checker
certifies finite algebra, not an NS existence interval or global regularity.
"""

import json
from fractions import Fraction as Q

import sympy as sy

import heat_remainder_payment as hp
from reciprocal_pattern_cycles import mode

nr, s, f = hp.nr, hp.s, hp.f


def horizontal_seed():
    waves = ((1, 0, 1), (1, -1, 1), (2, 0, 1), (2, -1, 1))
    coefficients = (-2, 2, -2, 3)
    v = [{}, {}, {}]
    for k, c in zip(waves, coefficients):
        for j, a in enumerate((-k[1], k[0], 0)):
            v[j] = f.add(v[j], mode(k, c*a))
    f.equal(f.trace(f.jac(v)), {}, 'horizontal seed is exactly solenoidal')
    s.require(not v[2] and any(k[2] for k in s.modes(v)),
              'horizontal velocity still depends on all three spatial variables')
    s.require(s.inner(v, v) == Q(73, 2), 'exact original envelope energy')
    return v


def field_equal(a, b, label):
    for j in range(3):
        f.equal(a[j], b[j], (label, j))


def carrier_checks(v):
    w = s.nonlinear(v)
    rows = []
    for n in (4, 8, 16):
        carrier = mode((0, 0, n), n)
        u = [f.mul(carrier, row) for row in v]
        f.equal(f.trace(f.jac(u)), {}, 'carrier multiplication preserves incompressibility')
        source = s.nonlinear(u)
        low = [{k: a for k, a in row.items() if abs(k[2]) <= 2} for row in source]
        field_equal(low, s.vector_scale(Q(n*n, 2), w),
                    'all low difference outputs give the complete projected slow source')
        high = s.vector_add(source, s.vector_scale(-1, low))
        s.require(any(high), 'high sum outputs are present and retained')
        s.require(s.inner(u, u) == Q(73*n*n, 4), 'carrier energy has no alias cross term')
        rows.append({'carrier': n, 'low_modes': len(s.modes(low)),
                     'high_modes': len(s.modes(high))})
    return rows


def profile_checks(v):
    w = s.nonlinear(v)
    B = [f.adv(v, row) for row in v]
    T = [f.mul(w[2], row) for row in v]
    s.require(any(w[2]) and any(T), 'generated vertical motion has a nonzero return into the carrier')
    f.equal(B[2], {}, 'the raw source is horizontal before its slow pressure projection')
    q, tau, eps, nu = sy.symbols('q tau eps nu', positive=True)
    m = eps**2*(1-q**2)/(4*nu)
    c2 = -eps**2*(q**2-q**4)/(4*nu)
    c1 = eps**3*q*(tau-(1-q**2)/(2*nu))/(4*nu)
    derivative = lambda a: sy.diff(a, tau)-nu*q*sy.diff(a, q)
    identities = (derivative(m)-eps**2*q**2/2,
                  derivative(c2)+4*nu*c2+eps**2*q**2/2,
                  derivative(c1)+nu*c1-eps*q*m)
    s.require(all(sy.cancel(a) == 0 for a in identities),
              'all three layer channels satisfy their complete limiting evolution')
    s.require(all(a.subs({q: 1, tau: 0}) == 0 for a in (m, c2, c1)),
              'every generated layer component starts from zero')
    # The first response alone omits the sin(theta) feedback channel.
    s.require(sy.cancel(eps*q*m) != 0,
              'the omitted channel has a real evolution defect')
    return {'vertical_parent_squared': str(s.inner([{}, {}, w[2]], [{}, {}, w[2]])),
            'return_channel_squared': str(s.inner(T, T)),
            'all_three_coefficient_ODEs': True}


def lifted_project(k, a, n=None):
    """P_N on a four-index mode, or its limiting projector P_infinity."""
    if n is None and k[3]:
        return a[0], a[1], f.ZERO
    wave = (k[0], k[1], k[2]+(n*k[3] if n is not None else 0))
    kk = sum(x*x for x in wave)
    if not kk:
        return a
    dot = sum(x*z for x, z in zip(wave, a))
    return tuple(a[j]-wave[j]*dot/kk for j in range(3))


def projection_checks(v):
    w = s.nonlinear(v)
    B = [f.adv(v, row) for row in v]
    T = [f.mul(w[2], row) for row in v]
    count = 0
    for field, phases in ((w, (0,)), (B, (-2, 2)), (T, (-1, 1))):
        for k, a in s.modes(field).items():
            for phase in phases:
                lifted = (*k, phase)
                s.require(lifted_project(lifted, a) == a,
                          'explicit layer is solenoidal for the limiting projection')
                for n in (4, 8, 16):
                    projected = lifted_project(lifted, a, n)
                    wave = (k[0], k[1], k[2]+n*phase)
                    s.require(not sum((x*z for x, z in zip(wave, projected)), f.ZERO),
                              'projected lift pulls back to a genuine solenoidal physical mode')
                    s.require(lifted_project(lifted, projected, n) == projected,
                              'exact lifted pressure projection is idempotent')
                    count += 1
    return {'projected_modes_checked': count, 'zero_physical_frequency_uses_identity': True}


def released_state_checks(v):
    w = s.nonlinear(v)
    Aw, nw = s.minus_laplacian(w), s.nonlinear(w)
    Z, D, g = s.inner(w, Aw), s.inner(Aw, Aw), s.cubic(w)
    s.require((Z, D, g) == (Q(443), Q(4767), Q(14040, 119)),
              'exact generated geometry and strictly positive self-stretching')
    s.require(s.inner(Aw, nw) == g and s.inner(w, nw) == 0,
              'independent enstrophy and kinetic identities retain pressure')
    H, C = s.forecast(w), nr.rc.capacity(w)
    R, P = s.forecast_derivative(w, nw), nr.rc.derivative(w, nw)
    N2 = s.inner(nw, nw)
    expected = (Q(13403, 1785), Q(4759369226919706030857271, 8265219767113767658200),
                Q(1748226002447041281253, 3876382948413175200),
                Q(-7256100350950386259417953493748198375201,
                  4391703164685010312286190283904863200),
                Q(2429763618398464903837, 227983729441042575))
    s.require((H, C, R, P, N2) == expected,
              'full heat forecast, source capacity and nonlinear derivatives')
    # These endpoint identities check both heat parts of the tangent separately.
    s.require(s.forecast_derivative(w, s.vector_scale(-1, Aw)) == -2*g,
              'heat forecast spends the current full cubic')
    s.require(nr.rc.derivative(w, s.vector_scale(-1, Aw)) == -N2,
              'heat source capacity spends the complete source square')
    rows = []
    for alpha in (1, 16, 32, 36):
        j = dict(Z=alpha**2*Z, H=alpha**3*H, C=alpha**4*C,
                 Zd=-2*alpha**2*D+2*alpha**3*g,
                 Hd=-2*alpha**3*g+alpha**4*R,
                 Cd=-alpha**4*N2+alpha**5*P)
        value, rate, changing_weight = nr.common_weight(j)
        defect = rate+2*alpha**3*g-alpha**2*D/2
        s.require(changing_weight != 0, 'the complete normalization derivative is retained')
        s.require((defect > 0) == (alpha >= 32), 'strict state-defect signs')
        if alpha == 36:
            s.require(defect > 7_000_000 and defect > alpha**2*D,
                      'rational positive margin for the released state with epsilon twelve')
        rows.append({'alpha': alpha, 'W8': float(value), 'defect': float(defect),
                     'strict_sign_checked_exactly': True})
    return {'generated_cubic': str(g), 'state_defects': rows,
            'PDE_reachability': 'analytic lifting and stability argument in README.md'}


def main():
    v = horizontal_seed()
    result = {'carrier': carrier_checks(v), 'layer': profile_checks(v),
              'projection': projection_checks(v), 'released_state': released_state_checks(v)}
    print(json.dumps({'status': 'all exact checks passed', **result,
                      'scope': 'finite algebra; actual initial layer and failure interval analytic'}, indent=2))


if __name__ == '__main__':
    main()
