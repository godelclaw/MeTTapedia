#!/usr/bin/env python3
"""Exact phase-dependent descendant renewal and fixed-band force bounds.

All Fourier outputs, physical tangent terms and changing observer weights
are retained. Actual release intervals and arbitrary-history energy
payments are analytic in README.md, not certified by these finite checks.
"""

import json
from fractions import Fraction as Q
from itertools import product

import oscillatory_parent_release as release
from reciprocal_pattern_cycles import mode

nr, s, f = release.nr, release.s, release.f


def phase_seed(last_sign):
    waves = ((1, 0, 1), (1, -1, 1), (2, 0, 1), (2, -1, 1))
    v = [{}, {}, {}]
    for k, c in zip(waves, (3, 1, 3, 3*last_sign)):
        for j, a in enumerate((-k[1], k[0], 0)):
            v[j] = f.add(v[j], mode(k, c*a))
    f.equal(f.trace(f.jac(v)), {}, 'each phase is solenoidal')
    s.require(not v[2] and s.inner(v, v) == 46,
              'same horizontal envelope energy in both phases')
    return v


def spectrum(v):
    return {k: sum(z.x*z.x+z.y*z.y for z in a) for k, a in s.modes(v).items()}


def normalized_defect_coefficients(j, cost):
    """Numerator of W_beta'+cost, retaining every changing-weight term."""
    Z, H, C, Zd, Hd, Cd = (j[k] for k in ('Z', 'H', 'C', 'Zd', 'Hd', 'Cd'))
    return (Z**2*(Zd/2+Hd+Cd+cost),
            Zd*C*(Z+H+C)+Z*C*Hd-Z*H*Cd+2*cost*Z*C,
            C*C*(Zd/2+cost))


def descendant_jet(v, growing):
    w = s.nonlinear(v)
    alpha = 256  # epsilon=32, nu=1 in the actual release construction.
    b = s.vector_scale(alpha, w)
    j = nr.physical_jet(b, full=True)
    W, Wd, weight_rate = nr.common_weight(j)
    Qfree = Wd+2*j['g']-j['D']/2
    expected = (846, 10620, Q(1755, 28)) if growing else (657, 7623, Q(-585, 476))
    s.require((j['Z']/alpha**2, j['D']/alpha**2, j['g']/alpha**3) == expected,
              'exact source geometry in the selected phase')
    s.require(any(w[2]) and any(s.vertical_mean(w)),
              'pressure-generated vertical motion and slow mean are retained')
    s.require(all(sum(x*x for x in k) < 49 for k in s.modes(w)),
              'the adverse released seed stays entirely in the unpaid core at Lambda seven')
    s.require(weight_rate != 0, 'the normalization changes along the full NS tangent')
    n = s.nonlinear(b)
    production = (j['Cd']+s.inner(n, n))/alpha**5
    if growing:
        s.require(Qfree > 2_000_000_000 and j['Cd'] > 2_000_000_000_000_000,
                  'positive base defect and positive complete capacity derivative')
        s.require(j['Zd'] == Q(4978114560, 7) > 0,
                  'actual enstrophy production is positive after viscosity')
        s.require(production > 1900,
                  'nonlinear capacity renewal is strictly positive')
        coefficients = normalized_defect_coefficients(j, 2*j['g']-j['D']/2)
        s.require(all(a > 0 for a in coefficients),
                  'the complete defect numerator has strictly positive coefficients for every beta')
        for beta in (Q(8), Q(16), Q(1000)):
            value, rate, _ = nr.common_weight(j, beta)
            poly = sum(a*beta**i for i, a in enumerate(coefficients))
            s.require(poly == (j['Z']+beta*j['C'])**2*(rate+2*j['g']-j['D']/2),
                      'independent weight evaluation matches the complete quadratic numerator')
            kappa = Q(5, 7)
            cooled = {**j, **{d: j[d]-kappa*j[v]
                             for d, v in (('Zd', 'Z'), ('Hd', 'H'), ('Cd', 'C'))}}
            _, cooled_rate, _ = nr.common_weight(cooled, beta)
            s.require(cooled_rate == rate-kappa*value,
                      'common cooling is exactly retained through all observer slots')
        # Two positive summands imply Qfree+sigma*Cd>0 for every sigma>=0.
        for sigma in (Q(0), Q(1, 1000), Q(1), Q(1000)):
            s.require(Qfree+sigma*j['Cd'] > 0, 'sampled members of the exact coefficient obstruction')
    else:
        s.require(j['g'] < 0 and j['Zd'] < 0 and j['Cd'] < 0 and production < -3700,
                  'one phase reversal gives depleting stretching and capacity decay')
    return {'phase': 'growing' if growing else 'depleting', 'alpha': alpha,
            'generated_cubic': str(j['g']/alpha**3),
            'nonlinear_capacity_production': str(production),
            'physical_enstrophy_derivative': str(j['Zd']),
            'physical_capacity_derivative': str(j['Cd']),
            'W8': float(W), 'base_defect': float(Qfree),
            'all_beta_at_least_eight_positive': growing,
            'capacity_derivative_decimal': float(j['Cd'])}


def select(v, predicate):
    return [{k: a for k, a in row.items() if predicate(sum(x*x for x in k))} for row in v]


def lattice_constant_squared(M):
    return sum(sum(x*x for x in k) for k in product(range(-M, M+1), repeat=3)
               if sum(x*x for x in k) <= M*M)


def fixed_band_fixtures(v):
    carrier = mode((0, 0, 8), 8)
    u = s.vector_add([f.mul(carrier, row) for row in v],
                     s.vector_scale(Q(1, 3), s.nonlinear(v)))
    Au = s.minus_laplacian(u)
    Z = s.inner(u, Au)
    # The full tangent is tested before making any frequency restriction.
    direction = s.vector_add(s.vector_scale(Q(-2, 7), Au), s.nonlinear(u))
    s.require(2*s.inner(u, direction) == -Q(4, 7)*Z,
              'actual full kinetic identity supplies the reserve derivative')
    rows = []
    for lam, M in ((1, 1), (3, 3), (7, 5)):
        high = select(u, lambda k2: k2 >= lam*lam)
        source = s.nonlinear(high)
        low = select(source, lambda k2: 0 < k2 <= M*M)
        Ehigh = s.inner(high, high)
        Zhigh = s.inner(high, s.minus_laplacian(high))
        K2 = lattice_constant_squared(M)
        q2 = s.inner(low, low)
        s.require(q2 <= K2*Ehigh**2,
                  'complete pressure-projected force obeys the low-output Fourier bound')
        s.require(lam*lam*Ehigh <= Zhigh <= Z,
                  'high parents are paid from their actual contribution to dissipation')
        s.require(q2*lam**4 <= K2*Z**2,
                  'the force charge is bounded by the linear energy-reserve spending rate')
        rows.append({'parent_cutoff': lam, 'output_cutoff': M,
                     'K_squared': K2, 'force_squared': str(q2),
                     'high_output_modes_retained': len(s.modes(source))-len(s.modes(low))})
    s.require(rows[-1]['K_squared'] == 7650,
              'explicit fixed-band lattice constant')
    return rows


def remainder_stretching_fixtures(v):
    carrier = mode((0, 0, 8), 8)
    u = s.vector_add([f.mul(carrier, row) for row in v],
                     s.vector_scale(Q(1, 3), s.nonlinear(v)))
    u0 = s.vector_scale(2, u)
    h = release.hp.heat_at(u0, Q(1, 2))
    b = s.vector_add(u, s.vector_scale(-1, h))
    E0, Eu, Eh, Eb = (s.inner(w, w) for w in (u0, u, h, b))
    Zu, Zh, Zb = (s.inner(w, s.minus_laplacian(w)) for w in (u, h, b))
    s.require(Eu <= E0 and Eh <= E0 and Eb <= 4*E0,
              'state fixture obeys the required original-energy envelope')
    s.require(Zb <= 2*(Zu+Zh), 'two kinetic dissipations pay the remainder gradient')
    Ab, Nb = s.minus_laplacian(b), s.nonlinear(b)
    g = s.cubic(b)
    s.require(s.inner(Ab, Nb) == g, 'full remainder stretching includes every output')
    rows = []
    for lam, M in ((1, 1), (3, 3), (7, 5)):
        high = select(b, lambda k2: k2 >= lam*lam)
        force = select(s.nonlinear(high), lambda k2: 0 < k2 <= M*M)
        observer = select(Ab, lambda k2: 0 < k2 <= M*M)
        T = s.inner(observer, force)
        K2 = lattice_constant_squared(M)
        s.require(T*T <= 4*M**4*E0*s.inner(force, force),
                  'the actual low-band enstrophy observer has its own explicit norm price')
        s.require(T*T*lam**4 <= 16*M**4*E0*K2*(Zu+Zh)**2,
                  'two decaying energies pay the named portion of generated stretching')
        residual = s.vector_add(Nb, s.vector_scale(-1, force))
        s.require(s.inner(Ab, residual) == g-T,
                  'the unremoved physical interactions remain exactly in the continuation target')
        rows.append({'parent_cutoff': lam, 'output_cutoff': M,
                     'paid_stretching_sign': (T > 0)-(T < 0),
                     'complete_residual_retained': True})
    return rows


def main():
    growing, depleting = phase_seed(-1), phase_seed(1)
    s.require(spectrum(growing) == spectrum(depleting),
              'all original modal energies agree, hence every quadratic heat energy curve agrees')
    jets = [descendant_jet(growing, True), descendant_jet(depleting, False)]
    fixed = fixed_band_fixtures(growing)
    remainder = remainder_stretching_fixtures(growing)
    print(json.dumps({'status': 'all exact checks passed', 'matched_modal_energies': True,
                      'descendants': jets, 'fixed_band': fixed, 'remainder_stretching': remainder,
                      'scope': 'exact algebra; actual history and all-prefix bounds analytic'}, indent=2))


if __name__ == '__main__':
    main()
