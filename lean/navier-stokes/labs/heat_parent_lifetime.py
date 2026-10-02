#!/usr/bin/env python3
"""Exact fixtures for an original-heat reserve with finite total lifetime.

All Fourier outputs and heat rates are retained. General heat estimates,
actual solution intervals and continuation are analytic in README.md.
The checker does not prove the remaining generated-stretching budget.
"""

import json
from fractions import Fraction as Q

import heat_remainder_payment as hp
from reciprocal_pattern_cycles import mode

nr, s, f = hp.nr, hp.s, hp.f


def coefficient_size(vector):
    return sum((Q(str(abs(z.x)+abs(z.y))) for z in vector), Q(0))


def parent_envelopes(u, q, nu, length):
    """Rational Fourier upper bounds, with their exact remaining integrals."""
    G = L = Gtail = Ltail = Gtail_rate = Ltail_rate = Q(0)
    for k, vector in s.modes(u).items():
        rate = sum(x*x for x in k)
        if not rate:
            continue
        d = sum(abs(x) for x in k)
        size = coefficient_size(vector)
        value = size*q**rate
        G += d*value
        L += d*d*value
        Gtail += d*value/(nu*rate)
        Ltail += d*d*value/(nu*rate)
        # Differentiate each q^rate with q'=-nu*q.
        Gtail_rate += d*size/(nu*rate)*rate*q**(rate-1)*(-nu*q)
        Ltail_rate += d*d*size/(nu*rate)*rate*q**(rate-1)*(-nu*q)
    s.require(Gtail_rate == -G and Ltail_rate == -L,
              'remaining parent integrals decrease at their exact current rates')
    return dict(G=G, L=L, Gtail=Gtail, Ltail=Ltail,
                kappa=4*G+length*L, log_weight=4*Gtail+length*Ltail)


def source_lifetime_upper(u, q, nu):
    total = instantaneous = Q(0)
    for (_, rate), vector in nr.rc.source_blocks(u, u).items():
        s.require(rate > 0, 'every nonzero source block has positive original heat rate')
        size = coefficient_size(vector)*q**rate
        instantaneous += size
        total += size/(nu*rate)
    h = hp.heat_at(u, q)
    source = s.nonlinear(h)
    s.require(s.inner(source, source) <= instantaneous**2,
              'the grouped original source has the stated integrable norm envelope')
    return total


def complete_remainder_fixture(u0, q, nu, length, sign):
    h = hp.heat_at(u0, q)
    b = s.vector_scale(Q(sign, 5), hp.positive_seed())
    u = s.vector_add(h, b)
    direction = s.vector_add(s.vector_scale(-nu, s.minus_laplacian(b)), s.nonlinear(u))
    Ab = s.minus_laplacian(b)
    Z, D, E = s.inner(b, Ab), s.inner(Ab, Ab), s.inner(b, b)
    Ebar = 4*s.inner(u0, u0)
    s.require(E <= Ebar, 'off-trajectory fixture satisfies the required kinetic envelope')
    H, C = s.forecast(b, nu), nr.rc.capacity(b, nu)
    Zd = 2*s.inner(Ab, direction)
    Hd, Cd = s.forecast_derivative(b, direction, nu), nr.rc.derivative(b, direction, nu)
    if sign == 1:
        observations = {}
        for k in (-2, -1, 1, 2):
            v = s.vector_add(b, s.vector_scale(k, direction))
            observations[k] = (s.inner(v, s.minus_laplacian(v)),
                               s.forecast(v, nu), nr.rc.capacity(v, nu))
        polarized = tuple((8*(observations[1][j]-observations[-1][j])
                           -observations[2][j]+observations[-2][j])/12 for j in range(3))
        s.require(polarized == (Zd, Hd, Cd),
                  'independent polynomial polarization checks every physical derivative slot')
    W, Wd, changing_weight = nr.common_weight(dict(Z=Z, H=H, C=C, Zd=Zd, Hd=Hd, Cd=Cd))
    env = parent_envelopes(u0, q, nu, length)
    B = nr.rc.capacity(h, nu)
    loss = s.inner(s.nonlinear(h), s.nonlinear(h))/nu
    s.require(nr.rc.derivative(h, s.vector_scale(-nu, s.minus_laplacian(h)), nu) == -loss,
              'the original source capacity keeps its original heat age')
    tail = Ebar*env['Ltail']/length+2*B
    f0 = Ebar*env['L']/length+2*loss
    # This is the derivative divided by a, so no exponential approximation.
    energy_storage_rate = Zd-f0-env['kappa']*(Z+tail)
    g = s.cubic(b)
    strengthened_margin = energy_storage_rate+Q(3, 2)*nu*D-2*g+env['kappa']*tail
    s.require(strengthened_margin <= 0,
              'full physical estimate retains the extra cooling of unspent credit')
    # The trial normalized storage still uses the complete coupled tangent.
    normalized_defect = Wd+2*g-nu*D/2-env['kappa']*(W+tail)-f0
    s.require(changing_weight != 0, 'the normalization is genuinely evolving')
    return {'q': str(q), 'nu': str(nu), 'length': str(length),
            'kinetic_envelope': '4 times original energy; valid relaxed source bound',
            'energy_estimate_margin': str(strengthened_margin),
            'normalized_trial_defect': str(normalized_defect),
            'trial_scope': 'state algebra only; no claim that this fixture is a reached state'}


def delayed_source_family(A, B, nu):
    cx, cy = mode((1, 0, 0), 1), mode((0, 1, 0), 1)
    sx, sy = mode((1, 0, 0), 1, True), mode((0, 1, 0), 1, True)
    psi = f.add(cx, cy)
    u = [f.scale(A, sy), f.scale(-A, sx),
         f.scale(B, f.add(f.mul(psi, psi), {f.ORIGIN: -f.QQ_I.one}))]
    f.equal(f.trace(f.jac(u)), {}, 'the full initial field is solenoidal')
    for v in s.nonlinear(u):
        f.equal(v, {}, 'the initial projected nonlinearity vanishes exactly')
    expected_capacity = A*A*B*B/(120*nu*nu)
    s.require(nr.rc.capacity(u, nu) == expected_capacity > 0,
              'zero initial nonlinear source can have strictly positive heat-source lifetime')
    rows = []
    shape = f.mul(f.mul(sx, sy), f.add(cx, f.scale(-1, cy)))
    heat_tangent = s.vector_scale(-nu, s.minus_laplacian(u))
    plus = s.nonlinear(s.vector_add(u, heat_tangent))
    minus = s.nonlinear(s.vector_add(u, s.vector_scale(-1, heat_tangent)))
    source_tangent = s.vector_scale(Q(1, 2), s.vector_add(plus, s.vector_scale(-1, minus)))
    for component in source_tangent[:2]:
        f.equal(component, {}, 'the first heat-source derivative stays vertical')
    f.equal(source_tangent[2], f.scale(-4*nu*A*B, shape),
            'independent nonlinear polarization gives the actual second remainder derivative')
    for q in (Q(1), Q(3, 4), Q(1, 2)):
        h = hp.heat_at(u, q)
        n = s.nonlinear(h)
        f.equal(n[0], {}, 'horizontal heat parent remains autonomous')
        f.equal(n[1], {}, 'horizontal pressure cancellation is exact')
        f.equal(n[2], f.scale(2*A*B*q**3*(q*q-1), shape),
                'unequal original heat rates generate the vertical source')
        size = A*A*B*B*q**6*(1-q*q)**2/2
        s.require(s.inner(n, n) == size, 'exact generated heat source norm')
        tail = A*A*B*B/(2*nu*nu)*(q**6/6-q**8/4+q**10/10)
        s.require(nr.rc.capacity(h, nu) == tail, 'the same source reserve at every heat age')
        # Any vertical, z-independent remainder has identically zero self-source.
        residual = [{}, {}, f.add(f.scale(q, shape), f.scale(q*q, psi))]
        for v in s.nonlinear(residual):
            f.equal(v, {}, 'vertical remainder cannot advect itself')
        s.require(s.cubic(residual) == 0, 'generated remainder stretching vanishes in this class')
        rows.append({'q': str(q), 'source_squared': str(size), 'remaining_capacity': str(tail)})
    return {'A': str(A), 'B': str(B), 'nu': str(nu),
            'initial_capacity': str(expected_capacity),
            'second_remainder_derivative_coefficient': str(-4*nu*A*B), 'ages': rows}


def main():
    seed = s.real_field(s.seed())
    rates = [parent_envelopes(seed, q, Q(2, 7), Q(3, 2)) for q in (Q(1), Q(3, 4), Q(1, 2))]
    s.require(rates[0]['log_weight'] > rates[1]['log_weight'] > rates[2]['log_weight'] > 0,
              'the finite all-time weight decreases without resetting')
    source_lifetime_upper(seed, Q(1), Q(2, 7))
    fixtures = [complete_remainder_fixture(seed, Q(3, 4), Q(1), Q(1), 1),
                complete_remainder_fixture(seed, Q(1, 2), Q(2, 7), Q(3, 2), -1)]
    delayed = [delayed_source_family(Q(2), Q(3), Q(1)),
               delayed_source_family(Q(-5), Q(7, 3), Q(2, 7))]
    # A single Laplace-eigenvalue planar flow has no projected heat source at any age.
    zero_source = [mode((0, 1, 0), 1), mode((1, 0, 0), 1), {}]
    s.require(not nr.rc.source_blocks(zero_source, zero_source),
              'all original heat-source blocks vanish in the source-free control')
    s.require(source_lifetime_upper(zero_source, Q(1), Q(1)) == nr.rc.capacity(zero_source) == 0,
              'the source-funded allowance is exactly zero for a nonconstant heat solution')
    print(json.dumps({'status': 'all exact checks passed', 'physical_fixtures': fixtures,
                      'delayed_source_family': delayed,
                      'scope': 'finite algebra; all-time PDE reserve and triangular solution analytic'}, indent=2))


if __name__ == '__main__':
    main()
