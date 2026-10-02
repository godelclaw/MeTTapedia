#!/usr/bin/env python3
"""Exact test of a signed heat-lifetime correction for receiver stretching.

All convolutions and pressure outputs are retained. The Fourier identities
are exact; their smooth NS interval interpretation is analytic in README.md.
The correction is a candidate history reserve, not an established budget.
"""

import json
from fractions import Fraction as Q

import pressure_history_source as f
from cellular_parent_refeeding import seed
from cellular_transfer_reversal import real_field
from generated_mean_enstrophy import (
    minus_laplacian, oscillation, second_gradient_squared,
)
from reciprocal_pattern_cycles import inner, require, vector_add, vector_scale
from refeeding_stretching import cubic, linear_cubic_term, nonlinear, vertical_mean


def modes(u):
    keys = set().union(*(component.keys() for component in u))
    return {k: tuple(component.get(k, f.ZERO) for component in u) for k in keys}


def dot(a, b):
    return sum((x*y for x, y in zip(a, b)), f.ZERO)


def curl_mode(k, a):
    return tuple(f.II*(k[(i+1) % 3]*a[(i+2) % 3]
                      - k[(i+2) % 3]*a[(i+1) % 3]) for i in range(3))


def heat_trilinear(u, v, w, nu=Q(1), integrate=True):
    """2 integral_0^infinity <curl H_s u, grad H_s v curl H_s w> ds.

    H_s=exp(nu*s*Delta). With integrate=False return the unweighted
    physical trilinear observation, using the same complete triads.
    """
    require(nu > 0, 'positive viscosity')
    a, b, c = modes(u), modes(v), modes(w)
    a = {k: curl_mode(k, z) for k, z in a.items()}
    c = {k: curl_mode(k, z) for k, z in c.items()}
    total = f.ZERO
    for k, aa in a.items():
        for ell, bb in b.items():
            m = tuple(-x-y for x, y in zip(k, ell))
            if m not in c:
                continue
            term = f.II*dot(aa, bb)*dot(ell, c[m])
            if integrate:
                rate = sum(x*x for wave in (k, ell, m) for x in wave)
                if rate == 0:
                    require(term == 0, 'constant triad has zero curls and strain')
                    continue
                term *= f.QQ_I(2)/(nu*rate)
            total += term
    require(total.y == 0, 'complete real fields have a real trilinear integral')
    return Q(str(total.x))


def forecast(w, nu=Q(1)):
    return heat_trilinear(w, w, w, nu)


def forecast_derivative(w, tangent, nu=Q(1)):
    return (heat_trilinear(tangent, w, w, nu)
            + heat_trilinear(w, tangent, w, nu)
            + heat_trilinear(w, w, tangent, nu))


def dilation(u, frequency):
    return [{tuple(frequency*j for j in k): a for k, a in component.items()}
            for component in u]


def triad(a, k, b, ell, c, m):
    return f.II*dot(curl_mode(k, a), b)*dot(ell, curl_mode(m, c))


def quartic_heat(u1, u2, u3, u4, nu=Q(1), integrate=True):
    """Polarization of the heat forecast of nonlinear receiver renewal.

    Its first denominator uses the generated mode's actual wave number.
    Its second uses the four ORIGINAL heat rates, not the generated mode's
    heat rate. The Leray projection and non-mean output projection remain.
    """
    require(nu > 0, 'positive viscosity')
    a, b, c, d = map(modes, (u1, u2, u3, u4))
    total = f.ZERO
    for p, aa in a.items():
        for q, bb in b.items():
            r = tuple(x+y for x, y in zip(p, q))
            if r[2] == 0:
                continue
            rr = sum(x*x for x in r)
            source = tuple(-f.II*dot(aa, q)*(bb[i]-r[i]*dot(r, bb)/rr)
                           for i in range(3))
            if not any(source):
                continue
            for k, cc in c.items():
                ell = tuple(-x-y for x, y in zip(r, k))
                if ell not in d:
                    continue
                dd = d[ell]
                value = (triad(source, r, cc, k, dd, ell)
                         + triad(cc, k, source, r, dd, ell)
                         + triad(cc, k, dd, ell, source, r))
                rate = rr+sum(x*x for wave in (k, ell) for x in wave)
                factor = f.QQ_I(2)/(nu*rate)
                if integrate:
                    original_rate = sum(x*x for wave in (p, q, k, ell) for x in wave)
                    factor /= nu*original_rate
                total += factor*value
    require(total.y == 0, 'complete real fields have a real quartic forecast')
    return Q(str(total.x))


def generation_reserve(w, nu=Q(1)):
    return quartic_heat(w, w, w, w, nu)


def generation_derivative(w, tangent, nu=Q(1)):
    return sum(quartic_heat(*(tangent if i == j else w for i in range(4)), nu=nu)
               for j in range(4))


SELF_RETURN = Q(46234957, 600600000)
MEAN_RETURN = Q(-4331, 75000)


def checks():
    r = real_field(seed())
    N = nonlinear(r)
    require(vertical_mean(r) == [{}, {}, {}], 'initial receiver has zero vertical mean')
    require({abs(k[2]) for k in modes(r)} == {1}, 'all initial modes have vertical frequency one')
    require(cubic(r) == forecast(r) == 0, 'both initial stretching and heat forecast vanish')
    require(forecast_derivative(r, oscillation(N)) == SELF_RETURN > 0,
            'complete generated non-mean modes increase the heat forecast')
    require(linear_cubic_term(r, oscillation(N)) == Q(6252773, 5460000),
            'the funded seed has genuinely positive first stretching production')
    require(forecast_derivative(r, vertical_mean(N)) == MEAN_RETURN < 0,
            'the generated mean is retained and has a different contribution')
    require(forecast_derivative(r, N) == SELF_RETURN+MEAN_RETURN,
            'mean and non-mean variations reconstruct the full forecast derivative')
    require(second_gradient_squared(r) == Q(631, 20), 'original full dissipation norm')

    records = []
    for delta in (Q(-1, 10), Q(1, 10)):
        u = vector_add(r, vector_scale(delta, N))
        w = oscillation(u)
        Nu = nonlinear(u)
        nu = Q(2, 7)
        rhs = vector_add(Nu, vector_scale(-nu, minus_laplacian(u)))
        f.equal(f.trace(f.jac(u)), {}, 'actual smooth datum is divergence free')
        f.equal(f.trace(f.jac(rhs)), {}, 'full positive-viscosity tangent is divergence free')
        require(inner(u, Nu) == 0, 'complete internal transfer conserves kinetic energy')
        require(inner(minus_laplacian(u), Nu) == cubic(u),
                'independent vorticity and energy-production observations agree')
        require(heat_trilinear(w, w, w, integrate=False) == cubic(w),
                'triad observation equals independent physical-space convolution')
        require(forecast(w) == delta*SELF_RETURN, 'opposite phases have opposite signed forecast')
        heat_rate = forecast_derivative(w, vector_scale(-nu, minus_laplacian(w)), nu)
        require(heat_rate == -2*cubic(w), 'heat evolution cancels the full cubic cost exactly')
        renewal = forecast_derivative(w, oscillation(Nu), nu)
        require(forecast_derivative(w, oscillation(rhs), nu)+2*cubic(w) == renewal,
                'actual equation retains all nonlinear receiver renewal')
        records.append({'delta': str(delta), 'forecast_at_nu_one': str(forecast(w)),
                        'renewal_at_nu_two_sevenths': str(renewal)})
    require(records[0]['renewal_at_nu_two_sevenths']
            == records[1]['renewal_at_nu_two_sevenths'],
            'opposite forecasts conceal equal positive renewal')
    require(Q(records[0]['renewal_at_nu_two_sevenths']) > 0,
            'both hidden phases replenish the correction')

    scaled = []
    for nu, frequency in ((Q(1, 7), 1), (Q(1), 1), (Q(3), 3)):
        amplitude = 16*nu*frequency
        u = vector_scale(amplitude, dilation(r, frequency))
        Nu = nonlinear(u)
        renewal = forecast_derivative(u, oscillation(Nu), nu)
        D = second_gradient_squared(u)
        require(renewal == amplitude**4*frequency**2*SELF_RETURN/nu,
                'complete source and receiver give the predicted quartic scaling')
        require(D == amplitude**2*frequency**4*Q(631, 20),
                'full dissipation has the predicted scaling')
        require(forecast(u, nu) == cubic(u) == 0, 'scaled original forecast remains empty')
        require(renewal-nu*D/2 > 0,
                'actual initial tangent violates the heat-correction half-dissipation budget')
        scaled.append({'nu': str(nu), 'frequency': frequency, 'amplitude': str(amplitude),
                       'renewal_over_half_dissipation': str(renewal/(nu*D/2))})
    return {'self_return_at_nu_one': str(SELF_RETURN),
            'mean_return_at_nu_one': str(MEAN_RETURN), 'phases': records,
            'scaled_positive_viscosity_data': scaled,
            'failed_claim': 'H(w(t))+2 integral g(w) <= H(w(0))+(nu/2) integral D',
            'scope': 'exact actual initial tangents; short-time PDE implication analytic',
            'still_open': 'original-datum reserve paying the nonlinear renewal over all histories'}


def generation_checks():
    r = real_field(seed())
    Nside = oscillation(nonlinear(r))
    initial_stock = Q(9212971, 2402400000)
    require(generation_reserve(r) == initial_stock > 0,
            'first generated interactions have a nonzero original quartic allowance')
    require(quartic_heat(r, r, r, r, integrate=False) == SELF_RETURN,
            'independent four-parent expansion reconstructs the nonlinear renewal')
    require(generation_derivative(r, vector_scale(-1, minus_laplacian(r))) == -SELF_RETURN,
            'diffusion spends the quartic allowance at precisely the required rate')
    require(generation_derivative(r, Nside) == 0,
            'next nonlinear cost initially vanishes for the original seed')

    phases = []
    for delta in (Q(-1, 10), Q(1, 10)):
        w = vector_add(r, vector_scale(delta, Nside))
        Nw = oscillation(nonlinear(w))
        Qself = forecast_derivative(w, Nw)
        require(quartic_heat(w, w, w, w, integrate=False) == Qself,
                'four-parent expansion retains all generated pressure-corrected modes')
        require(generation_derivative(w, vector_scale(-1, minus_laplacian(w))) == -Qself,
                'heat cancellation holds with existing generated receivers')
        P = generation_derivative(w, Nw)
        phases.append({'delta': str(delta), 'H': str(forecast(w)),
                       'K': str(generation_reserve(w)), 'next_cost': str(P)})
    require(phases[0]['K'] == phases[1]['K'], 'opposite phases have the same quartic stock')
    require(Q(phases[0]['next_cost']) == -Q(phases[1]['next_cost']) > 0,
            'the next renewal has opposite signs at equal quartic stock')

    # This is a smooth actual NS datum with zero initial vertical mean.
    # The mean is not suppressed in its subsequent actual evolution.
    w = vector_add(r, vector_scale(Q(-1, 10), Nside))
    H, K = forecast(w), generation_reserve(w)
    P = generation_derivative(w, oscillation(nonlinear(w)))
    D = second_gradient_squared(w)
    amplitude = Q(64)
    require(amplitude**3*H+amplitude**4*K > 0,
            'the combined correction is strictly positive at the failing datum')
    require(amplitude**5*P-amplitude**2*D/2 > 0,
            'the second correction still fails its universal differential budget')

    # Retain the nonzero evolving mean when testing the complete identity.
    u = vector_add(r, vector_scale(Q(1, 10), nonlinear(r)))
    w = oscillation(u)
    source = oscillation(nonlinear(u))
    self_source = oscillation(nonlinear(w))
    cross = vector_add(source, vector_scale(-1, self_source))
    require(any(vertical_mean(u)) and any(cross), 'existing mean and its receiver coupling are nonzero')
    rhs = vector_add(source, vector_scale(-1, minus_laplacian(w)))
    actual_rate = forecast_derivative(w, rhs)+generation_derivative(w, rhs)+2*cubic(w)
    complete_defect = forecast_derivative(w, cross)+generation_derivative(w, source)
    require(actual_rate == complete_defect,
            'complete corrected history keeps the evolving mean and all nonlinear outputs')
    return {'initial_quartic_stock_at_nu_one': str(initial_stock), 'phases': phases,
            'positive_stock_counterexample_ratio': str(2*amplitude**3*P/D),
            'complete_defect': 'D H(w)[mean coupling] + D K(w)[non-mean N(u)]',
            'scope': 'local first-generation payment analytic; arbitrary-history payment remains open'}


def matched_summary_checks():
    r = real_field(seed())
    N = oscillation(nonlinear(r))
    keys = ((2, -1, 2), (3, -2, 2), (3, -1, 2))
    weights = (Q(1), Q(559, 2376), Q(-3311, 4335))
    y = [{}, {}, {}]
    for k, weight in zip(keys, weights):
        pair = (k, tuple(-j for j in k))
        component = [{ell: a for ell, a in row.items() if ell in pair} for row in N]
        y = vector_add(y, vector_scale(weight, component))
    require(forecast_derivative(r, y) == linear_cubic_term(r, y) == 0,
            'the selected generated phases cancel both current cubic observations')
    rows = []
    for sign in (-1, 1):
        w = vector_add(r, vector_scale(Q(sign, 10), y))
        f.equal(f.trace(f.jac(w)), {}, 'matched datum remains divergence free')
        require(vertical_mean(w) == [{}, {}, {}], 'both full data start with zero vertical mean')
        require(forecast(w) == cubic(w) == 0, 'both current stretching and signed forecast vanish')
        K = generation_reserve(w)
        P = generation_derivative(w, oscillation(nonlinear(w)))
        require(K > 0, 'the matched quartic reserve is strictly positive')
        Z = inner(minus_laplacian(w), w)
        rows.append({'sign': sign, 'energy': str(inner(w, w)), 'enstrophy': str(Z),
                     'D': str(second_gradient_squared(w)), 'quartic_stock': str(K),
                     'next_cost': str(P)})
    for key in ('energy', 'enstrophy', 'D', 'quartic_stock'):
        require(rows[0][key] == rows[1][key], 'opposite phases retain '+key)
    P, D = Q(rows[0]['next_cost']), Q(rows[0]['D'])
    require(P == -Q(rows[1]['next_cost']) > 0,
            'identical recorded summaries have opposite actual next reserve rates')
    ratio = 2*512**3*P/D
    require(ratio > 11, 'A=512nu gives a positive-stock counterexample with a strict margin')
    return {'selected_modes': keys, 'weights': [str(x) for x in weights], 'data': rows,
            'counterexample_amplitude': '512*nu',
            'next_cost_over_half_dissipation': str(ratio),
            'scope': 'two distinct smooth NS initial data; not two asserted times on one trajectory',
            'limitation': 'a bound covering both phases with further original-data allowance remains possible'}


if __name__ == '__main__':
    print(json.dumps({'first_correction': checks(), 'generated_allowance': generation_checks(),
                      'matched_summaries': matched_summary_checks()}, indent=2))
