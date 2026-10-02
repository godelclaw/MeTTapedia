#!/usr/bin/env python3
"""Complete derivative test of a signed covariance--Poisson correction.

The two principal Laplacians cancel covariance work. Every remaining
covariance and observer derivative is retained. Exact planar input data
reject universal payment by this correction with the stated energy cube.
Smooth-solution and short-interval conclusions are analytic in README.md.
"""

import json
from fractions import Fraction as Q

import receiver_transport_covariance as t
from refeeding_stretching import linear_cubic_term

s, f = t.s, t.f
GAMMA = Q(1, 10**8)


def inverse_laplacian(blocks):
    s.require(all(any(k) for k, _ in blocks), 'observer has no constant mode')
    return {key: tuple(x/sum(j*j for j in key[0]) for x in a)
            for key, a in blocks.items()}


def laplacian(blocks):
    return t.cleaned({key: tuple(-sum(j*j for j in key[0])*x for x in a)
                      for key, a in blocks.items()})


def partial(blocks, j):
    return t.cleaned({key: tuple(f.II*key[0][j]*x for x in a)
                      for key, a in blocks.items()})


def observed(w, direction=None):
    v, n = t.heat(w), s.source_blocks(w, w)
    tau, observer = t.covariance(w), t.source_observer(v, n)
    if direction is None:
        return tau, observer
    dn = s.add_blocks(s.source_blocks(w, direction), s.source_blocks(direction, w))
    dtau = t.add_tensors(t.covariance(direction, w), t.covariance(w, direction))
    dobserver = s.add_blocks(t.source_observer(t.heat(direction), n),
                            t.source_observer(v, dn))
    return tau, observer, dtau, dobserver


def pairing(tau, observer, nu):
    return t.stress_pair(tau, inverse_laplacian(observer), nu)/nu


def correction(w, nu=Q(1)):
    return pairing(*observed(w), nu)


def correction_derivative(w, direction, nu=Q(1)):
    tau, observer, dtau, dobserver = observed(w, direction)
    return pairing(dtau, observer, nu)+pairing(tau, dobserver, nu)


def complete_split(u, nu=Q(1)):
    w = s.oscillation(u)
    h = s.oscillation(s.nonlinear(u))
    heat = s.vector_scale(-nu, s.minus_laplacian(w))
    tau, observer, dtau_heat, dobserver_heat = observed(w, heat)
    _, _, dtau_nl, dobserver_nl = observed(w, h)
    cov_work = 2*t.stress_pair(tau, observer, nu)
    covariance_principal = pairing(t.scale(nu, laplacian(tau)), observer, nu)
    observer_principal = pairing(tau, t.scale(nu, laplacian(observer)), nu)
    s.require(covariance_principal == observer_principal == -cov_work/2,
              'the two principal Laplacians each pay exactly half the covariance work')

    gradient_covariance = t.add_tensors(*(t.covariance([f.diff(a, j) for a in w])
                                         for j in range(3)))
    cov_diff = pairing(t.scale(-2*nu, gradient_covariance), observer, nu)
    observer_diff = s.add_blocks(dobserver_heat, t.scale(-nu, laplacian(observer)))
    v, n = t.heat(w), s.source_blocks(w, w)
    G = s.add_blocks(*(s.source_blocks([f.diff(a, j) for a in w],
                                      [f.diff(a, j) for a in w]) for j in range(3)))
    explicit_diff = t.scale(-2*nu, s.add_blocks(
        t.source_observer(v, G),
        *(t.source_observer(partial(v, j), partial(n, j)) for j in range(3))))
    s.require(observer_diff == explicit_diff,
              'observer diffusion keeps all product derivatives and the source defect G')
    observer_diff_work = pairing(tau, observer_diff, nu)
    cov_nl = pairing(dtau_nl, observer, nu)
    observer_nl = pairing(tau, dobserver_nl, nu)
    direct = correction_derivative(w, s.vector_add(heat, h), nu)
    s.require(direct+cov_work == cov_diff+observer_diff_work+cov_nl+observer_nl,
              'the complete actual derivative retains all four remainder works')
    s.require(pairing(dtau_heat, observer, nu)+pairing(tau, dobserver_heat, nu)
              == -cov_work+cov_diff+observer_diff_work, 'independent pure-heat identity')
    return {'correction': correction(w, nu), 'covariance_work': cov_work,
            'covariance_diffusion_defect': cov_diff,
            'observer_diffusion_defect': observer_diff_work,
            'covariance_nonlinear': cov_nl, 'observer_nonlinear': observer_nl,
            'complete_rate': direct}


def planar_belt(length):
    weights = (Q(4, 5), Q(3, 5), Q(-1, 5), Q(2, 5))
    horizontal = ((1, 0), (1, -1), (2, 0), (2, -1))
    return s.real_field({(length*x, length*y): (-y*c, x*c, Q(0))
                         for (x, y), c in zip(horizontal, weights)})


def trial_reserve(u, nu):
    w = s.oscillation(u)
    return s.storage(w, nu)+correction(w, nu)+GAMMA*s.inner(u, u)**3/nu**4


def belt_check(length, amplitude, nu):
    w = planar_belt(length)
    f.equal(f.trace(f.jac(w)), {}, 'planar input is exactly solenoidal')
    s.require(not w[2] and not any(s.vertical_mean(w)),
              'all initial velocity is horizontal and the initial vertical mean vanishes')
    s.require(all(k[2]**2*length**2 <= sum(j*j for j in k) for k in s.modes(w)),
              'entire spectrum lies in the belt of relative width at most 1/length')
    h = s.oscillation(s.nonlinear(w))
    Aw = s.minus_laplacian(w)
    E, Z, D = s.inner(w, w), s.inner(Aw, w), s.inner(Aw, Aw)
    b = s.forecast_derivative(w, h)-s.inner(h, h)
    p = correction_derivative(w, h)
    q = 6*GAMMA*E**2*Z
    s.require(s.cubic(w) == s.forecast(w) == correction(w) == 0,
              'odd observations vanish on the original vertical band')
    s.require(s.capacity_derivative(w, h) == correction_derivative(w, s.vector_scale(-1, Aw)) == 0,
              'both fifth-degree terms vanish initially, with all outputs retained')
    s.require(b < 0 and p > 0, 'negative quartic term competes with positive sixth-degree correction')
    rate = -nu*amplitude**2*D+amplitude**4*b/nu+amplitude**6*(p-q)/nu**3
    u = s.vector_scale(amplitude, w)
    full_source = s.nonlinear(u)
    full_direction = s.vector_add(full_source, s.vector_scale(-nu, s.minus_laplacian(u)))
    receiver_direction = s.oscillation(full_direction)
    actual = (s.storage_derivative(u, receiver_direction, nu)
              + correction_derivative(u, receiver_direction, nu)
              - 6*GAMMA*s.inner(u, u)**2*s.inner(s.minus_laplacian(u), u)/nu**3
              + 2*s.cubic(u))
    s.require(actual == rate, 'direct full physical tangent verifies viscosity and amplitude scaling')
    reserve = trial_reserve(u, nu)
    s.require(reserve > 0, 'failure is tested inside strictly positive total storage')
    ratio = 2*rate/(nu*amplitude**2*D)
    if length in (2, 16):
        s.require(p > q and ratio > (88 if length == 2 else 13),
                  'corrected total budget exceeds half the full dissipation')
    else:
        s.require(length == 32 and p < q and ratio < -2,
                  'thinner tested profile has favorable initial payment at every amplitude')
    generated_stretching = linear_cubic_term(w, s.nonlinear(w))
    s.require(generated_stretching > 0, 'full actual nonlinearity initially generates stretching')
    return {'length': length, 'nu': nu, 'amplitude': amplitude,
            'E': E, 'Z': Z, 'D': D, 'quartic': b, 'sixth_degree_production': p,
            'energy_cube_loss': q, 'reserve': reserve, 'rate_over_half_dissipation': ratio,
            'initial_full_stretching_derivative': generated_stretching}


def polarization_check():
    u, nu = planar_belt(2), Q(2, 7)
    source = s.nonlinear(u)
    direction = s.vector_add(source, s.vector_scale(-nu, s.minus_laplacian(u)))
    w_direction = s.oscillation(direction)
    # Central differences are exact for the derivative of a polynomial of degree <=6.
    differences = {j: trial_reserve(s.vector_add(u, s.vector_scale(j, direction)), nu)
                      - trial_reserve(s.vector_add(u, s.vector_scale(-j, direction)), nu)
                   for j in (1, 2, 3)}
    polarized = (45*differences[1]-9*differences[2]+differences[3])/60
    direct = (s.storage_derivative(u, w_direction, nu)
              + correction_derivative(u, w_direction, nu)
              - 6*GAMMA*s.inner(u, u)**2*s.inner(s.minus_laplacian(u), u)/nu**3)
    s.require(polarized == direct, 'independent degree-six polarization checks the complete reserve derivative')
    s.require(any(s.vertical_mean(source)), 'polarization retains genuinely generated mean motion')
    return polarized


def main():
    r = s.real_field(s.seed())
    full = s.vector_add(r, s.vector_scale(Q(-1, 10), s.nonlinear(r)))
    splits = [complete_split(w) for w in s.matched_fields()]
    s.require(splits[0]['covariance_diffusion_defect'] < 0
              < splits[1]['covariance_diffusion_defect'], 'PSD diffusion covariance gives either signed work')
    splits.append(complete_split(full, Q(2, 7)))
    belts = [belt_check(2, Q(64), Q(1)), belt_check(16, Q(512, 7), Q(2, 7)),
             belt_check(32, Q(1), Q(1))]
    result = {'status': 'all exact checks passed', 'splits': splits, 'belts': belts,
              'polarized_derivative': polarization_check(),
              'scope': 'finite exact algebra; smooth-interval interpretation analytic',
              'failed_claim': 'J plus the unit Poisson correction universally pays the half-dissipation budget',
              'retained': 'the original J and the controlled-history theorem remain unchanged'}
    print(json.dumps(result, default=str, indent=2))


if __name__ == '__main__':
    main()
