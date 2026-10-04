#!/usr/bin/env python3
"""Complete filtered NS identities for an evolving-parent reserve payment.

The Gaussian filter is applied to the current full fluid. Every nonlinear
output, the filter feedback and the nonorthogonal cross energy are retained.
The general kernel estimates and all-prefix reserve bound are analytic in
README.md, not consequences of these fixtures or Lean certificates.
"""

import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path

import sympy as s
import pressure_history_source as f
import heat_work_reserve as reserve
from heat_work_parent_payment import heat
from heat_covariance_renewal import tensor_divergence
from cyclic_pressure_history import velocity_time_jets
from generated_fourth_moment import pressure, mixed_pressure, vector_pair, fourth_work
from heat_remainder_pressure import plus, times, adv, solenoidal, require, same, mean


def gradient_pair(u, v):
    return sum((vector_pair([f.diff(row, j) for row in u],
                            [f.diff(row, j) for row in v]) for j in range(3)), Q(0))


def physical_fixture(u, q, nu, check_heat_profile=False):
    v = heat(u, q)
    w = plus(u, times(-1, v))
    source = reserve.nonlinear(u)
    parent_source = heat(source, q)
    g = plus(reserve.nonlinear(v), times(-1, parent_source))
    B = times(-1, solenoidal(plus(adv(v, w), adv(w, v))))
    self_source = reserve.nonlinear(w)
    tangent = velocity_time_jets(u, nu, 1)[0][1]
    vt = heat(tangent, q)
    wt = plus(tangent, times(-1, vt))
    same(vt, plus(times(nu, [f.lap(row) for row in v]), parent_source),
         'The current parent evolves with the full internally generated source')
    same(wt, plus(times(nu, [f.lap(row) for row in w]), self_source, B, g),
         'The unresolved equation retains the filter feedback and every interaction')
    f.equal(pressure(u), f.add(pressure(v), pressure(w), mixed_pressure(v, w)),
            'The complete canonical pressure is reconstructed from all three terms')
    require(any(parent_source) and any(g), 'Both retained filter-source terms are nonzero')
    omitted = plus(wt, times(-1, plus(times(nu, [f.lap(row) for row in w]),
                                     self_source, B, reserve.nonlinear(v))))
    same(omitted, times(-1, parent_source), 'Omitting the evolving-filter feedback changes the actual equation')

    tau = [[f.add(heat([f.mul(u[i], u[j])], q)[0], f.scale(-1, f.mul(v[i], v[j])))
            for j in range(3)] for i in range(3)]
    same(g, solenoidal(tensor_divergence(tau)), 'The apparent fine source is exactly the retained covariance divergence')

    energy, coarse_energy, remainder_energy = (vector_pair(z, z) for z in (u, v, w))
    cross = vector_pair(v, w)
    Z, Zv = gradient_pair(u, u), gradient_pair(v, v)
    exchange = vector_pair(v, parent_source)
    coarse_rate = 2*vector_pair(v, vt)
    full_rate = 2*vector_pair(u, tangent)
    variance_rate = full_rate-coarse_rate
    require(full_rate == -2*nu*Z < 0, 'Only viscosity removes the full kinetic energy')
    require(coarse_rate == -2*nu*Zv+2*exchange,
            'Resolved energy retains the signed internal exchange')
    require(variance_rate == -2*nu*(Z-Zv)-2*exchange,
            'The same exchange is paid with opposite sign by the covariance energy')
    require(energy == coarse_energy+remainder_energy+2*cross and cross > 0,
            'The heat split has a nonzero cross energy; it is not orthogonal')
    require(energy-coarse_energy == mean(f.trace(tau)),
            'Integrated covariance is the nonnegative unresolved energy reserve')
    require(0 < remainder_energy <= energy-coarse_energy <= energy and 0 <= Zv <= Z,
            'Filter contraction controls both energy and the unresolved diffusion')

    work, diffusion, fourth = fourth_work(w)
    cubic = [f.mul(f.dot(w, w), row) for row in w]
    physical_fourth_rate = vector_pair(cubic, wt)
    mixed_work = -vector_pair(cubic, plus(adv(w, v), f.grad(mixed_pressure(v, w))))
    source_work = vector_pair(cubic, g)
    require(physical_fourth_rate == -nu*diffusion+work+mixed_work+source_work,
            'The actual fourth moment retains self pressure, mixed pressure and filter feedback')
    profile_report = None
    if check_heat_profile:
        z = reserve.heat(w)
        actual_profile = reserve.variation(z, reserve.heat(wt))
        separate_profiles = [reserve.variation(z, reserve.heat(direction)) for direction in
                             (times(nu, [f.lap(row) for row in w]), self_source, B, g)]
        require(s.expand(actual_profile-sum(separate_profiles)) == 0,
                'All physical directions reconstruct the whole heat-work variation before the selector')
        require(s.expand(separate_profiles[0]+nu*reserve.q*s.diff(reserve.profile(z), reserve.q)) == 0,
                'Actual diffusion agrees with the complete heat-age shift')
        profile_report = dict(full_variation=str(s.factor(actual_profile)),
                              scope='Pointwise linearity of the smooth pressure-work variation; no additivity of the positive-part reserve derivative is assumed')
    return dict(heat_parameter=str(q), viscosity=str(nu), full_energy=str(energy),
                resolved_energy=str(coarse_energy), remainder_energy=str(remainder_energy),
                cross_energy=str(cross), resolved_exchange=str(exchange),
                variance_energy=str(energy-coarse_energy), full_energy_rate=str(full_rate),
                resolved_energy_rate=str(coarse_rate), variance_energy_rate=str(variance_rate),
                pressure_work=str(work), mixed_fourth_work=str(mixed_work),
                source_fourth_work=str(source_work), fourth_diffusion=str(diffusion),
                input_modes=len(set().union(*u)), full_source_modes=len(set().union(*source)),
                heat_variation=profile_report)


def reserve_algebra():
    a, nu, H, E, Z = s.symbols('a nu H E Z', positive=True)
    cs, cm, ct = s.symbols('c_s c_m c_t', nonnegative=True)
    source_cost = cs*H**3*a**(-s.Rational(11, 2))*E**3*Z
    mixed_cost = cm*nu**(-7)*a**(-4)*E**5*Z
    torus_cost = ct*nu**(-1)*a**(-s.Rational(5, 4))*E**2*Z
    Qenergy = (cs*H**3/(8*nu)*a**(-s.Rational(11, 2))*E**4
               +cm/(12*nu**8)*a**(-4)*E**6
               +ct/(6*nu**2)*a**(-s.Rational(5, 4))*E**3)
    require(s.simplify(s.diff(Qenergy, E)*(-2*nu*Z)+source_cost+mixed_cost+torus_cost) == 0,
            'One nonnegative full-energy reserve pays the complete constant losses')
    require(s.simplify((a**(-s.Rational(13, 8))*E)**2
                       *(a**(-s.Rational(9, 8))*s.sqrt(E*Z))**2
                       -a**(-s.Rational(11, 2))*E**3*Z) == 0,
            'The two source estimates retain only one power of dissipation')
    require(s.simplify((a**(-s.Rational(5, 4))*s.sqrt(E))**2
                       *(a**(-s.Rational(3, 4))*s.sqrt(Z))**2*E**4
                       -a**(-4)*E**5*Z) == 0,
            'The two parent estimates retain only one power of dissipation')
    # These powers follow from the actual three-dimensional smoothed
    # multipliers: L4 is the interpolation of kernel L2 and L-infinity.
    require((s.Rational(5, 4)+2)/2 == s.Rational(13, 8)
            and (s.Rational(3, 4)+s.Rational(3, 2))/2 == s.Rational(9, 8),
            'Smoothed derivative and order-zero kernel exponents')
    return dict(energy_reserve=str(Qenergy), paid_cost=str(source_cost+mixed_cost+torus_cost),
                fixed_scale_derivative=str(s.factor(s.diff(Qenergy, a))),
                scope='c_s and c_m are fixed positive analytic estimate constants; c_t may be zero on R3. These identities do not assert unit constants in the PDE inequalities.')


def checks():
    base = reserve.weighted_datum(2, (1, 1, 1))
    W = plus(base, times(Q(1, 4), reserve.nonlinear(base)))
    A = reserve.nonlinear(reserve.weighted_datum(0, (1, 1, 1)))
    results = {}
    for name, datum in (('oblique', W), ('reversed_oblique', times(-1, W)), ('cyclic_source', A)):
        results[name] = [physical_fixture(datum, q, Q(2, 7), name == 'oblique' and q == Q(1, 2))
                         for q in (Q(1, 2), Q(3, 4))]
    for i in range(2):
        left, right = results['oblique'][i], results['reversed_oblique'][i]
        require(Q(left['resolved_exchange']) < 0 < Q(right['resolved_exchange'])
                and Q(left['resolved_exchange']) == -Q(right['resolved_exchange']),
                'The same energy and scale permit either direction of internal transfer')
        require(left['full_energy'] == right['full_energy'] and left['cross_energy'] == right['cross_energy'],
                'The signed-transfer test retains equal energy and the same nonorthogonal split')
    report = dict(physical_cases=results, reserve_algebra=reserve_algebra(),
                  scope='Exact complete Fourier and reserve identities; the arbitrary-data evolving-parent estimates and continuation consequence are analytic in README.md, not Lean-certified')
    root = Path(__file__).resolve().parent
    sources = ['evolving_filter_parent_payment.py', 'heat_work_parent_payment.py',
               'heat_covariance_renewal.py', 'heat_work_reserve.py', 'pressure_history_source.py',
               'heat_remainder_pressure.py', 'generated_fourth_moment.py', 'cyclic_pressure_history.py',
               'pressure_gradient_stock.py', 'pressure_quadratic_storage.py']
    report['source_sha256'] = {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in sources}
    return report


if __name__ == '__main__':
    print(json.dumps(checks(), indent=2))
