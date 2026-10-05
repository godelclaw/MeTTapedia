#!/usr/bin/env python3
"""Complete feedback into stretching from a family of balanced NS data.

Polynomial identities retain every generated mode and pressure tangent.
The first Picard iterate is an auxiliary forecast, not another NS solution.
Actual-interval and uniform-remainder conclusions are analytic in README.md.
"""

import hashlib
import json
from pathlib import Path

import sympy as s

import shell_strain_return as sr
from cyclic_pressure_history import velocity_time_jets
import cyclic_pressure_history as cp

js, f, wh, og, Q, hr, am = sr.js, sr.f, sr.wh, sr.og, sr.Q, sr.hr, sr.am
require = og.require
add, scale, dn = wh.addv, wh.scalev, sr.differential
RING = f.QQ_I.poly_ring('a', 'nu')
AA, NU = RING.gens
a, nu = s.symbols('a nu')


def expression(value):
    return s.factor(RING.to_sympy(RING.convert(value)))


def weight(v, order):
    return [f.scale(-1, f.lap(x)) for x in v] if order == 1 else js.metric(v)


def pair(v, h, order):
    return am.pairing(weight(v, order), h)


def work(v, order):
    return pair(v, hr.nonlinear(v), order)


def derivative(v, h, order):
    return pair(h, hr.nonlinear(v), order)+pair(v, dn(v, h), order)


def second(v, h, ell, order):
    return (pair(h, dn(v, ell), order)+pair(ell, dn(v, h), order)
            +pair(v, dn(h, ell), order))


def family(phase):
    seed = add(wh.project([og.cosine((1, 1, 0)), {}, {}]),
               wh.project([{}, og.vd.sine((0, 1, 1)), {}]),
               wh.project([{}, {}, og.cosine((1, 0, 1))]))
    extra = wh.project([og.vd.sine((1, 0, -1)), f.scale(phase, og.cosine((0, 1, -1))), {}])
    return [{k: RING.convert(z) for k, z in row.items()}
            for row in add(seed, scale(AA, extra))]


def exact_zero(value, label):
    require(s.expand(expression(value)) == 0, label)


def symbolic_checks(phase):
    v = family(phase)
    f.equal(f.trace(f.jac(v)), {}, 'every family member is incompressible')
    require(all(sum(j*j for j in k) == 2 for row in v for k in row),
            'all original waves have the same wavelength')
    b = hr.nonlinear(v)
    require(all(sum(j*j for j in k) == 6 for row in b for k in row),
            'the entire first generation occupies the sixth shell')
    c = dn(v, b)
    d = add(dn(v, c), scale(2, hr.nonlinear(b)))
    e = add(dn(v, d), scale(3, dn(b, c)))
    predicted_j = (a*a+1)*(a*a+3)/6
    ordinary_a2 = 1636 if phase == 1 else 576
    joint_a2 = 39508 if phase == 1 else 30888
    predicted = [(15*a**6+358*a**4+ordinary_a2*a*a-165)/4320,
                 (1185*a**6+13894*a**4+joint_a2*a*a+1905)/4320]
    rows = []
    for order in (1, 2):
        exact_zero(work(v, order), 'initial nonlinear work vanishes')
        exact_zero(work(b, order), 'pure first-generation cubic work vanishes')
        exact_zero(derivative(v, c, order), 'no second-order work correction')
        j = expression(derivative(v, b, order))
        require(s.expand(j-(1 if order == 1 else 7)*predicted_j) == 0,
                'the complete first return agrees with the shell law')
        mixed = derivative(v, d, order)/6
        cross = second(v, b, c, order)/2
        coefficient = expression(mixed+cross)
        require(s.expand(coefficient-predicted[order-1]) == 0,
                'complete third-order work correction is the stated polynomial')
        energy4 = pair(v, e, order)/12+pair(b, d, order)/3+pair(c, c, order)/4
        exact_zero(2*energy4-mixed-cross, 'independent fourth-order energy identity')
        rows.append({'observer': 'ordinary stretching' if order == 1 else 'joint strain',
                     'first_return': str(j), 'mixed_third_jet': str(expression(mixed)),
                     'first_second_cross': str(expression(cross)),
                     'third_work_correction': str(coefficient),
                     'inviscid_energy_t4': str(expression(energy4))})

    L = lambda w: scale(NU, [f.lap(x) for x in w])
    u1 = add(L(v), b)
    u2 = add(L(u1), dn(v, u1))
    u3 = add(L(u2), dn(v, u2), scale(2, hr.nonlinear(u1)))
    forecast2 = add(L(L(v)), L(b), scale(-4*NU, b))
    forecast3 = add(L(L(L(v))), L(L(b)), scale(-4*NU, L(b)), scale(16*NU*NU, b))
    delta2, delta3 = add(u2, scale(-1, forecast2)), add(u3, scale(-1, forecast3))
    wh.same_vectors(delta2, c, 'first forecast defect is the complete parent return')
    for order in (1, 2):
        exact_zero(derivative(v, delta2, order), 'physical second-order difference vanishes')
        value = expression(derivative(v, delta3, order)/6+second(v, u1, delta2, order)/2)
        require(s.expand(value-predicted[order-1]) == 0,
                'full positive-viscosity correction has no omitted heat terms')

    # Polarization, already checked above, gives work(s*v+d*b)=s^2*d*J.
    exact_zero(derivative(b, v, 1), 'the alternative cubic mixed slot vanishes')
    exact_zero(derivative(b, v, 2), 'the alternative joint mixed slot vanishes')
    energy = expression(am.pairing(v, v))
    ordinary_diffusion = expression(sr.energy_pair(v, v, 2))
    require(s.expand(energy-(3+2*a*a)/4) == 0, 'original kinetic energy')
    require(s.expand(ordinary_diffusion-(3+2*a*a)) == 0, 'full initial diffusion')
    return v, [v, u1, u2, u3], [v, u1, forecast2, forecast3], rows, predicted


def evaluate(v, amplitude, viscosity):
    return [{k: Q.from_sympy(RING.to_sympy(RING.convert(z)).subs({a: amplitude, nu: viscosity}))
             for k, z in row.items() if RING.to_sympy(RING.convert(z)).subs({a: amplitude, nu: viscosity}) != 0}
            for row in v]


def independent_checks(v, symbolic, forecast, polynomials):
    rows = []
    for amplitude, viscosity in ((s.Rational(0), s.Rational(1, 3)),
                                 (s.Rational(1, 2), s.Rational(2, 7)),
                                 (s.Rational(1, 3), s.Rational(2))):
        initial = evaluate(v, amplitude, viscosity)
        actual, pressures = velocity_time_jets(initial, Q.from_sympy(viscosity), 3)
        for j in range(4):
            wh.same_vectors(actual[j], evaluate(symbolic[j], amplitude, viscosity),
                            'independent complete advective NS recurrence')
        ff = [evaluate(w, amplitude, viscosity) for w in forecast]
        delta2, delta3 = add(actual[2], scale(-1, ff[2])), add(actual[3], scale(-1, ff[3]))
        values = []
        for order in (1, 2):
            value = expression(derivative(initial, delta3, order)/6
                               +second(initial, actual[1], delta2, order)/2)
            require(value == polynomials[order-1].subs(a, amplitude),
                    'physical fixture agrees with the full polynomial')
            values.append(str(value))
        rows.append({'mixing_parameter': str(amplitude), 'viscosity': str(viscosity),
                     'work_corrections': values,
                     'actual_jet_modes': [len(set().union(*(row.keys() for row in w))) for w in actual],
                     'canonical_pressure_modes': [len(p) for p in pressures]})
    return rows


def sign_and_interval_checks(polynomials):
    ordinary, joint = polynomials
    x = s.symbols('x', nonnegative=True)
    numerator = 15*x**3+358*x*x+1636*x-165
    require(all(c > 0 for c in s.Poly(s.diff(numerator, x), x).all_coeffs()),
            'ordinary sign polynomial is strictly increasing on nonnegative x')
    require(ordinary.subs(a, s.Rational(3, 10)) < 0 < ordinary.subs(a, s.Rational(1, 3)),
            'unique transition lies strictly between 3/10 and 1/3')
    require(all(c > 0 for c in s.Poly(1185*x**3+13894*x*x+39508*x+1905, x).all_coeffs()),
            'joint-work correction is positive at every parameter')
    kappa = ordinary.subs(a, s.Rational(1, 2))
    coefficient = s.factor(kappa*6**4/2-s.Rational(7, 2)*6)
    require(coefficient == s.Rational(24309, 1280), 'entire diffusion credit is retained')
    require((s.Rational(1, 8)-s.Rational(1, 10))/2 == s.Rational(1, 80),
            'the original first forecast has a finite explicit all-time integral')
    return {'transition_bracket': '3/10 < critical |a| < 1/3',
            'ordinary_seed_correction': str(ordinary.subs(a, 0)),
            'joint_seed_correction': str(joint.subs(a, 0)),
            'adverse_parameter': '1/2', 'adverse_correction': str(kappa),
            'physical_interval': 't=6*nu^(1/3)*A^(-4/3)',
            'integrated_excess_leading_coefficient': str(coefficient),
            'integrated_excess_scale': 'nu^(4/3)*A^(2/3)',
            'first_forecast_integral': 'A^4*J(a)/(80*nu^2)'}


if __name__ == '__main__':
    families = []
    for phase in (1, -1):
        v, actual, forecast, rows, polynomials = symbolic_checks(phase)
        families.append({'relative_phase': phase, 'symbolic_returns': rows,
                         'independent_physical_checks': independent_checks(v, actual, forecast, polynomials)})
        if phase == 1:
            signs = sign_and_interval_checks(polynomials)
    plus, minus = family(1), family(-1)
    modes = set().union(*(row.keys() for row in plus))
    for k in modes:
        nk = tuple(-j for j in k)
        norm_plus = sum(row.get(k, f.ZERO)*row.get(nk, f.ZERO) for row in plus)
        norm_minus = sum(row.get(k, f.ZERO)*row.get(nk, f.ZERO) for row in minus)
        exact_zero(norm_plus-norm_minus, 'the two phase families have identical modal energy polynomials')
    ordinary_plus = s.sympify(families[0]['symbolic_returns'][0]['third_work_correction'])
    ordinary_minus = s.sympify(families[1]['symbolic_returns'][0]['third_work_correction'])
    require(ordinary_plus.subs(a, s.Rational(1, 3)) == s.Rational(1289, 262440),
            'same-resource positive correction')
    require(ordinary_minus.subs(a, s.Rational(1, 3)) == -s.Rational(2933, 131220),
            'same-resource negative correction')
    result = {'family': 'v_(a,phase)=v0+a*q_phase, all input modes have |k|^2=2',
              'phase_families': families,
              'signs_and_integrated_test': signs,
              'same_resource_pair': {'mixing_parameter': '1/3', 'positive_correction': '1289/262440',
                                     'negative_correction': '-2933/131220',
                                     'retained_equalities': 'Every initial modal energy, the first stretching return, and the entire first-Picard stretching forecast agree.'},
              'status': 'Exact polynomial and full Fourier checks passed. No new Lean certificate.',
              'scope': 'Actual local viscous NS comparisons, with all generated parents. No indefinite renewal or failure of every full-datum allowance is asserted.'}
    files = [Path(__file__), Path(sr.__file__), Path(js.__file__), Path(cp.__file__),
             Path(og.__file__), Path(hr.__file__), Path(f.__file__), Path(wh.__file__), Path(am.__file__)]
    result['source_sha256'] = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    print(json.dumps(result, indent=2), flush=True)
