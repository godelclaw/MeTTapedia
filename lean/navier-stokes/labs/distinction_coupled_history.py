#!/usr/bin/env python3
"""Distinction observers for a complete nonlinear caloric return.

The degree-twelve correction retains every spatial output and canonical
pressure. Positive differential cascades certify all-time depletion in
each parent channel. Equal initial energy/source summaries hide different
signed costs, while a common upper comparison survives at this order.
Actual small-amplitude interval comparisons remain analytic; higher-order
history payment is open.
"""

import hashlib
import json
from fractions import Fraction
from pathlib import Path

import coupled_caloric_return as cc
import paired_stretching_history as ep
import helicity_renewal as h

Q, require = Fraction, ep.require
ONSET = dict(A=Q(-150354011, 950400), B=Q(-18702523, 129600),
             C=Q(-35270591, 2376000))


def complete_return(amplitudes):
    original = cc.initial(amplitudes)
    heat = {k: tuple({(1, 0): Q(str(v.get(k, cc.f.ZERO).y))}
                     if v.get(k, cc.f.ZERO) else {} for v in original)
            for k in h.modes(original)}
    U, N, P = ep.evolve_amplitudes(heat, 8)
    b = [{}, {}] + U[2:] + [{} for _ in range(4)]
    terms = []
    for i in range(2, 9):
        source = ep.field_add(ep.advection(b[j], b[12-i-j])
                              for j in range(2, 9) if 2 <= 12-i-j <= 8)
        terms.append(ep.weighted_pair(b[i], source, 1))
    correction = ep.add(*terms)
    require(correction == ep.literal_cubic(b, 12),
            'Independent complete physical vorticity contraction at degree twelve')
    return correction, dict(amplitudes=amplitudes,
                            complete_velocity_mode_counts=[len(U[i]) for i in range(1, 9)],
                            complete_pressure_mode_counts=[len(P[i]) for i in range(2, 9)])


def negative_cascade(function):
    """Nonnegative initial data for (D+rate) applied to -function."""
    rates = [rate for rate in sorted({i for i, _ in function}, reverse=True)
             for _ in range(1+max(j for i, j in function if i == rate))]
    current, values = ep.scale(-1, function), []
    for rate in rates:
        value = ep.jet(current, 0)
        require(value >= 0, 'Nonnegative cascade data certify negative correction')
        values.append(value)
        current = ep.add(ep.derivative(current), ep.scale(rate, current))
    require(not current and any(value > 0 for value in values),
            'Zero terminal function and a strictly positive cascade datum')
    return dict(rates=rates, initial_values=[str(v) for v in values],
                conclusion='Strictly negative at every t>0')


def shared_shadow():
    left, right = (2, 1, 1), (1, 1, 2)
    originals = [cc.initial(amps, sine=False) for amps in (left, right)]
    sources = [cc.c.nonlinear(u) for u in originals]
    cc.equal(sources[0], sources[1], 'The complete original nonlinear sources agree')
    energies = [sum(cc.c.mean(cc.f.mul(component, component))
                    for component in u) for u in originals]
    require(energies[0] == energies[1] == 3,
            'Normalized original kinetic energies agree')
    # All original modes have radius one: every isotropic integer
    # derivative energy and every original heat-source age agrees.
    for u in originals:
        require(all(sum(j*j for j in k) == 1 for k in h.modes(u)),
                'Every original parent is a unit Laplacian eigenmode')
    joint = lambda amps: amps[0]**4*amps[1]**2*amps[2]**4
    require(joint(left) == joint(right) == 16,
            'The complete leading degree-ten forecast agrees')
    return dict(left=left, right=right, original_energy=3,
                source_amplitude=2, source_capacity_at_unit_viscosity='1/4',
                shared_leading_factor=16,
                retained_refinement='Ordered parent squares (A^2,B^2,C^2)',
                scope='Exact cost descent fails; upper cost domination is a separate contract')


def physical_ninth_jet(G10, G12):
    original = cc.initial()
    jets, pressure = cc.c.velocity_time_jets(original, cc.Q(1), 7)
    remainder = [cc.c.addv(v, cc.c.scale(-(-cc.Q(1))**j, original))
                 for j, v in enumerate(jets)]
    actual = Q(str(cc.cubic_jet(remainder, 9)))
    expected = ep.jet(G10, 9) + ep.jet(G12, 9)
    require(actual == expected,
            'Independent full positive-viscosity PDE time jet identifies both amplitude degrees')
    return dict(nu=1, amplitudes=(1, 1, 1), ninth_derivative=str(actual),
                complete_velocity_mode_counts=[len(h.modes(v)) for v in jets],
                complete_pressure_mode_counts=[len(v) for v in pressure],
                degree_ten_contribution=str(ep.jet(G10, 9)),
                degree_twelve_contribution=str(ep.jet(G12, 9)))


def main():
    computed, fixtures = {}, []
    for amps in [(1, 1, 1), (2, 1, 1), (1, 2, 1), (1, 1, 2)]:
        computed[amps], row = complete_return(amps)
        fixtures.append(row)
    unit = computed[(1, 1, 1)]
    A = ep.scale(Q(1, 3), ep.add(ep.scale(Q(1, 16), computed[(2, 1, 1)]),
                                ep.scale(-1, unit)))
    B = ep.scale(Q(1, 3), ep.add(ep.scale(Q(1, 4), computed[(1, 2, 1)]),
                                ep.scale(-1, unit)))
    C = ep.add(unit, ep.scale(-1, A), ep.scale(-1, B))
    require(computed[(1, 1, 2)] == ep.scale(16, ep.add(A, B, ep.scale(4, C))),
            'Independent C-parent fixture reconstructs the three channels')
    channels = dict(A=A, B=B, C=C)
    rows = {}
    for name, function in channels.items():
        require(all(ep.jet(function, j) == 0 for j in range(9)) and
                ep.jet(function, 9) == ONSET[name],
                'Exact ninth-order channel onset')
        rows[name] = dict(coefficients=ep.encode(function),
                          integral=str(ep.integral_infinity(function)),
                          ninth_derivative=str(ONSET[name]),
                          sign_certificate=negative_cascade(function))
    difference = ep.add(A, ep.scale(-1, C))
    require(ep.jet(difference, 9) == Q(-25230699, 176000),
            'Exact nontrivial fibre in the energy/source cost shadow')
    require(ep.add(computed[(2, 1, 1)], ep.scale(-1, computed[(1, 1, 2)]))
            == ep.scale(48, difference), 'Cost difference retains the joint factor')
    shadow = shared_shadow()
    shadow['difference_coefficients'] = ep.encode(ep.scale(48, difference))
    shadow['difference_sign_certificate'] = negative_cascade(difference)
    shadow['difference_ninth_derivative'] = str(48*ep.jet(difference, 9))
    leading = json.loads(Path(cc.__file__).with_name('coupled_caloric_return_results.json').read_text())
    G10 = {(i, j): Q(v) for i, j, v in leading['full_leading_history']['coefficients']}
    report = dict(physical_fixtures=fixtures, full_degree_twelve_channels=rows,
                  summary_obstruction=shadow, independent_physical_jet=physical_ninth_jet(G10, unit),
                  comparison='Degree twelve is strictly depleting when A*B*C is nonzero; the exact higher remainder is open',
                  viscosity='Degree twelve scales as nu^(-9) F(nu*t), and its integral as nu^(-10)',
                  actual_scope='Small common amplitude on each fixed compact interval inside t>0; analytic remainder, not a large-data or all-time bound',
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
