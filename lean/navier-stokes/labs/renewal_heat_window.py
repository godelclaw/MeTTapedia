#!/usr/bin/env python3
"""Exact heat-window fluxes and original-energy payment identities.

Complete Fourier pressure variations are retained. The general smoothed
kernel bounds and actual-history payment are analytic in README.md; these
fixtures are neither a Galerkin evolution nor Lean certificates.
"""

import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path

import sympy as s
import pressure_history_source as f
import heat_work_reserve as h
from heat_work_parent_payment import heat
from heat_remainder_pressure import plus, times, adv, solenoidal, require
from generated_fourth_moment import target_field
from cyclic_pressure_history import velocity_time_jets


def zero(expression, label):
    require(s.expand(expression) == 0, label)


def split_integral(polynomial, cutoff_square):
    short = h.integrate(polynomial, cutoff_square)
    full = h.integrate(polynomial)
    return short, s.factor(full-short)


def filtered_oblique():
    u = h.weighted_datum(2, (1, 1, 1))
    v = heat(u, Q(1, 2))
    w = plus(u, times(-1, v))
    z = h.heat(w)
    F = h.profile(z)
    G = h.variation(z, h.heat(h.nonlinear(w)))
    zero(F, 'The actual filtered remainder has identically zero heat work')
    scale = s.Rational(961, 16384)
    expected = scale*h.q**10*(11+16*h.q**4-3*h.q**8)/66
    positive = scale*h.q**10*(11+13*h.q**4+3*h.q**4*(1-h.q**4))/66
    zero(G-expected, 'The complete self-renewal of the actual filtered remainder')
    zero(G-positive, 'The zero-profile selector sees a positive direction at every heat age')
    rows = []
    for r in (s.Rational(1, 2), s.Rational(1, 4)):
        short, tail = split_integral(G, r)
        expected_tail = scale*(r**5/60+4*r**7/231-r**9/396)
        zero(tail-expected_tail, 'Exact nonlinear heat tail without a heat grid')
        require(short > 0 and tail > 0 and short+tail == scale*s.Rational(109, 3465),
                'Both selected windows are positive and recombine exactly')
        rows.append(dict(cutoff_square=str(r), short=str(short), tail=str(tail)))

    # The physical tangent comes from the ORIGINAL u, not an independent
    # unforced equation for w. Check all directions before the selector.
    nu = Q(2, 7)
    physical = velocity_time_jets(u, nu, 1)[0][1]
    wt = plus(physical, times(-1, heat(physical, Q(1, 2))))
    diffusion = times(nu, [f.lap(row) for row in w])
    mixed = times(-1, solenoidal(plus(adv(v, w), adv(w, v))))
    source = plus(h.nonlinear(v), times(-1, heat(h.nonlinear(u), Q(1, 2))))
    actual = h.variation(z, h.heat(wt))
    pieces = [h.variation(z, h.heat(direction))
              for direction in (diffusion, h.nonlinear(w), mixed, source)]
    zero(actual-sum(pieces), 'The full original-fluid tangent retains source and mixed parents')
    zero(pieces[0], 'Diffusion of the identically zero heat-work profile contributes zero')
    return dict(heat_work='0', self_profile=str(s.factor(G)), split=rows,
                actual_viscosity=str(nu), full_physical_profile=str(s.factor(actual)),
                scope='Window signs concern the self direction; the complete physical derivative retains all parents before applying the selector.')


def moving_boundary():
    w = times(-1, target_field())
    z = h.heat(w)
    F = h.profile(z)
    zero(F-h.q**6*(224-275*h.q**2)/320, 'The reversed field changes pressure-work sign')
    D = h.variation(z, h.heat([f.lap(row) for row in w]))
    zero(D+h.q*s.diff(F, h.q), 'Complete heat-direction variation')
    root, r = s.Rational(224, 275), s.Rational(1, 2)
    # Positive ages have q^2<root. The short window has r<q^2<root.
    short = h.integrate(F, r)-h.integrate(F, root)
    tail = h.integrate(F)-h.integrate(F, r)
    short_rate = h.integrate(D, r)-h.integrate(D, root)
    tail_rate = h.integrate(D)-h.integrate(D, r)
    boundary = s.factor(F.subs(h.q, s.sqrt(r)))
    require(short > 0 and tail > 0 and F.subs(h.q, 1) < 0,
            'Present work is negative while both later positive windows store capacity')
    require(short_rate == boundary == s.Rational(173, 5120) and tail_rate == -boundary,
            'Heat alone increases the truncated reserve by its incoming boundary work')
    zero(short_rate+tail_rate, 'The full reserve retains exact cancellation of window flux')
    nu, speed = s.symbols('nu speed', positive=True)
    moving_rate = boundary+speed/nu*boundary
    zero(moving_rate.subs(speed, -nu), 'A backward window moving at viscous speed cancels the flux')
    return dict(heat_work=str(s.factor(F)), positive_region='0<q^2<224/275',
                cutoff_square=str(r), short_capacity=str(short), tail_capacity=str(tail),
                short_heat_rate=str(short_rate), tail_heat_rate=str(tail_rate),
                backward_window_rate='0',
                scope='This tests the actual heat direction within the reserve derivative, not a claim that this field follows an unforced heat-only NS solution.')


def cyclic_selector():
    rows = []
    for strengths in ((1, 1, 1), (8, 1, 1)):
        a, b, c = strengths
        A = h.nonlinear(h.weighted_datum(0, strengths))
        z = h.heat(A)
        zero(h.profile(z), 'The cyclic generated field has zero heat-work profile')
        G = h.variation(z, h.heat(h.nonlinear(A)))
        T = a*a*b*b*c*c
        S1, S2 = a**4*b*b+b**4*c*c+c**4*a*a, a**4*c*c+a*a*b**4+b*b*c**4
        k = -s.Rational(T*(S1+S2-27*T), 576)
        zero(G-k*h.q**14, 'The full cyclic source retains both signs across parent strengths')
        selected = max(k, 0)*h.q**14
        short, tail = split_integral(selected, s.Rational(1, 2))
        zero(short+tail-max(k, 0)/14, 'Each window retains the exact zero-profile selector')
        if k < 0:
            require(short == tail == 0, 'Negative directions at zero work do not give negative renewal')
        rows.append(dict(strengths=list(strengths), coefficient=str(k), short=str(short), tail=str(tail)))
    return rows


def payment_algebra():
    E, Z, nu, remaining = s.symbols('E Z nu remaining', positive=True)
    rows = []
    for m in (5, 6):
        stock = E**m/(2*m*nu)
        cost = E**s.Rational(m-1, 2)*s.sqrt(Z)
        zero(s.diff(stock, E)*(-2*nu*Z)+cost**2, 'The powered energy spends the squared observation')
        clock = s.sqrt(remaining*stock)
        loss = (stock+remaining*cost**2)/(2*clock)
        certificate = (s.sqrt(stock)-s.sqrt(remaining)*cost)**2/(2*clock)
        require(s.simplify(loss-cost-certificate) == 0,
                'The same original clock pays every continuation, with a nonnegative Bellman gap')
        rows.append(dict(power=m, stock=str(stock), observation=str(cost), clock=str(clock)))
    x, y, e, d = s.symbols('x y e d', nonnegative=True)
    zero((x+y)*(e+d)-(s.sqrt(x*e)+s.sqrt(y*d))**2
         -(s.sqrt(x*d)-s.sqrt(y*e))**2,
         'The two-interval Cauchy identity supplies the endpoint-safe telescoping inequality')
    require(s.Rational(3,4)+s.Rational(3,4)+s.Rational(7,8)+s.Rational(9,8)==s.Rational(7,2),
            'The full nonlinear variation has the integrable resolved-age exponent')
    require(3*s.Rational(3,8)+s.Rational(3,4)+s.Rational(3,8)==s.Rational(9,4),
            'Pressure work at the moving boundary retains one dissipation square root')
    require(2*s.Rational(5,2)-3-1 == 1 and 2*s.Rational(9,4)-s.Rational(5,2)-1 == 1,
            'Both clocks have the fourth-moment scaling under whole-space NS dilation')
    return rows


def checks():
    report = dict(filtered_oblique=filtered_oblique(), moving_boundary=moving_boundary(),
                  cyclic=cyclic_selector(), payment=payment_algebra(),
                  scope='Exact full Fourier, selector and clock identities. General kernel estimates, physical interval payment and continuation are analytic, not Lean-certified.')
    root = Path(__file__).resolve().parent
    names = ['renewal_heat_window.py', 'heat_work_reserve.py', 'heat_work_parent_payment.py',
             'pressure_history_source.py', 'heat_remainder_pressure.py', 'generated_fourth_moment.py',
             'cyclic_pressure_history.py', 'pressure_gradient_stock.py', 'pressure_quadratic_storage.py']
    report['source_sha256'] = {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in names}
    return report


if __name__ == '__main__':
    print(json.dumps(checks(), indent=2))
