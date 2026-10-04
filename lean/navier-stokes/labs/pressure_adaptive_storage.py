#!/usr/bin/env python3
"""Actual NS jets for a bounded, adaptive signed pressure correction.

Exact Fourier coefficients retain all generated modes. The positive-viscosity
interval and uniform Taylor remainder are analytic in README.md; these checks
do not numerically enclose a PDE history or certify it in Lean.
"""

import json
from fractions import Fraction as Q

import sympy as s
import pressure_history_source as f
from pressure_impulse_return import RING, mean, require, viscosity_jets


nu = s.Symbol('nu')


def wave(k, cosine=False):
    c = f.QQ_I(Q(1, 2)) if cosine else -f.II/2
    return {k: c, tuple(-j for j in k): f.QQ_I(c.x, -c.y)}


def datum(m):
    y, z = wave((0, 1, 0)), wave((0, 0, 1))
    return [f.add(y, f.scale(-m, z)), z, wave((1, m, 0))]


def avg(field):
    result = s.expand(RING.to_sympy(RING.convert(mean(field))))
    require(not result.has(s.I), 'Real exact spatial mean')
    return result


def formulas(m):
    m = s.sympify(m)
    dp, dm = m*m+2*m+3, m*m-2*m+3
    r = 3*m*m/(2*dp*dm)
    q = s.Rational(9, 4)*(1/dp**2+1/dm**2)
    gradient_q = s.Rational(9, 4)*(1/dp+1/dm)
    E0 = (3*m**4+22*m*m+21)/32
    d = (5*m**4+29*m*m+21)/8
    h = (m**6+12*m**4+36*m*m+21)/4
    return dict(dp=dp, dm=dm, E0=E0, d=d, h=h, r=s.factor(r), q=s.factor(q),
                gradient_q=s.factor(gradient_q))


def physical_jet(m):
    u = datum(m)
    velocity, pressure = viscosity_jets(u, 2)
    require(not pressure[0], 'No initial canonical pressure, for any viscosity')
    f.equal(f.trace(f.jac(u)), {}, 'Actual solenoidal initial datum')
    require(all(avg(a) == 0 for a in u), 'Zero initial spatial mean')
    shift = (1-m, 1, 1)
    for field in u:
        translated = {k: c*(1 if sum(a*b for a, b in zip(k, shift)) % 2 == 0 else -1)
                      for k, c in field.items()}
        f.equal(translated, f.scale(-1, field),
                'Half-period translation reverses all parents and removes the mixed viscous coefficient')
    values = formulas(m)
    predicted_p1 = f.mul(wave((0, 0, 1), True), f.add(
        f.scale(-Q(3, int(values['dp'])), wave((1, m+1, 0), True)),
        f.scale(-Q(3, int(values['dm'])), wave((1, m-1, 0), True))))
    f.equal(pressure[1], predicted_p1,
            'Full generated pressure derivative, with zero viscous contribution')
    e = f.scale(Q(1, 2), f.dot(u, u))
    e1 = f.dot(u, velocity[1])
    e2 = f.add(f.dot(velocity[1], velocity[1]), f.dot(u, velocity[2]))
    E0 = avg(f.mul(e, e))
    E1 = 2*avg(f.mul(e, e1))
    E2 = avg(f.add(f.mul(e1, e1), f.mul(e, e2)))
    P2 = avg(f.mul(pressure[1], pressure[1]))
    gradient_p1 = f.grad(pressure[1])
    source_gradient = avg(f.dot(gradient_p1, gradient_p1))
    require(s.expand(E0-values['E0']) == 0, 'Exact original fourth-speed storage')
    require(s.expand(E1+nu*values['d']) == 0, 'Complete first viscous loss')
    require(s.expand(E2-values['r']-nu**2*values['h']) == 0,
            'Full NS second coefficient, including viscosity and its vanishing linear term')
    require(s.expand(P2-values['q']) == 0, 'Exact generated pressure-square coefficient')
    require(s.expand(source_gradient-values['gradient_q']) == 0,
            'The original pressure-production gradient supplies a larger physical resource')

    # Independent integrated pressure-work calculation of the inviscid return.
    r = avg(f.mul(pressure[1], f.adv(u, e)))
    require(s.expand(r-values['r']) == 0, 'Independent pressure-work second coefficient')
    resonant = f.scale(-m, f.mul(f.mul(wave((0, 1, 0)), wave((1, m, 0))),
                                  wave((0, 0, 1), True)))
    require(avg(f.mul(pressure[1], f.add(f.adv(u, e), f.scale(-1, resonant)))) == 0,
            'All other transport terms are orthogonal to the generated pressure')
    heat = [f.lap(a) for a in u]
    energy_euler = avg(f.dot(u, [f.scale(-1, f.adv(u, a)) for a in u]))
    grad_square = f.add(*(f.mul(a, a) for row in f.jac(u) for a in row))
    require(energy_euler == 0 and s.expand(avg(f.dot(u, heat))+avg(grad_square)) == 0,
            'Kinetic energy decreases despite the later storage rebound')
    require(avg(grad_square) == s.Rational(2*m*m+3, 2), 'Exact original gradient norm')
    return dict(m=m, initial_E=str(E0), first_E=str(E1), second_E=str(E2),
                second_P=str(P2), inviscid_ratio=str(s.factor(values['r']/values['q'])),
                source_gradient_squared=str(source_gradient),
                return_over_source_gradient=str(s.factor(values['r']/source_gradient)),
                margin_at_cap_one_quarter=str(s.factor(values['r']-values['q']/4)))


def general_algebra():
    m, t, mu, cap = s.symbols('m t mu cap', nonnegative=True)
    v = formulas(m)
    # Independent angle averages: theta=x+m*y preserves normalized measure.
    heat = ((3*m**4+18*m*m+10)*s.exp(-4*mu*t)/32
            +(m*m+2)*s.exp(-(2*m*m+4)*mu*t)/8
            +3*s.exp(-4*(m*m+1)*mu*t)/32)
    require(s.simplify(heat.subs(t, 0)-v['E0']) == 0, 'Heat forecast initial mass')
    require(s.simplify(s.diff(heat, t).subs(t, 0)+mu*v['d']) == 0,
            'Independently integrated first heat coefficient')
    require(s.simplify(s.diff(heat, t, 2).subs(t, 0)/2-mu**2*v['h']) == 0,
            'Independently integrated second heat coefficient')
    ratio = s.factor(v['r']/v['q'])
    gap = m*m*(m*m-3)**2/(6*(m**4+10*m*m+9))
    require(s.simplify(ratio-m*m/6-gap) == 0,
            'Required subtraction is unbounded with obliquity: r/q>=m^2/6')
    require(s.simplify(v['r']-3*m*(1/v['dm']-1/v['dp'])/8) == 0,
            'Exact general resonant pressure pairing')
    require(s.simplify(v['r']/v['gradient_q']-m*m/(3*(m*m+3))) == 0,
            'The pressure-production gradient pays the first inviscid return uniformly in obliquity')

    # This is algebra for the analytic Taylor argument, not a numerical
    # evaluation of its uniform Sobolev remainder constant B or time T0.
    d, k, B = s.symbols('d k B', positive=True)
    c = 2*d/k
    require(s.simplify(-d*c+k*c*c-k*c*c/2) == 0,
            'A later time exceeds the original storage after the initial viscous drop')
    require(s.simplify((B*c**3*mu**3).subs(mu, k/(4*B*c))
                      -(k*c*c*mu**2/4).subs(mu, k/(4*B*c))) == 0,
            'Uniform cubic remainder is absorbed by mu<=k/(4Bc)')
    exemplar = formulas(2)
    k2 = s.factor(exemplar['r']-exemplar['q']/4)
    c2 = s.factor(2*exemplar['d']/k2)
    require(k2 == s.Rational(111, 968) and c2 == s.Rational(52514, 111),
            'Explicit m=2 witness for the entire coercive range up to one quarter')
    return dict(ratio=str(ratio), ratio_minus_m_squared_over_six=str(gap),
                return_over_source_gradient=str(m*m/(3*(m*m+3))),
                m2=dict(cap='1/4', positive_margin=str(k2), later_time_factor=str(c2)),
                physical_transfer='Uniform short-time H10 bounds and Taylor remainder are analytic; B and T0 are not numerically evaluated',
                feasible_storage='E-cap*P+nu*C <= min_{0<=s<=t}(E(s)+nu*C(s))',
                failed_control='Every time-dependent a in [0,cap], even with future information, on the constructed viscous interval')


if __name__ == '__main__':
    print(json.dumps(dict(status='All exact checks passed',
                          jets=[physical_jet(m) for m in (0, 1, 2, 4, 8)],
                          general=general_algebra(),
                          scope='Full NS algebra; actual positive-viscosity interval and adaptive-control obstruction analytic, not Lean-certified'), indent=2))
