#!/usr/bin/env python3
"""Exact checks for pressure histories paid through forward/backward diffusion.

The smooth time-reversal theorem and stochastic estimates are analytic in
README.md. These checks retain full canonical NS sources and do not declare
the forward and backward martingales independent.
"""

import argparse
import json
from fractions import Fraction as Q
from pathlib import Path

import sympy as s
import pressure_history_source as f
from planar_parent_reserve import average, feedback_datum
from planar_pressure_history import datum as planar_datum
from pressure_oblique_parents import datum as oblique_datum
from pressure_impulse_return import NU, mean, require, viscosity_jets
from pressure_parent_bellman import trig


def field_l2_squared(field):
    value = mean(f.mul(field, field))
    require(not value.y, 'Real squared norm')
    return value.x


def matrix_square(matrix):
    return f.add(*(f.mul(a, a) for row in matrix for a in row))


def generators():
    initial = feedback_datum(Q(1), 1)
    hidden = [f.add(a, f.scale(-1, average(a))) for a in initial]
    cases = [('adverse planar', planar_datum(4, True)),
             ('favorable planar', planar_datum(2)),
             ('adverse oblique', oblique_datum((Q(1, 8), Q(1), Q(1, 8)))),
             ('opposite oblique', oblique_datum((Q(1), Q(1), Q(1)))),
             ('coupled hidden parents', initial), ('initially hidden only', hidden)]
    rows = []
    for name, u in cases:
        f.equal(f.trace(f.jac(u)), {}, 'Actual solenoidal datum')
        _, pressures = viscosity_jets(u, 2)
        parent = list(map(average, u))
        p_parent = f.tensor_pressure(f.tensor(parent, parent))
        r = f.add(pressures[0], f.scale(-1, p_parent))
        stress = [[f.add(a, f.scale(-1, b)) for a, b in zip(row, base)]
                  for row, base in zip(f.tensor(u, u), f.tensor(parent, parent))]
        f.equal(r, f.tensor_pressure(stress), 'Complete pressure residual of the actual mean split')
        corrector = f.hess(f.green(r))
        lhs = sum(field_l2_squared(f.diff(a, j)) for row in corrector for a in row for j in range(3))
        rhs = sum(field_l2_squared(f.diff(a, j)) for row in stress for a in row for j in range(3))
        require(0 <= lhs <= rhs, 'The exact pressure-corrector H1 contraction retains every output')

        # The time derivative is the actual generated canonical pressure,
        # including diffusion, rather than an independent supplied scalar.
        chi, chi_t = f.grad(f.green(pressures[0])), f.grad(f.green(pressures[1]))
        g = f.grad(pressures[0])
        for i in range(3):
            forward = f.add(chi_t[i], f.adv(u, chi[i]), f.scale(NU, f.lap(chi[i])))
            backward = f.add(f.scale(-1, chi_t[i]), f.scale(-1, f.adv(u, chi[i])),
                             f.scale(NU, f.lap(chi[i])))
            f.equal(f.add(forward, backward), f.scale(-2*NU, g[i]),
                    'Full forward/backward generators cancel time and transport, all viscosities')
            f.equal(f.lap(chi[i]), f.scale(-1, g[i]), 'The corrector solves its complete Poisson equation')
        # Nonzero pressure-time derivatives make the sign check informative
        # also for the original oblique data, whose initial pressure is zero.
        require(bool(pressures[1]), 'Evolving canonical pressure is retained')
        rows.append(dict(fixture=name, original_pressure_modes=len(pressures[0]),
                         generated_pressure_modes=len(pressures[1]),
                         residual_corrector_H1_squared=str(lhs), stress_H1_squared=str(rhs)))
    return rows


def martingale_algebra():
    m = s.Matrix(s.symbols('m0:3', real=True))
    sigma = s.Matrix(3, 3, s.symbols('s0:9', real=True))
    square = m.dot(m)
    generator = s.trace((sigma*sigma.T)*s.hessian(square**2, tuple(m)))/2
    rate = s.trace(sigma*sigma.T)
    wedge = sum((m[i]*sigma[j, k]-m[j]*sigma[i, k])**2
                for k in range(3) for i in range(3) for j in range(i+1, 3))
    require(s.expand(6*square*rate-generator-4*wedge) == 0,
            'Quartic Ito drift upper bound with the full covariance matrix')
    y, h, eps = s.symbols('y h eps', positive=True)
    upper = 6*s.sqrt(y)*h/(2*s.sqrt(y+eps))
    require(s.simplify(upper/(3*h)-s.sqrt(y/(y+eps))) == 0,
            'Regularized square-root integration gives constant three')
    return dict(ito_drift='2|m|^2||sigma||_F^2+4|sigma^T m|^2 <=6|m|^2||sigma||_F^2',
                martingale_bound='||M_T||_4^2 <= 3 integral ||sigma_t||_(L4 probability)^2 dt',
                pressure_bound='||P_r(T)||_4^2 <= (6/nu) integral ||Hess(-Delta)^(-1)r||_4^2 dt',
                independence='not assumed; the two martingales are on the same reversed path')


def cellular_benchmark():
    u = [trig(1, 1, 'sin'), trig(0, 1, 'sin'), {}]
    velocity, pressure = viscosity_jets(u, 2)
    p = f.mul(trig(0, 1, 'cos'), trig(1, 1, 'cos'))
    f.equal(pressure[0], p, 'Exact cellular canonical pressure')
    f.equal(pressure[1], f.scale(-2*NU, p), 'Actual pressure decay')
    for i in range(3):
        f.equal(velocity[1][i], f.scale(-NU, u[i]), 'Actual NS heat eigenflow')
    A = f.hess(f.green(p))
    require(mean(matrix_square(A)) == f.QQ_I(Q(1, 4)), 'Corrector variance')
    require(mean(f.mul(matrix_square(A), matrix_square(A))) == f.QQ_I(Q(5, 64)),
            'Exact corrector spatial fourth norm')

    nu, T, t = s.symbols('nu T t', positive=True)
    impulse_second = (1-(1+4*nu*T)*s.exp(-4*nu*T))/(16*nu**2)
    # Independent two-time heat covariance: E[g(t,X_t).g(s,X_s)]
    # equals (1/2)exp(-4nu*max(t,s)) on this actual pressure source.
    ordered = s.integrate(t*s.exp(-4*nu*t), (t, 0, T))
    require(s.simplify(ordered-impulse_second) == 0, 'Ordered-time Brownian pressure covariance')
    each_variance = (1-s.exp(-4*nu*T))/(16*nu)
    cross = s.simplify(nu*impulse_second-each_variance)
    require(s.simplify(cross+T*s.exp(-4*nu*T)/4) == 0,
            'The forward/backward martingales have nonzero negative correlation')
    clock = s.sqrt(5)*(1-s.exp(-4*nu*T))/(32*nu)
    fourth_bound = s.simplify(36*clock**2/nu**2)
    require(s.simplify(fourth_bound-45*(1-s.exp(-4*nu*T))**2/(256*nu**4)) == 0,
            'All-time fourth-moment allowance for the actual cellular pressure')
    # Frequency changes preserve the corrector's amplitude but increase the
    # source gradient. These are exact actual NS data, not a truncated flow.
    frequency = []
    for k in (1, 4, 16):
        pk = {tuple(k*j for j in q): value for q, value in p.items()}
        Ak = f.hess(f.green(pk))
        gk = f.grad(pk)
        require(mean(f.mul(matrix_square(Ak), matrix_square(Ak))) == f.QQ_I(Q(5, 64)),
                'No spatial derivative in the pressure amplitude clock')
        gg = f.dot(gk, gk)
        require(mean(f.mul(gg, gg)) == f.QQ_I(Q(5, 16)*k**4),
                'The old gradient fourth norm carries four additional frequency powers')
        frequency.append(dict(k=k, corrector_L4_fourth='5/64', gradient_L4_fourth=str(Q(5, 16)*k**4)))
    return dict(physical_flow='u=e^(-nu t)(sin y,sin x,0), p=e^(-2nu t)cos x cos y',
                brownian_observer_second_moment=str(impulse_second),
                each_normalized_martingale_variance=str(each_variance),
                martingale_cross_correlation=str(cross),
                fourth_moment_bound_for_either_observer=str(fourth_bound), frequency=frequency)


def replay(record):
    """Evaluate the new bound on an existing accepted comparison history.

    This checks scalar arithmetic and seam continuity. The original spatial
    enclosures and common original datum remain hypotheses of the input.
    No live solver, velocity control or inherited moment is changed.
    """
    from pressure_history_certificate import root2, root4
    from pressure_polynomial_enclosure import rational_upper

    rows = [json.loads(line) for line in Path(record).read_text().splitlines()]
    config = rows[0]
    nu, h = Q(config['nu']), Q(config['h'])
    require(nu > 0 and h > 0, 'Positive input viscosity and slab length')
    L2 = Y6 = Q(0)
    end, time, reports = None, Q(0), []
    for row in rows[1:]:
        if row.get('status') != 'interval accepted':
            continue
        require(Q(row['time']) == time+h, 'Contiguous original-time intervals')
        if end is not None:
            require(row['initial_endpoint_sha256'] == end, 'Same inherited physical endpoint')
        end, time = row['final_endpoint_sha256'], Q(row['time'])
        fields, control = row['row'], row['control']
        x, y, V0, V1, E = map(Q, (control['Xmax'], control['Ymax'], fields['V0'],
                                   fields['V1'], control['energy_rhs']))
        require(min(x, y, V0, V1, E) >= 0, 'Nonnegative supplied majorants')
        L2 += h*(V0*y+V1*x)**2
        Y6 += h*y**6
        new = 6*root2(6/nu)*(root2(L2)+10*root4(Y6)*root4(E/nu))
        old = min(Q(control['local_pressure_sum']), Q(control['cumulative_pressure']))
        reports.append(dict(time=float(time), new_spatial_upper=rational_upper(new),
                            old_spatial_upper=float(old), new_is_smaller=new < old,
                            chosen_spatial_upper=rational_upper(min(old, new))))
    require(bool(reports), 'At least one complete accepted interval')
    return dict(scope='Outward scalar replay, conditional on the original spatial/velocity enclosures',
                config={k: config[k] for k in ('n', 'nu', 'dt', 'h')},
                intervals=len(reports), improved_intervals=sum(r['new_is_smaller'] for r in reports),
                reports=reports)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--replay', type=Path)
    args = parser.parse_args()
    result = (replay(args.replay) if args.replay else
              dict(status='All exact checks passed', generators=generators(),
                   martingale=martingale_algebra(), cellular=cellular_benchmark(),
                   scope='Exact algebra and Fourier checks; stochastic theorem and PDE consumer analytic'))
    print(json.dumps(result, indent=2))
