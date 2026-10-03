#!/usr/bin/env python3
"""Physical forcing defects and internal-source compatibility.

The imported-candidate obstruction and Feynman--Kac argument are analytic
in README.md. These checks cover normalized generator algebra, an actual
smooth forced shear, heat constants, and complete unforced NS time jets.
No forced singular solution is simulated or constructed by this script.
"""

import json
import sympy as sp

import passive_parent_bellman as parent
from cyclic_pressure_history import velocity_time_jets
from metric_loss_bellman import zero

f, Q, r = parent.f, parent.Q, parent.r


def vec(name):
    return sp.Matrix(sp.symbols(name+'0:3', real=True))


def force_generator():
    nu, delta, alpha = sp.symbols('nu delta alpha', positive=True)
    beta = sp.symbols('beta', real=True)
    impulse, omega, score, force, torque = [vec(p) for p in ('I', 'w', 'k', 'f', 'c')]
    s = omega.dot(omega)+delta
    n = omega/sp.sqrt(s)
    normalized_torque = torque/sp.sqrt(s)
    correction_n = -(sp.eye(3)-n*n.T)*normalized_torque
    # Independently differentiate in raw omega: backward physical forcing
    # changes omega by -curl(f), and changes I by +f.
    literal_n = -n.jacobian(omega)*torque
    for j, entry in enumerate(literal_n-correction_n):
        zero(entry, ('normalized force, including radial correction', j))
    d, z = impulse.dot(n), n.dot(score)
    reserve = impulse.dot(impulse)/nu
    reserve += 2*beta*impulse.dot(omega)*omega.dot(score)/s
    reserve += alpha*nu*omega.dot(score)**2/s
    literal = sum(sp.diff(reserve, impulse[j])*force[j]
                  -sp.diff(reserve, omega[j])*torque[j] for j in range(3))
    predicted = 2*impulse.dot(force)/nu+2*beta*z*n.dot(force)
    predicted += (2*beta*z*impulse+2*beta*d*score+2*alpha*nu*z*score).dot(correction_n)
    zero(literal-predicted, 'complete independent force differentiation of Q')
    g_force = 2*omega.dot(torque)/s
    zero(g_force-2*n.dot(normalized_torque), 'physical reaction has the forward sign')
    age = sp.symbols('a', nonnegative=True)
    zero(2*g_force+age*literal-(4*n.dot(normalized_torque)+age*predicted),
         'complete reward and capped-reserve source correction')
    return dict(impulse_source='+f in backward L', direction_source='-(Id-n n^T)c_f',
                reserve_source='2 I.f/nu+2 beta z n.f+(2 beta z I+2 beta d k+2 alpha nu z k).F_n',
                complete_source='4 n.c_f+a times reserve_source',
                scope='generator difference at identical instantaneous spatial fields')


def rotating_forced_shear():
    x, y, z, time = sp.symbols('x y z t', real=True)
    amplitude, nu, rotation = sp.symbols('A nu Omega', positive=True)
    coords = (x, y, z)
    grad = lambda v: sp.Matrix([sp.diff(v, c) for c in coords])
    lap = lambda v: sum(sp.diff(v, c, 2) for c in coords)
    curl = lambda v: sp.Matrix([sp.diff(v[2], y)-sp.diff(v[1], z),
                                sp.diff(v[0], z)-sp.diff(v[2], x),
                                sp.diff(v[1], x)-sp.diff(v[0], y)])
    decay = amplitude*sp.exp(-nu*time)
    e = sp.Matrix([sp.cos(rotation*time), sp.sin(rotation*time), 0])
    e_perp = sp.Matrix([-sp.sin(rotation*time), sp.cos(rotation*time), 0])
    u = decay*sp.sin(z)*e
    force = decay*rotation*sp.sin(z)*e_perp
    omega, torque = curl(u), curl(force)
    B = u.jacobian(coords)
    residual = u.diff(time)+B*u-nu*u.applyfunc(lap)-force
    for j, value in enumerate(residual):
        zero(sp.trigsimp(value), ('actual all-time forced NS, pressure zero', j))
    zero(B.trace(), 'rotating shear remains incompressible')
    zero(sp.trigsimp(u.dot(force)), 'force has zero kinetic work pointwise')
    zero(sp.trigsimp(omega.dot(torque)), 'force has zero enstrophy work pointwise')
    zero(sp.trigsimp(torque.dot(torque)-decay**2*rotation**2*sp.cos(z)**2),
         'curl forcing is nonzero despite zero work')
    H = decay*sp.sin(z)*sp.Matrix([1, 0, 0])
    impulse = H-u
    D = lambda v: v.diff(time)+u.dot(grad(v))-nu*lap(v)
    for j in range(3):
        zero(sp.trigsimp(D(H[j])), ('original passive parent, no restart', j))
        zero(sp.trigsimp(D(impulse[j])+force[j]), ('literal impulse retains force', j))
    delta = sp.symbols('delta', positive=True)
    s = sp.trigsimp(omega.dot(omega))+delta
    normalized = omega/sp.sqrt(s)
    nforce = -(sp.eye(3)-normalized*normalized.T)*torque/sp.sqrt(s)
    for j, value in enumerate(nforce+torque/sp.sqrt(s)):
        zero(sp.trigsimp(value), ('zero radial work still rotates the direction', j))
    zero(sp.trigsimp(omega.dot(B*omega)), 'rotating shear has no vortex stretching')
    zero(sp.trigsimp(omega.dot(impulse.jacobian(coords)*omega)),
         'this calibration has no positive impulse stretching')
    return dict(velocity='A exp(-nu t) sin(z) (cos(Omega t),sin(Omega t),0)',
                pressure='0', kinetic_force_work='0 pointwise', enstrophy_force_work='0 pointwise',
                nonzero_orientation_source=True, original_passive_parent_retained=True,
                remaining_reaction='-2 nu |grad omega|^2/(|omega|^2+delta) <= 0',
                scope='smooth periodic forced flow, not the imported singular candidate')


def curl_and_heat_constants():
    magnitude, regularizer = sp.symbols('magnitude regularizer', nonnegative=True)
    zero(magnitude**2+regularizer**2-2*magnitude*regularizer
         -(magnitude-regularizer)**2, 'sharp normalized curl-force bound')
    radius, heat_time = sp.symbols('radius heat_time', positive=True)
    heat = (4*sp.pi*heat_time)**(-sp.Rational(3, 2))*sp.exp(-radius**2/(4*heat_time))
    square_integral = sp.integrate(4*sp.pi*radius**2*heat**2, (radius, 0, sp.oo))
    gradient_integral = sp.integrate(4*sp.pi*radius**2*radius*heat/(2*heat_time),
                                   (radius, 0, sp.oo))
    zero(square_integral-(8*sp.pi*heat_time)**(-sp.Rational(3, 2)), 'R3 heat L2 constant')
    zero(gradient_integral-2/sp.sqrt(sp.pi*heat_time), 'R3 heat gradient L1 constant')
    ell = sp.symbols('ell', positive=True)
    zero(sp.integrate(gradient_integral, (heat_time, 0, ell**2))-4*ell/sp.sqrt(sp.pi),
         'integrated heat-curl bound')
    a, b = sp.symbols('a b', positive=True)
    balanced_radius = (a/b)**sp.Rational(2, 5)
    zero(a*balanced_radius**(-sp.Rational(3, 2))+b*balanced_radius
         -2*a**sp.Rational(2, 5)*b**sp.Rational(3, 5), 'velocity-vorticity interpolation powers')
    return dict(normalized_force_bound='sup|curl f|/sqrt(delta)',
                heat_L2='(8 pi s)^(-3/4)', heat_gradient_L1='2/sqrt(pi s)',
                velocity_bound='(8 pi)^(-3/4) R^(-3/2)||u||_2+(4/sqrt(pi)) R||omega||_infinity',
                scope='exact constants; convolution estimates and Feynman--Kac are analytic')


def internal_sources(u0, label, cutoff_squared):
    # P observes a fixed Fourier ball selected from the original datum. The evolving velocity is
    # never projected: every output and its pressure-dependent next jet stay.
    project = lambda p: {k: c for k, c in p.items() if sum(j*j for j in k) <= cutoff_squared}
    pv = lambda v: [project(p) for p in v]
    add = lambda v, w: [f.add(a, b) for a, b in zip(v, w)]
    sub = lambda v, w: [f.add(a, f.scale(-1, b)) for a, b in zip(v, w)]
    adv = lambda u, v: [f.adv(u, p) for p in v]
    nu = Q(1)
    jets, pressures = velocity_time_jets(u0, nu, 2)
    omega = [f.curl(u) for u in jets]
    eta = [pv(w) for w in omega]
    zeta = [sub(w, e) for w, e in zip(omega, eta)]
    B = [f.jac(u) for u in jets]
    sources = []
    for order in range(2):
        stretch = [{}, {}, {}]
        resolved_stretch = [{}, {}, {}]
        transport = [{}, {}, {}]
        resolved_transport = [{}, {}, {}]
        for j in range(order+1):
            stretch = add(stretch, f.matvec(B[j], omega[order-j]))
            resolved_stretch = add(resolved_stretch, f.matvec(B[j], eta[order-j]))
            transport = add(transport, adv(jets[j], omega[order-j]))
            resolved_transport = add(resolved_transport, adv(jets[j], eta[order-j]))
        xi = add(sub(pv(stretch), resolved_stretch), sub(resolved_transport, pv(transport)))
        left = add(eta[order+1], resolved_transport)
        left = sub(left, [f.scale(nu, f.lap(e)) for e in eta[order]])
        for k in range(3):
            f.equal(left[k], f.add(resolved_stretch[k], xi[k]),
                    (label, order, k, 'resolved full-drift vorticity equation'))
        hidden_transport = sub(transport, resolved_transport)
        hidden_stretch = sub(stretch, resolved_stretch)
        left_hidden = add(zeta[order+1], hidden_transport)
        left_hidden = sub(left_hidden, [f.scale(nu, f.lap(v)) for v in zeta[order]])
        for k in range(3):
            f.equal(left_hidden[k], f.add(hidden_stretch[k], f.scale(-1, xi[k])),
                    (label, order, k, 'same internal source has the opposite hidden sign'))
        sources.append(xi)
    diagonal_source = f.scale(2, f.dot(sub(eta[0], zeta[0]), sources[0]))
    cross_source = f.scale(2, f.add(f.dot(sources[0], zeta[0]),
                                  f.scale(-1, f.dot(eta[0], sources[0]))))
    f.equal(f.add(diagonal_source, cross_source), {},
            (label, 'cross correlation cancels the artificial total source'))
    if not any(sources[0]):
        raise ArithmeticError((label, 'fixture must have an actual internal source'))
    return dict(fixture=label, cutoff_squared=cutoff_squared, pressure_modes=[len(p) for p in pressures],
                source_modes=[len(set().union(*(set(p) for p in v))) for v in sources],
                diagonal_source_modes=len(diagonal_source),
                source_at_origin=[str(f.evaluate(p)) for p in sources[0]],
                full_time_derivatives_checked=2,
                scope='actual unforced NS jets, not an autonomous projected evolution')


def main():
    simple = parent.carrier(r.c.simple_parent(), Q(16), 4, [{}, {}, {}])
    background = r.ns.vector_scale(Q(-20000), r.ns.nonlinear(r.c.resonant_parent()))
    resonant = parent.carrier(r.c.resonant_parent(), Q(200), 4, background)
    cases = [(r.counterstrain_datum(Q(4), Q(8)), 'pressure_start', 1),
             (r.record_datum(Q(4), Q(8)), 'original_maximum', 1),
             (simple, 'original_simple_carrier', 10), (resonant, 'original_resonant_carrier', 3)]
    result = dict(status='all exact checks passed', force=force_generator(),
                  rotating_shear=rotating_forced_shear(), constants=curl_and_heat_constants(),
                  internal_sources=[internal_sources(*case) for case in cases],
                  scope='forced history obstruction analytic; arbitrary-data unforced payment open; no new Lean')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
