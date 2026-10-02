#!/usr/bin/env python3
"""Exact fixtures for filtered source histories and their full-energy payment.

The heat cutoff is rho=-log(q), with rational 0<q<1. Every Fourier
coefficient, physical derivative and heat integral below is exact.
The general PDE estimates and adjoint construction are analytic in README.md.
"""

import json
import sys
from fractions import Fraction as Q

import covariance_poisson_corrector as p

t, s, f = p.t, p.s, p.f

# Exact heat weights in the thin-belt fixtures have very large denominators.
# The shared rational helpers convert these internally through decimal text.
sys.set_int_max_str_digits(0)


def heat_filter(u, q):
    return [{k: a*q**sum(j*j for j in k) for k, a in row.items()}
            for row in u]


def filtered_blocks(blocks, q):
    return t.scale(1, {key: tuple(q**key[1]*a for a in value)
                       for key, value in blocks.items()})


def project(u):
    divergence = f.add(*(f.diff(row, j) for j, row in enumerate(u)))
    return s.oscillation(s.vector_add(u, f.grad(f.green(divergence))))


def bilinear(a, b):
    return project([f.scale(-1, f.adv(a, row)) for row in b])


def linearized(v, y):
    return s.vector_add(bilinear(v, y), bilinear(y, v))


def adjoint(v, psi):
    transposed = list(zip(*f.jac(v)))
    return project(s.vector_add([f.adv(v, row) for row in psi],
                                s.vector_scale(-1, f.matvec(transposed, psi))))


def same(a, b, label):
    for left, right in zip(a, b):
        f.equal(left, right, label)


def coarse_capacity(w, q, nu):
    n = filtered_blocks(s.source_blocks(w, w), q)
    return s.heat_pair(n, n, nu)


def coarse_derivative(w, direction, q, nu):
    n = filtered_blocks(s.source_blocks(w, w), q)
    dn = filtered_blocks(s.add_blocks(s.source_blocks(w, direction),
                                      s.source_blocks(direction, w)), q)
    return 2*s.heat_pair(n, dn, nu)


def lattice_majorant(q):
    r = q*q
    s.require(0 < r < 1, 'positive fixed heat cutoff')
    return (1+r)**3*(1+4*r+r*r)/(1-r)**5


def physical_source(u, q, nu):
    w, h = s.oscillation(u), s.oscillation(s.nonlinear(u))
    v, z = heat_filter(w, q), heat_filter(h, q)
    n = s.oscillation(s.nonlinear(v))
    w_rate = s.vector_add(s.vector_scale(-nu, s.minus_laplacian(w)), h)
    direct = linearized(v, heat_filter(w_rate, q))
    G = [{}, {}, {}]
    for j in range(3):
        dv = [f.diff(row, j) for row in v]
        G = s.vector_add(G, bilinear(dv, dv))
    hidden = s.vector_add(z, s.vector_scale(-1, n))
    forcing = s.vector_add(linearized(v, hidden), s.vector_scale(-2*nu, G))
    rhs = s.vector_add(s.vector_add(s.vector_scale(-nu, s.minus_laplacian(n)),
                                   linearized(v, n)), forcing)
    same(direct, rhs, 'actual source evolution keeps hidden parents and product diffusion')

    # A nontrivial solenoidal terminal test; no closed adjoint mode set is used.
    psi = s.vector_add(w, s.vector_scale(Q(1, 7), h))
    star = adjoint(v, psi)
    s.require(s.inner(psi, linearized(v, n)) == s.inner(star, n),
              'projected physical adjoint with its pressure')
    psi_rate = s.vector_add(s.vector_scale(nu, s.minus_laplacian(psi)),
                            s.vector_scale(-1, star))
    s.require(s.inner(psi_rate, n)+s.inner(psi, direct) == s.inner(psi, forcing),
              'backward adjoint cancels both linear terms and retains the actual source')
    adjoint_generator = s.vector_add(s.vector_scale(-nu, s.minus_laplacian(psi)), star)
    deformation = -s.inner(psi, f.matvec(list(zip(*f.jac(v))), psi))
    s.require(s.inner(psi, adjoint_generator)
              == -nu*s.inner(psi, s.minus_laplacian(psi))+deformation,
              'adjoint norm keeps viscosity and signed deformation; transport cancels')
    return {'source_modes': len(s.modes(n)), 'hidden_force_nonzero': any(forcing),
            'adjoint_pair_nonzero': bool(s.inner(psi, forcing))}


def history_check(u, q=Q(1, 2), nu=Q(1)):
    w, h = s.oscillation(u), s.oscillation(s.nonlinear(u))
    heat = s.vector_scale(-nu, s.minus_laplacian(w))
    boundary = s.oscillation(s.nonlinear(heat_filter(w, q)))
    loss = s.inner(boundary, boundary)/nu
    coarse = coarse_capacity(w, q, nu)
    renewal = coarse_derivative(w, h, q, nu)
    s.require(coarse_derivative(w, heat, q, nu) == -loss,
              'coarse heat lifetime spends precisely its lower endpoint source')
    s.require(coarse_derivative(w, s.vector_add(heat, h), q, nu) == -loss+renewal,
              'complete physical coarse derivative')

    observer = t.source_observer(t.heat(w), s.source_blocks(w, w))
    by_adjoint = 2*s.heat_pair(filtered_blocks(t.heat(h), q),
                              filtered_blocks(observer, q), nu)
    # Move all spatial derivatives onto the actual smoothed observer.
    tensor = {}
    for k, a in s.modes(u).items():
        for ell, b in s.modes(u).items():
            wave = tuple(x+y for x, y in zip(k, ell))
            t.accumulate(tensor, (wave, 0), tuple(x*y for x in a for y in b))
    smoothed = {}
    for (k, rate), a in observer.items():
        t.accumulate(smoothed, (k, rate+sum(j*j for j in k)), a)
    by_tensor = 2*t.stress_pair(t.cleaned(tensor), filtered_blocks(t.cleaned(smoothed), q), nu)
    s.require(renewal == by_adjoint == by_tensor,
              'complete renewal equals the full-fluid tensor and moving observer pairing')

    E, Z = s.inner(u, u), s.inner(u, s.minus_laplacian(u))
    L = lattice_majorant(q)
    price = 3*L*L/(2*nu**2)
    s.require(renewal**2 <= price**2*E**3*Z**2,
              'exact squared test of the universal full-energy payment bound')
    s.require(s.inner(u, s.nonlinear(u)) == 0,
              'the paying full-energy reserve has no nonlinear renewal defect')
    s.require(s.capacity(w, nu)-coarse >= 0,
              'the remaining small-heat-time capacity is nonnegative')
    s.require(s.capacity_derivative(w, heat, nu)-coarse_derivative(w, heat, q, nu)
              == -(s.inner(s.oscillation(s.nonlinear(w)), s.oscillation(s.nonlinear(w)))/nu-loss),
              'fine and coarse boundary losses cancel without spending twice')
    row = physical_source(u, q, nu)
    row.update({'nu': str(nu), 'q': str(q), 'renewal_sign': (renewal > 0)-(renewal < 0),
                'capacity_positive': coarse > 0, 'bound_passed': True,
                'full_mean_retained': any(s.vertical_mean(u)),
                'mean_generated': any(s.vertical_mean(s.nonlinear(u)))})
    return row


def scalar_checks():
    s.require(lattice_majorant(Q(1, 2)) == Q(1375, 81),
              'closed rational upper bound on the heat lattice sum')
    # Cauchy-Schwarz on interval lengths and energy actually spent.
    lengths, spending = (Q(1), Q(4), Q(9)), (Q(4), Q(1), Q(9))
    s.require((Q(2)+Q(2)+Q(9))**2 <= sum(lengths)*sum(spending),
              'composed adjoint growth uses a single original energy reserve')


def polarization_check():
    u, nu, q = p.planar_belt(2), Q(2, 7), Q(1, 2)
    direction = s.vector_add(s.nonlinear(u), s.vector_scale(-nu, s.minus_laplacian(u)))
    receiver_direction = s.oscillation(direction)
    values = {j: coarse_capacity(s.oscillation(s.vector_add(u, s.vector_scale(j, direction))), q, nu)
              for j in (-2, -1, 1, 2)}
    polarized = (8*(values[1]-values[-1])-values[2]+values[-2])/12
    s.require(polarized == coarse_derivative(u, receiver_direction, q, nu),
              'independent exact quartic polarization of the full physical tangent')


def shear_adjoint_check():
    from reciprocal_pattern_cycles import mode
    nu, amplitude, q = Q(2, 7), Q(256, 7), Q(1, 2)
    # Exact NS shear u=(A exp(-nu t) sin(z),0,0), tested at t=0.
    u = [mode((0, 0, 1), amplitude, True), {}, {}]
    cosine_y, cosine_z = mode((0, 1, 0), 1), mode((0, 0, 1), 1)
    sine_y, sine_2z = mode((0, 1, 0), 1, True), mode((0, 0, 2), 1, True)
    psi = [f.mul(cosine_y, cosine_z), f.scale(-2, f.mul(sine_y, sine_2z)),
           f.scale(-1, f.mul(cosine_y, mode((0, 0, 2), 1)))]
    f.equal(f.trace(f.jac(psi)), {}, 'shear adjoint test is solenoidal')
    s.require(s.inner(psi, psi) == Q(3, 2) and s.inner(psi, s.minus_laplacian(psi)) == Q(27, 4),
              'exact shear-test normalization')
    s.require(not any(s.vertical_mean(u)) and not any(s.vertical_mean(psi)),
              'both the shear and terminal test belong to the receiver subspace')
    generator = s.vector_add(s.vector_scale(-nu, s.minus_laplacian(psi)),
                             adjoint(heat_filter(u, q), psi))
    rate = s.inner(psi, generator)
    s.require(rate == -27*nu/4+amplitude*q/8 == 5*nu/4 > 0,
              'an actual decaying shear permits transient backward-adjoint norm growth')
    return str(rate)


def main():
    scalar_checks()
    polarization_check()
    shear_rate = shear_adjoint_check()
    rows = []
    for label, u in zip(('matched_minus', 'matched_plus'), s.matched_fields()):
        rows.append(dict(name=label, **history_check(u)))
    r = s.real_field(s.seed())
    full = s.vector_add(r, s.vector_scale(Q(-1, 10), s.nonlinear(r)))
    rows.append(dict(name='generated_mean', **history_check(full, nu=Q(2, 7))))
    for length in (2, 16, 32):
        rows.append(dict(name=f'planar_belt_{length}',
                         **history_check(p.planar_belt(length), nu=Q(2, 7))))
    s.require(all(row['hidden_force_nonzero'] for row in rows),
              'none of the fixtures silently deletes the hidden source')
    s.require(rows[0]['renewal_sign'] == 1 and rows[1]['renewal_sign'] == -1,
              'the same reserve pays both actual signed hidden phases')
    print(json.dumps({'status': 'all exact checks passed', 'cases': rows,
                      'shear_adjoint_half_norm_rate': shear_rate,
                      'scope': 'finite algebra; arbitrary-history estimates analytic',
                      'open': 'payment uniform as the heat cutoff tends to zero'}, indent=2))


if __name__ == '__main__':
    main()
