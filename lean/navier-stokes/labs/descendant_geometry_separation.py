#!/usr/bin/env python3
"""Complete descendant geometry and absorption of separated interactions.

The checker retains every Fourier output and the vertical mean. Finite
algebra is exact; PDE realization and the all-frequency estimate are
analytic in README.md. Selected interactions are observations of the full
flow, not an independently evolved truncation.
"""

import json
from fractions import Fraction as Q

import descendant_capacity_transfer as d
import receiver_transport_covariance as c

rc, s, f = d.nr.rc, d.s, d.f


def full_project(blocks):
    result = {}
    for (k, rate), a in blocks.items():
        kk = sum(x*x for x in k)
        value = tuple(a[j]-k[j]*s.dot(k, a)/kk for j in range(3)) if kk else a
        if any(value):
            result[k, rate] = value
    return result


def full_observer(v, n):
    result = {}
    for (p, r), a in v.items():
        for (q, t), b in n.items():
            k = tuple(x+y for x, y in zip(p, q))
            value = tuple(f.II*(s.dot(a, q)*b[i]-p[i]*s.dot(a, b)) for i in range(3))
            c.accumulate(result, (k, r+t), value)
    return full_project(c.cleaned(result))


def full_covariance_force(tau):
    return full_project({(k, r): tuple(-f.II*sum((k[j]*a[3*i+j] for j in range(3)), f.ZERO)
                                     for i in range(3)) for (k, r), a in tau.items()})


def collapse(blocks):
    result = {}
    for (k, _), a in blocks.items():
        c.accumulate(result, k, a)
    return rc.field(c.cleaned(result))


def source_derivative(w, direction):
    return collapse(s.add_blocks(rc.source_blocks(w, direction), rc.source_blocks(direction, w)))


def triple_rate(a, b, v, ad, bd, vd):
    return sum(c.advective_pair(x, y, z, Q(1))
               for x, y, z in ((ad, b, v), (a, bd, v), (a, b, vd)))


def geometry_check(phase):
    w = s.nonlinear(d.phase_seed(phase))
    nw = s.nonlinear(w)
    v, n = c.heat(w), rc.source_blocks(w, w)
    comm = s.add_blocks(c.heat(nw), c.scale(-1, n))
    transport = -2*c.advective_pair(n, v, n, Q(1))
    geometry = -2*c.advective_pair(n, n, v, Q(1))
    cov_deform = -2*c.advective_pair(n, comm, v, Q(1))
    cov_transport = -2*c.advective_pair(n, v, comm, Q(1))
    production = rc.derivative(w, nw)
    s.require(transport == 0 and geometry+cov_deform+cov_transport == production,
              'full capacity derivative equals source deformation plus both covariance terms')
    tau, observer = c.covariance(w), full_observer(v, n)
    s.require(full_covariance_force(tau) == comm == full_covariance_force(c.anisotropic(tau)),
              'full shared-heat covariance retains pressure and every mean output')
    s.require(cov_deform+cov_transport == 2*s.heat_pair(comm, observer)
              == 2*c.stress_pair(tau, observer, Q(1)),
              'independent projected tensor work agrees with both covariance terms')
    s.require(any(s.vertical_mean(w)) and any(s.vertical_mean(nw)),
              'input and new parent mean motion are present')

    # Rescaled actual NS evolution, viscosity 1/256. C1 is a fixed observer.
    # Physical b(t)=256*w(256*t) has viscosity one.
    mu = Q(1, 256)
    direction = s.vector_add(nw, s.vector_scale(-mu, s.minus_laplacian(w)))
    source_rate = source_derivative(w, direction)
    acceleration = s.vector_add(source_rate, s.vector_scale(-mu, s.minus_laplacian(direction)))
    vd = c.heat(direction)
    nd = s.add_blocks(rc.source_blocks(direction, w), rc.source_blocks(w, direction))
    cd = s.add_blocks(c.heat(source_rate), c.scale(-1, nd))
    geometry_rate = -2*triple_rate(n, n, v, nd, nd, vd)
    covariance_rate = -2*(triple_rate(n, comm, v, nd, cd, vd)
                         + triple_rate(n, v, comm, nd, vd, cd))
    Cprime = rc.derivative(w, direction)
    Csecond = geometry_rate+covariance_rate-2*mu*s.inner(nw, source_rate)
    ndd = s.add_blocks(rc.source_blocks(acceleration, w), rc.source_blocks(w, acceleration),
                       c.scale(2, rc.source_blocks(direction, direction)))
    s.require(Cprime == production-mu*s.inner(nw, nw),
              'viscosity spends the complete source square in the fixed C1 observer')
    s.require(Csecond == 2*s.heat_pair(nd, nd)+2*s.heat_pair(n, ndd),
              'independent second derivative retains source acceleration and every changing slot')
    gprime = s.inner(s.minus_laplacian(direction), nw)+s.inner(s.minus_laplacian(w), source_rate)
    sign = -phase
    s.require(all(sign*x > 0 for x in (geometry, cov_deform, cov_transport, Cprime, Csecond)),
              'both complete capacity rates and all production components have the stated signs')
    if phase == -1:
        s.require(Q(4, 5)*production < geometry < Q(9, 10)*production,
                  'source deformation supplies more than four fifths of adverse renewal')
        s.require(geometry_rate > 0 and covariance_rate > 0 and gprime > 0,
                  'adverse production initially strengthens under the full viscous evolution')
    return dict(phase=phase, geometry=geometry, covariance_deformation=cov_deform,
                covariance_transport=cov_transport, nonlinear_production=production,
                geometry_rate=geometry_rate, covariance_rate=covariance_rate,
                capacity_rate=Cprime, capacity_second_rate=Csecond, stretching_rate=gprime)


def separated(k, p, q, B2, nu, delta):
    """Exact torus selector; no fractional powers or rounded thresholds."""
    k2, p2, q2 = (sum(x*x for x in v) for v in (k, p, q))
    low, middle, _ = sorted((k2, p2, q2))
    return bool(low and 4*low <= middle
                and 59049*B2**2*low**5 <= (delta*nu)**4*middle**4)


def selected_vorticity_work(b, B2, nu, delta):
    """Independent masked integral of omega_i omega_j partial_j b_i."""
    velocity, vorticity = s.modes(b), s.modes(f.curl(b))
    total = f.ZERO
    for p, wp in vorticity.items():
        for q, uq in velocity.items():
            k = tuple(x+y for x, y in zip(p, q))
            wk = vorticity.get(tuple(-j for j in k))
            if wk is not None and separated(k, p, q, B2, nu, delta):
                total += f.II*s.dot(wp, q)*s.dot(wk, uq)
    s.require(total.y == 0, 'symmetric triad observation is real')
    return Q(str(total.x))


def selected_sources(b, B2, nu, delta, M=5, lam=7):
    outputs = [{}, {}, {}]
    counts = [0, 0, 0]
    for p, a in s.modes(b).items():
        for q, z in s.modes(b).items():
            k = tuple(x+y for x, y in zip(p, q))
            k2, p2, q2 = (sum(x*x for x in v) for v in (k, p, q))
            if not k2:
                continue
            value = tuple(-f.II*s.dot(a, k)*(z[j]-k[j]*s.dot(k, z)/k2) for j in range(3))
            is_sep = separated(k, p, q, B2, nu, delta)
            s.require(is_sep == separated(k, q, p, B2, nu, delta),
                      'the paid selector is symmetric in its two parents')
            index = 0 if is_sep else (1 if k2 <= M*M and min(p2, q2) >= lam*lam else 2)
            if any(value):
                c.accumulate(outputs[index], k, value)
                counts[index] += 1
    return [rc.field(c.cleaned(row)) for row in outputs], counts


def separation_checks():
    rows = []
    delta, nu = Q(1, 8), Q(1)
    v = d.phase_seed(-1)
    w = s.nonlinear(v)
    for carrier in (64, 128, 256):
        b = s.vector_add([f.mul(d.mode((0, 0, carrier), 1), a) for a in v],
                         s.vector_scale(Q(1, 3), w))
        E0 = s.inner(b, b)  # Algebra fixture with an admissible fixed L2 envelope.
        pieces, counts = selected_sources(b, 4*E0, nu, delta)
        complete = s.vector_add(s.vector_add(pieces[0], pieces[1]), pieces[2])
        for a, z in zip(complete, s.nonlinear(b)):
            f.equal(a, z, 'all three observations reconstruct the complete nonlinear source')
        Ab = s.minus_laplacian(b)
        Tsep, Tfixed, Tcore = (s.inner(Ab, n) for n in pieces)
        D = s.inner(Ab, Ab)
        s.require(0 < abs(Tsep) <= delta*nu*D,
                  'nonzero separated work is absorbed by its single full dissipation allocation')
        s.require(Tsep == selected_vorticity_work(b, 4*E0, nu, delta),
                  'all receiving roles give the identical masked vorticity-stretching observation')
        if carrier == 64:
            opposite = s.vector_scale(-1, b)
            reverse, _ = selected_sources(opposite, 4*E0, nu, delta)
            for a, z in zip(reverse[0], pieces[0]):
                f.equal(a, z, 'opposite initial velocity has the same quadratic selected source')
            reverse_work = s.inner(s.minus_laplacian(opposite), reverse[0])
            s.require(0 < reverse_work == -Tsep <= delta*nu*D,
                      'the same absorption also pays a strictly positive transfer phase')
        high = d.select(b, lambda k2: k2 >= 49)
        s.require(s.inner(pieces[1], pieces[1]) <= d.lattice_constant_squared(5)*s.inner(high, high)**2,
                  'the disjoint fixed-band remainder keeps the original force payment bound')
        s.require(Tsep+Tfixed+Tcore == s.cubic(b),
                  'the continuation core contains exactly every unpaid interaction')
        rows.append(dict(carrier=carrier, paid_pairs=counts[0], fixed_pairs=counts[1],
                         core_pairs=counts[2], separated_stretching=Tsep,
                         absorption_fraction=Tsep/(nu*D)))
    for phase in (-1, 1):
        b = s.vector_scale(256, s.nonlinear(d.phase_seed(phase)))
        pieces, counts = selected_sources(b, 4*s.inner(b, b), nu, delta)
        s.require(counts[:2] == [0, 0], 'both released descendants remain entirely in the unpaid core')
    s.require(1-2*delta == Q(3, 4), 'the new sufficient core budget retains three quarters of viscosity')
    return rows


def main():
    result = dict(status='all exact checks passed',
                  geometry=[geometry_check(phase) for phase in (-1, 1)],
                  separation=separation_checks(),
                  scope='exact finite algebra; actual local intervals and all-frequency absorption analytic')
    print(json.dumps(result, default=str, indent=2))


if __name__ == '__main__':
    main()
