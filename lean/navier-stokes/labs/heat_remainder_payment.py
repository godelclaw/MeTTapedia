#!/usr/bin/env python3
"""Exact physical identities for the remainder after the original heat flow.

The reference is fixed by the original datum. The full remainder equation,
pressure cancellation in its integrated enstrophy, and signed generated
source fixtures are checked here. The arbitrary-prefix estimates and local
solution interpretation are analytic in README.md, not certified by Python.
"""

import json
from fractions import Fraction as Q

import normalized_receiver as nr
from reciprocal_pattern_cycles import mean, mode

s, f = nr.s, nr.f


def positive_seed():
    waves = ((1, 0, 1), (1, -1, 1), (2, 0, 1), (2, -1, 1))
    vectors = ((3, 1, -3), (-1, -3, -2), (-2, 9, 4), (3, 9, 3))
    u = [{}, {}, {}]
    for k, v in zip(waves, vectors):
        s.require(sum(a*b for a, b in zip(k, v)) == 0, 'transverse polarization')
        for j in range(3):
            u[j] = f.add(u[j], mode(k, Q(v[j], 10)))
    return u


def heat_at(u, q):
    return nr.rc.field({k: tuple(q**sum(x*x for x in k)*a for a in z)
                        for k, z in s.modes(u).items()})


def magnitude_bound(field):
    return sum((Q(str(abs(a.x)+abs(a.y))) for a in field.values()), Q(0))


def integrated_mixed(h, b):
    """Integrate both linearized transport terms by parts, with all slots."""
    terms = [Q(0), Q(0), Q(0)]
    for i in range(3):
        for j in range(3):
            for k in range(3):
                db = f.diff(b[j], i)
                terms[0] -= mean(f.mul(db, f.mul(f.diff(h[k], i), f.diff(b[j], k))))
                terms[1] -= mean(f.mul(db, f.mul(f.diff(b[k], i), f.diff(h[j], k))))
                terms[2] -= mean(f.mul(db, f.mul(b[k], f.diff(f.diff(h[j], k), i))))
    return terms


def physical_identity(h, b, nu, length):
    u = s.vector_add(h, b)
    for name, v in (('heat reference', h), ('remainder', b)):
        f.equal(f.trace(f.jac(v)), {}, (name, 'solenoidal'))
    Nh, Nb, Nu = (s.nonlinear(v) for v in (h, b, u))
    cross = s.vector_add(s.vector_add(Nu, s.vector_scale(-1, Nh)), s.vector_scale(-1, Nb))
    ht = s.vector_scale(-nu, s.minus_laplacian(h))
    ut = s.vector_add(s.vector_scale(-nu, s.minus_laplacian(u)), Nu)
    bt = s.vector_add(ut, s.vector_scale(-1, ht))
    split = s.vector_add(s.vector_scale(-nu, s.minus_laplacian(b)),
                         s.vector_add(Nh, s.vector_add(cross, Nb)))
    for a, c in zip(bt, split):
        f.equal(a, c, 'complete actual remainder direction')
    Ab = s.minus_laplacian(b)
    E, Z, D = s.inner(b, b), s.inner(b, Ab), s.inner(Ab, Ab)
    kinetic_parent = s.inner(b, f.matvec(f.jac(h), b))
    s.require(2*s.inner(b, bt)+2*nu*Z == -2*kinetic_parent+2*s.inner(b, Nh),
              'kinetic remainder identity cancels self-advection and reference transport')
    mixed, supplied = s.inner(Ab, cross), s.inner(Ab, Nh)
    parts = integrated_mixed(h, b)
    s.require(mixed == sum(parts), 'all integrated mixed transport and deformation terms')
    zd = 2*s.inner(Ab, bt)
    g = s.cubic(b)
    s.require(zd+2*nu*D == 2*g+2*mixed+2*supplied,
              'physical relative enstrophy identity retains complete pressure')
    G = sum(magnitude_bound(f.diff(a, j)) for a in h for j in range(3))
    L = sum(magnitude_bound(f.diff(f.diff(a, j), k))
            for a in h for j in range(3) for k in range(3))
    s.require(abs(kinetic_parent) <= G*E,
              'only the known heat strain enters the kinetic comparison coefficient')
    gap = abs(mixed)-2*G*Z
    s.require(gap <= 0 or gap*gap <= L*L*E*Z,
              'mixed work has the stated first- and second-derivative bound')
    source_sq = s.inner(Nh, Nh)
    s.require(2*supplied <= nu*D/2+2*source_sq/nu,
              'half of one viscous unit pays the original heat source pairing')
    rhs = (4*G+length*L)*Z+L*E/length+2*source_sq/nu
    s.require(zd+Q(3, 2)*nu*D-2*g <= rhs,
              'complete generated-remainder estimate with the residual cubic retained')
    s.require(E <= 2*s.inner(u, u)+2*s.inner(h, h),
              'the physical difference has a full-field energy bound')
    s.require(any(s.vertical_mean(bt)), 'the evolving mean is retained')
    return {'viscosity': str(nu), 'length': str(length),
            'mixed_terms': [str(t) for t in parts], 'supplied_pairing': str(supplied),
            'remainder_cubic': str(g), 'exact_relative_balance': True}


def generated_sign(u, expected):
    v = s.nonlinear(u)
    s.require(s.cubic(v) == s.inner(s.minus_laplacian(v), s.nonlinear(v)) == expected,
              'two independent physical formulas give the generated self-stretching')
    for nu in (Q(1), Q(2, 7)):
        heat_tangent = s.vector_scale(-nu, s.minus_laplacian(u))
        actual_tangent = s.vector_add(heat_tangent, v)
        for a, b in zip(s.vector_add(actual_tangent, s.vector_scale(-1, heat_tangent)), v):
            f.equal(a, b, 'zero-initial remainder has exactly the full nonlinear first derivative')
    s.require(any(s.vertical_mean(v)), 'generated source includes its vertical mean')
    return {'energy': str(s.inner(u, u)), 'generated_cubic': str(expected),
            'sign': 'positive' if expected > 0 else 'negative'}


def main():
    negative = s.real_field(s.seed())
    positive = positive_seed()
    signs = [generated_sign(negative, Q(-75009477, 773500000)),
             generated_sign(positive, Q(706789431, 24752000000))]
    h = heat_at(negative, Q(3, 4))
    b = s.vector_add(s.vector_scale(Q(1, 10), s.nonlinear(positive)),
                     s.vector_scale(Q(1, 3), positive))
    identities = [physical_identity(h, b, Q(1), Q(1)),
                  physical_identity(h, s.vector_scale(-1, b), Q(2, 7), Q(3, 2))]
    print(json.dumps({'status': 'all exact checks passed', 'generated_signs': signs,
                      'physical_identities': identities,
                      'scope': 'finite physical algebra; arbitrary-prefix payment and solution jets analytic'},
                     indent=2))


if __name__ == '__main__':
    main()
