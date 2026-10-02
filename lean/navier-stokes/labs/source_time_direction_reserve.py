#!/usr/bin/env python3
"""Physical source-direction squares and their complete growth matrices.

Fourier algebra is exact and retains pressure and generated means.
Actual solution intervals and parent release are analytic in README.md.
The two directions are the time derivative and its filtered-transport
adjustment; neither is a separately evolved closure model.
"""

import json
from fractions import Fraction as Q

import capacity_return_cycle as r

s, a, rc, f = r.s, r.a, r.rc, r.f


def advect(left, right):
    result = {}
    for (p, pr), v in left.items():
        for (q, qr), n in right.items():
            factor = f.II*s.dot(v, q)
            if factor:
                k = tuple(x+y for x, y in zip(p, q))
                a.c.accumulate(result, (k, pr+qr), tuple(factor*z for z in n))
    return a.c.cleaned(result)


def determinant(matrix):
    x, y, z = matrix
    return x*z-y*y


def quadratic(matrix, eta):
    x, y, z = matrix
    return x+2*eta*y+eta*eta*z


def positive(matrix):
    return matrix[0] > 0 and determinant(matrix) > 0


def bilinear(u, v):
    return a.collapse(rc.source_blocks(u, v))


def original_parent_derivatives():
    h = s.vector_scale(Q(1, 5), a.d.phase_seed(-1))
    b = s.vector_scale(Q(1, 3), s.nonlinear(h))
    nu = Q(3, 7)
    u = s.vector_add(b, h)
    ht = s.vector_scale(-nu, s.minus_laplacian(h))
    d = s.vector_add(s.vector_scale(-nu, s.minus_laplacian(b)), s.nonlinear(u))
    e = s.vector_add(s.vector_scale(-nu, s.minus_laplacian(d)),
                     a.source_derivative(u, s.vector_add(d, ht)))
    expanded = s.vector_scale(-nu, s.minus_laplacian(d))
    for term in (a.source_derivative(b, d), a.source_derivative(h, ht),
                 bilinear(ht, b), bilinear(h, d), bilinear(d, h), bilinear(b, ht)):
        expanded = s.vector_add(expanded, term)
    for x, y in zip(e, expanded):
        f.equal(x, y, 'the actual remainder acceleration retains every original-heat interaction')
    free = s.vector_add(s.vector_scale(-nu, s.minus_laplacian(d)), a.source_derivative(b, d))
    s.require(e != free, 'the parent terms cannot be discarded before release')


def matrices(w, mu):
    row, d, e = r.physical_jet(w, mu)
    n = rc.source_blocks(w, w)
    n1 = s.add_blocks(rc.source_blocks(w, d), rc.source_blocks(d, w))
    n2 = s.add_blocks(rc.source_blocks(w, e), rc.source_blocks(e, w),
                      a.c.scale(2, rc.source_blocks(d, d)))
    v, vd = a.c.heat(w), a.c.heat(d)
    m = s.add_blocks(n1, advect(v, n))
    md = s.add_blocks(n2, advect(vd, n), advect(v, n1))
    s.require(2*s.heat_pair(n, m) == row['capacity_rate'],
              'filtered transport cancels from the mixed square')
    s.require(s.heat_pair(n1, m)+s.heat_pair(n, md) == row['capacity_second_rate']/2,
              'the derivative retains the changing transport velocity')
    result = {}
    for name, z, zd in (('time', n1, n2), ('transport_adjusted', m, md)):
        G = (rc.capacity(w), s.heat_pair(n, z), s.heat_pair(z, z))
        L = (row['capacity_rate'], s.heat_pair(n1, z)+s.heat_pair(n, zd),
             2*s.heat_pair(z, zd))
        s.require(positive(G), 'the source and its direction are independent in the heat norm')
        s.require(G[1] == row['capacity_rate']/2 and L[1] == row['capacity_second_rate']/2,
                  'both exact mixed entries agree with capacity derivatives')
        for eta in (Q(-1, 50), Q(0), Q(1, 50)):
            y = s.add_blocks(n, a.c.scale(eta, z))
            yd = s.add_blocks(n1, a.c.scale(eta, zd))
            s.require(s.heat_pair(y, y) == quadratic(G, eta)
                      and 2*s.heat_pair(y, yd) == quadratic(L, eta),
                      'direct full-square differentiation agrees with its coefficient matrix')
        C, x, K = G
        optimal = -x/K
        reduced = C-x*x/K
        reduced_rate = L[0]-2*x*L[1]/K+x*x*L[2]/K**2
        s.require(reduced > 0 and quadratic(G, optimal) == reduced
                  and quadratic(L, optimal) == reduced_rate,
                  'Schur elimination reconstructs the minimizing direction and its full rate')
        for eta in (Q(-1), Q(1, 50), Q(2)):
            s.require(quadratic(G, eta) == reduced+K*(eta-optimal)**2,
                      'the exact square completion retains its interior witness')
        result[name] = dict(gram=G, rate=L, rate_determinant=determinant(L),
                            reduced=reduced, reduced_rate=reduced_rate)
    return row, result


def main():
    original_parent_derivatives()
    rows = []
    for label, V, mu in (('growing', a.d.phase_seed(-1), Q(1, 256)),
                         ('depleting', a.d.phase_seed(1), Q(1, 256)),
                         ('return', r.envelope(), None)):
        w = s.nonlinear(V)
        if mu is None:
            n = s.nonlinear(w)
            mu = rc.derivative(w, n)/s.inner(n, n)
        row, pairs = matrices(w, mu)
        for name, pair in pairs.items():
            G, L = pair['gram'], pair['rate']
            cooled = tuple(x-Q(1, 2)*y for x, y in zip(L, G))
            pair['half_rate_margin'] = cooled
            pair['half_rate_determinant'] = determinant(cooled)
            if label == 'growing':
                s.require(positive(cooled),
                          'every constant real mixture grows, even after half-rate cooling')
                s.require(pair['reduced_rate'] > pair['reduced']/2,
                          'pointwise optimal Schur elimination still increases the reserve')
                s.require(row['uniform_core_lower_at_seed'] > 80,
                          'the remaining cost stays positive after both paid regions')
            elif label == 'depleting':
                s.require(positive(tuple(-x for x in L)),
                          'the opposite phase makes both complete rate matrices negative definite')
            else:
                # Physical viscosity-one eta is mu/50, not 1/50.
                upper_cost = 2*s.cubic(w)-mu*s.inner(s.minus_laplacian(w), s.minus_laplacian(w))/2
                defect = quadratic(L, Q(1, 50))+mu**2*upper_cost
                s.require(defect < -400,
                          'strict seed margin for the analytic local return payment')
                s.require(pair['reduced_rate'] == 0,
                          'minimizing the reserve value does not minimize its payment defect')
                pair['return_defect_upper'] = defect
        rows.append(dict(label=label, physical=row, directions=pairs))
    print(json.dumps(dict(status='all exact checks passed', rows=rows,
                          scope='exact source matrices and parent identities; physical intervals and release analytic'),
                     default=str, indent=2))


if __name__ == '__main__':
    main()
