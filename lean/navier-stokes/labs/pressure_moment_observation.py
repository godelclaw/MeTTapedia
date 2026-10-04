"""Exact finite-order moment dependencies for a prescribed mean observation.

All supplied velocity and pressure fields remain complete. Only auxiliary
moment modes with no route to the requested mean observations are omitted.
The recurrence below is valid because the requested sets are closed
backwards under every source and transport edge before evaluation.
"""
from fractions import Fraction as Q
import paired_stretching_history as e
import pressure_impulse_payment as p
from pressure_oblique_return import require


def difference(target, source):
    return {tuple(x-y for x, y in zip(q, k)) for q in target for k in source}


def supports(u, g, degree):
    """Close the observed modes under all lower-amplitude parent dependencies.

    A product contributing at q uses every pair k+l=q. Thus a required
    output set D requires the other parent's modes D-supp(known source).
    Transport lowers amplitude degree; a pressure source also lowers
    moment order. These two strict decreases make this backward sweep finite.
    """
    gs = {n: set().union(*fields) for n, fields in g.items()}
    us = {n: set(v) for n, v in enumerate(u)}
    needs = {1: {n: set() for n in range(3, degree-8)},
             2: {n: set() for n in range(6, degree-5)},
             3: {n: set() for n in range(9, degree-2)}}
    for n in needs[3]:
        for total in range(12, degree+1):
            for q in gs.get(total-n, set()):
                needs[3][n].add(tuple(-x for x in q))
    for level in (3, 2, 1):
        minimum = 3*level
        for n in sorted(needs[level], reverse=True):
            target = needs[level][n]
            for a in range(1, n-minimum+1):
                needs[level][n-a].update(difference(target, us[a]))
            if level > 1:
                for a in needs[level-1]:
                    if n-a in gs:
                        needs[level-1][a].update(difference(target, gs[n-a]))
    return needs


def multiply(a, b, target):
    result = {}
    for k, v in a.items():
        for ell, w in b.items():
            q = tuple(x+y for x, y in zip(k, ell))
            if q in target:
                result[q] = e.add(result.get(q, {}), e.multiply(v, w))
    return p.clean(result)


def transport(u, a, target):
    result = {}
    for k, v in u.items():
        for ell, w in a.items():
            q = tuple(x+y for x, y in zip(k, ell))
            if q in target:
                factor = e.add(*(e.scale(ell[i], v[i]) for i in range(3)))
                if factor:
                    result[q] = e.add(result.get(q, {}), e.multiply(factor, w))
    return p.clean(result)


def observed_history(u, pressure, degree=14):
    """Exact mean coefficients through degree, with zero-amplitude background.

    Induct on moment order and then amplitude degree. For each retained
    mode, the source contains every full-recurrence parent, by supports().
    Its heat equation and zero initial value therefore agree with the full
    recurrence. The final mean uses only these retained modes. This is an
    exact finite-order observation, not a closed model of the actual flow.
    """
    require(degree >= 14 and len(u) >= degree-8 and len(pressure) >= degree-8,
            'All physical amplitude levels supplied')
    require(not u[0] and not pressure[0],
            'Expansion about zero; a nonzero background needs a different dependency argument')
    require(all(not e.add(*(e.scale(q[i], v[i]) for i in range(3)))
                for level in u[1:] for q, v in level.items()),
            'Every supplied velocity amplitude is solenoidal; mean transport must cancel')
    require(not pressure[1] and not pressure[2], 'Cubic first pressure degree')
    g = {n: [{q: e.scale(q[i], v) for q, v in pressure[n].items() if q[i]}
             for i in range(3)] for n in range(3, degree-8)}
    needs = supports(u, g, degree)
    first, second, third = {}, {}, {}
    for n in range(3, degree-8):
        target = needs[1][n]
        first[n] = [p.heat(p.add({q: v for q, v in g[n][i].items() if q in target},
                                *(transport(u[a], first[n-a][i], target) for a in range(1, n-2))))
                    for i in range(3)]
    for n in range(6, degree-5):
        target = needs[2][n]
        second[n] = [[p.heat(p.add(*(
            p.add(multiply(first[a][i], g[n-a][j], target),
                  multiply(first[a][j], g[n-a][i], target))
            for a in first if n-a in g),
            *(transport(u[a], second[n-a][i][j], target) for a in range(1, n-5))))
            for j in range(3)] for i in range(3)]
    for n in range(9, degree-2):
        target = needs[3][n]
        third[n] = [p.heat(p.add(*(
            p.add(p.scale(2, p.add(*(multiply(second[a][i][j], g[n-a][j], target)
                                    for j in range(3)))),
                  multiply(p.add(*(second[a][j][j] for j in range(3))), g[n-a][i], target))
            for a in second if n-a in g),
            *(transport(u[a], third[n-a][i], target) for a in range(1, n-8))))
            for i in range(3)]
    result = {}
    for n in range(12, degree+1):
        source = e.scale(4, e.add(*(p.mean_product(third[a][i], g[n-a][i])
                                   for a in third if n-a in g for i in range(3))))
        result[n] = e.heat_convolution(source, 0)
        require(e.derivative(result[n]) == source and e.jet(result[n], 0) == 0,
                'Original accumulated moment solves its exact source equation')
        require(result[n].get((0, 0), Q(0)) == e.integral_infinity(source),
                'Two exact evaluations of the complete integrated coefficient')
        if n % 2:
            require(not result[n], 'Odd-amplitude symmetry')
    return result, {level: {n: len(v) for n, v in fields.items()} for level, fields in needs.items()}
