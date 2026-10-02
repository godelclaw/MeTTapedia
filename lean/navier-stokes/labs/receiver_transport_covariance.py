#!/usr/bin/env python3
"""Exact source-transport and heat-covariance identities for receiver storage.

Every Fourier output and Leray pressure contribution is retained. Auxiliary
heat rates are distinct from generated wave numbers. The PDE and stochastic
interpretations, including their scope, are analytic in README.md.
"""

import json
from fractions import Fraction as Q

import receiver_source_square as s

f = s.f


def scale(c, blocks):
    return {key: tuple(c*x for x in a) for key, a in blocks.items()
            if c and any(a)}


def heat(u):
    return {(k, sum(j*j for j in k)): a for k, a in s.modes(u).items()}


def advective_pair(a, b, c, nu):
    """(1/nu) integral <a,(b.grad)c> over auxiliary heat time."""
    s.require(nu > 0, 'positive viscosity')
    by_mode = {}
    for (k, rate), aa in a.items():
        by_mode.setdefault(k, []).append((rate, aa))
    total = f.ZERO
    for (p, r), bb in b.items():
        for (q, t), cc in c.items():
            contraction = f.II*s.dot(bb, q)
            if not contraction:
                continue
            k = tuple(-x-y for x, y in zip(p, q))
            for rate, aa in by_mode.get(k, []):
                s.require(rate+r+t > 0, 'positive heat rate in nonzero pairing')
                total += contraction*s.dot(aa, cc)/(nu**2*(rate+r+t))
    s.require(total.y == 0, 'real integrated advection')
    return Q(str(total.x))


def projected(blocks):
    result = {}
    for (k, rate), a in blocks.items():
        if k[2] == 0:
            continue
        kk = sum(j*j for j in k)
        value = tuple(a[j]-k[j]*s.dot(k, a)/kk for j in range(3))
        if any(value):
            result[k, rate] = value
    return result


def accumulate(blocks, key, a):
    old = blocks.get(key, (f.ZERO,)*len(a))
    blocks[key] = tuple(x+y for x, y in zip(old, a))


def cleaned(blocks):
    return {key: a for key, a in blocks.items() if any(a)}


def covariance(w, z=None):
    """S_s(w tensor z)-(S_s w) tensor (S_s z), as nine entries."""
    if z is None:
        z = w
    result = {}
    for p, a in s.modes(w).items():
        for q, b in s.modes(z).items():
            k = tuple(x+y for x, y in zip(p, q))
            rate = sum(j*j for wave in (p, q) for j in wave)
            tensor = tuple(x*y for x in a for y in b)
            accumulate(result, (k, sum(j*j for j in k)), tensor)
            accumulate(result, (k, rate), tuple(-x for x in tensor))
    return cleaned(result)


def add_tensors(*blocks):
    result = {}
    for block in blocks:
        for key, a in block.items():
            accumulate(result, key, a)
    return cleaned(result)


def covariance_force(tau):
    # -Pi P div Tau, not the unprojected tensor divergence.
    return projected({(k, rate): tuple(-f.II*sum((k[j]*a[3*i+j]
                       for j in range(3)), f.ZERO) for i in range(3))
                      for (k, rate), a in tau.items()})


def anisotropic(tau):
    result = {}
    for key, a in tau.items():
        trace_third = sum((a[3*i+i] for i in range(3)), f.ZERO)/3
        result[key] = tuple(a[3*i+j]-(trace_third if i == j else f.ZERO)
                            for i in range(3) for j in range(3))
    return cleaned(result)


def source_observer(v, n):
    """Pi P[(v.grad)n-(grad v)^T n], with every product output."""
    result = {}
    for (p, r), a in v.items():
        for (q, t), b in n.items():
            k = tuple(x+y for x, y in zip(p, q))
            value = tuple(f.II*(s.dot(a, q)*b[i]-p[i]*s.dot(a, b))
                          for i in range(3))
            accumulate(result, (k, r+t), value)
    return projected(cleaned(result))


def stress_pair(tau, observer, nu):
    """(1/nu) integral Tau : grad(observer), an independent tensor pairing."""
    by_mode = {}
    for (k, rate), a in observer.items():
        by_mode.setdefault(k, []).append((rate, a))
    total = f.ZERO
    for (k, rate), a in tau.items():
        ell = tuple(-j for j in k)
        for other, b in by_mode.get(ell, []):
            s.require(rate+other > 0, 'constant covariance pairs with a decaying observer')
            total += sum((a[3*i+j]*f.II*ell[j]*b[i]
                          for i in range(3) for j in range(3)), f.ZERO)/(nu**2*(rate+other))
    s.require(total.y == 0, 'real covariance work')
    return Q(str(total.x))


def check(u, nu=Q(1)):
    w = s.oscillation(u)
    v, n = heat(w), s.source_blocks(w, w)
    h = s.oscillation(s.nonlinear(u))
    self_source = s.oscillation(s.nonlinear(w))
    commutator = s.add_blocks(heat(self_source), scale(-1, n))
    parents = heat(s.vector_add(h, s.vector_scale(-1, self_source)))
    f.equal(f.trace(f.jac(u)), {}, 'actual initial field is solenoidal')
    for blocks in (v, n, commutator, parents):
        s.require(all(not s.dot(k, a) for (k, _), a in blocks.items()),
                  'each heat block retains incompressibility and its pressure')
    transport = -2*advective_pair(n, v, n, nu)
    geometry = -2*advective_pair(n, n, v, nu)
    memory = -2*(advective_pair(n, commutator, v, nu)
                 + advective_pair(n, v, commutator, nu))
    parent = -2*(advective_pair(n, parents, v, nu)
                 + advective_pair(n, v, parents, nu))
    direct = s.capacity_derivative(w, h, nu)
    s.require(transport == 0, 'complete source transport cancels')
    s.require(geometry+memory+parent == direct,
              'exact deformation/covariance/parent split agrees with direct derivative')

    tau = covariance(w)
    s.require(covariance_force(tau) == commutator,
              'shared-parent covariance gives the full projected heat commutator')
    tau_dev = anisotropic(tau)
    s.require(covariance_force(tau_dev) == commutator,
              'isotropic covariance is a pressure gradient and has no projected force')
    observer = source_observer(v, n)
    s.require(memory == 2*s.heat_pair(commutator, observer, nu)
              == 2*stress_pair(tau, observer, nu) == 2*stress_pair(tau_dev, observer, nu),
              'integration by parts identifies the signed covariance stress work')
    s.require(parent == 2*s.heat_pair(parents, observer, nu),
              'the same pressure-corrected observer retains surrounding parents')

    # Physical time, distinct from auxiliary heat time: w_t=nu Delta w+h.
    direction = s.vector_add(s.vector_scale(-nu, s.minus_laplacian(w)), h)
    tau_rate = add_tensors(covariance(direction, w), covariance(w, direction))
    gradient_covariance = add_tensors(*(covariance([f.diff(a, j) for a in w])
                                         for j in range(3)))
    lap_tau = scale(nu, {key: tuple(-sum(j*j for j in key[0])*x for x in a)
                        for key, a in tau.items()})
    physical_rhs = add_tensors(lap_tau, scale(-2*nu, gradient_covariance),
                              covariance(h, w), covariance(w, h))
    s.require(tau_rate == physical_rhs,
              'actual physical covariance evolution retains viscous loss and full parents')
    s.require(anisotropic(tau_rate) == anisotropic(physical_rhs),
              'the observed anisotropic covariance inherits the actual evolution')

    # (partial_s-nu Delta) commutator = 2nu G, with zero initial value.
    G = s.add_blocks(*(s.source_blocks([f.diff(a, j) for a in w],
                                      [f.diff(a, j) for a in w]) for j in range(3)))
    residual = cleaned({(k, rate): tuple((sum(j*j for j in k)-rate)*x for x in a)
                        for (k, rate), a in commutator.items()})
    s.require(residual == scale(2, G), 'exact Duhamel generator of covariance')
    collapsed = {}
    for (k, _), a in commutator.items():
        accumulate(collapsed, k, a)
    s.require(not cleaned(collapsed), 'heat covariance initially vanishes at auxiliary s=0')

    # Source heat diffusion has its own derivative-product term G.
    gradient_pair = s.heat_pair(n, {key: tuple(sum(j*j for j in key[0])*x for x in a)
                                    for key, a in n.items()}, nu)
    s.require(s.inner(self_source, self_source)/nu
              == 2*nu*gradient_pair+4*nu*s.heat_pair(n, G, nu),
              'source dissipation keeps the derivative-product defect')
    return {'transport': transport, 'source_deformation': geometry,
            'heat_covariance': memory, 'surrounding_parents': parent,
            'complete_quintic': direct}


def main():
    rows = []
    matched = [check(w) for w in s.matched_fields()]
    s.require(matched[0]['source_deformation'] > 0 and matched[0]['heat_covariance'] > 0,
              'both geometric and covariance work contribute to the earlier adverse phase')
    s.require(all(matched[0][k] == -matched[1][k] for k in matched[0]),
              'all signed contributions reverse on the matched phase data')
    rows.extend(zip(('matched_minus', 'matched_plus'), matched))

    r = s.real_field(s.seed())
    full_source = s.nonlinear(r)
    for delta in (Q(-1, 10), Q(1, 10)):
        full = s.vector_add(r, s.vector_scale(delta, full_source))
        mean_free = s.oscillation(full)
        isolated, coupled = check(mean_free), check(full, Q(2, 7))
        s.require(isolated['surrounding_parents'] == 0,
                  'covariance obstruction also holds with zero initial mean')
        s.require(isolated['source_deformation']*delta > 0
                  and isolated['complete_quintic']*delta < 0,
                  'heat covariance reverses the geometry-only sign')
        s.require(coupled['surrounding_parents']*delta < 0,
                  'nonzero generated mean is included with its actual phase')
        s.require(coupled['source_deformation'] == Q(49, 4)*isolated['source_deformation']
                  and coupled['heat_covariance'] == Q(49, 4)*isolated['heat_covariance'],
                  'exact nonunit-viscosity scaling retains the auxiliary heat rate')
        rows.extend(((f'mean_free_{delta}', isolated), (f'with_mean_{delta}_nu_2_7', coupled)))

    print(json.dumps({'cases': [dict(name=name, **{k: str(v) for k, v in row.items()})
                               for name, row in rows],
                      'scope': 'exact Fourier identities and smooth initial data; PDE conclusions analytic',
                      'failed_claim': 'positive heat covariance cannot reverse depleting source geometry',
                      'open': 'original-data payment of the combined deformation and covariance work'}, indent=2))


if __name__ == '__main__':
    main()
