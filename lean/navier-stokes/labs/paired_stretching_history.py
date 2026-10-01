#!/usr/bin/env python3
"""Complete three-parent stretching minus complete two-parent histories.

The torus has period 2*pi and normalized volume. Exact amplitude
coefficients retain every convolution output, the Leray projection and
the physical viscous clock. They are finite derivatives of the NS
solution map, not an exact finite-amplitude solution or a remainder bound.
An independent symbolic radius calculation and Gaussian-rational time
jets check the first mixed term across scales and nontrivial profiles.

Optional dealiased prefixes compare the full nonlinear flow with evolving
pair flows. They are numerical Galerkin evidence, not continuum enclosures.
The continuation question concerns payment for all compatible histories;
a favorable coefficient or a finite prefix does not answer it.
"""

import argparse
import json
import math
import time
from collections import defaultdict
from fractions import Fraction as Q

import numpy as np
import sympy as s
import pressure_history_source as f
from cyclic_pressure_history import velocity_time_jets
from joint_source_history import seed
from parent_return_history import ReturnFlow


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


# Exact exponential polynomials sum c_(lambda,j) t^j exp(-lambda*t).
# All lambda and j below are nonnegative integers. There is no time grid.
def clean(a):
    return {k: v for k, v in a.items() if v}


def constant(v):
    return {(0, 0): Q(v)} if v else {}


def scale(c, a):
    return clean({k: Q(c)*v for k, v in a.items()})


def add(*arrays):
    result = defaultdict(Q)
    for a in arrays:
        for k, v in a.items():
            result[k] += v
    return clean(result)


def multiply(a, b):
    result = defaultdict(Q)
    for (i, j), v in a.items():
        for (k, ell), w in b.items():
            result[i+k, j+ell] += v*w
    return clean(result)


def derivative(a):
    result = defaultdict(Q)
    for (i, j), v in a.items():
        if j:
            result[i, j-1] += j*v
        result[i, j] -= i*v
    return clean(result)


def heat_convolution(a, damping):
    """Integral_0^t exp[-damping*(t-r)] a(r) dr, including resonance."""
    result = defaultdict(Q)
    for (i, j), v in a.items():
        if i == damping:
            result[i, j+1] += v/Q(j+1)
            continue
        beta = damping-i
        for k in range(j+1):
            result[i, j-k] += v*Q((-1)**k*math.factorial(j),
                                    math.factorial(j-k)*beta**(k+1))
        result[damping, 0] -= v*Q((-1)**j*math.factorial(j), beta**(j+1))
    return clean(result)


def jet(a, order):
    for _ in range(order):
        a = derivative(a)
    return sum((v for (_, j), v in a.items() if j == 0), Q(0))


def integral_infinity(a):
    require(all(i > 0 for i, _ in a), 'positive decay in complete coefficient integral')
    return sum((v*Q(math.factorial(j), i**(j+1)) for (i, j), v in a.items()), Q(0))


def tail_integral(a):
    """Exact integral from t to infinity; a nonnegative majorant stays so."""
    require(all(i > 0 for i, _ in a), 'positive decay in original tail reserve')
    result = defaultdict(Q)
    for (i, j), v in a.items():
        for ell in range(j+1):
            result[i, ell] += v*Q(math.factorial(j), math.factorial(ell)*i**(j-ell+1))
    return clean(result)


def encode(a):
    return [(i, j, str(v)) for (i, j), v in sorted(a.items())]


def dot(a, b):
    return add(*(multiply(x, y) for x, y in zip(a, b)))


def vector_scale(c, a):
    return tuple(scale(c, z) for z in a)


def vector_add(a, b):
    return tuple(add(x, y) for x, y in zip(a, b))


def field_add(arrays):
    result = {}
    for u in arrays:
        for k, a in u.items():
            result[k] = vector_add(result.get(k, ({}, {}, {})), a)
    return {k: a for k, a in result.items() if any(a)}


def advection(u, v):
    # Write the odd real velocity coefficient as u_hat(k)=i*a(k).
    # Then -u.grad(v) has coefficient i*sum (a(p).q)*b(q).
    result = {}
    for p, a in u.items():
        for q, b in v.items():
            k = tuple(x+y for x, y in zip(p, q))
            factor = add(*(scale(q[i], a[i]) for i in range(3)))
            if factor:
                result[k] = vector_add(result.get(k, ({}, {}, {})),
                                       tuple(multiply(factor, z) for z in b))
    return {k: a for k, a in result.items() if any(a)}


def project(source):
    result, pressure = {}, {}
    for k, a in source.items():
        norm = sum(q*q for q in k)
        if norm:
            p = scale(Q(1, norm), add(*(scale(k[i], a[i]) for i in range(3))))
            if p:
                pressure[k] = p
            z = tuple(add(a[i], scale(-k[i], p)) for i in range(3))
        else:
            z = a
        if any(z):
            result[k] = z
    return result, pressure


def weighted_pair(u, v, order):
    return add(*(scale(sum(q*q for q in k)**order,
                       dot(a, v.get(k, ({}, {}, {})))) for k, a in u.items()))


def amplitude_fields(amplitudes, order=7):
    initial = {}
    for i, j in enumerate((1, 2, 0)):
        k = tuple(1 if ell == j else 0 for ell in range(3))
        a = tuple({(1, 0): -Q(amplitudes[i], 2)} if i == ell and amplitudes[i] else {}
                  for ell in range(3))
        if any(a):
            initial[k] = a
            initial[tuple(-q for q in k)] = vector_scale(-1, a)
    U, N, P = [{}, initial], [{}, {}], [{}, {}]
    for m in range(2, order+1):
        source, pressure = project(field_add(advection(U[i], U[m-i]) for i in range(1, m)))
        N.append(source)
        P.append(pressure)
        U.append({k: tuple(heat_convolution(z, sum(q*q for q in k)) for z in a)
                  for k, a in source.items()})
    for m in range(1, order+1):
        for k, a in U[m].items():
            require(not add(*(scale(k[i], a[i]) for i in range(3))), ('transverse', m, k))
            require(tuple(add(derivative(z), scale(sum(q*q for q in k), z)) for z in a)
                    == N[m].get(k, ({}, {}, {})), ('complete coefficient equation', m, k))
            require(U[m].get(tuple(-q for q in k)) == vector_scale(-1, a),
                    ('real odd Fourier coefficients', m, k))
            if m > 1:
                require(all(jet(z, 0) == 0 for z in a), ('zero original generated datum', m, k))
        require((0, 0, 0) not in U[m], ('no mean flow generated', m))
    return U, N, P


def curl_coefficient(k, a):
    # Curl coefficients are real: i*k cross (i*a)=-k cross a.
    return tuple(add(scale(-k[j], a[ell]), scale(k[ell], a[j]))
                 for j, ell in ((1, 2), (2, 0), (0, 1)))


def literal_cubic(U, degree):
    """Independent mean omega^T grad(u) omega at an amplitude degree."""
    terms = []
    for i in range(1, degree-1):
        for j in range(1, degree-i):
            ell = degree-i-j
            for p, a in U[i].items():
                w = curl_coefficient(p, a)
                for q, b in U[j].items():
                    k = tuple(-x-y for x, y in zip(p, q))
                    if k not in U[ell]:
                        continue
                    v = curl_coefficient(k, U[ell][k])
                    qv = add(*(scale(q[r], v[r]) for r in range(3)))
                    terms.append(scale(-1, multiply(dot(w, b), qv)))
    return add(*terms)


def observers(U, N, degree):
    G = add(*(weighted_pair(U[i], N[degree-i], 1) for i in range(1, degree)))
    Z = add(*(weighted_pair(U[i], U[degree-i], 1) for i in range(1, degree)))
    D = add(*(weighted_pair(U[i], U[degree-i], 2) for i in range(1, degree)))
    E = add(*(weighted_pair(U[i], U[degree-i], 0) for i in range(1, degree)))
    require(not add(derivative(Z), scale(2, D), scale(-2, G)), ('physical enstrophy balance', degree))
    require(not add(derivative(E), scale(2, Z)), ('physical kinetic balance', degree))
    require(G == literal_cubic(U, degree), ('literal actual-curl stretching', degree))
    return G, Z, D


def complete_coefficients():
    full = amplitude_fields((1, 1, 1))
    pair = amplitude_fields((1, 0, 1))
    require(not any(pair[2]), 'complete pair pressure stays zero')
    reports = []
    for degree in (6, 8):
        F, P = observers(*full[:2], degree), observers(*pair[:2], degree)
        # Cyclic permutation preserves every mean observer, so all three
        # pair contributions agree. Single heat contributions vanish here.
        G, Z, D = [add(a, scale(-3, b)) for a, b in zip(F, P)]
        if degree == 6:
            require(G == {(4, 0): Q(3, 32), (4, 1): Q(-3, 16),
                          (6, 0): Q(-3, 32), (6, 2): Q(3, 16)}, 'complete sixth-degree rate')
            require(Z == {(2, 0): Q(9, 256), (4, 1): Q(3, 16), (4, 2): Q(-3, 8),
                          (6, 0): Q(-9, 256), (6, 1): Q(-21, 64), (6, 2): Q(-9, 32)},
                    'complete sixth-degree enstrophy')
            primitive = {(0, 0): Q(-5, 2304), (4, 1): Q(3, 64), (4, 0): Q(-3, 256),
                         (6, 0): Q(1, 72), (6, 1): Q(-1, 96), (6, 2): Q(-1, 32)}
            require(derivative(primitive) == G and jet(primitive, 0) == 0, 'one original primitive')
            require(2*integral_infinity(G) == Q(-5, 1152), 'complete favorable loop integral')
        else:
            require([jet(G, n) for n in range(6)] == [0, 0, 0, 0, 0, Q(473, 20)],
                    'next loop has positive first time coefficient')
            require(2*integral_infinity(G) == Q(541543, 737280000),
                    'next loop has positive complete integrated stretching')
        require(not add(derivative(Z), scale(2, D), scale(-2, G)), 'complete mixed diffusion ledger')
        # An absolute coefficient can be paid from its original amplitude.
        # The exact tail primitive defines a decreasing reserve on every
        # compatible interval. No convergence of the infinite sum follows.
        majorant = {k: abs(v) for k, v in G.items()}
        reserve = scale(2, tail_integral(majorant))
        require(all(v >= 0 for v in reserve.values()), 'nonnegative coefficient reserve for every time')
        require(derivative(reserve) == scale(-2, majorant), 'same reserve pays every compatible interval')
        reserve0 = jet(reserve, 0)
        require(reserve0 == 2*integral_infinity(majorant), 'original coefficient reserve is finite')
        reports.append({'degree': degree, 'stretching': encode(G), 'enstrophy': encode(Z),
                        'dissipation': encode(D), 'twice_integral_infinity': str(2*integral_infinity(G)),
                        'absolute_history_reserve': encode(reserve),
                        'absolute_history_reserve_at_zero': str(reserve0),
                        'initial_time_jets': [str(jet(G, n)) for n in range(6)]})
    return {'full_mode_counts': list(map(len, full[0])), 'pressure_mode_counts': list(map(len, full[2])),
            'reports': reports, 'scope': 'complete finite amplitude coefficients; continuum identification analytic; remainder open'}


def generic_radius():
    r0, r1, r2 = s.symbols('r0 r1 r2', positive=True)
    radii = (r2, r0, r1)
    wave = lambda k: tuple(radii[i]*k[i] for i in range(3))
    sd = lambda a, b: sum(x*y for x, y in zip(a, b))

    def tidy(u):
        result = {k: tuple(s.cancel(v) for v in a) for k, a in u.items()}
        return {k: a for k, a in result.items() if any(v != 0 for v in a)}

    def plus(terms):
        result = {}
        for c, u in terms:
            for k, a in u.items():
                result[k] = tuple(x+c*y for x, y in zip(result.get(k, (0, 0, 0)), a))
        return tidy(result)

    def adv(u, v):
        result = {}
        for p, a in u.items():
            for q, b in v.items():
                k = tuple(x+y for x, y in zip(p, q))
                factor = sd(a, wave(q))
                if factor:
                    result[k] = tuple(x+factor*y for x, y in zip(result.get(k, (0, 0, 0)), b))
        return tidy(result)

    def projection(u):
        result = {}
        for k, a in u.items():
            q, norm = wave(k), sd(wave(k), wave(k))
            p = s.cancel(sd(q, a)/norm) if norm else 0
            result[k] = tuple(x-y*p for x, y in zip(a, q))
        return tidy(result)

    u0 = {}
    for i, j in enumerate((1, 2, 0)):
        k = tuple(1 if ell == j else 0 for ell in range(3))
        a = tuple(-s.Rational(1, 2) if ell == i else 0 for ell in range(3))
        u0[k], u0[tuple(-q for q in k)] = a, tuple(-v for v in a)
    U = [u0]
    for n in range(3):
        U.append(projection(plus((math.comb(n, i), adv(U[i], U[n-i])) for i in range(n+1))))
    raw4 = plus((math.comb(3, i), adv(U[i], U[3-i])) for i in range(4))
    # Only the final pressure gradient is omitted from this independent
    # scalar test: it is orthogonal to the initial solenoidal receiver.
    weighted = lambda u, v: sum(sd(wave(k), wave(k))*sd(a, v.get(k, (0, 0, 0))) for k, a in u.items())
    G3 = s.factor(weighted(U[0], raw4)+4*weighted(U[1], U[3])+3*weighted(U[2], U[2]))
    require(s.cancel(G3+s.Rational(3, 2)*(r0*r1*r2)**2) == 0, 'independent generic radius identity')
    return {'mixed_third_time_derivative': str(G3), 'jet_mode_counts': list(map(len, U)),
            'scope': 'generic radius rational identity; amplitude and viscosity extension by phase/degree balance'}


def profile_jets():
    profiles = [[(1, 1, 0), (2, 0, Q(1, 2))], [(1, 2, 0), (3, 0, Q(-1, 3))],
                [(1, 0, Q(3, 2)), (2, -2, 0)]]
    u = [{}, {}, {}]
    for i, j in enumerate((1, 2, 0)):
        for radius, sine, cosine in profiles[i]:
            k = tuple(radius if ell == j else 0 for ell in range(3))
            v = f.QQ_I(cosine, -sine)/2
            u[i][k], u[i][tuple(-q for q in k)] = v, f.QQ_I(v.x, -v.y)

    def inner(a, b, order):
        return sum((sum(q*q for q in k)**order*Q(str((v*b[i].get(tuple(-q for q in k), f.ZERO)).x))
                    for i, field in enumerate(a) for k, v in field.items()), Q(0))

    def G3(initial, nu):
        U, P = velocity_time_jets(initial, nu, 4)
        Z4 = sum((math.comb(4, i)*inner(U[i], U[4-i], 1) for i in range(5)), Q(0))
        D3 = sum((math.comb(3, i)*inner(U[i], U[3-i], 2) for i in range(4)), Q(0))
        return Z4/2+nu*D3, len(P[3])

    norms = [inner([x], [x], 1) for x in u]
    expected, reports = -12*math.prod(norms), []
    for nu in (Q(0), Q(1, 5)):
        full, pressure_modes = G3(u, nu)
        pairs = [G3([{} if i == omit else field for i, field in enumerate(u)], nu)[0] for omit in range(3)]
        require(full-sum(pairs, Q(0)) == expected, 'independent complete nontrivial profile jets')
        reports.append({'nu': str(nu), 'full': str(full), 'pairs': list(map(str, pairs)),
                        'mixed': str(expected), 'pressure_time_jet_three_modes': pressure_modes})
    return {'profile_derivative_norm_squares': list(map(str, norms)), 'tests': reports,
            'scope': 'exact finite Fourier fixtures; general smooth-profile extension analytic'}


class PairFlow(ReturnFlow):
    """Existing velocity integrator with full physical stretching rates."""

    def __init__(self, n, nu, amplitudes):
        super().__init__(n, nu, 1)
        self.initial *= 0
        for i, field in enumerate(seed(amplitudes)):
            for k, v in field.items():
                self.initial[tuple(q % n for q in k)+(i,)] = complex(float(v.x), float(v.y))*n**3

    def values(self, state, nonlinear):
        density = np.sum(abs(state/self.n**3)**2, axis=-1)
        G = float(np.real(np.sum(self.k2[..., None]*np.conj(state)*nonlinear))/self.n**6)
        return np.array([G, float(np.sum(self.k2*density)), float(np.sum(self.k2**2*density))])

    def rhs(self, state):
        u, grad = self.ifft(state), self.grad_hat(state)
        adv = sum(u[..., j, None]*grad[j] for j in range(3))
        N = self.project(self.fft(-adv))*self.mask[..., None]
        G, _, D = self.values(state, N)
        return N, np.array([2*G, 2*self.nu*D])

    def observation(self, state):
        N, _ = self.rhs(state)
        values = self.values(state, N)
        density = np.sum(abs(state/self.n**3)**2, axis=-1)
        high = np.any(abs(self.K) > .8*self.n/3, axis=-1)
        return values, float(np.sum((self.k2*density)[high])/max(values[1], 1e-300))


def prefix_operator_check():
    """Check the new numerical observer against the complete exact PDE."""
    nu, h = Q(1, 5), Q(1, 7)
    initial = seed((1, 1, 1))
    U, _ = velocity_time_jets(initial, nu, 1)
    datum = [f.add(a, f.scale(f.QQ_I(h), b)) for a, b in zip(initial, U[1])]
    B = f.jac(datum)
    pressure = f.tensor_pressure(f.tensor(datum, datum))
    N = [f.add(f.scale(-1, f.adv(datum, datum[i])), f.scale(-1, f.diff(pressure, i)))
         for i in range(3)]
    flow = PairFlow(16, float(nu), (1, 1, 1))
    state, expected = np.zeros_like(flow.initial), np.zeros_like(flow.initial)
    for arrays, target in ((datum, state), (N, expected)):
        for i, field in enumerate(arrays):
            for k, v in field.items():
                target[tuple(q % flow.n for q in k)+(i,)] = complex(float(v.x), float(v.y))*flow.n**3
    actual, _ = flow.rhs(state)
    error = float(np.max(abs(actual-expected))/flow.n**3)
    require(error < 2e-14, 'prefix uses the complete canonical source at the exact probe')
    curl_hat = 1j*np.cross(flow.K, state)
    omega = flow.ifft(curl_hat)
    grad = np.stack(flow.grad_hat(state), axis=-1)
    G_literal = float(np.mean(np.einsum('...i,...ij,...j->...', omega, grad, omega)))
    G = float(flow.values(state, actual)[0])
    require(abs(G-G_literal) < 2e-14, 'prefix observer is literal vorticity stretching')
    w = f.curl(datum)
    exact_cubic = f.dot(w, f.matvec(B, w)).get(f.ORIGIN, f.ZERO)
    require(not exact_cubic.y, 'exact physical cubic is real')
    require(abs(G-float(exact_cubic.x)) < 2e-14, 'prefix cubic agrees with exact physical integration')
    return {'canonical_rhs_error': error, 'literal_cubic_error': abs(G-G_literal),
            'exact_cubic_error': abs(G-float(exact_cubic.x)),
            'stretching': G, 'scope': 'finite exact Fourier probe; not a continuum error bound'}


def prefix(n, nu, dt, final):
    require(n >= 12 and n % 2 == 0 and nu > 0 and dt > 0 and final > 0, 'valid periodic prefix parameters')
    F, P = PairFlow(n, nu, (1, 1, 1)), PairFlow(n, nu, (1, 0, 1))
    uf, up, lf, lp = F.initial.copy(), P.initial.copy(), np.zeros(2), np.zeros(2)
    z0f, z0p = F.observation(uf)[0][1], P.observation(up)[0][1]
    out, next_t, t, start = [], 0., 0., time.monotonic()
    steps, step_limit = 0, 2*(math.ceil(final/dt)+math.ceil(final/.25)+1)
    while True:
        if t >= next_t-1e-12 or t >= final-1e-12:
            vf, tf = F.observation(uf)
            vp, tp = P.observation(up)
            delta = vf-3*vp
            # The single heat histories complete quadratic inclusion-exclusion.
            # They have zero stretching but nonzero enstrophy and dissipation.
            delta[1:] += 1.5*math.exp(-2*nu*t)
            out.append({'t': t, 'nu_t': nu*t, 'mixed': delta.tolist(), 'full': vf.tolist(), 'pair': vp.tolist(),
                        'mixed_cumulative_stretching': float(lf[0]-3*lp[0]),
                        'mixed_cumulative_viscous_cost': float(lf[1]-3*lp[1]+1.5*(1-math.exp(-2*nu*t))),
                        'full_enstrophy_ledger_error': vf[1]-z0f-lf[0]+lf[1],
                        'pair_enstrophy_ledger_error': vp[1]-z0p-lp[0]+lp[1], 'tail_fractions': [tf, tp]})
            next_t += .25
            if t >= final-1e-12:
                break
        h = min(dt, final-t, next_t-t)
        uf, df = F.step(uf, h)
        lf += df
        up, dp = P.step(up, h)
        lp += dp
        t += h
        steps += 1
        require(steps <= step_limit, 'bounded diagnostic clock must advance')
    return {'n': n, 'nu': nu, 'dt': dt, 'final': final, 'samples': out,
            'steps': steps, 'seconds': time.monotonic()-start,
            'scope': 'complete dealiased Galerkin flows; no continuum enclosure'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prefix', action='store_true')
    parser.add_argument('--n', type=int, default=32)
    parser.add_argument('--nu', type=float, default=.2)
    parser.add_argument('--dt', type=float, default=.0125)
    parser.add_argument('--final', type=float, default=6.)
    args = parser.parse_args()
    start = time.monotonic()
    report = {'complete_coefficients': complete_coefficients(), 'generic_radius': generic_radius(),
              'independent_profile_jets': profile_jets(), 'prefix_operator': prefix_operator_check()}
    clock_probe = prefix(12, .2, .0125, .25)
    require(len(clock_probe['samples']) == 2 and abs(clock_probe['samples'][-1]['t']-.25) < 1e-14,
            'physical diagnostic clock reaches the prescribed horizon')
    clock_error = max(abs(x[k]) for x in clock_probe['samples']
                      for k in ('full_enstrophy_ledger_error', 'pair_enstrophy_ledger_error'))
    require(clock_error < 1e-9, 'physical clock and integrated production agree')
    report['clock_probe'] = {'final': clock_probe['samples'][-1]['t'], 'maximum_ledger_error': clock_error}
    if args.prefix:
        report['prefix'] = prefix(args.n, args.nu, args.dt, args.final)
    report['seconds'] = time.monotonic()-start
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
