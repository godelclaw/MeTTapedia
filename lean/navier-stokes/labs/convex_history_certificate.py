#!/usr/bin/env python3
"""Enclose gradient-energy histories for the convex-completion datum.

This reuses the complete residual and physical error comparison of
pressure_prefix_certificate. Rational initial rounding is included and
errors persist across seams. The arithmetic model and PDE comparison are
analytic/computational, not Lean certificates. H1 enclosures certify the
displayed projected gradient energies, not separate quartic work terms.
"""

import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import time

import numpy as np
from convex_reserve_history import datum, initialize
from pressure_prefix_control import VelocityFlow, require
from pressure_prefix_certificate import (SlabVerifier, add, arithmetic_check, bernstein,
                                         control_step, down, mul, reconstruct)
from pressure_polynomial_enclosure import rational_upper, sqrt_upper


def exact_square(a, k2, mask):
    result = Q(0)
    for row, weight in zip(a[mask], k2[mask]):
        for z in row:
            result += int(weight)*(Q(float(z.real))**2+Q(float(z.imag))**2)
    return result


def sqrt_lower(square):
    value = sqrt_upper(square)
    while Q(value)**2 > square:
        value = float(np.nextafter(value, -np.inf))
    return value


def observer(raw, verifier, error, parent):
    midpoint, radius = reconstruct(raw, verifier.K, verifier.k2)
    total = add(error, mul(verifier.kmax, radius))
    result = {}
    for name, mask in [('full', np.ones_like(parent)), ('parent', parent), ('generated', ~parent)]:
        square = exact_square(midpoint, verifier.k2, mask)
        low = max(0., float(down(sqrt_lower(square)-total)))
        high = add(sqrt_upper(square), total)
        low_square = Q(low)**2
        low_float = float(low_square)
        if Q(low_float) > low_square:
            low_float = float(down(low_float))
        result[name] = dict(lower=low_float, upper=rational_upper(Q(high)**2))
    return result


def initial_error(raw, flow):
    exact = datum(flow.nu)
    support = set().union(*exact)
    error0 = error1 = z0 = Q(0)
    for k in support:
        weight = sum(v*v for v in k)
        for j, field in enumerate(exact):
            value = field.get(k, 0)
            real, imag = (Q(str(value.x)), Q(str(value.y))) if value else (Q(0), Q(0))
            z = raw[tuple(v % flow.n for v in k)+(j,)]
            difference = (Q(float(z.real))-real)**2+(Q(float(z.imag))-imag)**2
            error0 += difference
            error1 += weight*difference
            z0 += weight*(real*real+imag*imag)
    outside = raw.copy()
    for k in support:
        outside[tuple(v % flow.n for v in k)] = 0
    require(np.count_nonzero(outside) == 0, 'No unaccounted initial coefficient')
    # The exact reference is P H(raw). The exact datum is real, mean-zero
    # and solenoidal, so these projections contract both error norms.
    return sqrt_upper(error0), sqrt_upper(error1), str(z0)


def run(n, nu, dt, h, final):
    arithmetic_check()
    require(n >= 16 and n & (n-1) == 0 and min(nu, dt, h, final) > 0,
            'Power-of-two retained grid and positive parameters')
    steps, slabs = round(h/dt), round(final/h)
    require(Q(steps)*Q(dt) == Q(h) and Q(slabs)*Q(h) == Q(final), 'Exact shared dyadic seams')
    flow, verifier = VelocityFlow(n, nu), SlabVerifier(n, nu)
    state = initialize(flow)
    X, Y, z0 = initial_error(state/n**3, flow)
    parent = np.zeros((n, n, n), bool)
    for field in datum(nu):
        for k in field:
            parent[tuple(v % n for v in k)] = True
    dependencies = ['convex_history_certificate.py', 'convex_reserve_history.py',
                    'pressure_prefix_certificate.py', 'pressure_prefix_control.py',
                    'pressure_polynomial_enclosure.py', 'signed_viscous_pressure.py',
                    'pressure_history_source.py', 'reciprocal_parent_history.py']
    hashes = {name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
              for name in dependencies}
    print(json.dumps(dict(status='physical comparison started', n=n, nu=nu, dt=dt,
                          h=h, final=final, initial_L2_error=X, initial_H1_error=Y,
                          exact_initial_Z=z0, source_hashes=hashes,
                          certification='analytic/computational under the existing arithmetic model; not Lean')), flush=True)
    previous = None
    start = time.time()
    for j in range(slabs):
        old = state.copy()
        f0, j0 = flow.jets(old)
        for _ in range(steps):
            state, _ = flow.step(state, dt)
        f1, j1 = flow.jets(state)
        raw = [np.ascontiguousarray(a/n**3) for a in bernstein(old, state, f0, f1, j0, j1, h)]
        require(previous is None or np.array_equal(raw[0], previous), 'Exact shared reference endpoint')
        previous = raw[-1].copy()
        row = verifier.slab(raw, h)
        controls = control_step(X, Y, row, h, nu)
        X, Y = controls['X'], controls['Y']
        observation = observer(raw[-1], verifier, Y, parent)
        print(json.dumps(dict(status='interval accepted', time=(j+1)*h, row=row,
                              controls=controls, Z=observation, elapsed=time.time()-start,
                              initial_endpoint_sha256=hashlib.sha256(raw[0].tobytes()).hexdigest(),
                              final_endpoint_sha256=hashlib.sha256(raw[-1].tobytes()).hexdigest())), flush=True)
    print(json.dumps(dict(status='finite physical prefix enclosed', final=final,
                          Z=observation, initial_Z=z0, elapsed=time.time()-start)), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--n', type=int, default=32)
    parser.add_argument('--nu', type=float, default=1.)
    parser.add_argument('--dt', type=float, default=1/8192)
    parser.add_argument('--h', type=float, default=1/1024)
    parser.add_argument('--final', type=float, default=1/64)
    a = parser.parse_args()
    run(a.n, a.nu, a.dt, a.h, a.final)
