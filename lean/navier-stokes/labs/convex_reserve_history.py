#!/usr/bin/env python3
"""Discovery histories for the actual datum in the convex-completion test.

The evolution is a dealiased Galerkin approximation. Enlarged-grid
diagnostics retain the full polynomial pressure and nonlinear outputs,
and report the discarded quartic-observer rate. These trajectories alone
are not continuum certificates or arbitrary-data history bounds.
"""

import argparse
import hashlib
import json
from pathlib import Path
import time

import numpy as np
import signed_viscous_pressure as sp
from pressure_prefix_control import VelocityFlow, require


def datum(nu):
    return [{k: -16*sp.f.QQ_I(nu)*a for k, a in field.items()}
            for field in sp.interacting_datum()]


def initialize(flow):
    flow.initial.fill(0)
    for j, field in enumerate(datum(flow.nu)):
        for k, a in field.items():
            flow.initial[tuple(v % flow.n for v in k)+(j,)] = complex(float(a.x), float(a.y))*flow.n**3
    return flow.initial.copy()


def diagnostic(flow, big, state, parent_mask):
    padded = flow.enlarged(state)
    u = big.ifft(padded)
    B = np.stack(big.grad_hat(padded), axis=-1)
    B2 = B@B
    r2 = np.sum(B*B, axis=(-1, -2))
    q = np.trace(B2, axis1=-2, axis2=-1)
    ph = big.fft(q)*big.inv
    P = np.empty_like(B)
    for i in range(3):
        for j in range(3):
            P[..., i, j] = big.ifft(-big.K[..., i]*big.K[..., j]*ph)
    self4 = -4*np.mean(r2*np.sum(B*B2, axis=(-1, -2)))
    pressure4 = -4*np.mean(r2*np.sum(B*P, axis=(-1, -2)))
    d2 = d4 = 0.
    for j in range(3):
        H = np.stack(big.grad_hat(1j*big.K[..., j, None]*padded), axis=-1)
        h2 = np.sum(H*H, axis=(-1, -2))
        d2 += 2*np.mean(h2)
        d4 += 4*np.mean(r2*h2+2*np.sum(B*H, axis=(-1, -2))**2)
    full_tangent = big.heat[..., None]*padded+big.bilinear(padded, padded)
    Bfull = np.stack(big.grad_hat(full_tangent), axis=-1)
    full_zrate = 2*np.mean(np.sum(B*Bfull, axis=(-1, -2)))
    full_wrate = 4*np.mean(r2*np.sum(B*Bfull, axis=(-1, -2)))
    native_tangent = flow.heat[..., None]*state+flow.bilinear(state, state)
    Bnative = np.stack(big.grad_hat(flow.enlarged(native_tangent)), axis=-1)
    retained_wrate = 4*np.mean(r2*np.sum(B*Bnative, axis=(-1, -2)))
    coefficients = state/flow.n**3
    zmode = flow.k2*np.sum(abs(coefficients)**2, axis=-1)
    nonlinear = flow.bilinear(state, state)/flow.n**3
    transfer = 2*flow.k2*np.real(np.sum(np.conj(coefficients)*nonlinear, axis=-1))
    balance_error = full_wrate-(self4+pressure4-flow.nu*d4)
    require(abs(balance_error) <= 1e-10*max(1., abs(self4), abs(pressure4), flow.nu*d4),
            'Complete pressure/self/viscous rate agrees with the full physical tangent')
    return {k: float(v) for k, v in dict(
        energy=np.mean(np.sum(u*u, axis=-1)), Z=np.mean(r2), W=np.mean(r2*r2),
        Z_parent=np.sum(zmode[parent_mask]), Z_generated=np.sum(zmode[~parent_mask]),
        Z_parent_nonlinear_rate=np.sum(transfer[parent_mask]),
        Z_generated_nonlinear_rate=np.sum(transfer[~parent_mask]),
        physical_Z_rate=full_zrate, physical_W_rate=full_wrate,
        quartic_self=self4, quartic_pressure=pressure4,
        quadratic_viscous_cost=flow.nu*d2, quartic_viscous_cost=flow.nu*d4,
        retained_W_rate=retained_wrate, discarded_W_rate=full_wrate-retained_wrate,
        quartic_balance_error=balance_error).items()}


def run(n, nu, dt, final, sample):
    require(n >= 16 and n % 2 == 0 and min(nu, dt, final, sample) > 0,
            'Even grid and positive physical parameters')
    steps = round(sample/dt)
    samples = round(final/sample)
    require(steps*dt == sample and samples*sample == final, 'Exact dyadic observation seams')
    flow, big = VelocityFlow(n, nu), VelocityFlow(2*n, nu)
    state = initialize(flow)
    parent_mask = np.zeros((n, n, n), bool)
    for field in datum(nu):
        for k in field:
            parent_mask[tuple(v % n for v in k)] = True
    print(json.dumps(dict(status='numerical discovery only', n=n, nu=nu, dt=dt,
                          final=final, sample=sample,
                          source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())), flush=True)
    start = time.time()
    for j in range(samples+1):
        row = diagnostic(flow, big, state, parent_mask)
        row.update(time=j*sample, elapsed=time.time()-start)
        print(json.dumps(row), flush=True)
        if j != samples:
            for _ in range(steps):
                state, _ = flow.step(state, dt)
                require(np.isfinite(state).all(), 'Finite numerical prefix')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--n', type=int, default=32)
    parser.add_argument('--nu', type=float, default=1.)
    parser.add_argument('--dt', type=float, default=1/2048)
    parser.add_argument('--final', type=float, default=1/8)
    parser.add_argument('--sample', type=float, default=1/64)
    args = parser.parse_args()
    run(args.n, args.nu, args.dt, args.final, args.sample)
