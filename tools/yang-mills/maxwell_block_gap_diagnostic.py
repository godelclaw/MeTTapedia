#!/usr/bin/env python3
"""Quadratic fluctuation test for ordered two-link SU(2) blocking.

The four-dimensional Maxwell action is the exact quadratic model at the
trivial Wilson background, one Lie-algebra color at a time.  Q retains the
two-edge path from each even vertex.  This is not a block average or a test
of a mass gap for the whole Maxwell field.  All spectral results below are
floating-point diagnostics, not uniform certificates.

Example: python3 maxwell_block_gap_diagnostic.py --grid 4 --random 64
"""
import argparse
import itertools
import json
import math
import platform

import numpy as np
import scipy
from scipy.linalg import null_space, eigh

D = 4
SITES = 2**D
PAIRS = list(itertools.combinations(range(D), 2))


def symbols(k):
    """Cell-Bloch symbols; k is momentum on the coarse lattice."""
    k = np.asarray(k, dtype=float)
    shift = []
    for mu in range(D):
        t = np.zeros((SITES, SITES), complex)
        for b in range(SITES):
            t[b, b ^ (1 << mu)] = np.exp(1j*k[mu]) if b & (1 << mu) else 1
        shift.append(t)
    grad = np.zeros((D*SITES, SITES), complex)
    curl = np.zeros((len(PAIRS)*SITES, D*SITES), complex)
    q = np.zeros((D, D*SITES), complex)
    for b in range(SITES):
        for mu in range(D):
            grad[D*b+mu] = shift[mu][b] - np.eye(SITES)[b]
        for j, (mu, nu) in enumerate(PAIRS):
            row = len(PAIRS)*b+j
            for a in range(SITES):
                curl[row, D*a+nu] += shift[mu][b, a] - (b == a)
                curl[row, D*a+mu] -= shift[nu][b, a] - (b == a)
    for mu in range(D):
        q[mu, mu] = 1
        q[mu, D*(1 << mu)+mu] = 1
    return q, grad, curl


def inspect_momentum(k):
    q, grad, curl = symbols(k)
    # Every fiber-preserving gradient has a representative with phi(0)=0.
    # This basis remains nonsingular even at zero coarse momentum.
    gauge = grad[:, 1:]
    physical = null_space(np.vstack([q, gauge.conj().T]), rcond=1.e-12)
    if physical.shape != (64, 45):
        raise ArithmeticError(f"Wrong physical sector dimension: {physical.shape}")
    cp = curl @ physical
    h = cp.conj().T @ cp
    values, vectors = eigh(h)
    v = vectors[:, 0]
    covariance = physical @ np.linalg.solve(h, physical.conj().T)
    return {
        'k': np.asarray(k).tolist(),
        'physical_dimension': physical.shape[1],
        'gauge_dimension': int(np.linalg.matrix_rank(gauge, tol=1.e-12)),
        'min_eigenvalue': float(values[0]),
        'max_eigenvalue': float(values[-1]),
        'eigenpair_residual': float(np.linalg.norm(h @ v-values[0]*v)),
        'orthogonality_error': float(np.linalg.norm(physical.conj().T @ physical-np.eye(45))),
        'q_physical_residual': float(np.linalg.norm(q @ physical)),
        'gauge_physical_residual': float(np.linalg.norm(gauge.conj().T @ physical)),
        'q_gauge_residual': float(np.linalg.norm(q @ gauge)),
        'curl_gradient_residual': float(np.linalg.norm(curl @ grad)),
        'inverse_residual': float(np.linalg.norm(h @ (physical.conj().T @ covariance @ physical)-np.eye(45))),
        'conditional_curvature_variance_01_at_origin': float((curl @ covariance @ curl.conj().T)[0, 0].real),
    }


def qmul(a, b):
    return np.r_[a[0]*b[0]-a[1:] @ b[1:], a[0]*b[1:]+b[0]*a[1:]+np.cross(a[1:], b[1:])]


def qexp(a):
    t = np.linalg.norm(a)
    return np.r_[math.cos(t), np.sinc(t/np.pi)*a]


def linearization_checks():
    rng = np.random.default_rng(10426)
    a = rng.normal(size=(4, 3))
    curl = a[0]+a[1]-a[2]-a[3]
    out = []
    for eps in [1.e-1, 3.e-2, 1.e-2, 3.e-3, 1.e-3, 3.e-4, 1.e-4]:
        u = [qexp(eps*v) for v in a]
        pair = qmul(u[0], u[1])
        hol = qmul(qmul(qmul(u[0], u[1]), qexp(-eps*a[2])), qexp(-eps*a[3]))
        # Stable exact identity for unit quaternions: 1-Re(tr U)/2 = |U-1|^2/2.
        potential = .5*np.sum((hol-np.array([1., 0., 0., 0.]))**2)
        out.append({'epsilon': eps,
                    'block_derivative_error': float(np.linalg.norm(pair[1:]/eps-a[0]-a[1])),
                    'holonomy_derivative_error': float(np.linalg.norm(hol[1:]/eps-curl)),
                    'wilson_quadratic_ratio': float(potential/eps**2),
                    'wilson_quadratic_target': float(.5*curl @ curl),
                    'unitarity_error': float(abs(hol @ hol-1))})
    return out


def run(grid, random):
    rows = []
    for mode in itertools.product(range(grid), repeat=D):
        row = inspect_momentum(2*np.pi*np.array(mode)/grid)
        row['source'] = f'full coarse torus grid side {grid}'
        rows.append(row)
    for size in [3, 4, 8, 16, 32, 64, 128, 256, 1024, 4096, 65536, 10**8]:
        for direction in [np.array([1, 0, 0, 0]), np.ones(4), np.array([1, 2, 3, 5])]:
            row = inspect_momentum(2*np.pi*direction/size)
            row['source'] = f'low momentum, coarse side {size}'
            rows.append(row)
    rng = np.random.default_rng(1042026)
    for k in rng.uniform(-np.pi, np.pi, size=(random, D)):
        row = inspect_momentum(k)
        row['source'] = 'seeded continuous momentum sample'
        rows.append(row)
    residual_keys = [k for k in rows[0] if k.endswith('residual') or k.endswith('error')]
    return {'model': '4D Maxwell quadratic action on ker Q modulo fiber-preserving gradients; one real color',
            'scope': 'trivial background; diagnostic sampling only; not a nonlinear Wilson or uniform spectral theorem',
            'normalization': 'energy=sum_(x,mu<nu) curl(A)^2; fine-link norm=sum_(x,mu) |A|^2; action beta*energy/2 per color',
            'versions': {'python': platform.python_version(), 'numpy': np.__version__, 'scipy': scipy.__version__},
            'sample_count': len(rows),
            'minimum_sampled_eigenvalue': min(r['min_eigenvalue'] for r in rows),
            'worst_residuals': {k: max(r[k] for r in rows) for k in residual_keys},
            'linearization': linearization_checks(), 'momenta': rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--grid', type=int, default=4)
    parser.add_argument('--random', type=int, default=64)
    args = parser.parse_args()
    if args.grid < 2 or args.random < 0:
        parser.error('grid must be at least 2 and random must be nonnegative')
    print(json.dumps(run(args.grid, args.random), indent=2))


if __name__ == '__main__':
    main()
