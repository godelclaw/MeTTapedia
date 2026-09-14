#!/usr/bin/env python3
"""Exact signed heat-work polynomials for finite Fourier perturbations.

Coefficients store u_hat/i as rationals on the angle torus. A monomial
key contains spatial frequency, auxiliary-heat damping, and perturbation
degree. Thus heat integration is exact: exp(-d*sigma) integrates to 1/d.
There is no grid, heat quadrature, or floating-point sign decision.

The background is the low-vorticity fixture. Its perturbation is
v=(0,0,sin(N(x+y))*(1+cos(x))/(2*N)), also divergence free.
This modulation breaks the background's horizontal parity. The program
retains both the resolved nonlinear work and the actual heat commutator.
These are initial-data diagnostics, not NS trajectories or Lean proofs.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from fractions import Fraction as Q

from projected_flux_viscosity import add, curl, mul as spatial_mul, scale, sine_over_i, wave_mul

Key = tuple[int, int, int, int, int]
Scalar = dict[Key, Q]
Vector = tuple[Scalar, Scalar, Scalar]


def mul(a: Scalar, b: Scalar) -> Scalar:
    out = defaultdict(Q)
    for k, x in a.items():
        for l, y in b.items():
            out[tuple(i+j for i, j in zip(k, l))] += x*y
    return {k: x for k, x in out.items() if x}


def leray(u: Vector) -> Vector:
    out = ({}, {}, {})
    for k in set().union(*u):
        size = sum(i*i for i in k[:3])
        contraction = sum(k[j]*u[j].get(k, Q(0)) for j in range(3))
        for j in range(3):
            value = u[j].get(k, Q(0)) - (k[j]*contraction/size if size else Q(0))
            if value:
                out[j][k] = value
    return out


def rhs(u: Vector) -> Vector:
    raw = tuple(add(*(mul(u[j], wave_mul(u[i], j)) for j in range(3))) for i in range(3))
    return leray(raw)


def heat(u: Vector) -> Vector:
    return tuple({(*k[:3], k[3]+sum(i*i for i in k[:3]), k[4]): value
                  for k, value in a.items()} for a in u)


def stretching(omega: Vector, u: Vector) -> Vector:
    return tuple(scale(Q(-1), add(*(mul(omega[j], wave_mul(u[i], j))
                                   for j in range(3)))) for i in range(3))


def flux(u: Vector):
    omega = curl(u)
    stretch = stretching(omega, u)
    return tuple(tuple(scale(Q(-1), mul(omega[j], stretch[i]))
                       for i in range(3)) for j in range(3))


def variation(u: Vector, v: Vector):
    omega, eta = curl(u), curl(v)
    stretch = stretching(omega, u)
    tangent = tuple(add(a, b) for a, b in zip(stretching(eta, u), stretching(omega, v)))
    return tuple(tuple(scale(Q(-1), add(mul(eta[j], stretch[i]), mul(omega[j], tangent[i])))
                       for i in range(3)) for j in range(3))


def gradient_projection(field):
    out = tuple(tuple({} for _ in range(3)) for _ in range(3))
    for k in set().union(*(a for row in field for a in row)):
        size = sum(i*i for i in k[:3])
        if size:
            for i in range(3):
                contraction = sum(k[j]*field[j][i].get(k, Q(0)) for j in range(3))
                for j in range(3):
                    value = k[j]*contraction/size
                    if value:
                        out[j][i][k] = value
    return out


def integrated_pairing(a, b) -> dict[int, Q]:
    out = defaultdict(Q)
    for j in range(3):
        for i in range(3):
            fibers = defaultdict(list)
            for k, value in b[j][i].items():
                fibers[k[:3]].append((k[3], k[4], value))
            for k, value in a[j][i].items():
                for damping, degree, other in fibers[tuple(-j for j in k[:3])]:
                    assert k[3]+damping > 0
                    out[k[4]+degree] += value*other/(k[3]+damping)
    return {p: v for p, v in sorted(out.items()) if v}


def evaluate_heat(field, base: Q, amplitude: Q):
    """Evaluate exp(-sigma)=base, retaining exact rational arithmetic."""
    return tuple({q: sum((value*base**k[3]*amplitude**k[4]
                         for k, value in a.items() if k[:3] == q), Q(0))
                  for q in {k[:3] for k in a}} for a in field)


def background_packet(n: int) -> Vector:
    p = {(0, 0, 0): Q(2), (0, 0, 1): Q(-1, 2), (0, 0, -1): Q(-1, 2)}
    q = {(0, 0, 0): Q(3), (0, 0, 1): Q(-1), (0, 0, -1): Q(-1)}
    background = (spatial_mul(sine_over_i(1), p), spatial_mul(sine_over_i(0), q), {})
    carrier = {(n, n, 0): Q(-1, 2*n), (-n, -n, 0): Q(1, 2*n)}
    envelope = {(0, 0, 0): Q(1, 2), (1, 0, 0): Q(1, 4), (-1, 0, 0): Q(1, 4)}
    out = tuple({(*k, 0, 0): v for k, v in a.items()} for a in background)
    out[2].update({(*k, 0, 1): v for k, v in spatial_mul(carrier, envelope).items()})
    return out


def check(n: int, brief: bool = False):
    u = background_packet(n)
    for k in set().union(*u):
        assert sum(k[j]*u[j].get(k, Q(0)) for j in range(3)) == 0
        for a in u:
            assert a.get((*(-i for i in k[:3]), k[3], k[4]), Q(0)) == -a.get(k, Q(0))
    filtered = heat(u)
    full_rate, resolved_rate = heat(rhs(u)), rhs(filtered)
    commutator = tuple(add(a, scale(Q(-1), b)) for a, b in zip(full_rate, resolved_rate))
    assert all(not any(a.values()) for a in evaluate_heat(commutator, Q(1), Q(1)))

    if n == 1:
        from projected_flux_viscosity import inviscid_rhs
        original = evaluate_heat(u, Q(1), Q(2, 3))
        expected_filtered_rhs = tuple({k: value*Q(1, 2)**sum(i*i for i in k)
                                       for k, value in a.items()} for a in inviscid_rhs(original))
        expected_resolved = inviscid_rhs(evaluate_heat(filtered, Q(1, 2), Q(2, 3)))
        expected = tuple(add(a, scale(Q(-1), b)) for a, b in zip(expected_filtered_rhs, expected_resolved))
        actual = evaluate_heat(commutator, Q(1, 2), Q(2, 3))
        assert all(not add(a, scale(Q(-1), b)) for a, b in zip(actual, expected))

    projected = gradient_projection(flux(filtered))
    commutator_variation = variation(filtered, commutator)
    if n == 1:
        from projected_flux_viscosity import gradient_projection as plain_projection
        from projected_flux_viscosity import flux as plain_flux, variation as plain_variation
        velocity_value = evaluate_heat(filtered, Q(1, 2), Q(2, 3))
        commutator_value = evaluate_heat(commutator, Q(1, 2), Q(2, 3))
        for graded, plain in ((projected, plain_projection(plain_flux(velocity_value))),
                              (commutator_variation, plain_variation(velocity_value, commutator_value))):
            for row, expected_row in zip(graded, plain):
                actual_row = evaluate_heat(row, Q(1, 2), Q(2, 3))
                assert all(not add(a, scale(Q(-1), b)) for a, b in zip(actual_row, expected_row))
    commutator_work = integrated_pairing(projected, commutator_variation)
    resolved_work = integrated_pairing(projected, variation(filtered, resolved_rate))
    full_work = integrated_pairing(projected, variation(filtered, full_rate))
    assert add(commutator_work, resolved_work) == full_work
    assert commutator_work.get(0, Q(0)) == resolved_work.get(0, Q(0)) == 0
    if n in (1, 2, 4, 8, 16, 32, 64):
        assert set(commutator_work) == set(resolved_work) == set(full_work) == {2, 4}
        assert commutator_work[2] > 0 and commutator_work[4] > 0 and resolved_work[4] < 0
    if n == 1:
        assert commutator_work[2] == Q(1572040178459, 12038651412480)
        assert commutator_work[4] == Q(2105782372404709157, 54805773287404339200)
        assert full_work[2] == Q(10250335608101, 71137485619200)
        assert full_work[4] == Q(-24174732099561803, 822086599311065088)
    print("N =", n, flush=True)
    for label, polynomial in (("commutator", commutator_work), ("resolved", resolved_work), ("full", full_work)):
        if brief:
            print(label, "N^2 times coefficients (decimal display only)",
                  {p: float(n*n*v) for p, v in polynomial.items()}, flush=True)
        else:
            print(label, {p: str(v) for p, v in polynomial.items()}, flush=True)
    print("Exact integrated coefficient polynomials; not a Lean proof.", flush=True)
    return commutator_work, resolved_work, full_work


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--frequency", type=int, default=1)
    parser.add_argument("--brief", action="store_true", help="Display scaled decimal summaries after exact checks")
    args = parser.parse_args()
    if args.frequency < 1:
        parser.error("frequency must be positive")
    check(args.frequency, args.brief)
