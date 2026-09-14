#!/usr/bin/env python3
"""Exact finite-Fourier test of projected cubic-flux viscous production.

On the angle torus, test u=(sin(y)(1+cos(z))^N,
sin(x)(1-cos(z))^N,0).  Fourier coefficients of u are imaginary;
the program stores u_hat/i as rational numbers.  Vorticity, stretching,
and cubic-flux coefficients are real rational numbers for this family.

J_j=-omega_j (omega dot grad)u and F=P_grad J.  The reported work is
<F,DJ[u][Delta u]>. For N=3 the program also evaluates the full inviscid
NS tangent: its work vanishes by disjoint horizontal frequency parity.
All sums are exact, over the complete finite support: no grid, truncation,
floating-point sign test, or aliasing is used.  This is an executable
mathematical diagnostic, not a Lean-checked counterexample.

Replacing each angle by 2*pi times the unit-torus coordinate multiplies
both work and dissipation by (2*pi)^8 and preserves their signs.
"""

from __future__ import annotations

import argparse
from fractions import Fraction as Q
from itertools import product

Mode = tuple[int, int, int]
Scalar = dict[Mode, Q]
Vector = tuple[Scalar, Scalar, Scalar]
Tensor = tuple[Vector, Vector, Vector]


def clean(a: Scalar) -> Scalar:
    return {k: v for k, v in a.items() if v}


def add(*fields: Scalar) -> Scalar:
    out: Scalar = {}
    for field in fields:
        for k, v in field.items():
            out[k] = out.get(k, Q(0)) + v
    return clean(out)


def scale(c: Q, a: Scalar) -> Scalar:
    return clean({k: c * v for k, v in a.items()})


def mul(a: Scalar, b: Scalar) -> Scalar:
    out: Scalar = {}
    for k, x in a.items():
        for l, y in b.items():
            n = tuple(k[j] + l[j] for j in range(3))
            out[n] = out.get(n, Q(0)) + x * y
    return clean(out)


def wave_mul(a: Scalar, j: int) -> Scalar:
    return clean({k: k[j] * v for k, v in a.items()})


def laplacian(a: Scalar) -> Scalar:
    return clean({k: -sum(x * x for x in k) * v for k, v in a.items()})


def profile(n: int, sign: int) -> Scalar:
    out = {(0, 0, 0): Q(1)}
    base = {(0, 0, 0): Q(1), (0, 0, 1): Q(sign, 2), (0, 0, -1): Q(sign, 2)}
    for _ in range(n):
        out = mul(out, base)
    return out


def sine_over_i(j: int) -> Scalar:
    k = tuple(int(i == j) for i in range(3))
    return {k: Q(-1, 2), tuple(-x for x in k): Q(1, 2)}


def two_shear(n: int) -> Vector:
    return (mul(sine_over_i(1), profile(n, 1)),
            mul(sine_over_i(0), profile(n, -1)), {})


def curl(u: Vector) -> Vector:
    # i*k cross (i*u) = - k cross u.
    return tuple(add(scale(Q(-1), wave_mul(u[(j + 2) % 3], (j + 1) % 3)),
                     wave_mul(u[(j + 1) % 3], (j + 2) % 3)) for j in range(3))


def stretching(omega: Vector, u: Vector) -> Vector:
    return tuple(scale(Q(-1), add(*(mul(omega[j], wave_mul(u[l], j))
                                   for j in range(3)))) for l in range(3))


def flux(u: Vector) -> Tensor:
    omega = curl(u)
    a = stretching(omega, u)
    return tuple(tuple(scale(Q(-1), mul(omega[j], a[l]))
                       for l in range(3)) for j in range(3))


def variation(u: Vector, v: Vector) -> Tensor:
    omega, eta = curl(u), curl(v)
    a = stretching(omega, u)
    av, b = stretching(eta, u), stretching(omega, v)
    return tuple(tuple(scale(Q(-1), add(mul(eta[j], a[l]),
                       mul(omega[j], add(av[l], b[l]))))
                       for l in range(3)) for j in range(3))


def inviscid_rhs(u: Vector) -> Vector:
    """Store N(u)_hat/i, where N(u)=-P_Leray((u dot grad)u)."""
    raw = tuple(add(*(mul(u[j], wave_mul(u[l], j)) for j in range(3))) for l in range(3))
    modes = set().union(*raw)
    out = ({}, {}, {})
    for k in modes:
        square = sum(x*x for x in k)
        contraction = sum(k[j] * raw[j].get(k, Q(0)) for j in range(3))
        for j in range(3):
            value = raw[j].get(k, Q(0)) - (k[j]*contraction/square if square else Q(0))
            if value:
                out[j][k] = value
    return out


def gradient_projection(jfield: Tensor) -> Tensor:
    out = tuple(tuple({} for _ in range(3)) for _ in range(3))
    modes = set().union(*(jfield[j][l] for j, l in product(range(3), repeat=2)))
    for k in modes:
        square = sum(x * x for x in k)
        if square:
            for l in range(3):
                contraction = sum(k[i] * jfield[i][l].get(k, Q(0)) for i in range(3))
                for j in range(3):
                    value = k[j] * contraction / square
                    if value:
                        out[j][l][k] = value
    return out


def pairing(a: Tensor, b: Tensor) -> Q:
    return sum((v * b[j][l].get(k, Q(0))
                for j, l in product(range(3), repeat=2)
                for k, v in a[j][l].items()), Q(0))


def polynomial(coefficients: list[Q]) -> Scalar:
    """Evaluate a polynomial in cos(z), coefficients in ascending order."""
    cosine = {(0, 0, 1): Q(1, 2), (0, 0, -1): Q(1, 2)}
    out: Scalar = {}
    for c in reversed(coefficients):
        out = add(mul(out, cosine), {(0, 0, 0): Q(c)})
    return out


def check_separated_certificate() -> None:
    """Independent polynomial reduction; compare every divergence coefficient."""
    # These are the expanded six polynomials checked in TwoShearViscousCertificate.
    a = polynomial([-6, Q(21, 2), 30, -78, 6, 111, -78, -30, 48, Q(-27, 2)])
    b = polynomial([3, Q(-33, 2), 30, -6, -48, 57, -6, -30, 21, Q(-9, 2)])
    c = polynomial([6, Q(33, 2), -3, -45, -27, 36, 39, -3, -15, Q(-9, 2)])
    ar = polynomial([-30, -15, -30, 600, -330, -1470, 1590, 480, -1200, 405])
    br = polynomial([15, -15, -120, 150, 390, -840, 240, 570, -525, 135])
    cr = polynomial([30, 15, -15, 270, 315, -450, -705, 30, 375, 135])

    def cosine(j: int, frequency: int) -> Scalar:
        k = tuple(frequency if i == j else 0 for i in range(3))
        return {k: Q(1, 2), tuple(-x for x in k): Q(1, 2)}

    def double_sine(j: int) -> Scalar:
        return {tuple(2*x for x in k): v for k, v in sine_over_i(j).items()}

    def shift(p: Scalar) -> Scalar:
        return {k: v if k[2] % 2 == 0 else -v for k, v in p.items()}

    def separation(aa: Scalar, bb: Scalar, cc: Scalar) -> Vector:
        first = add(mul(sine_over_i(1), aa),
                    mul(mul(sine_over_i(1), cosine(0, 2)), bb),
                    mul(mul(double_sine(1), cosine(0, 1)), cc))
        second = add(mul(sine_over_i(0), shift(aa)),
                     mul(mul(sine_over_i(0), cosine(1, 2)), shift(bb)),
                     mul(mul(double_sine(0), cosine(1, 1)), shift(cc)))
        return scale(Q(-1), first), scale(Q(-1), second), {}

    u = two_shear(3)
    jfield = flux(u)
    dj = variation(u, tuple(laplacian(field) for field in u))
    for tensor, expected in [(jfield, separation(a, b, c)), (dj, separation(ar, br, cr))]:
        for l in range(3):
            assert add(*(wave_mul(tensor[j][l], j) for j in range(3))) == expected[l]
    work = sum((a.get(k, Q(0))*ar.get(k, Q(0))/(1+k[2]**2) +
                (b.get(k, Q(0))*br.get(k, Q(0)) + c.get(k, Q(0))*cr.get(k, Q(0))) /
                (2*(5+k[2]**2)) for k in set().union(a, b, c)), Q(0))
    assert work == pairing(gradient_projection(jfield), dj)
    assert work == Q(16932543012172819, 351018510581760) > 0
    print('N=3: separated polynomial and full 3D coefficient calculations agree exactly.', flush=True)
    n0 = inviscid_rhs(u)
    assert all(sum(k[j]*n0[j].get(k, Q(0)) for j in range(3)) == 0
               for k in set().union(*n0))
    inviscid = variation(u, n0)
    f = gradient_projection(jfield)
    assert all((k[0]+k[1]) % 2 == 1 for row in f for field in row for k in field)
    assert all((k[0]+k[1]) % 2 == 0 for row in inviscid for field in row for k in field)
    assert pairing(f, inviscid) == 0
    full_rhs = tuple(add(n0[j], laplacian(u[j])) for j in range(3))
    assert pairing(f, variation(u, full_rhs)) == work
    print('N=3: inviscid NS work=0 by disjoint parity; full NS work at viscosity 1 equals viscous_work.', flush=True)


def check(n: int, polarization: bool = True) -> tuple[Q, Q, Q]:
    u = two_shear(n)
    modes = set().union(*u)
    assert all(sum(k[j] * u[j].get(k, Q(0)) for j in range(3)) == 0 for k in modes)
    assert all(u[j].get(tuple(-x for x in k), Q(0)) == -a
               for j in range(3) for k, a in u[j].items())
    assert all(field.get((0, 0, 0), Q(0)) == 0 for field in u)
    v = tuple(laplacian(field) for field in u)
    jfield, dj = flux(u), variation(u, v)
    if polarization:
        plus = flux(tuple(add(u[j], v[j]) for j in range(3)))
        minus = flux(tuple(add(u[j], scale(Q(-1), v[j])) for j in range(3)))
        cubic = flux(v)
        assert all(dj[j][l] == add(scale(Q(1, 2), plus[j][l]),
                                  scale(Q(-1, 2), minus[j][l]),
                                  scale(Q(-1), cubic[j][l]))
                   for j, l in product(range(3), repeat=2))
    f = gradient_projection(jfield)
    assert gradient_projection(f) == f
    assert pairing(f, jfield) == pairing(f, f)
    assert pairing(f, dj) == pairing(f, gradient_projection(dj))
    energy = pairing(f, f)
    dissipation = sum((sum(x * x for x in k) * value * value
                       for j, l in product(range(3), repeat=2)
                       for k, value in f[j][l].items()), Q(0))
    work = pairing(f, dj)
    assert energy >= 0 and dissipation >= 0
    return energy, dissipation, work


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n', type=int, default=4)
    args = parser.parse_args()
    if args.max_n < 0:
        parser.error('--max-n must be nonnegative')
    check_separated_certificate()
    for n in range(args.max_n + 1):
        e, d, w = check(n)
        print(f'N={n}: energy={e}; dissipation={d}; viscous_work={w}', flush=True)
        if d:
            print(f'  work/dissipation={w / d}; positive={w > 0}', flush=True)


if __name__ == '__main__':
    main()
