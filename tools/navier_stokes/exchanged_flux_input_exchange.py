#!/usr/bin/env python3
"""Exact coefficient diagnostics for the seven-input high-frequency exchange.

On the angle torus, store the purely imaginary velocity coefficient as i*a,
with a rational transverse vector and a(-k)=-a(k). Every curl coefficient
is real. Both the output gradient projection and inner Leray difference
are retained. These are finite-field diagnostics, not NS trajectories or
machine-checked proofs. Auxiliary heat integration uses exact rationals.
"""

from __future__ import annotations

import argparse
from fractions import Fraction as Q
from itertools import product


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def neg(a):
    return tuple(-x for x in a)


def scale(c, a):
    return tuple(c * x for x in a)


def dot(a, b):
    return sum((x * y for x, y in zip(a, b)), Q(0))


def cross(a, b):
    return (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0])


def leray(k, a):
    size = dot(k, k)
    return add(a, scale(-dot(k, a)/size, k)) if size else a


def project_tensor(k, tensor):
    size = dot(k, k)
    if not size:
        return tuple((Q(0),)*3 for _ in range(3))
    return tuple(tuple(k[j]*sum(k[r]*tensor[r][i] for r in range(3))/size
                       for i in range(3)) for j in range(3))


def tensor(p, curls):
    """Projected exchanged-flux tensor with its actual factor 1/2."""
    a, b, c = curls
    v = cross(b, c)
    difference = add(leray(p[1], v), neg(leray(p[2], v)))
    raw = tuple(scale(a[j]/2, difference) for j in range(3))
    return project_tensor(add(add(p[0], p[1]), p[2]), raw)


def test(inner, field, k, l, m, n, p):
    q = add(k, l)
    output = add(add(q, m), n)
    target = add(add(p[0], p[1]), p[2])
    if output not in (target, neg(target)):
        return Q(0)
    omega = lambda r: neg(cross(r, field.get(r, (Q(0),)*3)))
    convection = scale(dot(q, field[k]), leray(q, field[l]))
    conv_curl = neg(cross(q, convection))
    # Curl kills the convection Leray projection exactly.
    assert conv_curl == scale(-dot(q, field[k]), cross(q, field[l]))
    a = tensor((m, q, n), (omega(m), conv_curl, omega(n))) if inner else \
        tensor((q, m, n), (conv_curl, omega(m), omega(n)))
    b = tensor(p, tuple(omega(r) for r in p))
    # Nonzero equal/opposite real characters have pairing 1/2.
    factor = Q(1, 2) if any(output) else Q(1)
    return factor * sum(dot(x, y) for x, y in zip(a, b))


def fixture(n, target_sign=1):
    k, l = (1, 0, 0), (n, 2*n, 0)
    low = (0, 1, 1)
    p = (k, (0, 1, 0), (0, 0, 1))
    field = {k: (Q(0), Q(1), Q(0)), l: (Q(0), Q(0), Q(1)),
             low: (Q(1), Q(1), Q(-1)), p[1]: (Q(1), Q(0), Q(1)),
             p[2]: (Q(1), Q(1), Q(0))}
    field[p[1]] = scale(target_sign, field[p[1]])
    field.update({neg(r): neg(a) for r, a in list(field.items())})
    for r, a in field.items():
        assert dot(r, a) == 0 and field[neg(r)] == neg(a)
    return field, k, l, neg(l), low, p


def check_reconstruction(field):
    """Check the exchanged tensor sum against the physical projected flux."""
    from projected_flux_viscosity import flux, gradient_projection
    original = tuple({k: a[j] for k, a in field.items() if a[j]} for j in range(3))
    expected = gradient_projection(flux(original))
    actual = tuple(tuple({} for _ in range(3)) for _ in range(3))
    for p in product(field, repeat=3):
        output = add(add(p[0], p[1]), p[2])
        value = tensor(p, tuple(neg(cross(r, field[r])) for r in p))
        for j in range(3):
            for i in range(3):
                actual[j][i][output] = actual[j][i].get(output, Q(0)) - value[j][i]
    for j in range(3):
        for i in range(3):
            assert {k: a for k, a in actual[j][i].items() if a} == expected[j][i]


def check(n, brief=False, target_sign=1):
    field, k, l, m, low, p = fixture(n, target_sign)
    center = sum(dot(r, r) for r in (k, l, m, low, *p))
    d, e = 2*dot(k, l), 2*dot(k, m)
    assert d + e == 0 and center > abs(d)
    kernel = lambda shift: 1/(center+shift)-1/center
    result = []
    for inner in (False, True):
        x = test(inner, field, k, l, m, low, p)
        y = test(inner, field, k, m, l, low, p)
        assert x == target_sign * (Q(n**3, 6) if inner else Q(n*n*(n-1), 6))
        assert y == -target_sign * (Q(n**3, 6) if inner else Q(n*n*(n+1), 6))
        value = kernel(d)*x + kernel(e)*y
        common = d*d/(center*(center*center-d*d))*(x+y)
        mismatch = -d/(center*center-d*d)*(x-y)
        assert value == common + mismatch
        result.append((x, y, value, common, mismatch))
        render = float if brief else str
        print(n, "inner" if inner else "outer",
              dict(zip(("X", "Y", "integrated", "common", "mismatch"),
                       map(render, result[-1]))), flush=True)
    if n == 2:
        check_reconstruction(field)
        assert result[1][2] == -target_sign*Q(8, 1575)
    return result


def check_full_work(n, brief=False, target_sign=1):
    """Keep every term in the physical resolved and commutator contributions.

    The high pair has formal amplitude epsilon; the output is the exact
    coefficient polynomial of its auxiliary-heat-integrated nonlinear work.
    This is not the full Gram-energy derivative: viscous dissipation is
    separate, and no physical-time trajectory is being integrated.
    """
    import heat_commutator_packet as h
    field, _, l, m, _, _ = fixture(n, target_sign)
    u = tuple({(*q, 0, int(q in (l, m))): a[j]
               for q, a in field.items() if a[j]} for j in range(3))
    filtered = h.heat(u)
    full, resolved = h.heat(h.rhs(u)), h.rhs(filtered)
    commutator = tuple(h.add(a, h.scale(Q(-1), b)) for a, b in zip(full, resolved))
    projected = h.gradient_projection(h.flux(filtered))
    out = {label: h.integrated_pairing(projected, h.variation(filtered, rate))
           for label, rate in (("commutator", commutator), ("resolved", resolved), ("full", full))}
    assert h.add(out["commutator"], out["resolved"]) == out["full"]
    if target_sign == 1 and n in (4, 8, 16, 32, 64, 128):
        assert all(set(a) == {0, 2, 4} for a in out.values())
        assert out["commutator"][2] > 0 and out["commutator"][4] < 0
        assert out["resolved"][4] > 0 and out["full"][4] > 0
        assert out["full"][0] == Q(11886991, 245700)
    render = float if brief else str
    print("Full nonlinear work", n,
          {name: {degree: render(value) for degree, value in a.items()} for name, a in out.items()},
          flush=True)
    return out


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--frequency", type=int, default=8)
    parser.add_argument("--brief", action="store_true")
    parser.add_argument("--reverse-target", action="store_true",
                        help="Reverse one target-only Fourier input to reverse the pair sign")
    parser.add_argument("--full-work", action="store_true",
                        help="Also evaluate the complete nonlinear heat-work polynomial")
    args = parser.parse_args()
    if args.frequency < 2:
        parser.error("frequency must be at least two")
    check(args.frequency, args.brief, -1 if args.reverse_target else 1)
    if args.full_work:
        check_full_work(args.frequency, args.brief, -1 if args.reverse_target else 1)
