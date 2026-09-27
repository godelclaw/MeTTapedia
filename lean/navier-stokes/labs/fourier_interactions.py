#!/usr/bin/env python3
"""Exact finite Fourier calculations for the unforced Navier--Stokes source.

Run with Python 3 and its standard library. See README.md for conventions,
formulas and scope. These checks are not Lean certificates or PDE time steps.
Source fields retain every convolution output. Pairings sum all contributing
input pairs directly. Fractions are used for every check.
"""

from __future__ import annotations

import argparse
from fractions import Fraction as F
import itertools
import json

Mode = tuple[int, int, int]
Vector = tuple[F, F, F]
Field = dict[Mode, Vector]
ZERO = (F(0), F(0), F(0))


def require(condition: bool, description: str) -> None:
    """Checks also run when Python is invoked with -O."""
    if not condition:
        raise ArithmeticError(description)


def dot(a, b):
    return sum((x * y for x, y in zip(a, b)), F(0))


def cross(a, b):
    return (a[1] * b[2] - a[2] * b[1],
            a[2] * b[0] - a[0] * b[2],
            a[0] * b[1] - a[1] * b[0])


def radius_squared(k: Mode) -> int:
    return sum(x * x for x in k)


def scale(c, u: Field) -> Field:
    return {k: tuple(c * x for x in v) for k, v in u.items()
            if c and any(v)}


def add(*fields: Field) -> Field:
    out = {}
    for u in fields:
        for k, v in u.items():
            out[k] = tuple(a + b for a, b in zip(out.get(k, ZERO), v))
    return {k: v for k, v in out.items() if any(v)}


def pair(u: Field, v: Field) -> F:
    return sum((dot(a, v.get(k, ZERO)) for k, a in u.items()), F(0))


def A(u: Field) -> Field:
    """The positive operator -Delta, on the torus of period 2*pi."""
    return {k: tuple(radius_squared(k) * x for x in v)
            for k, v in u.items()}


def project(k: Mode, v: Vector) -> Vector:
    r = radius_squared(k)
    if not r:
        return v  # Leray is the identity on constants; do not discard them.
    parallel = dot(k, v) / r
    return tuple(x - parallel * j for x, j in zip(v, k))


def B(u: Field, v: Field) -> Field:
    """Imaginary amplitudes of -P[(u.grad)v], when u_hat=i*a, v_hat=i*b."""
    raw = {}
    for p, a in u.items():
        for q, b in v.items():
            coefficient = dot(a, q)
            if coefficient:
                k = tuple(x + y for x, y in zip(p, q))
                raw[k] = tuple(x + coefficient * y
                               for x, y in zip(raw.get(k, ZERO), b))
    out = {k: project(k, v) for k, v in raw.items()}
    return {k: v for k, v in out.items() if any(v)}


def pair_source(receiver: Field, u: Field, v: Field) -> F:
    """Pair with B(u,v) without constructing outputs outside the receiver.

    Transversality removes the final Leray projection. Every contributing
    input pair is included; this is not a projection of either source input.
    """
    validate(receiver)
    result = F(0)
    for k, w in receiver.items():
        for p, a in u.items():
            q = tuple(x - y for x, y in zip(k, p))
            if q in v:
                result += dot(a, q) * dot(w, v[q])
    return result


def stretching(u: Field) -> Field:
    """Real Fourier coefficients of (curl u . grad)u, without projection."""
    out = {}
    for p, a in u.items():
        for q, b in u.items():
            coefficient = dot(cross(p, a), q)
            if coefficient:
                k = tuple(x + y for x, y in zip(p, q))
                out[k] = tuple(x + coefficient * y
                               for x, y in zip(out.get(k, ZERO), b))
    return {k: v for k, v in out.items() if any(v)}


def inverse_curl(u: Field) -> Field:
    """Imaginary amplitudes of curl A^{-1} P applied to real coefficients."""
    out = {}
    for k, v in u.items():
        r = radius_squared(k)
        if r:
            out[k] = tuple(x / r for x in cross(k, project(k, v)))
    return {k: v for k, v in out.items() if any(v)}


def validate(u: Field) -> None:
    require((0, 0, 0) not in u, "nonzero mean")
    for k, v in u.items():
        require(all(isinstance(x, F) for x in v), "inexact amplitude")
        require(dot(k, v) == 0, "nonzero divergence")
        negative = tuple(-x for x in k)
        require(u.get(negative, ZERO) == tuple(-x for x in v),
                "failure of Fourier reality")


def sine(k: Mode, v) -> Field:
    require(k != (0, 0, 0), "zero sine frequency")
    return {k: tuple(-F(x) / 2 for x in v),
            tuple(-x for x in k): tuple(F(x) / 2 for x in v)}


def jets(u0: Field, nu: F, order: int = 4):
    """Exact coefficients u_r of t^r, using the full quadratic recurrence."""
    u = [u0]
    nonlinear = []
    for r in range(order):
        nr = add(*(B(u[i], u[r - i]) for i in range(r + 1)))
        nonlinear.append(nr)
        u.append(scale(F(1, r + 1), add(nr, scale(-nu, A(u[r])))))
    for field in u + nonlinear:
        validate(field)
    energy = [sum((pair(u[i], u[r - i]) for i in range(r + 1)), F(0)) / 2
              for r in range(order + 1)]
    enstrophy = [sum((pair(A(u[i]), u[r - i]) for i in range(r + 1)), F(0)) / 2
                for r in range(order + 1)]
    production = [sum((pair(A(u[i]), nonlinear[r - i]) for i in range(r + 1)), F(0))
                  for r in range(order)]
    for r in range(order):
        dissipation = nu * sum((pair(A(u[i]), A(u[r - i]))
                                for i in range(r + 1)), F(0))
        require((r + 1) * energy[r + 1] == -2 * nu * enstrophy[r],
                "kinetic energy identity")
        require((r + 1) * enstrophy[r + 1] == production[r] - dissipation,
                "enstrophy identity")
    return u, nonlinear, production


def matched_fields() -> dict[str, Field]:
    symmetric = add(sine((1, 0, 0), (0, -1, -1)),
                    sine((0, 1, 0), (-1, 0, -1)),
                    sine((0, 0, 1), (-1, -1, 0)))
    alternating = add(sine((1, 0, 0), (0, -1, 1)),
                      sine((0, 1, 0), (1, 0, -1)),
                      sine((0, 0, 1), (-1, 1, 0)))
    return {"symmetric": symmetric, "alternating": alternating}


def check_matched_fields():
    fields = matched_fields()
    expected_source = add(sine((0, 1, 1), (-1, 0, 0)),
                          sine((1, 0, 1), (0, -1, 0)),
                          sine((1, 1, 0), (0, 0, -1)))
    require(stretching(fields["symmetric"]) == stretching(fields["alternating"]),
            "the unprojected stretching sources differ")
    rows = []
    for name, u0 in fields.items():
        validate(u0)
        n0 = B(u0, u0)
        require(n0 == expected_source, "wrong complete initial source")
        require(A(u0) == u0 and A(n0) == scale(2, n0), "wrong shells")
        require(pair(u0, u0) == 3, "wrong squared velocity norm")
        require(pair(n0, n0) == F(3, 2), "wrong squared source norm")
        require(inverse_curl(stretching(u0)) == scale(F(1, 2), n0),
                "wrong projected stretching source")
        commutator = add(B(A(u0), u0), B(u0, A(u0)), scale(-1, A(n0)))
        require(not commutator, "heat commutator does not vanish")
        # Pi(u0 + z*n0) is cubic in z. Compute all four coefficients.
        polynomial = [u0, n0, {}, {}]
        npoly = [add(*(B(polynomial[i], polynomial[r - i])
                       for i in range(r + 1))) for r in range(4)]
        pi_poly = [sum((pair(A(polynomial[i]), npoly[r - i])
                        for i in range(r + 1)), F(0)) for r in range(4)]
        require(pi_poly == [0, F(3, 2), 0, 0], "first Picard production")
        correction = F(-1, 12) if name == "symmetric" else F(3, 4)
        for nu in (F(0), F(1), F(3, 2), F(2)):
            u, _, production = jets(u0, nu)
            predicted = [F(0), F(3, 2), -6 * nu, 12 * nu**2]
            require(production == predicted[:3] + [predicted[3] + correction],
                    "wrong physical production coefficients")
            rows.append({"field": name, "nu": str(nu),
                         "velocity_jet_supports": [len(v) for v in u],
                         "production_coefficients": list(map(str, production)),
                         "cubic_correction_to_first_picard": str(correction)})
    return {"viscosity_degree_bound": 3, "distinct_viscosity_samples": 4,
            "rows": rows}


def chain_field(n: int) -> Field:
    x, b = 2**n, (-1)**n
    a = (x - b) // 3
    require(3 * a + b == x, "nonintegral chain mode")
    out = {}
    for i in range(3):
        k = tuple(a + b * (j == i) for j in range(3))
        v = tuple(a + b - x * (j == i) for j in range(3))
        out = add(out, sine(k, v))
    validate(out)
    return out


def check_chain(generations: int):
    rows = []
    for n in range(generations):
        r = 4**n
        radius, next_radius = F(r + 2, 3), F(4 * r + 2, 3)
        u, v = chain_field(n), chain_field(n + 1)
        eu, ev = pair(u, u), pair(v, v)
        require(eu == 3 * radius and ev == 3 * next_radius, "chain energy")
        source = B(u, u)
        gamma = (-1)**n * 2**n * radius / next_radius
        require(source == scale(gamma, v), "diagonal chain identity")
        beta2 = F(r, 4 * r + 2)
        require(pair(source, source) / eu**2 == beta2, "normalized self source")
        mixed = add(B(u, v), B(v, u))
        validate(mixed)
        chain_support = set(u) | set(v) | set(chain_field(n + 2))
        retained = {k: w for k, w in mixed.items() if k in chain_support}
        spill = {k: w for k, w in mixed.items() if k not in chain_support}
        require(retained == scale(-gamma * ev / eu, u), "reverse chain source")
        require(pair(u, mixed) + pair(v, source) == 0, "mixed energy cancellation")
        sum_spill = {k: w for k, w in spill.items() if abs(sum(k)) == 3 * 2**n}
        diff_spill = {k: w for k, w in spill.items() if abs(sum(k)) == 2**n}
        require(add(sum_spill, diff_spill) == spill, "unclassified escaped modes")
        require([len(mixed), len(retained), len(sum_spill), len(diff_spill)]
                == [24, 6, 12, 6], "wrong mixed support counts")
        expected_sum = F(r, 2 * (r + 2))
        expected_diff = F(9 * r**3, 2 * (r + 2) * (r + 8) * (2 * r + 1))
        expected_total = F(3 * r * (4 * r*r + 9 * r + 8),
                           2 * (r + 2) * (r + 8) * (2 * r + 1))
        require(pair(retained, retained) / (eu * ev) == beta2, "retained norm")
        require(pair(sum_spill, sum_spill) / (eu * ev) == expected_sum, "sum spill norm")
        require(pair(diff_spill, diff_spill) / (eu * ev) == expected_diff, "difference spill norm")
        total = pair(mixed, mixed) / (eu * ev)
        escaped = pair(spill, spill) / (eu * ev)
        require(total == expected_total == beta2 + escaped, "complete mixed norm")
        rows.append({"generation": n, "radius_squared": str(radius),
                     "self_multiplier": str(gamma), "self_normalized_squared": str(beta2),
                     "mixed_modes": len(mixed), "escaped_modes": len(spill),
                     "mixed_normalized_squared": str(total),
                     "escaped_normalized_squared": str(escaped),
                     "escaped_fraction": str(escaped / total)})
    return {"checked_generations": generations, "rows": rows}


def cyclic_field(radii) -> Field:
    a, b, c = radii
    return add(sine((a, 0, 0), (0, 1, 0)),
               sine((0, b, 0), (0, 0, 1)),
               sine((0, 0, c), (1, 0, 0)))


def fully_3d(u: Field) -> Field:
    """A coordinate-support condition, not a claim about flow dimension."""
    return {k: v for k, v in u.items() if all(k)}


def check_cyclic():
    rows = []
    for radii in ((1, 1, 1), (1, 1, 2), (2, 3, 4), (12, 13, 13), (5, 5, 6)):
        a, b, c = radii
        u = cyclic_field(radii)
        validate(u)
        n = B(u, u)
        t = add(B(u, n), B(n, u))
        validate(t)
        triple = fully_3d(t)
        expected = {}
        for signs in itertools.product((-1, 1), repeat=3):
            aa, bb, cc = k = tuple(x * s for x, s in zip(radii, signs))
            amplitude = F(-signs[0] * signs[1] * signs[2], 4)
            value = tuple(amplitude * x for x in project(k, (bb*cc, cc*aa, aa*bb)))
            if any(value):
                expected[k] = value
        require(triple == expected, "cyclic triple projection")
        squared = F(a*a*(b*b-c*c)**2 + b*b*(c*c-a*a)**2 + c*c*(a*a-b*b)**2,
                    2 * (a*a + b*b + c*c))
        require(pair(triple, triple) == squared, "cyclic triple norm")
        rows.append({"radii": radii, "triple_modes": len(triple),
                     "triple_source_squared": str(squared)})
    reference = None
    for nu in (F(0), F(1), F(3, 2), F(2)):
        u, _, _ = jets(cyclic_field((1, 1, 1)), nu)
        require(not fully_3d(u[2]), "equal-radius second coefficient")
        third = fully_3d(u[3])
        require(len(third) == 24 and pair(third, third) == F(31, 1152),
                "equal-radius third coefficient")
        require(third[(2, 1, 1)] == (F(-5, 288), F(1, 144), F(1, 36)),
                "third coefficient at (2,1,1)")
        if reference is not None:
            require(third == reference, "viscous dependence of third coefficient")
        reference = third
    return {"radius_checks": rows, "equal_radius_third_coefficient_modes": 24,
            "equal_radius_third_coefficient_squared": "31/1152",
            "viscosity_degree_bound": 3, "distinct_viscosity_samples": 4}


def crossing_field() -> Field:
    """Three finite boxes with cyclic, transverse polarizations."""
    out = {}
    for axis in range(3):
        ranges = [range(2, 4) if j == axis else range(-1, 2)
                  for j in range(3)]
        for k in itertools.product(*ranges):
            v = [F(0), F(0), F(0)]
            v[axis] = -F(k[(axis + 1) % 3])
            v[(axis + 1) % 3] = F(k[axis])
            out = add(out, {k: tuple(v),
                           tuple(-x for x in k): tuple(-x for x in v)})
    validate(out)
    return out


def check_crossing():
    # Check the direct pairing against complete source fields on smaller data.
    for u in matched_fields().values():
        n = B(u, u)
        for receiver, left, right in ((u, n, n), (n, u, n),
                                      (n, n, u), (A(u), n, n)):
            require(pair_source(receiver, left, right) == pair(receiver, B(left, right)),
                    "direct source pairing disagrees with full convolution")
    u = crossing_field()
    n = B(u, u)
    generated = {k: v for k, v in n.items() if k not in u}
    validate(n)
    validate(generated)
    require([len(u), len(n), len(generated)] == [108, 852, 756],
            "crossing support counts")
    require(pair(u, u) == 774, "crossing squared velocity norm")
    require(pair(u, n) == 0, "initial kinetic energy cancellation")
    kinetic = pair_source(u, generated, generated)
    enstrophy = pair_source(A(u), generated, generated)
    require(kinetic == F(7481477195560, 2909907), "parent kinetic return")
    require(enstrophy == F(3185491560402752, 140645505), "parent enstrophy return")
    require(kinetic > 0 and enstrophy > 0, "return signs")
    require(pair_source(generated, u, generated) == 0,
            "transport kinetic cancellation")
    require(pair_source(generated, generated, u) == -kinetic,
            "companion mixed kinetic work")
    return {"parent_modes": len(u), "complete_initial_source_modes": len(n),
            "generated_source_modes": len(generated), "squared_velocity_norm": "774",
            "kinetic_return_t2_coefficient": str(kinetic),
            "enstrophy_return_t2_coefficient": str(enstrophy),
            "normalization_factor_for_norm_alpha": "alpha^5 / 774^(5/2)",
            "scope": "one source channel; not net parent energy growth"}


def positive_int(text: str) -> int:
    value = int(text)
    if value <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return value


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", choices=("all", "matched", "chain", "cyclic", "crossing"),
                        default="all")
    parser.add_argument("--generations", type=positive_int, default=8,
                        help="number of exact chain instances (default: 8)")
    args = parser.parse_args()
    results = {"arithmetic": "fractions.Fraction", "period": "2*pi",
               "scope": "finite Fourier algebra and initial time derivatives; no Lean certificate"}
    for name, check in (("matched", check_matched_fields),
                        ("chain", lambda: check_chain(args.generations)),
                        ("cyclic", check_cyclic), ("crossing", check_crossing)):
        if args.case in ("all", name):
            results[name] = check()
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
