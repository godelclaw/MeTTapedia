#!/usr/bin/env python3
"""Compute our finite-H(4), SU(2)-singlet operator count through fixed degree."""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from pathlib import Path


POWER_TRACES = (
    (-4, 4),
    (-2, 0, -2, 4),
    (-2, 4),
    (-1, 1, -4, 1, -1, 4),
    (-1, 1, 2, 1, -1, 4),
    (0, -4, 0, 4),
    (0, 0, 0, -4, 0, 0, 0, 4),
    (0, 0, 0, 4),
    (0, 4),
    (1, 1, -2, 1, 1, 4),
    (1, 1, 4),
    (2, 0, 2, 4),
    (2, 4),
    (4,),
)

ORIENTATION = (1, 1, -1, 1, -1, 1, 1, -1, 1, -1, 1, 1, -1, 1)
MULTIPLICITY = (1, 12, 16, 32, 32, 12, 48, 96, 42, 32, 32, 12, 16, 1)


def power_trace(trace_class: int, exponent: int) -> int:
    if exponent == 0:
        return 4
    row = POWER_TRACES[trace_class]
    return row[(exponent - 1) % len(row)]


def exterior_character(trace_class: int, power: int, degree: int) -> int:
    p1 = power_trace(trace_class, power)
    p2 = power_trace(trace_class, 2 * power)
    p3 = power_trace(trace_class, 3 * power)
    if degree == 0:
        return 1
    if degree == 1:
        return p1
    if degree == 2:
        numerator = p1 * p1 - p2
        assert numerator % 2 == 0
        return numerator // 2
    if degree == 3:
        numerator = p1**3 - 3 * p1 * p2 + 2 * p3
        assert numerator % 6 == 0
        return numerator // 6
    if degree == 4:
        return ORIENTATION[trace_class] ** power
    return 0


def determinant_coefficient(trace_class: int, power: int, degree: int) -> int:
    return (-1) ** degree * exterior_character(trace_class, power, degree)


def inverse_determinant_series(trace_class: int, power: int, maximum: int) -> list[int]:
    values = [1]
    for degree in range(1, maximum + 1):
        correction = sum(
            determinant_coefficient(trace_class, power, shift)
            * values[degree - shift]
            for shift in range(1, min(4, degree) + 1)
        )
        values.append(-correction)
    return values


def single_particle_numerator(policy: str, trace_class: int, power: int, degree: int) -> int:
    if degree == 2:
        return exterior_character(trace_class, power, 2)
    if policy == "off_shell" and degree == 3:
        return -exterior_character(trace_class, power, 3)
    if policy == "off_shell" and degree == 4:
        return exterior_character(trace_class, power, 4)
    if policy == "on_shell" and degree == 3:
        return -(
            exterior_character(trace_class, power, 1)
            + exterior_character(trace_class, power, 3)
        )
    if policy == "on_shell" and degree == 4:
        return 1 + exterior_character(trace_class, power, 4)
    return 0


def single_particle_series(policy: str, trace_class: int, power: int, maximum: int) -> list[int]:
    inverse = inverse_determinant_series(trace_class, power, maximum)
    values = []
    for degree in range(maximum + 1):
        values.append(
            sum(
                single_particle_numerator(policy, trace_class, power, shift)
                * inverse[degree - shift]
                for shift in range(2, min(4, degree) + 1)
            )
        )
    return values


ColorPolynomial = dict[int, int]


def add_scaled(target: defaultdict[int, int], source: ColorPolynomial, scale: int) -> None:
    for exponent, coefficient in source.items():
        target[exponent] += scale * coefficient


def multiply(left: ColorPolynomial, right: ColorPolynomial) -> ColorPolynomial:
    result: defaultdict[int, int] = defaultdict(int)
    for left_exponent, left_coefficient in left.items():
        for right_exponent, right_coefficient in right.items():
            result[left_exponent + right_exponent] += left_coefficient * right_coefficient
    return {exponent: coefficient for exponent, coefficient in result.items() if coefficient}


def adjoint_character(power: int) -> ColorPolynomial:
    return {-2 * power: 1, 0: 1, 2 * power: 1}


def plethystic_data(policy: str, trace_class: int, maximum: int) -> dict[str, object]:
    particles = [None] + [
        single_particle_series(policy, trace_class, power, maximum // power)
        for power in range(1, maximum + 1)
    ]
    weighted_log: list[ColorPolynomial] = [{}]
    for degree in range(1, maximum + 1):
        coefficient: defaultdict[int, int] = defaultdict(int)
        for power in range(1, degree + 1):
            if degree % power == 0:
                source_degree = degree // power
                add_scaled(
                    coefficient,
                    adjoint_character(power),
                    source_degree * particles[power][source_degree],
                )
        weighted_log.append(dict(coefficient))

    values: list[ColorPolynomial] = [{0: 1}]
    for degree in range(1, maximum + 1):
        numerator: defaultdict[int, int] = defaultdict(int)
        for source_degree in range(1, degree + 1):
            add_scaled(
                numerator,
                multiply(weighted_log[source_degree], values[degree - source_degree]),
                1,
            )
        quotient: ColorPolynomial = {}
        for exponent, coefficient in numerator.items():
            assert coefficient % degree == 0, (trace_class, degree, exponent, coefficient)
            value = coefficient // degree
            if value:
                quotient[exponent] = value
        values.append(quotient)
    return {
        "particles": particles,
        "logarithm": weighted_log,
        "plethystic": values,
    }


def plethystic_series(policy: str, trace_class: int, maximum: int) -> list[ColorPolynomial]:
    return plethystic_data(policy, trace_class, maximum)["plethystic"]


def ibp_series(policy: str, trace_class: int, maximum: int) -> list[ColorPolynomial]:
    series = plethystic_series(policy, trace_class, maximum)
    values: list[ColorPolynomial] = []
    for degree in range(maximum + 1):
        coefficient: defaultdict[int, int] = defaultdict(int)
        for shift in range(0, min(4, degree) + 1):
            add_scaled(
                coefficient,
                series[degree - shift],
                determinant_coefficient(trace_class, 1, shift),
            )
        values.append({exponent: value for exponent, value in coefficient.items() if value})
    return values


def class_certificate(policy: str, trace_class: int, maximum: int) -> dict[str, object]:
    data = plethystic_data(policy, trace_class, maximum)
    series = data["plethystic"]
    ibp: list[ColorPolynomial] = []
    for degree in range(maximum + 1):
        coefficient: defaultdict[int, int] = defaultdict(int)
        for shift in range(0, min(4, degree) + 1):
            add_scaled(
                coefficient,
                series[degree - shift],
                determinant_coefficient(trace_class, 1, shift),
            )
        ibp.append({exponent: value for exponent, value in coefficient.items() if value})
    data["ibp"] = ibp
    data["singlets"] = [su2_singlet_multiplicity(value) for value in ibp]
    return data


def su2_singlet_multiplicity(character: ColorPolynomial) -> int:
    return character.get(0, 0) - character.get(2, 0)


def hilbert_series(policy: str, maximum: int) -> tuple[list[int], list[list[int]]]:
    class_rows = [
        [su2_singlet_multiplicity(value) for value in ibp_series(policy, trace_class, maximum)]
        for trace_class in range(14)
    ]
    result = []
    for degree in range(maximum + 1):
        numerator = sum(
            MULTIPLICITY[trace_class] * class_rows[trace_class][degree]
            for trace_class in range(14)
        )
        assert numerator % 384 == 0, (policy, degree, numerator)
        result.append(numerator // 384)
    return result, class_rows


def dense_color_row(row: ColorPolynomial, maximum: int) -> list[int]:
    return [row.get(index - 2 * maximum, 0) for index in range(4 * maximum + 1)]


def lean_int(value: int) -> str:
    return str(value) if value >= 0 else f"({value})"


def lean_array(values: list[int]) -> str:
    return "#[" + ", ".join(lean_int(value) for value in values) + "]"


def lean_nested_array(rows: list[list[int]]) -> str:
    return "#[\n    " + ",\n    ".join(lean_array(row) for row in rows) + "\n  ]"


def lean_sparse_row(row: ColorPolynomial) -> str:
    entries = ", ".join(
        f"({lean_int(exponent)}, {lean_int(coefficient)})"
        for exponent, coefficient in sorted(row.items())
        if coefficient
    )
    return "[" + entries + "]"


def lean_sparse_array(rows: list[ColorPolynomial]) -> str:
    return "#[\n    " + ",\n    ".join(lean_sparse_row(row) for row in rows) + "\n  ]"


def certificate_names(policy: str, trace_class: int) -> tuple[str, str]:
    policy_name = "OffShell" if policy == "off_shell" else "OnShell"
    block = f"HypercubicSU2HilbertCertificate{policy_name}Block{trace_class}"
    return policy_name, block


def render_lean_certificate_data(policy: str, trace_class: int, maximum: int) -> str:
    data = class_certificate(policy, trace_class, maximum)
    _, block = certificate_names(policy, trace_class)
    namespace = f"{block}Data"
    particles = [row if row is not None else [] for row in data["particles"]]
    logarithm = data["logarithm"]
    plethystic = data["plethystic"]
    ibp = data["ibp"]
    singlets = data["singlets"]
    return f'''import Mettapedia.QuantumTheory.YangMills.HypercubicSU2HilbertCertificate

/-! # SU(2) Hilbert data: {policy.replace("_", "-")} class {trace_class} -/

set_option autoImplicit false
set_option maxHeartbeats 0

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace {namespace}

open HypercubicCartanMaxwellHilbertCertificate
open HypercubicSU2HilbertCertificate

def certificate : SparseSU2ClassCertificate where
  particles := {lean_nested_array(particles)}
  logarithm := {lean_sparse_array(logarithm)}
  plethystic := {lean_sparse_array(plethystic)}
  ibp := {lean_sparse_array(ibp)}
  singlets := {lean_array(singlets)}

end {namespace}
end YangMills
end QuantumTheory
end Mettapedia
'''


def render_lean_certificate_replay(
    policy: str, trace_class: int, maximum: int, chunk: int, degrees: list[int]
) -> str:
    _, block = certificate_names(policy, trace_class)
    data_namespace = f"{block}Data"
    namespace = f"{block}Replay{chunk}"
    policy_ctor = ".offShell" if policy == "off_shell" else ".onShell"
    particles = ""
    if chunk == 0:
        particles = f'''theorem certificate_particles :
    sparseCertificateParticlesValid {policy_ctor} ({trace_class} : Fin 14) {maximum}
        certificate = true := by
  decide

'''
    degree_lemmas = "\n\n".join(
        f'''theorem certificate_degree_{degree} :
    sparseCertificateDegreeValidAt ({trace_class} : Fin 14) {maximum} {degree}
        certificate = true := by
  decide'''
        for degree in degrees
    )
    axiom_prints = "\n".join(
        ["#print axioms certificate_particles"] if chunk == 0 else []
    )
    if axiom_prints:
        axiom_prints += "\n"
    axiom_prints += "\n".join(
        f"#print axioms certificate_degree_{degree}" for degree in degrees
    )
    return f'''import Mettapedia.QuantumTheory.YangMills.{data_namespace}

/-! # SU(2) Hilbert replay: {policy.replace("_", "-")} class {trace_class}, block {chunk} -/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace {namespace}

open HypercubicCartanMaxwellHilbertCertificate
open HypercubicSU2HilbertCertificate
open {data_namespace}

{particles}{degree_lemmas}

{axiom_prints}

end {namespace}
end YangMills
end QuantumTheory
end Mettapedia
'''


def write_lean_certificates(
    output_dir: Path,
    maximum: int,
    requested_policy: str | None,
    requested_trace_class: int | None,
) -> None:
    output_dir.mkdir(parents=True, exist_ok=True)
    policies = (requested_policy,) if requested_policy else ("off_shell", "on_shell")
    trace_classes = (
        (requested_trace_class,)
        if requested_trace_class is not None
        else tuple(range(14))
    )
    for policy in policies:
        policy_name = "OffShell" if policy == "off_shell" else "OnShell"
        for trace_class in trace_classes:
            block = f"HypercubicSU2HilbertCertificate{policy_name}Block{trace_class}"
            (output_dir / f"{block}Data.lean").write_text(
                render_lean_certificate_data(policy, trace_class, maximum),
                encoding="utf-8",
            )
            chunk_size = (maximum + 4) // 4
            for chunk in range(4):
                start = chunk * chunk_size
                stop = min((chunk + 1) * chunk_size, maximum + 1)
                degrees = list(range(start, stop))
                (output_dir / f"{block}Replay{chunk}.lean").write_text(
                    render_lean_certificate_replay(
                        policy, trace_class, maximum, chunk, degrees
                    ),
                    encoding="utf-8",
                )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--maximum", type=int, default=16)
    parser.add_argument("--lean-output-dir", type=Path)
    parser.add_argument("--policy", choices=("off_shell", "on_shell"))
    parser.add_argument("--trace-class", type=int, choices=range(14))
    args = parser.parse_args()
    if args.maximum < 0:
        parser.error("--maximum must be nonnegative")
    if args.lean_output_dir is not None:
        write_lean_certificates(
            args.lean_output_dir,
            args.maximum,
            args.policy,
            args.trace_class,
        )
    payload = {"maximum": args.maximum, "realization": "H4_SU2_singlet_Hilbert"}
    for policy in ("off_shell", "on_shell"):
        values, class_rows = hilbert_series(policy, args.maximum)
        payload[policy] = {"values": values, "class_rows": class_rows}
    print(json.dumps(payload, sort_keys=True, separators=(",", ":")))


if __name__ == "__main__":
    main()
