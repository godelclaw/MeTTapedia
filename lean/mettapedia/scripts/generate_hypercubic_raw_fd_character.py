#!/usr/bin/env python3
"""Generate kernel-replayable H(4) raw-tensor character certificates."""

from __future__ import annotations

import argparse
import hashlib
import itertools
from pathlib import Path


PERMUTATIONS = tuple(itertools.permutations(range(4)))
PERMUTATION_COUNT = 24
REFLECTION_COUNT = 16
MAX_RANK = 16


def permutation_sign(permutation: tuple[int, ...]) -> int:
    inversions = sum(
        permutation[left] > permutation[right]
        for left in range(4)
        for right in range(left + 1, 4)
    )
    return -1 if inversions % 2 else 1


def axis_sign(mask: int, axis: int) -> int:
    return -1 if mask & (1 << axis) else 1


def signed_trace(permutation: tuple[int, ...], mask: int) -> int:
    return sum(axis_sign(mask, axis) for axis in range(4)
               if permutation[axis] == axis)


def orientation(permutation: tuple[int, ...], mask: int) -> int:
    result = permutation_sign(permutation)
    for axis in range(4):
        result *= axis_sign(mask, axis)
    return result


TRACE = tuple(
    tuple(signed_trace(permutation, mask) for mask in range(REFLECTION_COUNT))
    for permutation in PERMUTATIONS
)
ORIENTATION = tuple(
    tuple(orientation(permutation, mask) for mask in range(REFLECTION_COUNT))
    for permutation in PERMUTATIONS
)
PERMUTATION_SIGN = tuple(permutation_sign(permutation) for permutation in PERMUTATIONS)


def reflection_moment(parity: int, permutation: int, rank: int) -> int:
    return sum(
        (1 if parity == 0 else ORIENTATION[permutation][mask])
        * TRACE[permutation][mask] ** rank
        for mask in range(REFLECTION_COUNT)
    )


REFLECTION_MOMENT = tuple(
    tuple(
        tuple(reflection_moment(parity, permutation, rank)
              for rank in range(MAX_RANK + 1))
        for permutation in range(PERMUTATION_COUNT)
    )
    for parity in range(2)
)

TOTAL_MOMENT = tuple(
    tuple(
        sum(REFLECTION_MOMENT[parity][permutation][rank]
            for permutation in range(PERMUTATION_COUNT))
        for rank in range(MAX_RANK + 1)
    )
    for parity in range(2)
)

MULTIPLICITY = tuple(
    tuple(total // 384 for total in totals)
    for totals in TOTAL_MOMENT
)


def lean_integer(value: int) -> str:
    return str(value) if value >= 0 else f"({value})"


def fin_table(name: str, first_size: int, second_size: int,
              values: tuple[tuple[int, ...], ...], codomain: str = "ℚ") -> str:
    outer = []
    for first in range(first_size):
        inner = "\n".join(
            f"      | {second} => {lean_integer(values[first][second])}"
            for second in range(second_size)
        )
        outer.append(
            f"  | {first} =>\n"
            f"    match second.1 with\n{inner}\n"
            f"      | _ => 0"
        )
    return (
        f"def {name} (first : Fin {first_size}) "
        f"(second : Fin {second_size}) : {codomain} :=\n"
        f"  match first.1 with\n" + "\n".join(outer) + "\n  | _ => 0\n"
    )


def parity_rank_table(name: str, values: tuple[tuple[int, ...], ...],
                      codomain: str) -> str:
    scalar = "\n".join(
        f"      | {rank} => {lean_integer(values[0][rank])}"
        for rank in range(MAX_RANK + 1)
    )
    pseudo = "\n".join(
        f"      | {rank} => {lean_integer(values[1][rank])}"
        for rank in range(MAX_RANK + 1)
    )
    return f'''def {name}
    (parity : ContractionParity) (rank : Fin 17) : {codomain} :=
  match parity with
  | .scalar =>
    match rank.1 with
{scalar}
      | _ => 0
  | .pseudoscalar =>
    match rank.1 with
{pseudo}
      | _ => 0
'''


def expected_reflection_moment_table() -> str:
    parity_parts = []
    for parity, constructor in enumerate(("scalar", "pseudoscalar")):
        permutation_parts = []
        for permutation in range(PERMUTATION_COUNT):
            ranks = "\n".join(
                f"        | {rank} => "
                f"{lean_integer(REFLECTION_MOMENT[parity][permutation][rank])}"
                for rank in range(MAX_RANK + 1)
            )
            permutation_parts.append(
                f"    | {permutation} =>\n"
                f"      match rank.1 with\n{ranks}\n"
                f"        | _ => 0"
            )
        parity_parts.append(
            f"  | .{constructor} =>\n"
            f"    match permutation.1 with\n" +
            "\n".join(permutation_parts) + "\n    | _ => 0"
        )
    return (
        "def expectedReflectionCharacterMoment\n"
        "    (parity : ContractionParity) (permutation : Fin 24)\n"
        "    (rank : Fin 17) : ℚ :=\n"
        "  match parity with\n" + "\n".join(parity_parts) + "\n"
    )


def generated_data(digest: str) -> str:
    signs = "\n".join(
        f"  | {index} => {lean_integer(value)}"
        for index, value in enumerate(PERMUTATION_SIGN)
    )
    return f'''import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterCensus

/-!
# Generated character data for the unpadded raw `F,D` carrier

The tables contain all 384 signed-permutation trace and determinant values,
their rank-zero-through-sixteen moments, and the resulting Reynolds
multiplicities.  The certificate digest is `{digest}`.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicRawFDCharacterCensus

open V14HypercubicFDCensus

def expectedPermutationSign (permutation : Fin 24) : ℚ :=
  match permutation.1 with
{signs}
  | _ => 0

{fin_table("expectedSignedAxisTrace", 24, 16, TRACE)}
{fin_table("expectedOrientationSign", 24, 16, ORIENTATION)}
{expected_reflection_moment_table()}
{parity_rank_table("expectedTotalCharacterMoment", TOTAL_MOMENT, "ℚ")}
{parity_rank_table("certifiedTensorInvariantMultiplicity", MULTIPLICITY, "ℕ")}

end HypercubicRawFDCharacterCensus
end YangMills
end QuantumTheory
end Mettapedia
'''


def trace_expression(permutation: int, mask: int) -> str:
    terms = [
        axis_sign(mask, axis) if PERMUTATIONS[permutation][axis] == axis else 0
        for axis in range(4)
    ]
    return f"((({lean_integer(terms[0])} : ℚ) + {lean_integer(terms[1])}) + " \
        f"{lean_integer(terms[2])}) + {lean_integer(terms[3])}"


def orientation_expression(mask: int) -> str:
    signs = [axis_sign(mask, axis) for axis in range(4)]
    return f"({lean_integer(signs[0])} : ℚ) * " \
        f"({lean_integer(signs[1])} * ({lean_integer(signs[2])} * " \
        f"{lean_integer(signs[3])}))"


def block_file(permutation: int) -> str:
    trace_cases = []
    orientation_cases = []
    for mask in range(REFLECTION_COUNT):
        trace_cases.append(
            f"  · change {trace_expression(permutation, mask)} = "
            f"expectedSignedAxisTrace {permutation} {mask}\n"
            f"    norm_num [expectedSignedAxisTrace]"
        )
        orientation_cases.append(
            f"  · change ((Equiv.Perm.sign (permutationCode {permutation}) : ℤ) : ℚ) *\n"
            f"        ({orientation_expression(mask)}) =\n"
            f"      expectedOrientationSign {permutation} {mask}\n"
            f"    rw [permutationSign_certificate_block{permutation}]\n"
            f"    norm_num [expectedPermutationSign, expectedOrientationSign]"
        )
    return f'''import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterGeneratedData

/-! Kernel-checked raw `F,D` character certificate block {permutation}. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicRawFDCharacterCensus

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus

theorem permutationSign_certificate_block{permutation} :
    ((Equiv.Perm.sign (permutationCode {permutation}) : ℤ) : ℚ) =
      expectedPermutationSign {permutation} := by
  decide

theorem signedAxisTrace_certificate_block{permutation} :
    ∀ reflectionMask : Fin 16,
      signedAxisTrace
          (decodedHypercubicCharacterElement {permutation} reflectionMask) =
        expectedSignedAxisTrace {permutation} reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [signedAxisTrace_four_terms]
{chr(10).join(trace_cases)}

theorem orientationSign_certificate_block{permutation} :
    ∀ reflectionMask : Fin 16,
      Hypercubic4.orientationSign
          (decodedHypercubicCharacterElement {permutation} reflectionMask) =
        expectedOrientationSign {permutation} reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [orientationSign_four_factors]
{chr(10).join(orientation_cases)}

theorem reflectionCharacterMoment_certificate_block{permutation} :
    ∀ parity : ContractionParity, ∀ rank : Fin 17,
      encodedReflectionCharacterMoment parity {permutation} rank =
        expectedReflectionCharacterMoment parity {permutation} rank := by
  intro parity rank
  cases parity <;> fin_cases rank <;>
    norm_num [encodedReflectionCharacterMoment,
      ContractionParity.character,
      signedAxisTrace_certificate_block{permutation},
      orientationSign_certificate_block{permutation},
      expectedSignedAxisTrace, expectedOrientationSign,
      expectedReflectionCharacterMoment, Fin.sum_univ_succ]

end HypercubicRawFDCharacterCensus
end YangMills
end QuantumTheory
end Mettapedia
'''


def aggregate_file() -> str:
    imports = "\n".join(
        "import Mettapedia.QuantumTheory.YangMills."
        f"HypercubicRawFDCharacterCertificateBlock{permutation}"
        for permutation in range(PERMUTATION_COUNT)
    )
    sign_cases = "\n".join(
        f"  · exact permutationSign_certificate_block{permutation}"
        for permutation in range(PERMUTATION_COUNT)
    )
    trace_cases = "\n".join(
        f"  · exact signedAxisTrace_certificate_block{permutation} reflectionMask"
        for permutation in range(PERMUTATION_COUNT)
    )
    orientation_cases = "\n".join(
        f"  · exact orientationSign_certificate_block{permutation} reflectionMask"
        for permutation in range(PERMUTATION_COUNT)
    )
    moment_cases = "\n".join(
        f"  · exact reflectionCharacterMoment_certificate_block{permutation} parity rank"
        for permutation in range(PERMUTATION_COUNT)
    )
    return f'''{imports}

/-! # Complete kernel-checked raw `F,D` character certificate -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicRawFDCharacterCensus

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus

theorem permutationSign_certificate (permutation : Fin 24) :
    ((Equiv.Perm.sign (permutationCode permutation) : ℤ) : ℚ) =
      expectedPermutationSign permutation := by
  fin_cases permutation
{sign_cases}

theorem signedAxisTrace_certificate
    (permutation : Fin 24) (reflectionMask : Fin 16) :
    signedAxisTrace
        (decodedHypercubicCharacterElement permutation reflectionMask) =
      expectedSignedAxisTrace permutation reflectionMask := by
  fin_cases permutation
{trace_cases}

theorem orientationSign_certificate
    (permutation : Fin 24) (reflectionMask : Fin 16) :
    Hypercubic4.orientationSign
        (decodedHypercubicCharacterElement permutation reflectionMask) =
      expectedOrientationSign permutation reflectionMask := by
  fin_cases permutation
{orientation_cases}

theorem reflectionCharacterMoment_certificate
    (parity : ContractionParity) (permutation : Fin 24) (rank : Fin 17) :
    encodedReflectionCharacterMoment parity permutation rank =
      expectedReflectionCharacterMoment parity permutation rank := by
  fin_cases permutation
{moment_cases}

theorem encodedCharacterMoment_certificate
    (parity : ContractionParity) (rank : Fin 17) :
    encodedCharacterMoment parity rank =
      expectedTotalCharacterMoment parity rank := by
  unfold encodedCharacterMoment
  simp_rw [reflectionCharacterMoment_certificate]
  cases parity <;> fin_cases rank <;>
    norm_num [expectedReflectionCharacterMoment,
      expectedTotalCharacterMoment, Fin.sum_univ_succ]

theorem expectedTotalCharacterMoment_eq_multiplicity
    (parity : ContractionParity) (rank : Fin 17) :
    expectedTotalCharacterMoment parity rank =
      384 * certifiedTensorInvariantMultiplicity parity rank := by
  cases parity <;> fin_cases rank <;>
    norm_num [expectedTotalCharacterMoment,
      certifiedTensorInvariantMultiplicity]

theorem rawTensorInvariantCharacterMultiplicity_certificate
    (parity : ContractionParity) (rank : Fin 17) :
    rawTensorInvariantCharacterMultiplicity parity rank =
      certifiedTensorInvariantMultiplicity parity rank := by
  unfold rawTensorInvariantCharacterMultiplicity
  rw [hypercubic_character_sum_eq_encoded,
    encodedCharacterMoment_certificate,
    expectedTotalCharacterMoment_eq_multiplicity]
  ring

theorem finrank_axisTensorInvariantSubmodule_certificate
    (parity : ContractionParity) (rank : Fin 17) :
    Module.finrank ℚ (axisTensorInvariantSubmodule parity rank) =
      certifiedTensorInvariantMultiplicity parity rank := by
  apply Nat.cast_injective (R := ℚ)
  rw [finrank_axisTensorInvariantSubmodule,
    rawTensorInvariantCharacterMultiplicity_certificate]

end HypercubicRawFDCharacterCensus
end YangMills
end QuantumTheory
end Mettapedia
'''


def validate() -> str:
    assert len(PERMUTATIONS) == PERMUTATION_COUNT
    assert len(set(PERMUTATIONS)) == PERMUTATION_COUNT
    assert all(total % 384 == 0 for totals in TOTAL_MOMENT for total in totals)
    assert MULTIPLICITY[0] == (
        1, 0, 1, 0, 4, 0, 31, 0, 379, 0, 5611, 0, 87979, 0,
        1400491, 0, 22379179,
    )
    assert MULTIPLICITY[1] == (
        0, 0, 0, 0, 1, 0, 20, 0, 336, 0, 5440, 0, 87296, 0,
        1397760, 0, 22368256,
    )
    payload = "\n".join(
        f"{permutation}:{PERMUTATION_SIGN[permutation]}:"
        f"{TRACE[permutation]}:{ORIENTATION[permutation]}:"
        f"{REFLECTION_MOMENT[0][permutation]}:"
        f"{REFLECTION_MOMENT[1][permutation]}"
        for permutation in range(PERMUTATION_COUNT)
    )
    return hashlib.sha256(payload.encode()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    output_dir = args.output_dir
    output_dir.mkdir(parents=True, exist_ok=True)
    digest = validate()
    (output_dir / "HypercubicRawFDCharacterGeneratedData.lean").write_text(
        generated_data(digest)
    )
    for permutation in range(PERMUTATION_COUNT):
        (output_dir /
         f"HypercubicRawFDCharacterCertificateBlock{permutation}.lean").write_text(
            block_file(permutation)
        )
    (output_dir / "HypercubicRawFDCharacterCertificate.lean").write_text(
        aggregate_file()
    )
    print(digest)


if __name__ == "__main__":
    main()
