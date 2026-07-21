#!/usr/bin/env python3
"""Generate sparse Lean certificates for the dimension-16 Cartan census."""

from __future__ import annotations

import argparse
import hashlib
import itertools
from pathlib import Path


DEGREE = 8
PLANE_COUNT = 6
BLOCK_SIZE = 33
RAW_COUNT = 1287
BLOCK_COUNT = RAW_COUNT // BLOCK_SIZE
PLANES = ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3))
PLANE_INDEX = {plane: index for index, plane in enumerate(PLANES)}
PERMUTATIONS = tuple(itertools.permutations(range(4)))

REPRESENTATIVES = (
    (0, 0, 0, 0, 0, 8),
    (0, 0, 0, 0, 2, 6),
    (0, 0, 0, 0, 4, 4),
    (0, 0, 0, 2, 2, 4),
    (0, 0, 2, 0, 2, 4),
    (0, 0, 2, 2, 0, 4),
    (0, 0, 2, 2, 2, 2),
    (0, 0, 2, 4, 0, 2),
    (0, 0, 2, 6, 0, 0),
    (0, 0, 4, 4, 0, 0),
    (0, 1, 1, 1, 1, 4),
    (0, 1, 1, 1, 3, 2),
    (0, 1, 1, 1, 5, 0),
    (0, 1, 1, 3, 3, 0),
    (0, 1, 3, 3, 1, 0),
    (0, 2, 2, 2, 2, 0),
    (1, 1, 2, 2, 1, 1),
)


def exponent_vectors(degree: int) -> list[tuple[int, ...]]:
    vectors = []
    for multiset in itertools.combinations_with_replacement(range(PLANE_COUNT), degree):
        exponent = tuple(multiset.count(index) for index in range(PLANE_COUNT))
        vectors.append(exponent)
    return sorted(vectors, key=base_code)


def base_code(exponent: tuple[int, ...]) -> int:
    return sum(value * (DEGREE + 1) ** index for index, value in enumerate(exponent))


def plane_action(permutation: tuple[int, ...], plane_index: int) -> tuple[int, int]:
    first, second = PLANES[plane_index]
    mapped_first, mapped_second = permutation[first], permutation[second]
    sign = 1 if mapped_first < mapped_second else -1
    plane = tuple(sorted((mapped_first, mapped_second)))
    return PLANE_INDEX[plane], sign


def act(exponent: tuple[int, ...], permutation_code: int, mask: int) -> tuple[tuple[int, ...], int]:
    permutation = PERMUTATIONS[permutation_code]
    output = [0] * PLANE_COUNT
    total_sign = 1
    for plane_index, power in enumerate(exponent):
        target, reorder_sign = plane_action(permutation, plane_index)
        first, second = PLANES[plane_index]
        reflection_sign = -1 if ((mask >> first) ^ (mask >> second)) & 1 else 1
        factor_sign = reorder_sign * reflection_sign
        output[target] += power
        if factor_sign < 0 and power % 2:
            total_sign = -total_sign
    return tuple(output), total_sign


def classify(exponent: tuple[int, ...]) -> tuple[str, int, int, int]:
    for coordinate, representative in enumerate(REPRESENTATIVES):
        for permutation_code in range(24):
            target, _ = act(representative, permutation_code, 0)
            if target == exponent:
                return ("orbit", coordinate, permutation_code, 0)
    for permutation_code in range(24):
        for mask in range(16):
            target, sign = act(exponent, permutation_code, mask)
            if target == exponent and sign == -1:
                return ("killed", -1, permutation_code, mask)
    raise RuntimeError(f"unclassified exponent vector: {exponent}")


def planes_from_exponent(exponent: tuple[int, ...]) -> str:
    entries = [str(index) for index, power in enumerate(exponent) for _ in range(power)]
    assert len(entries) == DEGREE
    return " ".join(entries)


def lean_certificate(certificate: tuple[str, int, int, int]) -> str:
    kind, coordinate, permutation, mask = certificate
    if kind == "orbit":
        return f".orbit {coordinate} {permutation} {mask}"
    return f".killed {permutation} {mask}"


def validate(vectors: list[tuple[int, ...]], certificates: list[tuple[str, int, int, int]]) -> None:
    assert len(vectors) == RAW_COUNT
    assert len(set(vectors)) == RAW_COUNT
    assert len(certificates) == RAW_COUNT
    orbit_coordinates = {certificate[1] for certificate in certificates if certificate[0] == "orbit"}
    assert orbit_coordinates == set(range(len(REPRESENTATIVES)))
    unseen = set(vectors)
    admissible_orbits = 0
    killed_orbits = 0
    while unseen:
        representative = min(unseen)
        orbit = {
            act(representative, permutation_code, 0)[0]
            for permutation_code in range(24)
        }
        negative = any(
            act(representative, permutation_code, mask) == (representative, -1)
            for permutation_code in range(24)
            for mask in range(16)
        )
        if negative:
            killed_orbits += 1
        else:
            admissible_orbits += 1
        unseen -= orbit
    assert admissible_orbits == 17
    assert killed_orbits == 58
    for coordinate, representative in enumerate(REPRESENTATIVES):
        for permutation_code in range(24):
            for mask in range(16):
                target, sign = act(representative, permutation_code, mask)
                if target == representative:
                    assert sign == 1, (coordinate, permutation_code, mask)

    quartic_vectors = exponent_vectors(4)
    quartic_representatives = {
        (0, 0, 0, 0, 0, 4),
        (0, 0, 0, 0, 2, 2),
        (0, 0, 2, 2, 0, 0),
        (0, 1, 1, 1, 1, 0),
    }
    quartic_good = set()
    quartic_killed = 0
    for exponent in quartic_vectors:
        negative = any(
            act(exponent, permutation_code, mask) == (exponent, -1)
            for permutation_code in range(24)
            for mask in range(16)
        )
        if negative:
            quartic_killed += 1
        else:
            quartic_good.add(min(act(exponent, permutation_code, 0)[0]
                for permutation_code in range(24)))
    assert quartic_good == quartic_representatives
    assert quartic_killed == 102


def generated_data(vectors: list[tuple[int, ...]], certificates: list[tuple[str, int, int, int]]) -> str:
    codes = [base_code(exponent) for exponent in vectors]
    digest = hashlib.sha256(
        "\n".join(f"{exponent}:{certificate}" for exponent, certificate in zip(vectors, certificates)).encode()
    ).hexdigest()
    code_lines = [
        f"  | {index} => {code}"
        for index, code in enumerate(codes)
    ]
    inverse_code_lines = [
        f"  | {code} => ⟨{index}, by decide⟩"
        for index, code in enumerate(codes)
    ]
    canonical_lines = [
        f"  | {index} => octicOfPlanes {planes_from_exponent(exponent)}"
        for index, exponent in enumerate(vectors)
    ]
    certificate_lines = [
        f"  | {index} => {lean_certificate(certificate)}"
        for index, certificate in enumerate(certificates)
    ]
    return f'''import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCensus

/-!
# Generated data for the dimension-sixteen Cartan census

This file contains the canonical 1,287-entry stars-and-bars table and one
sparse signed-orbit certificate per entry.  The certificate digest is
`{digest}`.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16CartanCensus

def canonicalOcticCode (index : Fin 1287) : Nat :=
  match index with
{chr(10).join(code_lines)}
  | _ => 472392

def canonicalOcticIndexOfCode : Nat → Fin 1287
{chr(10).join(inverse_code_lines)}
  | _ => 0

def canonicalOctic : Fin 1287 → OcticMonomial
{chr(10).join(canonical_lines)}
  | _ => octicOfPlanes 5 5 5 5 5 5 5 5

def canonicalOcticCertificate : Fin 1287 → OcticCertificate
{chr(10).join(certificate_lines)}
  | _ => .orbit 0 0 0

def octicWitnessBlockIndex (offset : Nat)
    (hoffset : offset + 33 ≤ 1287) (entry : Fin 33) : Fin 1287 :=
  ⟨offset + entry.1, by omega⟩

end HypercubicDimension16CartanCensus
end YangMills
end QuantumTheory
end Mettapedia
'''


def block_file(block: int) -> str:
    offset = block * BLOCK_SIZE
    return f'''import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanGeneratedData

/-! Kernel-checked dimension-sixteen Cartan certificate block {block}. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16CartanCensus

theorem canonicalOcticData_valid_block{block} :
    ∀ entry : Fin 33,
      let index := octicWitnessBlockIndex {offset} (by decide) entry
      octicCode (canonicalOctic index) = canonicalOcticCode index ∧
        (canonicalOcticCertificate index).Valid (canonicalOctic index) ∧
        canonicalOcticIndexOfCode (canonicalOcticCode index) = index := by
  set_option maxRecDepth 100000 in
    intro entry
    fin_cases entry <;> decide

end HypercubicDimension16CartanCensus
end YangMills
end QuantumTheory
end Mettapedia
'''


def aggregate_file() -> str:
    imports = "\n".join(
        f"import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificateBlock{block}"
        for block in range(BLOCK_COUNT)
    )
    branches = []
    for block in range(BLOCK_COUNT):
        lower = block * BLOCK_SIZE
        upper = (block + 1) * BLOCK_SIZE
        if block < BLOCK_COUNT - 1:
            branches.append(f'''  by_cases h{block} : index.1 < {upper}
  · let entry : Fin 33 := ⟨index.1 - {lower}, by omega⟩
    have valid := canonicalOcticData_valid_block{block} entry
    have hindex : octicWitnessBlockIndex {lower} (by decide) entry = index := by
      apply Fin.ext
      change {lower} + (index.1 - {lower}) = index.1
      omega
    simpa only [hindex] using valid''')
        else:
            branches.append(f'''  · let entry : Fin 33 := ⟨index.1 - {lower}, by omega⟩
    have valid := canonicalOcticData_valid_block{block} entry
    have hindex : octicWitnessBlockIndex {lower} (by decide) entry = index := by
      apply Fin.ext
      change {lower} + (index.1 - {lower}) = index.1
      omega
    simpa only [hindex] using valid''')
    return f'''{imports}

/-! # Kernel-checked dimension-sixteen Cartan census certificate -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16CartanCensus

open V14HypercubicQuarticCensus

theorem canonicalOcticData_valid :
    ∀ index : Fin 1287,
      octicCode (canonicalOctic index) = canonicalOcticCode index ∧
        (canonicalOcticCertificate index).Valid (canonicalOctic index) ∧
        canonicalOcticIndexOfCode (canonicalOcticCode index) = index := by
  intro index
{chr(10).join(branches)}

theorem canonicalOcticCode_injective :
    Function.Injective canonicalOcticCode := by
  exact Function.LeftInverse.injective
    (fun index => (canonicalOcticData_valid index).2.2)

theorem canonicalOctic_injective : Function.Injective canonicalOctic := by
  intro left right heq
  apply canonicalOcticCode_injective
  rw [← (canonicalOcticData_valid left).1,
    ← (canonicalOcticData_valid right).1, heq]

theorem canonicalOctic_bijective : Function.Bijective canonicalOctic := by
  apply (Fintype.bijective_iff_injective_and_card canonicalOctic).2
  exact ⟨canonicalOctic_injective, by simp [card_octicMonomial]⟩

theorem canonicalOctic_surjective : Function.Surjective canonicalOctic :=
  canonicalOctic_bijective.2

theorem octic_signedOrbit_classification (monomial : OcticMonomial) :
    (∃ coordinate : Fin 17,
      InSignedOcticOrbit (octicRepresentative coordinate) monomial) ∨
      HasNegativeOcticStabilizer monomial := by
  obtain ⟨index, rfl⟩ := canonicalOctic_surjective monomial
  have valid := (canonicalOcticData_valid index).2.1
  generalize certificateEquation :
    canonicalOcticCertificate index = certificate at valid
  cases certificate with
  | orbit coordinate permutation reflectionMask =>
      left
      exact ⟨coordinate, decodeHypercubic permutation reflectionMask, valid⟩
  | killed permutation reflectionMask =>
      right
      exact ⟨decodeHypercubic permutation reflectionMask, valid⟩

end HypercubicDimension16CartanCensus
end YangMills
end QuantumTheory
end Mettapedia
'''


def stabilizer_file(coordinate: int) -> str:
    return f'''import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCensus

/-! Positive-stabilizer certificate for dimension-sixteen representative {coordinate}. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16CartanCensus

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus

theorem octic_representative_{coordinate}_stabilizer_positive :
    ∀ h : Hypercubic4,
      (octicRepresentative {coordinate}).act h = octicRepresentative {coordinate} →
        (octicRepresentative {coordinate}).tensorSign h = 1 := by
  intro h hstable
  have reflectionCancellation :
      (octicRepresentative {coordinate}).tensorSign h =
        (octicRepresentative {coordinate}).tensorSign
          (unsignedHypercubic h.perm) := by
    set_option maxRecDepth 100000 in
      cases href0 : h.reflected 0 <;> cases href1 : h.reflected 1 <;>
        cases href2 : h.reflected 2 <;> cases href3 : h.reflected 3 <;>
        simp [octicRepresentative, octicOfPlanes,
          OcticMonomial.tensorSign, Sym.ofVector, Sym.toMultiset,
          planeTensorSign,
          SU2LatticeFDCensusNoGo.OrientedPlane.first,
          SU2LatticeFDCensusNoGo.OrientedPlane.second,
          href0, href1, href2, href3]
  rw [reflectionCancellation]
  have unsignedCheck : ∀ permutation : Equiv.Perm Axis,
      (octicRepresentative {coordinate}).act
          (unsignedHypercubic permutation) = octicRepresentative {coordinate} →
        (octicRepresentative {coordinate}).tensorSign
          (unsignedHypercubic permutation) = 1 := by
    set_option maxRecDepth 100000 in decide
  apply unsignedCheck h.perm
  exact (OcticMonomial.act_eq_unsigned h
    (octicRepresentative {coordinate})).symm.trans hstable

end HypercubicDimension16CartanCensus
end YangMills
end QuantumTheory
end Mettapedia
'''


def stabilizer_aggregate_file() -> str:
    imports = "\n".join(
        f"import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanStabilizer{coordinate}"
        for coordinate in range(len(REPRESENTATIVES))
    )
    cases = "\n".join(
        f"  · exact octic_representative_{coordinate}_stabilizer_positive"
        for coordinate in range(len(REPRESENTATIVES))
    )
    return f'''{imports}
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanCertificate

/-! # Positive stabilizers for all seventeen dimension-sixteen representatives -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16CartanCensus

open V14HypercubicFDCensus

theorem octic_representative_stabilizer_positive :
    ∀ coordinate : Fin 17, ∀ h : Hypercubic4,
      (octicRepresentative coordinate).act h =
          octicRepresentative coordinate →
        (octicRepresentative coordinate).tensorSign h = 1 := by
  intro coordinate
  fin_cases coordinate
{cases}

end HypercubicDimension16CartanCensus
end YangMills
end QuantumTheory
end Mettapedia
'''


def expected_outputs() -> dict[Path, str]:
    vectors = exponent_vectors(DEGREE)
    certificates = [classify(exponent) for exponent in vectors]
    validate(vectors, certificates)
    repo = Path(__file__).resolve().parents[3]
    target = repo / "lean/mettapedia/Mettapedia/QuantumTheory/YangMills"
    outputs = {
        target / "HypercubicDimension16CartanGeneratedData.lean": generated_data(vectors, certificates),
        target / "HypercubicDimension16CartanCertificate.lean": aggregate_file(),
        target / "HypercubicDimension16CartanStabilizers.lean": stabilizer_aggregate_file(),
    }
    for block in range(BLOCK_COUNT):
        outputs[target / f"HypercubicDimension16CartanCertificateBlock{block}.lean"] = block_file(block)
    for coordinate in range(len(REPRESENTATIVES)):
        outputs[target / f"HypercubicDimension16CartanStabilizer{coordinate}.lean"] = stabilizer_file(coordinate)
    return outputs


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    outputs = expected_outputs()
    stale = []
    for path, content in outputs.items():
        if args.check:
            if not path.exists() or path.read_text() != content:
                stale.append(path.name)
        else:
            path.write_text(content)
    if stale:
        raise SystemExit("stale generated files: " + ", ".join(stale))
    print(
        f"verified {RAW_COUNT} monomials, 75 orbits "
        f"(17 admissible, 58 killed), {BLOCK_COUNT} blocks"
    )


if __name__ == "__main__":
    main()
