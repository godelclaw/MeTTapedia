#!/usr/bin/env python3
"""Emit the flat product-signature payload for the dimension-sixteen chart."""

from __future__ import annotations

import argparse
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TARGET = (
    ROOT
    / "Mettapedia/QuantumTheory/YangMills/HypercubicDimension16TraceOrbitProductSignatureData.lean"
)
COUNT = 11_654
CHUNK_SIZE = 1_024
LABELS = (
    "representativeCanonicalProductSignatureCode",
    "sortedCanonicalProductSignatureCode",
    "productSignatureRankCode",
    "representativeAtProductSignatureRankCode",
)


def original_numbers(source: str, label: str) -> list[int]:
    start_marker = f"@[reducible] private def {label}Chunk0"
    end_marker = f"@[reducible] def {label}?"
    try:
        start = source.index(start_marker)
        end = source.index(end_marker, start)
    except ValueError as error:
        raise RuntimeError(f"missing generated section for {label}") from error
    numbers = [int(token) for token in re.findall(r"^\s*(\d+),?\s*$", source[start:end], re.MULTILINE)]
    if len(numbers) != COUNT:
        raise RuntimeError(f"{label} has {len(numbers)} entries, expected {COUNT}")
    return numbers


def packed_numbers(source: str, label: str) -> list[int] | None:
    pattern = re.compile(
        rf"(?:@\[[^]]+\]\s*)?private def {label}Payload\d+ : ByteArray :=\n"
        r"  r#\"(.*?)\"#\.toUTF8",
        re.DOTALL,
    )
    payloads = pattern.findall(source)
    if not payloads:
        return None
    numbers = [int(token, 16) for payload in payloads for token in payload.splitlines()]
    if len(numbers) != COUNT:
        raise RuntimeError(f"packed {label} has {len(numbers)} entries, expected {COUNT}")
    return numbers


def extract_numbers(source: str, label: str) -> list[int]:
    return packed_numbers(source, label) or original_numbers(source, label)


def render_payload(label: str, numbers: list[int]) -> tuple[str, str, str]:
    chunks = [numbers[offset : offset + CHUNK_SIZE] for offset in range(0, len(numbers), CHUNK_SIZE)]
    definitions = []
    for index, chunk in enumerate(chunks):
        payload = "\n".join(format(number, "x") for number in chunk)
        definitions.append(
            f'''@[reducible] private def {label}Payload{index} : ByteArray :=
  r#"{payload}"#.toUTF8'''
        )
    branches = "\n".join(
        f"  | {index} => decodeHexadecimalNatArray {label}Payload{index}"
        for index in range(len(chunks))
    )
    decoder = f'''@[irreducible] def decoded{label[0].upper() + label[1:]}Chunk
    (chunk : Nat) : Array Nat :=
  match chunk with
{branches}
  | _ => #[]'''
    lookup = f'''@[reducible] def {label}? (index : Nat) : Option Nat :=
  let chunk := decoded{label[0].upper() + label[1:]}Chunk (index / {CHUNK_SIZE})
  chunk[index % {CHUNK_SIZE}]?'''
    return "\n\n".join(definitions), decoder, lookup


def render(numbers_by_label: dict[str, list[int]]) -> str:
    rendered = [render_payload(label, numbers_by_label[label]) for label in LABELS]
    payloads = "\n\n".join(item[0] for item in rendered)
    decoders = "\n\n".join(item[1] for item in rendered)
    lookups = "\n\n".join(item[2] for item in rendered)
    return f'''import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PackedFiniteDataCodec

/-! Generated flat canonical product-signature chart for the positive
eight-field orbits.  This is part of OUR finite-data realization. -/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceOrbitProductSignatureData

open HypercubicDimension16PackedFiniteDataCodec

@[reducible] def productSignatureRepresentativeCount : Nat := {COUNT}

/-! Twelve sealed byte slices carry each product-signature coordinate. -/
{payloads}

{decoders}

{lookups}

end HypercubicDimension16TraceOrbitProductSignatureData
end YangMills
end QuantumTheory
end Mettapedia
'''


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    source = TARGET.read_text()
    rendered = render({label: extract_numbers(source, label) for label in LABELS})
    if args.check:
        if source != rendered:
            raise SystemExit("product-signature source is not freshly packed")
        return
    TARGET.write_text(rendered)


if __name__ == "__main__":
    main()
