#!/usr/bin/env python3
"""Emit the flat positive-orbit chart payload for the dimension-sixteen sector."""

from __future__ import annotations

import argparse
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "Mettapedia/QuantumTheory/YangMills/HypercubicDimension16TraceOrbitChartData.lean"
COUNT = 11_654
WIDTH = 24
CHUNK_SIZE = 1_024


def original_rows(source: str) -> list[list[int]]:
    start_marker = "@[reducible] private def positiveRepresentativeChunk0"
    end_marker = "@[reducible] def positiveRepresentativeCode?"
    try:
        start = source.index(start_marker)
        end = source.index(end_marker, start)
    except ValueError as error:
        raise RuntimeError("missing generated positive-representative rows") from error
    rows = [
        [int(token) for token in row.split(",")]
        for row in re.findall(r"^\s*#\[([0-9, ]+)\],?\s*$", source[start:end], re.MULTILINE)
    ]
    if len(rows) != COUNT or any(len(row) != WIDTH or any(value > 7 for value in row) for row in rows):
        raise RuntimeError("malformed generated positive-representative rows")
    return rows


def packed_rows(source: str) -> list[list[int]] | None:
    pattern = re.compile(
        r"(?:@\[[^]]+\]\s*)?private def positiveRepresentativePayload\d+ : ByteArray :=\n"
        r"  r#\"(.*?)\"#\.toUTF8",
        re.DOTALL,
    )
    payloads = pattern.findall(source)
    if not payloads:
        return None
    words = [int(token, 16) for payload in payloads for token in payload.splitlines()]
    rows = [[(word >> (3 * offset)) & 7 for offset in range(WIDTH)] for word in words]
    if len(rows) != COUNT:
        raise RuntimeError("packed positive-representative payload has wrong cardinality")
    return rows


def extract_rows(source: str) -> list[list[int]]:
    return packed_rows(source) or original_rows(source)


def pack_word(row: list[int]) -> int:
    return sum(value << (3 * offset) for offset, value in enumerate(row))


def render(rows: list[list[int]]) -> str:
    words = [pack_word(row) for row in rows]
    chunks = [words[offset : offset + CHUNK_SIZE] for offset in range(0, len(words), CHUNK_SIZE)]
    payloads = []
    for index, chunk in enumerate(chunks):
        payload = "\n".join(format(word, "x") for word in chunk)
        payloads.append(
            f'''@[reducible] private def positiveRepresentativePayload{index} : ByteArray :=
  r#"{payload}"#.toUTF8'''
        )
    branches = "\n".join(
        f"  | {index} => decodeHexadecimalNatArray positiveRepresentativePayload{index}"
        for index in range(len(chunks))
    )
    fields = ",\n    ".join(
        f"(word / 8 ^ {offset}) % 8" for offset in range(WIDTH)
    )
    return f'''import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PackedFiniteDataCodec

/-! Generated flat labeled representatives for the positive signed eight-field
orbits.  This is part of OUR finite-data realization. -/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceOrbitChartData

open HypercubicDimension16PackedFiniteDataCodec

@[reducible] def positiveRepresentativeCount : Nat := {COUNT}
@[reducible] def encodedRepresentativeWidth : Nat := {WIDTH}

/-! Twelve sealed byte slices carry the packed 24-letter representative codes. -/
{"\n\n".join(payloads)}

@[irreducible] def decodedPositiveRepresentativeWordChunk
    (chunk : Nat) : Array Nat :=
  match chunk with
{branches}
  | _ => #[]

@[reducible] def decodePositiveRepresentativeWord (word : Nat) : Array Nat :=
  #[{fields}]

@[reducible] def positiveRepresentativeCode? (index : Nat) : Option (Array Nat) :=
  let chunk := decodedPositiveRepresentativeWordChunk (index / {CHUNK_SIZE})
  (chunk[index % {CHUNK_SIZE}]?).map decodePositiveRepresentativeWord

@[reducible] def positiveRepresentativeShapeCheck : Bool :=
  positiveRepresentativeCount = {COUNT} && encodedRepresentativeWidth = {WIDTH}

end HypercubicDimension16TraceOrbitChartData
end YangMills
end QuantumTheory
end Mettapedia
'''


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    source = TARGET.read_text()
    rendered = render(extract_rows(source))
    if args.check:
        if source != rendered:
            raise SystemExit("trace-orbit chart source is not freshly packed")
        return
    TARGET.write_text(rendered)


if __name__ == "__main__":
    main()
