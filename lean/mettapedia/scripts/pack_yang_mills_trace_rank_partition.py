#!/usr/bin/env python3
"""Emit the flat column-owner payload for the exact trace-rank replay."""

from __future__ import annotations

import argparse
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "Mettapedia/QuantumTheory/YangMills/HypercubicDimension16TraceRankCertificateDataPartition.lean"
COUNT = 11_654
# Two bounded Array indices select a scalar owner; no lookup traverses a whole
# certificate payload.
CHUNK_SIZE = 1_024
PAGE_SIZE = 32
TOKEN_WIDTH = 16


def original_owners(source: str) -> list[int | None]:
    start_marker = "@[reducible] private def columnOwner?Chunk0"
    end_marker = "@[reducible] def columnOwner?"
    try:
        start = source.index(start_marker)
        end = source.index(end_marker, start)
    except ValueError as error:
        raise RuntimeError("missing generated column-owner table") from error
    section = source[start:end]
    chunk_pattern = re.compile(
        r"@\[reducible\] private def columnOwner\?Chunk\d+ : Nat → Option Nat := fun\n(.*?)\n\n",
        re.DOTALL,
    )
    owners: list[int | None] = []
    for chunk in chunk_pattern.findall(section):
        entries = re.findall(r"^\s*\|\s*(\d+)\s*=>\s*(some\s+(\d+)|none)\s*$", chunk, re.MULTILINE)
        if not entries:
            raise RuntimeError("empty generated column-owner chunk")
        length = max(int(index) for index, _, _ in entries) + 1
        values: list[int | None] = [None] * length
        for index, result, value in entries:
            values[int(index)] = int(value) if result.startswith("some") else None
        owners.extend(values)
    if len(owners) != COUNT:
        raise RuntimeError(f"column-owner table has {len(owners)} entries, expected {COUNT}")
    return owners


def packed_nat_literal(values: list[int], width: int) -> str:
    limit = 1 << width
    packed = 0
    for value in reversed(values):
        if not 0 <= value < limit:
            raise RuntimeError(f"packed {width}-bit field out of range: {value}")
        packed = (packed << width) | value
    return f"0x{packed:x}"


def packed_nat_field(payload: int, width: int, index: int) -> int:
    return (payload >> (width * index)) & ((1 << width) - 1)


def packed_owners(source: str) -> list[int | None] | None:
    page_headers = list(re.finditer(
        r"(?:@\[[^]]+\]\s*)?(?:private )?def columnOwnerPayload(\d+) : Array \(Array Nat\) :=",
        source,
    ))
    if page_headers:
        encoded: list[int] = []
        for position, header in enumerate(page_headers):
            end = page_headers[position + 1].start() if position + 1 < len(page_headers) else source.index(
                "@[irreducible] def", header.end()
            )
            encoded.extend(
                int(word, 16) if word.startswith("0x") else int(word)
                for word in re.findall(r"0x[0-9a-f]+|\b\d+\b", source[header.end() : end])
            )
        if len(encoded) != COUNT:
            raise RuntimeError("packed paged column-owner payload has wrong cardinality")
        return [None if owner == 0 else owner - 1 for owner in encoded]
    nat_pattern = re.compile(
        r"(?:@\[[^]]+\]\s*)?(?:private )?def columnOwnerPayload(\d+) : Nat :=\n"
        r"  (0x[0-9a-f]+)",
    )
    nat_payloads = {int(index): int(payload, 16) for index, payload in nat_pattern.findall(source)}
    if nat_payloads:
        marker = "@[irreducible] def decodedColumnOwnerChunk"
        start = source.index(marker)
        end = source.find("@[irreducible] def", start + len(marker))
        section = source[start:] if end == -1 else source[start:end]
        stored_counts = {
            int(index): int(count)
            for index, count in re.findall(
                r"^\s*\|\s*(\d+)\s*=>\s*\(List\.range\s+(\d+)\)\.toArray\.map",
                section,
                re.MULTILINE,
            )
        }
        encoded: list[int] = []
        for index in sorted(nat_payloads):
            chunk_count = stored_counts.get(index, min(CHUNK_SIZE, COUNT - len(encoded)))
            encoded.extend(
                packed_nat_field(nat_payloads[index], TOKEN_WIDTH, position)
                for position in range(chunk_count)
            )
        if len(encoded) != COUNT:
            raise RuntimeError("packed natural column-owner payload has wrong cardinality")
        return [None if owner == 0 else owner - 1 for owner in encoded]
    pattern = re.compile(
        r"(?:@\[[^]]+\]\s*)?(?:private )?def columnOwnerPayload\d+ : (?:ByteArray|String) :=\n"
        r"  r#\"(.*?)\"#(?:\.toUTF8)?",
        re.DOTALL,
    )
    payloads = pattern.findall(source)
    if not payloads:
        return None
    encoded = [int(token, 16) for payload in payloads for token in payload.splitlines()]
    if len(encoded) != COUNT:
        raise RuntimeError("packed column-owner payload has wrong cardinality")
    return [None if owner == 0 else owner - 1 for owner in encoded]


def render(owners: list[int | None]) -> str:
    chunks = [owners[offset : offset + CHUNK_SIZE] for offset in range(0, len(owners), CHUNK_SIZE)]
    payloads = []
    direct_branches = []
    for index, chunk in enumerate(chunks):
        pages = [chunk[offset : offset + PAGE_SIZE] for offset in range(0, len(chunk), PAGE_SIZE)]
        page_text = ",\n    ".join(
            f"#[{', '.join(str(0 if owner is None else owner + 1) for owner in page)}]"
            for page in pages
        )
        payloads.append(
            f'''@[reducible] def columnOwnerPayload{index} : Array (Array Nat) :=
  #[{page_text}]'''
        )
        direct_branches.append(
            f"  | {index} => some ((columnOwnerPayload{index}.getD ((index % {CHUNK_SIZE}) / {PAGE_SIZE}) #[]).getD "
            f"((index % {CHUNK_SIZE}) % {PAGE_SIZE}) 0)"
        )
    branches = "\n".join(
        f"  | {index} => (List.range {len(chunk)}).toArray.map fun row => "
        f"(columnOwnerPayload{index}.getD (row / {PAGE_SIZE}) #[]).getD (row % {PAGE_SIZE}) 0"
        for index, chunk in enumerate(chunks)
    )
    return f'''import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateDataTypes
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PackedFiniteDataCodec

/-! Flat column-owner data for OUR exact eight-field trace-rank replay. -/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceRankCertificateData

open HypercubicDimension16PackedFiniteDataCodec

/-! Bounded pages of natural numerals carry the column-owner map. -/
{"\n\n".join(payloads)}

@[irreducible] def decodedColumnOwnerChunk (chunk : Nat) : Array Nat :=
  match chunk with
{branches}
  | _ => #[]

@[irreducible] def columnOwner? (index : Nat) : Option Nat :=
  let encoded := if index < {COUNT} then
    match index / {CHUNK_SIZE} with
{chr(10).join(direct_branches)}
    | _ => none
  else none
  match encoded with
  | some 0 => none
  | some owner => some (owner - 1)
  | none => none

end HypercubicDimension16TraceRankCertificateData
end YangMills
end QuantumTheory
end Mettapedia
'''


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    source = TARGET.read_text()
    owners = packed_owners(source) or original_owners(source)
    rendered = render(owners)
    if args.check:
        if source != rendered:
            raise SystemExit("column-owner source is not freshly packed")
    else:
        TARGET.write_text(rendered)


if __name__ == "__main__":
    main()
