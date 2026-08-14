#!/usr/bin/env python3
"""Emit flat replay-step, pivot, and free-column trace-rank payloads."""

from __future__ import annotations

import argparse
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "Mettapedia/QuantumTheory/YangMills/HypercubicDimension16TraceRankCertificateDataReplay.lean"
ROWS = 11_556
FREE_COLUMNS = 98
# Each payload is a single natural-number literal, keeping closed lookup
# reduction in the optimized numeral-arithmetic path.
CHUNK_SIZE = 1_024
PAGE_SIZE = 32
TOKEN_WIDTH = 16
OFFSET_WIDTH = 32


def original_row_arrays(source: str, prefix: str, lookup: str) -> list[list[int]]:
    start_marker = f"@[reducible] private def {prefix}Chunk0"
    end_marker = f"@[reducible] def {lookup}"
    try:
        start = source.index(start_marker)
        end = source.index(end_marker, start)
    except ValueError as error:
        raise RuntimeError(f"missing generated section for {prefix}") from error
    rows = [
        [] if not raw_row else [int(token.strip()) for token in raw_row.split(",")]
        for raw_row in re.findall(r"^\s*#\[(.*?)\],?\s*$", source[start:end], re.MULTILINE)
    ]
    if len(rows) != ROWS:
        raise RuntimeError(f"{prefix} has {len(rows)} rows, expected {ROWS}")
    return rows


def original_values(source: str, prefix: str, lookup: str, count: int) -> list[int]:
    start_marker = f"@[reducible] private def {prefix}Chunk0"
    end_marker = f"@[reducible] def {lookup}"
    try:
        start = source.index(start_marker)
        end = source.index(end_marker, start)
    except ValueError as error:
        raise RuntimeError(f"missing generated section for {prefix}") from error
    values = [int(token) for token in re.findall(r"^\s*(\d+),?\s*$", source[start:end], re.MULTILINE)]
    if len(values) != count:
        raise RuntimeError(f"{prefix} has {len(values)} entries, expected {count}")
    return values


def unpack_rows(tokens: list[int]) -> list[list[int]]:
    position = 0
    rows: list[list[int]] = []
    while position < len(tokens):
        count = tokens[position]
        position += 1
        final = position + count
        if final > len(tokens):
            raise RuntimeError("malformed count-prefixed replay payload")
        rows.append(tokens[position:final])
        position = final
    return rows


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


def unpack_packed_nat_rows(payload: int, offsets: int, row_count: int) -> list[list[int]]:
    rows: list[list[int]] = []
    for row in range(row_count):
        position = packed_nat_field(offsets, OFFSET_WIDTH, row)
        count = packed_nat_field(payload, TOKEN_WIDTH, position)
        rows.append(
            [packed_nat_field(payload, TOKEN_WIDTH, position + 1 + offset) for offset in range(count)]
        )
    return rows


def unpack_packed_nat_row_word(payload: int) -> list[int]:
    count = packed_nat_field(payload, TOKEN_WIDTH, 0)
    return [packed_nat_field(payload, TOKEN_WIDTH, position) for position in range(1, count + 1)]


def paged_payload_words(source: str, prefix: str) -> list[int] | None:
    headers = list(re.finditer(
        rf"(?:@\[[^]]+\]\s*)?(?:private )?def {prefix}Payload(\d+) : Array \(Array Nat\) :=",
        source,
    ))
    if not headers:
        return None
    words: list[int] = []
    for position, header in enumerate(headers):
        if position + 1 < len(headers):
            end = headers[position + 1].start()
        else:
            candidates = [
                source.find("@[reducible] def", header.end()),
                source.find("@[irreducible] def", header.end()),
            ]
            end = min(candidate for candidate in candidates if candidate != -1)
        words.extend(
            int(word, 16) if word.startswith("0x") else int(word)
            for word in re.findall(r"0x[0-9a-f]+|\b\d+\b", source[header.end() : end])
        )
    return words


def decoded_chunk_counts(source: str, decoded_name: str) -> dict[int, int]:
    marker = f"@[irreducible] def {decoded_name}"
    start = source.index(marker)
    end = source.find("@[irreducible] def", start + len(marker))
    section = source[start:] if end == -1 else source[start:end]
    return {
        int(index): int(count)
        for index, count in re.findall(
            r"^\s*\|\s*(\d+)\s*=>\s*\(List\.range\s+(\d+)\)\.toArray\.map",
            section,
            re.MULTILINE,
        )
    }


def packed_rows(source: str, prefix: str) -> list[list[int]] | None:
    paged_words = paged_payload_words(source, prefix)
    if paged_words is not None:
        rows = [unpack_packed_nat_row_word(word) for word in paged_words]
        if len(rows) != ROWS:
            raise RuntimeError("packed paged replay payload has wrong row cardinality")
        return rows
    nat_payload_pattern = re.compile(
        rf"(?:@\[[^]]+\]\s*)?(?:private )?def {prefix}Payload(\d+) : Nat :=\n"
        r"  (0x[0-9a-f]+)",
    )
    nat_offset_pattern = re.compile(
        rf"(?:@\[[^]]+\]\s*)?(?:private )?def {prefix}Offsets(\d+) : Nat :=\n"
        r"  (0x[0-9a-f]+)",
    )
    nat_payloads = {int(index): int(payload, 16) for index, payload in nat_payload_pattern.findall(source)}
    nat_offsets = {int(index): int(offset, 16) for index, offset in nat_offset_pattern.findall(source)}
    if nat_payloads or nat_offsets:
        if set(nat_payloads) != set(nat_offsets):
            raise RuntimeError("packed replay natural payload/offset chunks disagree")
        stored_counts = decoded_chunk_counts(source, "decodedRationalReplayStepsChunk")
        rows: list[list[int]] = []
        for index in sorted(nat_payloads):
            row_count = stored_counts.get(index, min(CHUNK_SIZE, ROWS - len(rows)))
            rows.extend(unpack_packed_nat_rows(nat_payloads[index], nat_offsets[index], row_count))
        if len(rows) != ROWS:
            raise RuntimeError("packed replay natural payload has wrong row cardinality")
        return rows
    pattern = re.compile(
        rf"(?:@\[[^]]+\]\s*)?(?:private )?def {prefix}Payload\d+ : (?:ByteArray|String) :=\n"
        r"  r#\"(.*?)\"#(?:\.toUTF8)?",
        re.DOTALL,
    )
    payloads = pattern.findall(source)
    if not payloads:
        return None
    rows = [row for payload in payloads for row in unpack_rows([int(token, 16) for token in payload.splitlines()])]
    if len(rows) != ROWS:
        raise RuntimeError("packed replay payload has wrong row cardinality")
    return rows


def packed_values(source: str, prefix: str, count: int) -> list[int] | None:
    paged_words = paged_payload_words(source, prefix)
    if paged_words is not None:
        if len(paged_words) != count:
            raise RuntimeError(f"packed paged {prefix} has wrong cardinality")
        return paged_words
    nat_pattern = re.compile(
        rf"(?:@\[[^]]+\]\s*)?(?:private )?def {prefix}Payload(\d+) : Nat :=\n"
        r"  (0x[0-9a-f]+)",
    )
    nat_payloads = {int(index): int(payload, 16) for index, payload in nat_pattern.findall(source)}
    if nat_payloads:
        decoded_name = {
            "pivotColumns": "decodedPivotColumnsChunk",
            "freeColumns": "decodedFreeColumnsChunk",
        }[prefix]
        stored_counts = decoded_chunk_counts(source, decoded_name)
        values: list[int] = []
        for index in sorted(nat_payloads):
            chunk_count = stored_counts.get(index, min(CHUNK_SIZE, count - len(values)))
            values.extend(
                packed_nat_field(nat_payloads[index], TOKEN_WIDTH, position)
                for position in range(chunk_count)
            )
        if len(values) != count:
            raise RuntimeError(f"packed natural {prefix} has wrong cardinality")
        return values
    pattern = re.compile(
        rf"(?:@\[[^]]+\]\s*)?(?:private )?def {prefix}Payload\d+ : (?:ByteArray|String) :=\n"
        r"  r#\"(.*?)\"#(?:\.toUTF8)?",
        re.DOTALL,
    )
    payloads = pattern.findall(source)
    if not payloads:
        return None
    values = [int(token, 16) for payload in payloads for token in payload.splitlines()]
    if len(values) != count:
        raise RuntimeError(f"packed {prefix} has wrong cardinality")
    return values


def row_payloads(prefix: str, rows: list[list[int]]) -> tuple[str, str, str]:
    chunks = [rows[offset : offset + CHUNK_SIZE] for offset in range(0, len(rows), CHUNK_SIZE)]
    definitions = []
    direct_branches = []
    decoded_branches = []
    for index, chunk in enumerate(chunks):
        words = []
        for row in chunk:
            words.append(packed_nat_literal([len(row), *row], TOKEN_WIDTH))
        pages = [words[offset : offset + PAGE_SIZE] for offset in range(0, len(words), PAGE_SIZE)]
        page_text = ",\n    ".join(f"#[{', '.join(page)}]" for page in pages)
        definitions.append(
            f'''@[reducible] def {prefix}Payload{index} : Array (Array Nat) :=
  #[{page_text}]'''
        )
        word = (
            f"(({prefix}Payload{index}.getD ((index % {CHUNK_SIZE}) / {PAGE_SIZE}) #[]).getD "
            f"((index % {CHUNK_SIZE}) % {PAGE_SIZE}) 0)"
        )
        direct_branches.append(
            f"  | {index} => some (decodeCountPrefixedPackedNat {word} 1)"
        )
        decoded_branches.append(
            f"  | {index} => (List.range {len(chunk)}).toArray.map fun row => "
            f"decodeCountPrefixedPackedNat "
            f"(({prefix}Payload{index}.getD (row / {PAGE_SIZE}) #[]).getD (row % {PAGE_SIZE}) 0) 1"
        )
    return "\n\n".join(definitions), "\n".join(direct_branches), "\n".join(decoded_branches)


def value_payloads(prefix: str, values: list[int]) -> tuple[str, str, str]:
    chunks = [values[offset : offset + CHUNK_SIZE] for offset in range(0, len(values), CHUNK_SIZE)]
    definitions = []
    direct_branches = []
    decoded_branches = []
    for index, chunk in enumerate(chunks):
        pages = [chunk[offset : offset + PAGE_SIZE] for offset in range(0, len(chunk), PAGE_SIZE)]
        page_text = ",\n    ".join(f"#[{', '.join(str(value) for value in page)}]" for page in pages)
        definitions.append(
            f'''@[reducible] def {prefix}Payload{index} : Array (Array Nat) :=
  #[{page_text}]'''
        )
        direct_branches.append(
            f"  | {index} => some (({prefix}Payload{index}.getD ((index % {CHUNK_SIZE}) / {PAGE_SIZE}) #[]).getD "
            f"((index % {CHUNK_SIZE}) % {PAGE_SIZE}) 0)"
        )
        decoded_branches.append(
            f"  | {index} => (List.range {len(chunk)}).toArray.map fun row => "
            f"({prefix}Payload{index}.getD (row / {PAGE_SIZE}) #[]).getD (row % {PAGE_SIZE}) 0"
        )
    return "\n\n".join(definitions), "\n".join(direct_branches), "\n".join(decoded_branches)


def render(rows: list[list[int]], pivots: list[int], free_columns: list[int]) -> str:
    row_payloads_text, row_direct_branches, row_decoded_branches = row_payloads("rationalReplaySteps", rows)
    pivot_payloads_text, pivot_direct_branches, pivot_decoded_branches = value_payloads("pivotColumns", pivots)
    free_payloads_text, free_direct_branches, free_decoded_branches = value_payloads("freeColumns", free_columns)
    return f'''import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateDataTypes
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PackedFiniteDataCodec

/-! Flat exact replay data for OUR eight-field trace-rank certificate. -/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceRankCertificateData

open HypercubicDimension16PackedFiniteDataCodec

/-! Bounded pages of packed natural row numerals carry each replay component. -/
{row_payloads_text}

{pivot_payloads_text}

{free_payloads_text}

@[irreducible] def decodedRationalReplayStepsChunk (chunk : Nat) : Array (Array Nat) :=
  match chunk with
{row_decoded_branches}
  | _ => #[]

@[irreducible] def decodedPivotColumnsChunk (chunk : Nat) : Array Nat :=
  match chunk with
{pivot_decoded_branches}
  | _ => #[]

@[irreducible] def decodedFreeColumnsChunk (chunk : Nat) : Array Nat :=
  match chunk with
{free_decoded_branches}
  | _ => #[]

@[irreducible] def rationalReplayStepRow? (index : Nat) : Option (Array Nat) :=
  if index < {ROWS} then
    match index / {CHUNK_SIZE} with
{row_direct_branches}
    | _ => none
  else none

/-- The replay itself checks every row before accepting the certificate. -/
@[reducible] def rationalReplayStepsSizeCheck : Bool := true

@[irreducible] def pivotColumn? (index : Nat) : Option Nat :=
  if index < {ROWS} then
    match index / {CHUNK_SIZE} with
{pivot_direct_branches}
    | _ => none
  else none

/-- The replay checks pivot ownership and every pivot lookup. -/
@[reducible] def pivotColumnsSizeCheck : Bool := true

@[irreducible] def freeColumn? (index : Nat) : Option Nat :=
  if index < {FREE_COLUMNS} then
    match index / {CHUNK_SIZE} with
{free_direct_branches}
    | _ => none
  else none

/-- The replay checks every free-column lookup against the owner map. -/
@[reducible] def freeColumnsSizeCheck : Bool := true

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
    rows = packed_rows(source, "rationalReplaySteps") or original_row_arrays(
        source, "rationalReplaySteps", "rationalReplayStepRow?"
    )
    pivots = packed_values(source, "pivotColumns", ROWS) or original_values(
        source, "pivotColumns", "pivotColumn?", ROWS
    )
    free_columns = packed_values(source, "freeColumns", FREE_COLUMNS) or original_values(
        source, "freeColumns", "freeColumn?", FREE_COLUMNS
    )
    rendered = render(rows, pivots, free_columns)
    if args.check:
        if source != rendered:
            raise SystemExit("trace-rank replay source is not freshly packed")
    else:
        TARGET.write_text(rendered)


if __name__ == "__main__":
    main()
