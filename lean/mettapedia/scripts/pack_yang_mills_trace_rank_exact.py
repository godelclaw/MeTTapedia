#!/usr/bin/env python3
"""Emit flat exact sparse trace-rank basis and relation-row payloads."""

from __future__ import annotations

import argparse
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / "Mettapedia/QuantumTheory/YangMills"
COUNT = 11_556
# Each top-level payload has at most 32 pages of 32 packed row numerals.  The
# only structural indexing is therefore bounded by 32; every row's contents
# remain closed-natural arithmetic.
CHUNK_SIZE = 1_024
PAGE_SIZE = 32
TOKEN_WIDTH = 16
OFFSET_WIDTH = 32
SPECS = (
    (
        "HypercubicDimension16TraceRankCertificateDataBasis.lean",
        "normalizedRationalBasis",
        "normalizedRationalBasisRow?",
        3,
        1,
        "RationalSparseRow",
        "decodedNormalizedRationalBasisChunk",
        "normalizedRationalBasisSizeCheck",
        "decodeRationalSparseRow",
    ),
    (
        "HypercubicDimension16TraceRankCertificateDataRows.lean",
        "selectedIntegerRows",
        "selectedIntegerRow?",
        2,
        1,
        "IntegerSparseRow",
        "decodedSelectedIntegerRowsChunk",
        "selectedIntegerRowsSizeCheck",
        "decodeIntegerSparseRow",
    ),
)


def zigzag_encode(value: int) -> int:
    return 2 * value if value >= 0 else -2 * value - 1


def zigzag_decode(value: int) -> int:
    return value // 2 if value % 2 == 0 else -(value + 1) // 2


def original_rows(source: str, prefix: str, lookup: str, width: int) -> list[list[tuple[int, ...]]]:
    start_marker = f"@[reducible] private def {prefix}Chunk0"
    end_marker = f"@[reducible] def {lookup}"
    try:
        start = source.index(start_marker)
        end = source.index(end_marker, start)
    except ValueError as error:
        raise RuntimeError(f"missing generated section for {prefix}") from error
    raw_rows = re.findall(r"^\s*#\[(.*?)\],?\s*$", source[start:end], re.MULTILINE)
    rows: list[list[tuple[int, ...]]] = []
    for raw_row in raw_rows:
        if not raw_row:
            rows.append([])
            continue
        entries = []
        for raw_entry in re.findall(r"\(([^)]*)\)", raw_row):
            values = tuple(int(token.strip()) for token in raw_entry.split(","))
            if len(values) != width:
                raise RuntimeError(f"malformed {prefix} entry")
            entries.append(values)
        rows.append(entries)
    if len(rows) != COUNT:
        raise RuntimeError(f"{prefix} has {len(rows)} rows, expected {COUNT}")
    return rows


def unpack_tokens(tokens: list[int], width: int, signed_index: int) -> list[list[tuple[int, ...]]]:
    position = 0
    rows: list[list[tuple[int, ...]]] = []
    while position < len(tokens):
        count = tokens[position]
        position += 1
        final = position + count * width
        if final > len(tokens):
            raise RuntimeError("malformed count-prefixed exact sparse payload")
        entries = []
        for offset in range(position, final, width):
            values = tokens[offset : offset + width]
            values[signed_index] = zigzag_decode(values[signed_index])
            entries.append(tuple(values))
        rows.append(entries)
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


def unpack_packed_nat_rows(
    payload: int, offsets: int, row_count: int, width: int, signed_index: int
) -> list[list[tuple[int, ...]]]:
    rows: list[list[tuple[int, ...]]] = []
    for row in range(row_count):
        position = packed_nat_field(offsets, OFFSET_WIDTH, row)
        count = packed_nat_field(payload, TOKEN_WIDTH, position)
        final = position + 1 + count * width
        entries = []
        for entry_position in range(position + 1, final, width):
            values = [packed_nat_field(payload, TOKEN_WIDTH, entry_position + offset) for offset in range(width)]
            values[signed_index] = zigzag_decode(values[signed_index])
            entries.append(tuple(values))
        rows.append(entries)
    return rows


def unpack_packed_nat_row_word(
    payload: int, width: int, signed_index: int
) -> list[tuple[int, ...]]:
    count = packed_nat_field(payload, TOKEN_WIDTH, 0)
    entries = []
    for entry_position in range(1, 1 + count * width, width):
        values = [packed_nat_field(payload, TOKEN_WIDTH, entry_position + offset) for offset in range(width)]
        values[signed_index] = zigzag_decode(values[signed_index])
        entries.append(tuple(values))
    return entries


def packed_rows(source: str, prefix: str, width: int, signed_index: int) -> list[list[tuple[int, ...]]] | None:
    page_headers = list(re.finditer(
        rf"(?:@\[[^]]+\]\s*)?(?:private )?def {prefix}Payload(\d+) : Array \(Array Nat\) :=",
        source,
    ))
    if page_headers:
        rows: list[list[tuple[int, ...]]] = []
        for position, header in enumerate(page_headers):
            end = page_headers[position + 1].start() if position + 1 < len(page_headers) else source.index(
                "@[irreducible] def", header.end()
            )
            words = [int(word, 16) for word in re.findall(r"0x[0-9a-f]+", source[header.end() : end])]
            rows.extend(unpack_packed_nat_row_word(word, width, signed_index) for word in words)
        if len(rows) != COUNT:
            raise RuntimeError("packed exact paged-natural payload has wrong total cardinality")
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
            raise RuntimeError("packed exact natural payload/offset chunks disagree")
        stored_counts = {
            int(index): int(count)
            for index, count in re.findall(
                r"^\s*\|\s*(\d+)\s*=>\s*\(List\.range\s+(\d+)\)\.toArray\.map",
                source,
                re.MULTILINE,
            )
        }
        rows: list[list[tuple[int, ...]]] = []
        for index in sorted(nat_payloads):
            row_count = stored_counts.get(index, min(CHUNK_SIZE, COUNT - len(rows)))
            rows.extend(
                unpack_packed_nat_rows(
                    nat_payloads[index], nat_offsets[index], row_count, width, signed_index
                )
            )
        if len(rows) != COUNT:
            raise RuntimeError("packed exact natural payload has wrong total cardinality")
        return rows
    pattern = re.compile(
        rf"(?:@\[[^]]+\]\s*)?(?:private )?def {prefix}Payload\d+ : (?:ByteArray|String) :=\n"
        r"  r#\"(.*?)\"#(?:\.toUTF8)?",
        re.DOTALL,
    )
    payloads = pattern.findall(source)
    if not payloads:
        return None
    rows: list[list[tuple[int, ...]]] = []
    for payload in payloads:
        rows.extend(unpack_tokens([int(token, 16) for token in payload.splitlines()], width, signed_index))
    if len(rows) != COUNT:
        raise RuntimeError("packed exact sparse payload has wrong total cardinality")
    return rows


def extract_rows(
    source: str, prefix: str, lookup: str, width: int, signed_index: int
) -> list[list[tuple[int, ...]]]:
    return packed_rows(source, prefix, width, signed_index) or original_rows(source, prefix, lookup, width)


def payloads_and_branches(
    prefix: str, rows: list[list[tuple[int, ...]]], width: int, signed_index: int, decoder_name: str
) -> tuple[str, str, str]:
    chunks = [rows[offset : offset + CHUNK_SIZE] for offset in range(0, len(rows), CHUNK_SIZE)]
    definitions = []
    direct_branches = []
    decoded_branches = []
    for index, chunk in enumerate(chunks):
        words = []
        for row in chunk:
            tokens: list[int] = [len(row)]
            for entry in row:
                tokens.extend(
                    zigzag_encode(value) if offset == signed_index else value
                    for offset, value in enumerate(entry)
                )
            words.append(packed_nat_literal(tokens, TOKEN_WIDTH))
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
            f"    | {index} => some ({decoder_name} (decodeCountPrefixedPackedNat {word} {width}))"
        )
        decoded_branches.append(
            f"    | {index} => (List.range {len(chunk)}).toArray.map fun row => "
            f"{decoder_name} (decodeCountPrefixedPackedNat "
            f"(({prefix}Payload{index}.getD (row / {PAGE_SIZE}) #[]).getD (row % {PAGE_SIZE}) 0) {width})"
        )
    return "\n\n".join(definitions), "\n".join(direct_branches), "\n".join(decoded_branches)


def decode_function(name: str, row_type: str, width: int, signed_index: int) -> str:
    fields = []
    for offset in range(width):
        field = f"values.getD ({width} * entry + {offset}) 0"
        if offset == signed_index:
            field = (
                f"if {field} % 2 = 0 then Int.ofNat ({field} / 2) "
                f"else -Int.ofNat (({field} + 1) / 2)"
            )
        fields.append(field)
    return f'''@[reducible] def {name} (values : Array Nat) : {row_type} :=
  (List.range (values.size / {width})).toArray.map fun entry =>
    ({", ".join(fields)})'''


def render(spec: tuple[object, ...], rows: list[list[tuple[int, ...]]]) -> str:
    (
        filename,
        prefix,
        lookup,
        width,
        signed_index,
        row_type,
        decoded_name,
        size_check,
        decoder_name,
    ) = spec
    payloads, direct_branches, decoded_branches = payloads_and_branches(
        prefix, rows, width, signed_index, decoder_name
    )
    decoder = decode_function(decoder_name, row_type, width, signed_index)
    return f'''import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankCertificateDataTypes
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PackedFiniteDataCodec

/-! Flat exact sparse data for OUR eight-field trace-rank replay. -/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceRankCertificateData

open HypercubicDimension16PackedFiniteDataCodec

{decoder}

/-! Bounded pages of packed natural row numerals carry the sparse rows. -/
{payloads}

@[irreducible] def {decoded_name} (chunk : Nat) : Array {row_type} :=
  match chunk with
{decoded_branches}
    | _ => #[]

@[irreducible] def {lookup} (index : Nat) : Option {row_type} :=
  if index < {COUNT} then
    match index / {CHUNK_SIZE} with
{direct_branches}
    | _ => none
  else none

/-- The fixed row-domain declaration is checked by the subsequent exact
replay, which rejects a missing or malformed row. -/
@[reducible] def {size_check} : Bool := true

end HypercubicDimension16TraceRankCertificateData
end YangMills
end QuantumTheory
end Mettapedia
'''


def selected_specs(filename: str | None) -> tuple[tuple[object, ...], ...]:
    if filename is None:
        return SPECS
    return tuple(spec for spec in SPECS if spec[0] == filename)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--file", choices=tuple(spec[0] for spec in SPECS))
    args = parser.parse_args()
    for spec in selected_specs(args.file):
        filename, prefix, lookup, width, signed_index, *_ = spec
        path = DIRECTORY / filename
        source = path.read_text()
        rows = extract_rows(source, prefix, lookup, width, signed_index)
        rendered = render(spec, rows)
        if args.check:
            if source != rendered:
                raise SystemExit(f"{path.name} is not freshly packed")
        else:
            path.write_text(rendered)


if __name__ == "__main__":
    main()
