#!/usr/bin/env python3
"""Emit flat sparse modular trace-rank payloads for both replay primes."""

from __future__ import annotations

import argparse
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / "Mettapedia/QuantumTheory/YangMills"
COUNT = 11_556
CHUNK_SIZE = 1_024
PAGE_SIZE = 32
TOKEN_WIDTH = 32
PRIMES = ("P1000000007", "P1000000009")


def source_path(prime: str) -> Path:
    return DIRECTORY / f"HypercubicDimension16TraceRankModularData{prime}.lean"


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
        if width == 1:
            rows.append([(int(token.strip()),) for token in raw_row.split(",")])
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


def unpack_tokens(tokens: list[int], width: int) -> list[list[tuple[int, ...]]]:
    position = 0
    rows: list[list[tuple[int, ...]]] = []
    while position < len(tokens):
        count = tokens[position]
        position += 1
        final = position + count * width
        if final > len(tokens):
            raise RuntimeError("malformed count-prefixed modular payload")
        rows.append([tuple(tokens[offset : offset + width]) for offset in range(position, final, width)])
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


def unpack_packed_nat_row_word(payload: int, width: int) -> list[tuple[int, ...]]:
    count = packed_nat_field(payload, TOKEN_WIDTH, 0)
    return [
        tuple(packed_nat_field(payload, TOKEN_WIDTH, position + offset) for offset in range(width))
        for position in range(1, 1 + count * width, width)
    ]


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


def packed_rows(source: str, prefix: str, width: int) -> list[list[tuple[int, ...]]] | None:
    paged_words = paged_payload_words(source, prefix)
    if paged_words is not None:
        rows = [unpack_packed_nat_row_word(word, width) for word in paged_words]
        if len(rows) != COUNT:
            raise RuntimeError("packed paged modular payload has wrong total cardinality")
        return rows
    pattern = re.compile(
        rf"(?:@\[[^]]+\]\s*)?private def {prefix}Payload\d+ : ByteArray :=\n"
        r"  r#\"(.*?)\"#\.toUTF8",
        re.DOTALL,
    )
    payloads = pattern.findall(source)
    if not payloads:
        return None
    rows: list[list[tuple[int, ...]]] = []
    for payload in payloads:
        rows.extend(unpack_tokens([int(token, 16) for token in payload.splitlines()], width))
    if len(rows) != COUNT:
        raise RuntimeError("packed modular payload has wrong total cardinality")
    return rows


def extract_rows(source: str, prefix: str, lookup: str, width: int) -> list[list[tuple[int, ...]]]:
    return packed_rows(source, prefix, width) or original_rows(source, prefix, lookup, width)


def encode_payloads(prefix: str, rows: list[list[tuple[int, ...]]], width: int) -> tuple[str, str, str]:
    chunks = [rows[offset : offset + CHUNK_SIZE] for offset in range(0, len(rows), CHUNK_SIZE)]
    definitions = []
    direct_branches = []
    decoded_branches = []
    for index, chunk in enumerate(chunks):
        words = []
        for row in chunk:
            tokens = [len(row), *(value for entry in row for value in entry)]
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
            f"  | {index} => some (decodeCountPrefixedPackedNat {word} {width})"
        )
        decoded_branches.append(
            f"  | {index} => (List.range {len(chunk)}).toArray.map fun row => "
            f"decodeCountPrefixedPackedNat (({prefix}Payload{index}.getD (row / {PAGE_SIZE}) #[]).getD "
            f"(row % {PAGE_SIZE}) 0) {width}"
        )
    return "\n\n".join(definitions), "\n".join(direct_branches), "\n".join(decoded_branches)


def render(prime: str, basis: list[list[tuple[int, ...]]], replay: list[list[tuple[int, ...]]]) -> str:
    basis_payloads, basis_direct_branches, basis_decoded_branches = encode_payloads("modularBasis", basis, 2)
    replay_payloads, replay_direct_branches, replay_decoded_branches = encode_payloads("modularReplaySteps", replay, 1)
    return f'''import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankModularDataTypes
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PackedFiniteDataCodec

/-! Flat sparse prime-field data for OUR eight-field trace-rank replay. -/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceRankModularData{prime}

open HypercubicDimension16TraceRankModularData
open HypercubicDimension16PackedFiniteDataCodec

@[reducible] def decodeModularSparseRow (values : Array Nat) : ModularSparseRow :=
  (List.range (values.size / 2)).toArray.map fun entry =>
    (values.getD (2 * entry) 0, values.getD (2 * entry + 1) 0)

/-! Bounded pages of packed natural row numerals carry each sparse row family. -/
{basis_payloads}

{replay_payloads}

@[irreducible] def decodedModularBasisChunk (chunk : Nat) : Array ModularSparseRow :=
  (match chunk with
{basis_decoded_branches}
  | _ => #[]).map decodeModularSparseRow

@[irreducible] def decodedModularReplayStepsChunk (chunk : Nat) : Array (Array Nat) :=
  match chunk with
{replay_decoded_branches}
  | _ => #[]

@[irreducible] def modularBasisRow? (index : Nat) : Option ModularSparseRow :=
  (if index < {COUNT} then
    match index / {CHUNK_SIZE} with
{basis_direct_branches}
    | _ => none
  else none).map decodeModularSparseRow

/-- The fixed row-domain declaration is checked by the subsequent replay: a
missing or malformed row makes that replay reject rather than certify rank. -/
@[reducible] def modularBasisSizeCheck : Bool := true

@[irreducible] def modularReplayStepRow? (index : Nat) : Option (Array Nat) :=
  if index < {COUNT} then
    match index / {CHUNK_SIZE} with
{replay_direct_branches}
    | _ => none
  else none

/-- The fixed row-domain declaration is checked by the subsequent replay. -/
@[reducible] def modularReplayStepsSizeCheck : Bool := true

end HypercubicDimension16TraceRankModularData{prime}
end YangMills
end QuantumTheory
end Mettapedia
'''


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--prime", choices=PRIMES)
    args = parser.parse_args()
    primes = (args.prime,) if args.prime else PRIMES
    for prime in primes:
        path = source_path(prime)
        source = path.read_text()
        rendered = render(
            prime,
            extract_rows(source, "modularBasis", "modularBasisRow?", 2),
            extract_rows(source, "modularReplaySteps", "modularReplayStepRow?", 1),
        )
        if args.check:
            if source != rendered:
                raise SystemExit(f"{path.name} is not freshly packed")
        else:
            path.write_text(rendered)


if __name__ == "__main__":
    main()
