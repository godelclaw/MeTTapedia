#!/usr/bin/env python3
"""Emit the flat kernel-decoded physical-trace witness payload.

This generator is deliberately narrow: it converts the previously emitted
packed hexadecimal witness words into one UTF-8 byte literal.  Lean performs
the verified decoding in `HypercubicDimension16PhysicalTraceWitnessPackedCodec`.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TARGET = (
    ROOT
    / "Mettapedia/QuantumTheory/YangMills/HypercubicDimension16PhysicalTraceWitnessData.lean"
)
START = "@[irreducible] private def physicalTraceWitnessPackedChunk0"
END = "@[reducible] def encodedPhysicalTraceWitness?"
FLAT_START = "@[irreducible] private def physicalTraceWitnessPayload : ByteArray :=\n  r#\""
FLAT_END = "\"#.toUTF8"
CHUNK_PAYLOAD_PATTERN = re.compile(
    r"(?:@\[[^]]+\]\s*)?private def physicalTraceWitnessPayload\d+ : ByteArray :=\n"
    r"  r#\"(.*?)\"#\.toUTF8",
    re.DOTALL,
)
CHUNK_SIZE = 1024


def extract_words(source: str) -> list[str]:
    chunk_payloads = CHUNK_PAYLOAD_PATTERN.findall(source)
    if chunk_payloads:
        words = [
            word
            for payload in chunk_payloads
            for word in payload.replace("\\n", "\n").splitlines()
        ]
        if not words or any(re.fullmatch(r"[0-9a-f]+", word) is None for word in words):
            raise RuntimeError("malformed chunked physical witness payload")
        return words
    if FLAT_START in source:
        start = source.index(FLAT_START) + len(FLAT_START)
        end = source.index(FLAT_END, start)
        words = source[start:end].splitlines()
        if not words or any(re.fullmatch(r"[0-9a-f]+", word) is None for word in words):
            raise RuntimeError("malformed flat physical witness payload")
        return words
    try:
        start = source.index(START)
        end = source.index(END, start)
    except ValueError as error:
        raise RuntimeError("expected pre-packed physical witness source") from error
    words = re.findall(r"0x([0-9a-f]+)", source[start:end])
    if not words:
        raise RuntimeError("no packed witness words found")
    return words


def render(words: list[str]) -> str:
    chunks = [words[offset : offset + CHUNK_SIZE] for offset in range(0, len(words), CHUNK_SIZE)]
    payload_definitions = []
    for index, chunk in enumerate(chunks):
        payload = "\n".join(chunk)
        payload_definitions.append(
            f'''@[reducible] private def physicalTraceWitnessPayload{index} : ByteArray :=
  r#"{payload}"#.toUTF8'''
        )
    payloads = "\n\n".join(payload_definitions)
    decode_branches = "\n".join(
        f"  | {index} => decodeHexadecimalNatArray physicalTraceWitnessPayload{index}"
        for index in range(len(chunks))
    )
    return f'''import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessPackedCodec
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PackedFiniteDataCodec

/-!
Generated flat orbit witnesses for selected standard eight-field trace rows.
This payload is part of OUR finite-data realization.  Its byte-level layout is
specified and kernel-decoded by `HypercubicDimension16PhysicalTraceWitnessPackedCodec`.
-/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PhysicalTraceWitnessData

open HypercubicDimension16PhysicalTraceWitnessTypes
open HypercubicDimension16PhysicalTraceWitnessPackedCodec
open HypercubicDimension16PackedFiniteDataCodec

/-! The generated words occupy twelve flat byte slices.  Each decoded slice is
sealed so importers cannot expand bulk data accidentally; a bounded replay
explicitly unfolds only the slice it checks. -/
{payloads}

/-- OUR decoder for one bounded physical-witness slice. -/
@[irreducible] def decodedPhysicalTraceWitnessChunk
    (chunk : Nat) : Array Nat :=
  match chunk with
{decode_branches}
  | _ => #[]

@[reducible] def encodedPhysicalTraceWitness?
    (index : Nat) : Option EncodedPhysicalTraceWitness :=
  let chunk := decodedPhysicalTraceWitnessChunk (index / {CHUNK_SIZE})
  (chunk[index % {CHUNK_SIZE}]?).map decodePhysicalTraceWitness

end HypercubicDimension16PhysicalTraceWitnessData
end YangMills
end QuantumTheory
end Mettapedia
'''


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    source = TARGET.read_text()
    rendered = render(extract_words(source))
    if args.check:
        if source != rendered:
            raise SystemExit("physical witness source is not freshly packed")
        return
    TARGET.write_text(rendered)


if __name__ == "__main__":
    main()
