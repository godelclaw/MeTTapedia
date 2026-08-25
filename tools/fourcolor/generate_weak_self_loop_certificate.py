#!/usr/bin/env python3
"""Emit a flat Lean weak-L2 certificate from an audited transition JSON.

The generator deliberately does not trust the JSON's Boolean conclusion.  It
reconstructs the CSR rows, self-loops, reverse-distance witness, and fingerprint
before emitting a module.  Transition targets and witness successors use
little-endian UInt16 entries; distances use one byte.
"""

from __future__ import annotations

import argparse
from collections import deque
import hashlib
import json
from pathlib import Path
from typing import Iterable


PAIR_LABEL = "alpha-beta, alpha-gamma (manuscript literal)"
TARGET_PAGE_ENTRIES = 512


def encode_u16(values: Iterable[int]) -> list[int]:
    encoded: list[int] = []
    for value in values:
        if not 0 <= value < 65536:
            raise ValueError(f"UInt16 overflow: {value}")
        encoded.extend((value & 0xFF, value >> 8))
    return encoded


def lean_bytes(values: list[int], indent: str = "    ") -> str:
    chunks = [values[index : index + 24] for index in range(0, len(values), 24)]
    rows = [", ".join(str(value) for value in chunk) for chunk in chunks]
    if not rows:
        return "ByteArray.empty"
    body = (",\n" + indent).join(rows)
    return f"ByteArray.mk #[\n{indent}{body}\n  ]"


def checked_payload(path: Path) -> tuple[dict, dict[str, list[int]]]:
    data = json.loads(path.read_text())
    state_count = data["states"]
    row_offset = data["rowOffset"]
    targets = data["targetIndex"]

    if data.get("pairTypes") != PAIR_LABEL:
        raise ValueError("certificate is not the manuscript's two-pair profile")
    if len(row_offset) != state_count + 1 or row_offset[0] != 0:
        raise ValueError("malformed row offsets")
    if any(first > after for first, after in zip(row_offset, row_offset[1:])):
        raise ValueError("row offsets are not monotone")
    if row_offset[-1] != len(targets):
        raise ValueError("final row offset does not equal target count")
    if any(not 0 <= target < state_count for target in targets):
        raise ValueError("transition target outside state carrier")

    rows = [
        set(targets[row_offset[source] : row_offset[source + 1]])
        for source in range(state_count)
    ]
    self_loops = [source for source, row in enumerate(rows) if source in row]
    if self_loops != data.get("selfLoops"):
        raise ValueError("claimed self-loop list disagrees with CSR")

    expected_fingerprint = hashlib.sha256(
        json.dumps([row_offset, targets, self_loops]).encode()
    ).hexdigest()[:16]
    if expected_fingerprint != data.get("fingerprint"):
        raise ValueError("fingerprint mismatch")

    reverse: list[list[int]] = [[] for _ in range(state_count)]
    for source, row in enumerate(rows):
        for target in row:
            reverse[target].append(source)

    distance = {state: 0 for state in self_loops}
    successor = {state: state for state in self_loops}
    queue = deque(self_loops)
    while queue:
        target = queue.popleft()
        for source in sorted(reverse[target]):
            if source not in distance:
                distance[source] = distance[target] + 1
                successor[source] = target
                queue.append(source)

    if len(distance) != state_count:
        raise ValueError("not every state reaches a self-loop")
    if max(distance.values(), default=0) > 2:
        raise ValueError("weak-L2 witness exceeds two transitions")
    if data.get("weakL2_allReachSelfLoop") is not True:
        raise ValueError("input metadata does not claim total weak-L2 coverage")
    if data.get("maxStepsToSelfLoop") != max(distance.values(), default=0):
        raise ValueError("input max-distance metadata disagrees with reconstruction")

    def edge_entry(source: int, target: int) -> int:
        first = row_offset[source]
        after = row_offset[source + 1]
        try:
            return first + targets[first:after].index(target)
        except ValueError as error:
            raise ValueError(f"missing selected edge {source} -> {target}") from error

    next_index = [successor[state] for state in range(state_count)]
    distances = [distance[state] for state in range(state_count)]
    first_entry: list[int] = []
    second_entry: list[int] = []
    loop_entry: list[int] = []
    for source in range(state_count):
        first = next_index[source]
        second = next_index[first]
        terminal = source if distances[source] == 0 else (
            first if distances[source] == 1 else second
        )
        first_entry.append(edge_entry(source, first) if distances[source] > 0 else 0)
        second_entry.append(edge_entry(first, second) if distances[source] == 2 else 0)
        loop_entry.append(edge_entry(terminal, terminal))

    return data, {
        "next_index": next_index,
        "distance": distances,
        "first_entry": first_entry,
        "second_entry": second_entry,
        "loop_entry": loop_entry,
    }


def emit_data_module(data: dict, witness_data: dict[str, list[int]],
                     namespace_name: str) -> str:
    state_count = data["states"]
    row_offset = data["rowOffset"]
    targets = data["targetIndex"]
    setting = data.get("setting", "measured")
    family = data.get("family", "unknown")
    levels = data.get("levels", [])
    fingerprint = data["fingerprint"]

    row_bytes = lean_bytes(encode_u16(row_offset))
    next_bytes = lean_bytes(encode_u16(witness_data["next_index"]))
    first_entry_bytes = lean_bytes(encode_u16(witness_data["first_entry"]))
    second_entry_bytes = lean_bytes(encode_u16(witness_data["second_entry"]))
    loop_entry_bytes = lean_bytes(encode_u16(witness_data["loop_entry"]))
    distance_bytes = lean_bytes(witness_data["distance"])

    target_pages = [
        targets[index : index + TARGET_PAGE_ENTRIES]
        for index in range(0, len(targets), TARGET_PAGE_ENTRIES)
    ]
    target_page_defs = "\n\n".join(
        f"def targetIndexLE16Page{index:02d} : ByteArray := "
        f"{lean_bytes(encode_u16(page))}"
        for index, page in enumerate(target_pages)
    )
    target_decoder_lines = []
    for index, page in enumerate(target_pages):
        start = index * TARGET_PAGE_ENTRIES
        after = start + len(page)
        prefix = "if" if index == 0 else "else if"
        target_decoder_lines.append(
            f"  {prefix} entry < {after} then\n"
            f"    readU16LE targetIndexLE16Page{index:02d} (entry - {start})"
        )
    target_decoder_lines.append("  else 0")
    target_decoder = "\n".join(target_decoder_lines)

    return f'''import Mettapedia.GraphTheory.FourColor.GoertzelV24FiniteTransitionWeakSelfLoop

/-!
# A checked weak-L2 certificate for a measured two-pair transition

This flat certificate records the `{setting}` `{family}` transition between
levels `{levels}`.  It has {state_count} states and {len(targets)} directed
edges.  Its source JSON fingerprint is `{fingerprint}`.

The theorem below concerns exactly the decoded finite transition.  Identifying
that transition with every source-legal corridor is a separate fidelity
theorem; no such global identification is claimed here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace {namespace_name}

open GoertzelV24FiniteTransitionWeakSelfLoop

{target_page_defs}

def decodedTargetIndex (entry : Nat) : Nat :=
{target_decoder}

set_option maxRecDepth 100000 in
def transition : ByteCSR where
  stateCount := {state_count}
  rowOffsetLE16 := {row_bytes}
  targetEntryCount := {len(targets)}
  targetIndex := decodedTargetIndex

set_option maxRecDepth 100000 in
def witness : TwoStepWitness where
  nextIndexLE16 := {next_bytes}
  firstEntryLE16 := {first_entry_bytes}
  secondEntryLE16 := {second_entry_bytes}
  loopEntryLE16 := {loop_entry_bytes}
  distanceU8 := {distance_bytes}

end {namespace_name}

end Mettapedia.GraphTheory.FourColor
'''


def emit_page_module(module_name: str, namespace_name: str, page_index: int,
                     start: int, count: int) -> str:
    return f'''import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import {module_name}Data

namespace Mettapedia.GraphTheory.FourColor

namespace {namespace_name}

open GoertzelV24FiniteTransitionWeakSelfLoop

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem valid_page_{page_index:02d} : witness.ValidPage transition {start} {count} := by
  intro offset
  fin_cases offset <;> decide

end {namespace_name}

end Mettapedia.GraphTheory.FourColor
'''


def emit_aggregate_module(data: dict, module_name: str, namespace_name: str,
                          pages: list[tuple[int, int]]) -> str:
    imports = "\n".join(
        f"import {module_name}Page{index:02d}" for index in range(len(pages))
    )
    if len(pages) == 1:
        page_assembly = "  exact valid_page_00"
    else:
        assembly_lines = [
            "  have joined_01 := valid_page_00.append valid_page_01"
        ]
        last_name = "joined_01"
        for index in range(2, len(pages)):
            next_name = f"joined_{index:02d}"
            assembly_lines.append(
                f"  have {next_name} := {last_name}.append valid_page_{index:02d}"
            )
            last_name = next_name
        assembly_lines.append(f"  simpa using {last_name}")
        page_assembly = "\n".join(assembly_lines)

    state_count = data["states"]
    setting = data.get("setting", "measured")
    family = data.get("family", "unknown")
    fingerprint = data["fingerprint"]
    return f'''{imports}

/-!
# Checked weak L2 for one measured source two-pair transition

The `{setting}` `{family}` payload has {state_count} states.  Its source JSON
fingerprint is `{fingerprint}`.  The theorem concerns exactly this decoded
finite transition; identifying it with every source-legal corridor remains a
separate fidelity theorem.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace {namespace_name}

open GoertzelV24FiniteTransitionWeakSelfLoop

theorem all_pages_valid : witness.ValidPage transition 0 {state_count} := by
{page_assembly}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem witness_valid : witness.Valid transition := by
  exact witness.valid_of_page_zero transition (by decide) (by decide)
    (by decide) (by decide) (by decide) all_pages_valid

/-- Every state in this measured transition reaches a self-loop in at most two
one-ring steps. -/
theorem all_states_reach_selfLoop_within_two
    (source : Fin transition.stateCount) :
    ReachesSelfLoopWithinTwo transition source.val :=
  witness.all_reach_selfLoop_within_two transition witness_valid source

end {namespace_name}

end Mettapedia.GraphTheory.FourColor
'''


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--module", required=True)
    parser.add_argument("--namespace", required=True)
    parser.add_argument("--page-size", type=int, default=32)
    args = parser.parse_args()

    data, witness_data = checked_payload(args.input)
    if args.page_size <= 0:
        raise ValueError("page size must be positive")

    data_output = args.output.with_name(args.output.stem + "Data.lean")
    data_output.write_text(emit_data_module(data, witness_data, args.namespace))

    for stale in args.output.parent.glob(args.output.stem + "Page*.lean"):
        stale.unlink()
    pages = [
        (start, min(args.page_size, data["states"] - start))
        for start in range(0, data["states"], args.page_size)
    ]
    for index, (start, count) in enumerate(pages):
        page_output = args.output.with_name(
            args.output.stem + f"Page{index:02d}.lean"
        )
        page_output.write_text(
            emit_page_module(args.module, args.namespace, index, start, count)
        )
    args.output.write_text(
        emit_aggregate_module(data, args.module, args.namespace, pages)
    )
    print(
        f"wrote {args.output} + data + {len(pages)} pages: "
        f"states={data['states']} edges={len(data['targetIndex'])} "
        f"fingerprint={data['fingerprint']}"
    )


if __name__ == "__main__":
    main()
