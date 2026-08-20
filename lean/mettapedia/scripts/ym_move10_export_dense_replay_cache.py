#!/usr/bin/env python3
"""Emit bounded decoded-input cache lemmas for OUR densest rank replay row."""

from __future__ import annotations

import argparse
import runpy
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / "Mettapedia/QuantumTheory/YangMills"
TARGET = 11_548
STEP_BLOCK_SIZE = 6


def exact_rows(prefix: str) -> list[list[tuple[int, ...]]]:
    module = runpy.run_path(str(ROOT / "scripts/pack_yang_mills_trace_rank_exact.py"))
    for spec in module["SPECS"]:
        filename, candidate, lookup, width, signed_index, *_ = spec
        if candidate == prefix:
            return module["extract_rows"](
                (DIRECTORY / filename).read_text(), candidate, lookup, width, signed_index
            )
    raise RuntimeError(f"unknown exact sparse payload {prefix}")


def replay_data() -> tuple[list[list[int]], list[int], list[int | None]]:
    replay_module = runpy.run_path(str(ROOT / "scripts/pack_yang_mills_trace_rank_replay.py"))
    partition_module = runpy.run_path(str(ROOT / "scripts/pack_yang_mills_trace_rank_partition.py"))
    replay_source = (DIRECTORY / "HypercubicDimension16TraceRankCertificateDataReplay.lean").read_text()
    partition_source = (DIRECTORY / "HypercubicDimension16TraceRankCertificateDataPartition.lean").read_text()
    steps = replay_module["packed_rows"](replay_source, "rationalReplaySteps")
    pivots = replay_module["packed_values"](replay_source, "pivotColumns", replay_module["ROWS"])
    owners = partition_module["packed_owners"](partition_source)
    if owners is None:
        owners = partition_module["original_owners"](partition_source)
    return steps, pivots, owners


def lean_int(value: int) -> str:
    if value < 0:
        return f"(-{abs(value)} : Int)"
    return f"({value} : Int)"


def lean_integer_row(row: list[tuple[int, ...]]) -> str:
    return "#[" + ", ".join(f"({column}, {lean_int(value)})" for column, value in row) + "]"


def lean_rational_row(row: list[tuple[int, ...]]) -> str:
    return "#[" + ", ".join(
        f"({column}, {lean_int(numerator)}, {denominator})"
        for column, numerator, denominator in row
    ) + "]"


def header(imports: list[str], title: str) -> str:
    import_lines = "\n".join(f"import Mettapedia.QuantumTheory.YangMills.{module}" for module in imports)
    return f'''{import_lines}

/-!
# {title}

These lemmas expose selected decoded finite inputs for one fixed dense replay
row.  They are bounded data checks only; they assert neither rank nor a
complete certificate replay.
-/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceRankCertificateData

set_option maxRecDepth 32768
'''


def footer() -> str:
    return '''
end HypercubicDimension16TraceRankCertificateData
end YangMills
end QuantumTheory
end Mettapedia
'''


def proof(accessor: str, payload: str) -> str:
    return f'''by
    unfold {accessor} {payload}
    decide +kernel'''


def render_input(
    selected: list[tuple[int, ...]], expected: list[tuple[int, ...]], steps: list[int], pivot: int, owner: int | None
) -> str:
    if owner is None:
        raise RuntimeError("the dense target pivot has no owner")
    names = [
        "denseReplay_selectedRow",
        "denseReplay_expectedRow",
        "denseReplay_steps",
        "denseReplay_targetPivot",
        "denseReplay_targetOwner",
    ]
    return header(
        [
            "HypercubicDimension16TraceRankCertificateDataRows",
            "HypercubicDimension16TraceRankCertificateDataBasis",
            "HypercubicDimension16TraceRankCertificateDataReplay",
            "HypercubicDimension16TraceRankCertificateDataPartition",
        ],
        "Bounded decoded input cache for OUR dense trace-rank replay",
    ) + f'''

theorem denseReplay_selectedRow :
    selectedIntegerRow? {TARGET} = some {lean_integer_row(selected)} :=
  {proof("selectedIntegerRow?", f"selectedIntegerRowsPayload{TARGET // 1024}")}

theorem denseReplay_expectedRow :
    normalizedRationalBasisRow? {TARGET} = some {lean_rational_row(expected)} :=
  {proof("normalizedRationalBasisRow?", f"normalizedRationalBasisPayload{TARGET // 1024}")}

theorem denseReplay_steps : rationalReplayStepRow? {TARGET} = some #[{', '.join(map(str, steps))}] :=
  {proof("rationalReplayStepRow?", f"rationalReplayStepsPayload{TARGET // 1024}")}

theorem denseReplay_targetPivot : pivotColumn? {TARGET} = some {pivot} :=
  {proof("pivotColumn?", f"pivotColumnsPayload{TARGET // 1024}")}

theorem denseReplay_targetOwner : columnOwner? {pivot} = some {owner} :=
  {proof("columnOwner?", f"columnOwnerPayload{pivot // 1024}")}

{chr(10).join(f'#print axioms {name}' for name in names)}
''' + footer()


def render_step_block(block: int, basis: list[list[tuple[int, ...]]], pivots: list[int]) -> str:
    names: list[str] = []
    body: list[str] = []
    for index in range(block * STEP_BLOCK_SIZE, min((block + 1) * STEP_BLOCK_SIZE, len(basis))):
        row_index = STEP_INDICES[index]
        basis_name = f"denseReplay_basis_{row_index}"
        pivot_name = f"denseReplay_pivot_{row_index}"
        names.extend([basis_name, pivot_name])
        body.append(f'''theorem {basis_name} :
    normalizedRationalBasisRow? {row_index} = some {lean_rational_row(basis[index])} :=
  {proof("normalizedRationalBasisRow?", f"normalizedRationalBasisPayload{row_index // 1024}")}

theorem {pivot_name} : pivotColumn? {row_index} = some {pivots[index]} :=
  {proof("pivotColumn?", f"pivotColumnsPayload{row_index // 1024}")}''')
    return header(
        [
            "HypercubicDimension16TraceRankCertificateDataBasis",
            "HypercubicDimension16TraceRankCertificateDataReplay",
        ],
        f"Bounded decoded step cache {block} for OUR dense trace-rank replay",
    ) + "\n\n".join(body) + "\n\n" + "\n".join(f"#print axioms {name}" for name in names) + footer()


def outputs() -> dict[Path, str]:
    selected = exact_rows("selectedIntegerRows")
    basis = exact_rows("normalizedRationalBasis")
    steps, pivots, owners = replay_data()
    global STEP_INDICES
    STEP_INDICES = steps[TARGET]
    selected_target = selected[TARGET]
    expected_target = basis[TARGET]
    step_basis = [basis[index] for index in STEP_INDICES]
    step_pivots = [pivots[index] for index in STEP_INDICES]
    return {
        DIRECTORY / "HypercubicDimension16TraceRankDenseReplayCacheInput.lean": render_input(
            selected_target, expected_target, STEP_INDICES, pivots[TARGET], owners[pivots[TARGET]]
        ),
        **{
            DIRECTORY / f"HypercubicDimension16TraceRankDenseReplayCacheStep{block}.lean": render_step_block(
                block, step_basis, step_pivots
            )
            for block in range((len(STEP_INDICES) + STEP_BLOCK_SIZE - 1) // STEP_BLOCK_SIZE)
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for path, rendered in outputs().items():
        if args.check:
            if not path.exists() or path.read_text() != rendered:
                raise SystemExit(f"{path.name} is not freshly generated")
        else:
            path.write_text(rendered)


if __name__ == "__main__":
    main()
