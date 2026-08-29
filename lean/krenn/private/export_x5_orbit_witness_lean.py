#!/usr/bin/env python3
"""Export an exact Lean witness for the 7776-to-336 X5 orbit cover."""

from __future__ import annotations

import os
import argparse
import contextlib
import hashlib
import io
import json
import sys
from pathlib import Path


KRENN_ROOT = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
sys.path.insert(0, str(KRENN_ROOT))

import f9_pipeline  # noqa: E402


SUPPORT_TEXT = "01,02,03,04,15"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


# Images of vertices 2,3,4, in the order of the Lean `LeafSymmetry` type.
LEAF_IMAGES = [
    (2, 3, 4),
    (3, 2, 4),
    (4, 3, 2),
    (2, 4, 3),
    (4, 2, 3),
    (3, 4, 2),
]
LEAF_NAMES = [
    ".identity", ".swap23", ".swap24", ".swap34",
    ".cycle234", ".cycle243",
]

# Images of colours 0,1,2, in the order of the Lean `ColourSymmetry` type.
COLOUR_IMAGES = [
    (0, 1, 2),
    (0, 2, 1),
    (1, 0, 2),
    (1, 2, 0),
    (2, 0, 1),
    (2, 1, 0),
]
COLOUR_NAMES = [".p012", ".p021", ".p102", ".p120", ".p201", ".p210"]


def vertex_map(images: tuple[int, int, int]) -> dict[int, int]:
    return {0: 0, 1: 1, 2: images[0], 3: images[1], 4: images[2], 5: 5}


def colour_map(images: tuple[int, int, int]) -> dict[int, int]:
    return dict(enumerate(images))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()

    support = f9_pipeline.parse_X(SUPPORT_TEXT)
    cases = f9_pipeline.cases_for(support)
    with contextlib.redirect_stdout(io.StringIO()):
        representatives = f9_pipeline.case_orbits(support, verify=True)
    representative_ordinal = {
        choice: ordinal
        for ordinal, (_case_index, choice, _orbit_size) in enumerate(representatives)
    }
    leaf_maps = [vertex_map(images) for images in LEAF_IMAGES]
    colour_maps = [colour_map(images) for images in COLOUR_IMAGES]

    def act(case, leaf_index: int, colour_index: int):
        moved = {}
        sigma = leaf_maps[leaf_index]
        tau = colour_maps[colour_index]
        for slot, edge in enumerate(support):
            moved_edge, left, right = f9_pipeline.vertex_perm_on_entry(
                sigma, edge, *case[slot]
            )
            moved[moved_edge] = (tau[left], tau[right])
        return tuple(moved[edge] for edge in support)

    witnesses: list[tuple[int, int, int]] = []
    for case in cases:
        colour = next(
            index for index, tau in enumerate(colour_maps)
            if (tau[case[0][0]], tau[case[0][1]]) == (0, 1)
        )
        coloured = act(case, 0, colour)
        leaf = next(
            index for index in range(6)
            if (lambda digits: digits[1] <= digits[2] <= digits[3])(
                [f9_pipeline.OFFDIAG.index(pair)
                 for pair in act(coloured, index, 0)]
            )
        )
        canonical = act(coloured, leaf, 0)
        ordinal = representative_ordinal.get(canonical)
        if ordinal is None:
            raise RuntimeError("canonicalized case is not an audited representative")
        if act(case, leaf, colour) != canonical:
            raise RuntimeError("combined orbit action disagrees with staged action")
        witnesses.append((ordinal, leaf, colour))

    if len(witnesses) != 6 ** 5:
        raise RuntimeError("witness table does not cover 7776 labelled cases")
    if len({row[0] for row in witnesses}) != 336:
        raise RuntimeError("witness table does not reach all 336 representatives")

    lines = [
        "import KrennX5GaugeNormalizationData",
        "import KrennX5Symmetry",
        "",
        "/-! Generated exact witness for the 7776-to-336 X5 orbit cover. -/",
        "",
        "namespace Krenn.X5OrbitWitness",
        "",
        "open MonochromaticQuantumGraph",
        "open Krenn.X5Symmetry",
        "open Krenn.X5GaugeNormalizationData",
        "",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 50000000",
        "",
        "def casePlaceValue : Fin 5 → Nat := ![1296, 216, 36, 6, 1]",
        "",
        "def labelledCaseChoice (case : Fin 7776) : CaseChoice := fun slot =>",
        "  ⟨(case.val / casePlaceValue slot) % 6, Nat.mod_lt _ (by decide)⟩",
        "",
        "def representativeLabelledCase (ordinal : Fin 336) : Fin 7776 :=",
        "  ⟨(representativeCase ordinal).val, by omega⟩",
        "",
        "def representativeChoice (ordinal : Fin 336) : CaseChoice :=",
        "  labelledCaseChoice (representativeLabelledCase ordinal)",
        "",
        "structure OrbitWitness where",
        "  representative : Fin 336",
        "  leaf : LeafSymmetry",
        "  colour : ColourSymmetry",
        "deriving DecidableEq",
        "",
        "def defaultOrbitWitness : OrbitWitness := ⟨0, .identity, .p012⟩",
        "",
        "theorem representativeChoice_eq_datum_selected : ∀ ordinal slot,",
        "    supportEntry (representativeChoice ordinal) slot =",
        "      (datum ordinal).selected slot := by",
        "  decide",
        "",
        "#print axioms Krenn.X5OrbitWitness.representativeChoice_eq_datum_selected",
        "",
        "end Krenn.X5OrbitWitness",
        "",
    ]
    args.output.write_text("\n".join(lines), encoding="utf-8")
    payload = {
        "format": "krenn-x5-orbit-witness-lean-v1",
        "support": SUPPORT_TEXT,
        "labelled_case_count": len(witnesses),
        "representative_count": len(representatives),
        "representative_case_indices": [row[0] for row in representatives],
        "representative_orbit_sizes": [row[2] for row in representatives],
        "output_sha256": digest(args.output),
        "exporter_sha256": digest(Path(__file__)),
    }
    if args.receipt is not None:
        args.receipt.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "labelled_cases": len(witnesses),
        "representatives": len(representatives),
        "output_sha256": payload["output_sha256"],
    }, sort_keys=True))

    chunk_size = 48
    chunk_count = (len(witnesses) + chunk_size - 1) // chunk_size
    chunk_dir = args.output.parent / (args.output.stem + "Chunks")
    chunk_dir.mkdir(parents=True, exist_ok=True)
    chunk_modules: list[str] = []
    for chunk_index in range(chunk_count):
        lower = chunk_index * chunk_size
        upper = min(len(witnesses), lower + chunk_size)
        module = f"{args.output.stem}Chunks.Chunk{chunk_index}"
        chunk_modules.append(module)
        path = chunk_dir / f"Chunk{chunk_index}.lean"
        local_rows = [
            f"⟨{representative}, {LEAF_NAMES[leaf]}, {COLOUR_NAMES[colour]}⟩"
            for representative, leaf, colour in witnesses[lower:upper]
        ]
        local_chunks = [", ".join(local_rows[offset:offset + 12])
                        for offset in range(0, len(local_rows), 12)]
        local_array = "#[\n    " + ",\n    ".join(local_chunks) + "\n  ]"
        chunk_lines = [
            f"import {args.output.stem}",
            "",
            f"namespace Krenn.X5OrbitWitnessChunks.Chunk{chunk_index}",
            "",
            "open Krenn.X5Symmetry",
            "open Krenn.X5OrbitWitness",
            "",
            "set_option maxRecDepth 100000",
            "",
            "def witnessTable : Array OrbitWitness :=",
            f"  {local_array}",
            "",
            f"theorem witnessTable_size : witnessTable.size = {upper - lower} := by",
            "  decide",
            "",
            "def witness (case : Fin 7776) : OrbitWitness :=",
            f"  witnessTable.getD (case.val - {lower}) defaultOrbitWitness",
            "",
            f"theorem correct (case : Fin 7776) (lower : {lower} ≤ case.val)",
            f"    (upper : case.val < {upper}) :",
            "    actCase (witness case).leaf",
            "        (witness case).colour",
            "        (labelledCaseChoice case) =",
            "      representativeChoice (witness case).representative := by",
        ]
        chunk_lines.append("  interval_cases value : case.val")
        for value in range(lower, upper):
            chunk_lines += [
                f"  · have equal : case = ({value} : Fin 7776) := Fin.ext value",
                "    subst case",
                "    decide",
            ]
        chunk_lines += [
            "",
            f"#print axioms Krenn.X5OrbitWitnessChunks.Chunk{chunk_index}.correct",
            "",
            f"end Krenn.X5OrbitWitnessChunks.Chunk{chunk_index}",
            "",
        ]
        path.write_text("\n".join(chunk_lines), encoding="utf-8")
    assembly = args.output.parent / f"{args.output.stem}Correct.lean"
    assembly_lines = [f"import {module}" for module in chunk_modules] + [
        "",
        "namespace Krenn.X5OrbitWitness",
        "",
        "open Krenn.X5Symmetry",
        "",
        "set_option maxRecDepth 100000",
        "",
        "theorem exists_orbitWitness_correct (case : Fin 7776) :",
        "    ∃ witness : OrbitWitness,",
        "      actCase witness.leaf witness.colour (labelledCaseChoice case) =",
        "        representativeChoice witness.representative := by",
    ]
    for chunk_index in range(chunk_count):
        lower = chunk_index * chunk_size
        upper = min(len(witnesses), lower + chunk_size)
        prefix = "  " if chunk_index == 0 else "  else "
        assembly_lines += [
            f"{prefix}if h{chunk_index} : case.val < {upper} then",
            f"    exact ⟨Krenn.X5OrbitWitnessChunks.Chunk{chunk_index}.witness case,",
            f"      Krenn.X5OrbitWitnessChunks.Chunk{chunk_index}.correct case (by omega) h{chunk_index}⟩",
        ]
    assembly_lines += [
        "  else omega",
        "",
        "#print axioms Krenn.X5OrbitWitness.exists_orbitWitness_correct",
        "",
        "end Krenn.X5OrbitWitness",
        "",
    ]
    assembly.write_text("\n".join(assembly_lines), encoding="utf-8")
    payload.update({
        "chunk_size": chunk_size,
        "chunk_count": chunk_count,
        "chunk_sha256": {
            f"Chunk{index}.lean": digest(chunk_dir / f"Chunk{index}.lean")
            for index in range(chunk_count)
        },
        "assembly_sha256": digest(assembly),
    })
    if args.receipt is not None:
        args.receipt.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
