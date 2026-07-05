#!/usr/bin/env python3
"""Verify the archived n6 radial-face blocker for the winding witness."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


DEFAULT_INPUT = Path(
    "results/fourcolor/"
    "section92_closed_collar_winding_simple_patch_n6_radial_face_archive_audit.json"
)
DEFAULT_OUTPUT = Path(
    "results/fourcolor/"
    "section92_closed_collar_winding_realizability_radial_face_blocker_verdict.json"
)
EXPECTED_SCHEMA = (
    "fourcolor-section-9-2-closed-collar-winding-simple-patch-n6-"
    "radial-face-archive-audit-v1"
)
OUTPUT_SCHEMA = (
    "fourcolor-section-9-2-winding-realizability-radial-face-blocker-"
    "verdict-v1"
)
EXPECTED_ROW_VERDICT = "row_has_no_radial_face_coherent_rotation"
EXPECTED_ARCHIVE_VERDICT = "radial_face_row_coverage_all_planar_rotations_incoherent"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Validate that archived n6 annular embedding rows block the "
            "winding witness at radial-face coherence."
        )
    )
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--results-dir", type=Path, default=Path("results/fourcolor"))
    return parser.parse_args()


def load_json(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    with tmp.open("w", encoding="utf-8") as handle:
        json.dump(payload, handle, indent=2, sort_keys=True)
        handle.write("\n")
    tmp.replace(path)


def as_int_dict(data: dict[str, Any]) -> dict[int, int]:
    out: dict[int, int] = {}
    for key, value in data.items():
        out[int(key)] = int(value)
    return out


def fail(failures: list[str], label: str, detail: str) -> None:
    failures.append(f"{label}: {detail}")


def verify_row(
    row: dict[str, Any],
    results_dir: Path,
    source_cache: dict[str, Any],
    failures: list[str],
) -> dict[str, Any]:
    case = row.get("case")
    label = f"case={case}"
    radial_cut_edge_count = int(row.get("radial_cut_edge_count", -1))
    max_on_face = int(row.get("max_radial_cut_edges_on_single_face", -1))
    coherent_count = int(row.get("radial_face_coherent_rotation_count", -1))
    planar_count = int(row.get("planar_rotation_system_count", -1))
    enumerated_count = int(row.get("enumerated_rotation_system_count", -1))
    histogram = as_int_dict(row.get("max_radial_cut_edges_on_single_face_histogram", {}))

    if radial_cut_edge_count <= 0:
        fail(failures, label, "missing positive radial_cut_edge_count")
    if max_on_face >= radial_cut_edge_count:
        fail(
            failures,
            label,
            "max_radial_cut_edges_on_single_face reaches the whole radial cut",
        )
    if coherent_count != 0:
        fail(failures, label, "radial_face_coherent_rotation_count is nonzero")
    if row.get("verdict") != EXPECTED_ROW_VERDICT:
        fail(failures, label, "unexpected row verdict")
    if row.get("rotation_system_enumeration_exhausted") is not True:
        fail(failures, label, "rotation-system enumeration is not exhausted")
    if sum(histogram.values()) != planar_count:
        fail(failures, label, "histogram count does not match planar rotation count")
    if any(cut_count >= radial_cut_edge_count for cut_count in histogram):
        fail(failures, label, "histogram contains a coherent radial-face count")
    source_file = row.get("source_file")
    if not isinstance(source_file, str):
        fail(failures, label, "missing source_file")
    elif not (results_dir / source_file).exists():
        fail(failures, label, f"source file is not present: {source_file}")
    else:
        source = source_cache.setdefault(
            source_file, load_json(results_dir / source_file)
        )
        source_samples = source.get("samples", [])
        matches = [
            sample
            for sample in source_samples
            if sample.get("patch_index") == row.get("patch_index")
            and sample.get("radial_order_index") == row.get("radial_order_index")
        ]
        if len(matches) != 1:
            fail(failures, label, "source sample match is not unique")
        else:
            audit = matches[0].get("embedding_audit", {})
            source_histogram = as_int_dict(
                audit.get("max_radial_cut_edges_on_single_face_histogram", {})
            )
            if audit.get("checked") is not True:
                fail(failures, label, "source embedding audit is not checked")
            if audit.get("rotation_system_enumeration_exhausted") is not True:
                fail(failures, label, "source enumeration is not exhausted")
            if int(audit.get("enumerated_rotation_system_count", -1)) != enumerated_count:
                fail(failures, label, "source enumerated count mismatch")
            if int(audit.get("planar_rotation_system_count", -1)) != planar_count:
                fail(failures, label, "source planar rotation count mismatch")
            if int(audit.get("radial_face_coherent_rotation_count", -1)) != coherent_count:
                fail(failures, label, "source coherent rotation count mismatch")
            if source_histogram != histogram:
                fail(failures, label, "source histogram mismatch")

    return {
        "case": case,
        "source_file": source_file,
        "radial_cut_edge_count": radial_cut_edge_count,
        "max_radial_cut_edges_on_single_face": max_on_face,
        "planar_rotation_system_count": planar_count,
        "enumerated_rotation_system_count": enumerated_count,
        "blocker": "no_face_contains_all_radial_cut_edges",
    }


def main() -> int:
    args = parse_args()
    archive = load_json(args.input)
    failures: list[str] = []

    if archive.get("schema") != EXPECTED_SCHEMA:
        fail(failures, "archive", "unexpected schema")
    if archive.get("row_coverage_verdict") != EXPECTED_ARCHIVE_VERDICT:
        fail(failures, "archive", "unexpected row coverage verdict")
    if int(archive.get("archive_radial_face_coherent_rotation_count", -1)) != 0:
        fail(failures, "archive", "coherent rotation count is nonzero")

    rows = archive.get("row_coverage_certificates", [])
    if not isinstance(rows, list):
        fail(failures, "archive", "row_coverage_certificates is not a list")
        rows = []
    if int(archive.get("row_coverage_certificate_count", -1)) != len(rows):
        fail(failures, "archive", "row coverage certificate count mismatch")

    aggregate_histogram = as_int_dict(
        archive.get("max_radial_cut_edges_on_single_face_histogram", {})
    )
    if any(cut_count >= 4 for cut_count in aggregate_histogram):
        fail(failures, "archive", "aggregate histogram contains a coherent count")

    source_cache: dict[str, Any] = {}
    validated_rows = [
        verify_row(row, args.results_dir, source_cache, failures)
        for row in rows
        if isinstance(row, dict)
    ]
    if len(validated_rows) != len(rows):
        fail(failures, "archive", "one or more row certificates are not objects")

    verdict = {
        "schema": OUTPUT_SCHEMA,
        "input_archive": args.input.name,
        "verdict": (
            "blocked_at_radial_face_coherence"
            if not failures
            else "radial_face_archive_verification_failed"
        ),
        "decisive_condition": (
            "max_radial_cut_edges_on_single_face < radial_cut_edge_count"
        ),
        "archive_radial_face_coherent_rotation_count": archive.get(
            "archive_radial_face_coherent_rotation_count"
        ),
        "archive_histogram": archive.get(
            "max_radial_cut_edges_on_single_face_histogram"
        ),
        "validated_row_count": len(validated_rows),
        "validated_source_file_count": len(source_cache),
        "validated_rows": validated_rows,
        "failures": failures,
    }
    write_json(args.output, verdict)
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
