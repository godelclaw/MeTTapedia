#!/usr/bin/env python3
"""Audit archived closed-collar winding simple-patch verdict artifacts."""

from __future__ import annotations

from collections import Counter
from pathlib import Path
import argparse
import json
import os


N6_EXACT_PATCH_TOPOLOGY_COUNT = 1_858_980
N8_EXACT_PATCH_TOPOLOGY_COUNT = 1_189_087_725
FIRST_PREFIX_END = 800_000
FIRST_PREFIX_SLICE_WIDTH = 50_000

STRUCTURAL_NAMES = (
    "connected_multigraph",
    "cubic_multigraph",
    "bridgeless_multigraph",
    "planar_multigraph",
    "simple_endpoint_realization",
)

TEMPLATE_BLOCKER_FILES = (
    "section92_closed_collar_winding_simple_patch_template_blockers_n6_800000_1000000.json",
    "section92_closed_collar_winding_simple_patch_template_blockers_n6_1000000_1200000.json",
    "section92_closed_collar_winding_simple_patch_template_blockers_n6_1200000_1400000.json",
    "section92_closed_collar_winding_simple_patch_template_blockers_n6_1400000_1600000.json",
    "section92_closed_collar_winding_simple_patch_template_blockers_n6_1600000_1858980.json",
)

RADIAL_FACE_SAMPLE_FILES = (
    "section92_closed_collar_winding_simple_patch_annular_embedding_n6_samples.json",
    "section92_closed_collar_winding_simple_patch_annular_embedding_n6_case_1000301_r0.json",
    "section92_closed_collar_winding_simple_patch_annular_embedding_n6_case_1000301_r1.json",
)

RADIAL_FACE_SLICE_FILES = (
    "section92_closed_collar_winding_simple_patch_annular_embedding_n6_slice_1000000_500_cases2.json",
    "section92_closed_collar_winding_simple_patch_annular_embedding_n6_slice_1000302_500_cases2.json",
    "section92_closed_collar_winding_simple_patch_annular_embedding_n6_slice_1000789_500_cases2.json",
    "section92_closed_collar_winding_simple_patch_annular_embedding_n6_slice_1001289_500_cases2.json",
)

N8_TEMPLATE_BLOCKER_FILES = (
    "section92_closed_collar_winding_simple_patch_template_blockers_n8_000000_050000.json",
    "section92_closed_collar_winding_simple_patch_template_blockers_n8_050000_500000.json",
    "section92_closed_collar_winding_simple_patch_template_blockers_n8_500000_1000000.json",
    "section92_closed_collar_winding_simple_patch_template_blockers_n8_1000000_1500000.json",
    "section92_closed_collar_winding_simple_patch_template_blockers_n8_1500000_2000000.json",
)

N8_STRATIFIED_SAMPLE_FILE = (
    "section92_closed_collar_winding_simple_patch_template_blockers_n8_stratified_33.json"
)

REVERSE_TEMPLATE_KEY = "edges:g0:F4F5,g1:F1F0|sideCollar:g0:F5,g1:F1"
REPO_ROOT = Path(__file__).resolve().parents[4]
PACKAGE_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_TAXONOMY_RESULTS_DIR = PACKAGE_ROOT / "results" / "fourcolor"
DEFAULT_RADIAL_FACE_RESULTS_DIR = REPO_ROOT / "results" / "fourcolor"
DEFAULT_TAXONOMY_OUTPUT = (
    DEFAULT_TAXONOMY_RESULTS_DIR
    / "section92_closed_collar_winding_simple_patch_n6_detailed_taxonomy_audit.json"
)
DEFAULT_RADIAL_FACE_OUTPUT = (
    DEFAULT_RADIAL_FACE_RESULTS_DIR
    / "section92_closed_collar_winding_simple_patch_n6_radial_face_archive_audit.json"
)
DEFAULT_N8_OUTPUT = (
    DEFAULT_RADIAL_FACE_RESULTS_DIR
    / "section92_closed_collar_winding_simple_patch_n8_frontier_audit.json"
)


def read_json(path: Path) -> dict[str, object]:
    with path.open() as handle:
        data = json.load(handle)
    if not isinstance(data, dict):
        raise ValueError(f"{path.name}: top-level JSON is not an object")
    return data


def summary(data: dict[str, object], name: str) -> dict[str, object]:
    value = data.get("summary")
    if not isinstance(value, dict):
        raise ValueError(f"{name}: missing object summary")
    return value


def int_field(data: dict[str, object], name: str, field: str) -> int:
    value = data.get(field)
    if not isinstance(value, int):
        raise ValueError(f"{name}: summary.{field} is not an integer")
    return value


def dict_field(data: dict[str, object], name: str, field: str) -> dict[str, int]:
    value = data.get(field)
    if not isinstance(value, dict):
        raise ValueError(f"{name}: summary.{field} is not an object")
    result: dict[str, int] = {}
    for key, item in value.items():
        if not isinstance(key, str) or not isinstance(item, int):
            raise ValueError(f"{name}: summary.{field} has non-string/non-int entry")
        result[key] = item
    return result


def samples(data: dict[str, object], name: str) -> list[dict[str, object]]:
    value = data.get("samples")
    if not isinstance(value, list):
        raise ValueError(f"{name}: missing list samples")
    result: list[dict[str, object]] = []
    for index, item in enumerate(value):
        if not isinstance(item, dict):
            raise ValueError(f"{name}: samples[{index}] is not an object")
        result.append(item)
    return result


def object_field(data: dict[str, object], name: str, field: str) -> dict[str, object]:
    value = data.get(field)
    if not isinstance(value, dict):
        raise ValueError(f"{name}: {field} is not an object")
    return value


def bool_field(data: dict[str, object], name: str, field: str) -> bool:
    value = data.get(field)
    if not isinstance(value, bool):
        raise ValueError(f"{name}: {field} is not a boolean")
    return value


def assert_equal(label: str, actual: object, expected: object) -> None:
    if actual != expected:
        raise AssertionError(f"{label}: expected {expected!r}, got {actual!r}")


def prefix_slice_names() -> list[str]:
    return [
        "section92_closed_collar_winding_simple_patch_slice_n6_"
        f"{start:06d}_{start + FIRST_PREFIX_SLICE_WIDTH:06d}.json"
        for start in range(0, FIRST_PREFIX_END, FIRST_PREFIX_SLICE_WIDTH)
    ]


def audit(results_dir: Path) -> dict[str, object]:
    prefix_hist: Counter[str] = Counter()
    prefix_processed = 0
    prefix_radial = 0
    prefix_profile = 0
    prefix_passes = 0

    prefix_files = prefix_slice_names()
    for name in prefix_files:
        data = read_json(results_dir / name)
        block = summary(data, name)
        prefix_processed += int_field(block, name, "processed_patch_topology_count")
        prefix_radial += int_field(block, name, "radial_order_case_count")
        prefix_profile += int_field(block, name, "profile_preserving_case_count")
        prefix_passes += int_field(block, name, "normal_form_prefix_passing_profile_case_count")
        prefix_hist.update(dict_field(block, name, "first_failed_normal_form_histogram"))

    assert_equal("prefix processed count", prefix_processed, FIRST_PREFIX_END)
    assert_equal("prefix radial-order count", prefix_radial, 2 * FIRST_PREFIX_END)
    assert_equal("prefix profile-preserving count", prefix_profile, 18_720)
    assert_equal("prefix normal-form pass count", prefix_passes, 0)
    assert_equal("prefix blocker histogram", dict(prefix_hist), {"planar_multigraph": 18_720})

    template_totals: Counter[str] = Counter()
    template_exact_hist: Counter[str] = Counter()
    template_failure_hist: Counter[str] = Counter()

    for name in TEMPLATE_BLOCKER_FILES:
        data = read_json(results_dir / name)
        block = summary(data, name)
        template_totals["processed_patch_topology_count"] += int_field(
            block, name, "processed_patch_topology_count"
        )
        template_totals["radial_order_case_count"] += int_field(
            block, name, "radial_order_case_count"
        )
        template_totals["profile_preserving_case_count"] += int_field(
            block, name, "profile_preserving_case_count"
        )
        template_totals["structural_first_blocker_count"] += int_field(
            block, name, "structural_first_blocker_count"
        )
        template_totals["exact_template_blocker_count"] += int_field(
            block, name, "exact_template_blocker_count"
        )
        template_totals["non_template_cyclic_cut_blocker_count"] += int_field(
            block, name, "non_template_cyclic_cut_blocker_count"
        )
        template_totals["cap5_like_blocker_count"] += int_field(
            block, name, "cap5_like_blocker_count"
        )
        template_totals["normal_form_after_template_exclusion_passing_count"] += int_field(
            block, name, "normal_form_after_template_exclusion_passing_count"
        )
        template_exact_hist.update(dict_field(block, name, "exact_template_histogram"))
        template_failure_hist.update(
            dict_field(block, name, "first_failed_after_template_exclusion_histogram")
        )

    assert_equal("template processed count", template_totals["processed_patch_topology_count"], 1_058_980)
    assert_equal("template radial-order count", template_totals["radial_order_case_count"], 2_117_960)
    assert_equal("template profile-preserving count", template_totals["profile_preserving_case_count"], 11_160)
    assert_equal("template structural count", template_totals["structural_first_blocker_count"], 9_000)
    assert_equal("template exact count", template_totals["exact_template_blocker_count"], 2_160)
    assert_equal("template residual pass count", template_totals["normal_form_after_template_exclusion_passing_count"], 0)
    assert_equal(
        "template exact histogram",
        dict(template_exact_hist),
        {
            "edges:g0:F1F0,g1:F4F5|sideCollar:g0:F1,g1:F5": 1_080,
            "edges:g0:F4F5,g1:F1F0|sideCollar:g0:F5,g1:F1": 1_080,
        },
    )
    assert_equal(
        "template failure histogram",
        dict(template_failure_hist),
        {
            "excluded_exact_diagonal_two_pole_template": 2_160,
            "planar_multigraph": 9_000,
        },
    )

    total_processed = prefix_processed + template_totals["processed_patch_topology_count"]
    total_radial = prefix_radial + template_totals["radial_order_case_count"]
    total_profile = prefix_profile + template_totals["profile_preserving_case_count"]
    total_structural = prefix_hist["planar_multigraph"] + template_failure_hist["planar_multigraph"]
    total_exact = template_totals["exact_template_blocker_count"]
    total_residual = (
        template_totals["non_template_cyclic_cut_blocker_count"]
        + template_totals["cap5_like_blocker_count"]
        + template_totals["normal_form_after_template_exclusion_passing_count"]
    )

    assert_equal("total processed count", total_processed, N6_EXACT_PATCH_TOPOLOGY_COUNT)
    assert_equal("total radial-order count", total_radial, 2 * N6_EXACT_PATCH_TOPOLOGY_COUNT)
    assert_equal("total profile-preserving count", total_profile, 29_880)
    assert_equal("total structural count", total_structural, 27_720)
    assert_equal("total exact-template count", total_exact, 2_160)
    assert_equal("total residual count", total_residual, 0)
    assert_equal("profile accounting", total_structural + total_exact + total_residual, total_profile)

    structural_histogram = {name: 0 for name in STRUCTURAL_NAMES}
    structural_histogram["planar_multigraph"] = total_structural

    return {
        "schema": "fourcolor-section-9-2-closed-collar-winding-simple-patch-n6-detailed-taxonomy-audit-v1",
        "source": "Artifact audit for the exhaustive n6 closed-collar winding simple-patch verdicts",
        "n6_exact_patch_topology_count": N6_EXACT_PATCH_TOPOLOGY_COUNT,
        "prefix_slice_files": prefix_files,
        "template_blocker_files": list(TEMPLATE_BLOCKER_FILES),
        "prefix": {
            "processed_patch_topology_count": prefix_processed,
            "radial_order_case_count": prefix_radial,
            "profile_preserving_case_count": prefix_profile,
            "normal_form_prefix_passing_profile_case_count": prefix_passes,
            "first_failed_normal_form_histogram": dict(prefix_hist),
        },
        "template_blockers": {
            **dict(template_totals),
            "exact_template_histogram": dict(template_exact_hist),
            "first_failed_after_template_exclusion_histogram": dict(template_failure_hist),
        },
        "exhaustive": {
            "processed_patch_topology_count": total_processed,
            "radial_order_case_count": total_radial,
            "profile_preserving_case_count": total_profile,
            "structural_blocker_histogram": structural_histogram,
            "exact_template_blocker_count": total_exact,
            "diagonal_forward_template_count": template_exact_hist[
                "edges:g0:F1F0,g1:F4F5|sideCollar:g0:F1,g1:F5"
            ],
            "diagonal_reverse_template_count": template_exact_hist[
                "edges:g0:F4F5,g1:F1F0|sideCollar:g0:F5,g1:F1"
            ],
            "non_template_cyclic_cut_blocker_count": template_totals[
                "non_template_cyclic_cut_blocker_count"
            ],
            "cap5_like_blocker_count": template_totals["cap5_like_blocker_count"],
            "normal_form_after_template_exclusion_passing_count": template_totals[
                "normal_form_after_template_exclusion_passing_count"
            ],
            "residual_after_structural_and_exact_template_count": total_residual,
            "verdict": "n6_exhaustive_detailed_taxonomy_all_profile_cases_blocked",
        },
    }


def audit_radial_face_archive(results_dir: Path) -> dict[str, object]:
    sample_cases: list[tuple[int, int]] = []
    slice_cases: list[tuple[int, int]] = []
    sample_row_certificates: list[dict[str, object]] = []
    slice_row_certificates: list[dict[str, object]] = []
    sample_patch_indices: set[int] = set()
    slice_patch_indices: set[int] = set()
    sample_planar_rotations = 0
    slice_planar_rotations = 0
    sample_enumerated_rotations = 0
    slice_enumerated_rotations = 0
    sample_coherent_rotations = 0
    slice_coherent_rotations = 0
    sample_template_blockers = 0
    slice_template_blockers = 0
    max_radial_cut_hist: Counter[str] = Counter()
    slice_template_hist: Counter[str] = Counter()

    def audit_case(
        name: str, case: dict[str, object], source: str
    ) -> tuple[tuple[int, int], dict[str, object]]:
        patch_index = case.get("patch_index")
        radial_order_index = case.get("radial_order_index")
        if not isinstance(patch_index, int) or not isinstance(radial_order_index, int):
            raise ValueError(f"{name}: sample is missing integer patch/radial indices")
        embedding = case.get("embedding_audit")
        if not isinstance(embedding, dict):
            raise ValueError(f"{name}: sample {patch_index}/{radial_order_index} missing embedding_audit")
        assert_equal(f"{name}: embedding checked", bool_field(embedding, name, "checked"), True)
        assert_equal(
            f"{name}: enumerated rotations for {patch_index}/{radial_order_index}",
            int_field(embedding, name, "enumerated_rotation_system_count"),
            262_144,
        )
        assert_equal(
            f"{name}: planar rotations for {patch_index}/{radial_order_index}",
            int_field(embedding, name, "planar_rotation_system_count"),
            8,
        )
        assert_equal(
            f"{name}: radial-face coherent rotations for {patch_index}/{radial_order_index}",
            int_field(embedding, name, "radial_face_coherent_rotation_count"),
            0,
        )
        enumerated_rotation_count = int_field(
            embedding, name, "enumerated_rotation_system_count"
        )
        planar_rotation_count = int_field(embedding, name, "planar_rotation_system_count")
        coherent_rotation_count = int_field(
            embedding, name, "radial_face_coherent_rotation_count"
        )
        hist = dict_field(embedding, name, "max_radial_cut_edges_on_single_face_histogram")
        assert_equal(
            f"{name}: max radial-cut face histogram for {patch_index}/{radial_order_index}",
            hist,
            {"2": 8},
        )
        max_radial_cut_hist.update(hist)
        assert_equal(
            f"{name}: template blocker for {patch_index}/{radial_order_index}",
            case.get("template_exclusion_blocker"),
            "excluded_exact_diagonal_two_pole_template",
        )
        if source == "slice":
            assert_equal(
                f"{name}: exact template key for {patch_index}/{radial_order_index}",
                case.get("exact_template_key"),
                REVERSE_TEMPLATE_KEY,
            )
            cut = case.get("exact_template_cut")
            if not isinstance(cut, dict):
                raise ValueError(f"{name}: slice case {patch_index}/{radial_order_index} missing cut")
            assert_equal(
                f"{name}: exact template cut edges for {patch_index}/{radial_order_index}",
                cut.get("cut_edges"),
                ["g0:F4F5", "g1:F1F0"],
            )
            assert_equal(
                f"{name}: exact template side vertex count for {patch_index}/{radial_order_index}",
                cut.get("side_vertex_count"),
                4,
            )
            slice_template_hist.update([REVERSE_TEMPLATE_KEY])
        certificate: dict[str, object] = {
            "archive_family": source,
            "case": [patch_index, radial_order_index],
            "enumerated_rotation_system_count": enumerated_rotation_count,
            "max_radial_cut_edges_on_single_face_histogram": hist,
            "patch_index": patch_index,
            "planar_rotation_system_count": planar_rotation_count,
            "radial_face_coherent_rotation_count": coherent_rotation_count,
            "radial_order_index": radial_order_index,
            "source_file": name,
            "template_exclusion_blocker": case.get("template_exclusion_blocker"),
            "verdict": "row_has_no_radial_face_coherent_rotation",
        }
        if source == "slice":
            certificate["exact_template_key"] = case.get("exact_template_key")
        return (patch_index, radial_order_index), certificate

    for filename in RADIAL_FACE_SAMPLE_FILES:
        data = read_json(results_dir / filename)
        file_cases = samples(data, filename)
        for case in file_cases:
            pair, certificate = audit_case(filename, case, "sample")
            sample_cases.append(pair)
            sample_row_certificates.append(certificate)
            sample_patch_indices.add(pair[0])
            embedding = case["embedding_audit"]
            if not isinstance(embedding, dict):
                raise AssertionError("unreachable: embedding_audit was checked above")
            sample_enumerated_rotations += int_field(
                embedding, filename, "enumerated_rotation_system_count"
            )
            sample_planar_rotations += int_field(embedding, filename, "planar_rotation_system_count")
            sample_coherent_rotations += int_field(
                embedding, filename, "radial_face_coherent_rotation_count"
            )
            sample_template_blockers += 1

    for filename in RADIAL_FACE_SLICE_FILES:
        data = read_json(results_dir / filename)
        file_cases = samples(data, filename)
        block = summary(data, filename)
        assert_equal(
            f"{filename}: embedding audited case count",
            int_field(block, filename, "embedding_audited_case_count"),
            len(file_cases),
        )
        assert_equal(
            f"{filename}: radial-face coherent rotation count",
            int_field(block, filename, "radial_face_coherent_rotation_count"),
            0,
        )
        for case in file_cases:
            pair, certificate = audit_case(filename, case, "slice")
            slice_cases.append(pair)
            slice_row_certificates.append(certificate)
            slice_patch_indices.add(pair[0])
            embedding = case["embedding_audit"]
            if not isinstance(embedding, dict):
                raise AssertionError("unreachable: embedding_audit was checked above")
            slice_enumerated_rotations += int_field(
                embedding, filename, "enumerated_rotation_system_count"
            )
            slice_planar_rotations += int_field(embedding, filename, "planar_rotation_system_count")
            slice_coherent_rotations += int_field(
                embedding, filename, "radial_face_coherent_rotation_count"
            )
            slice_template_blockers += 1

    sample_case_set = set(sample_cases)
    slice_case_set = set(slice_cases)
    overlap = sample_case_set & slice_case_set
    unique_cases = sample_case_set | slice_case_set
    row_coverage_sample_cases = {
        (821205, 0),
        (821205, 1),
        (852969, 0),
        (852969, 1),
        (1000301, 0),
        (1000301, 1),
    }
    row_coverage_slice1000302_cases = {(1000788, 0), (1000788, 1)}
    row_coverage_slice1001289_cases = {(1001293, 0), (1001293, 1)}
    row_coverage_slice_cases = (
        row_coverage_slice1000302_cases | row_coverage_slice1001289_cases
    )
    row_coverage_sample_certificates = [
        certificate
        for certificate in sample_row_certificates
        if tuple(certificate["case"]) in row_coverage_sample_cases
    ]
    row_coverage_slice_certificates = [
        certificate
        for certificate in slice_row_certificates
        if tuple(certificate["case"]) in row_coverage_slice_cases
    ]
    row_coverage_certificates = sorted(
        row_coverage_sample_certificates + row_coverage_slice_certificates,
        key=lambda certificate: tuple(certificate["case"]),
    )
    unique_patch_indices = sample_patch_indices | slice_patch_indices
    rows_with_overlap = len(sample_cases) + len(slice_cases)
    planar_rows_with_overlap = sample_planar_rotations + slice_planar_rotations
    overlap_planar_rotations = 8 * len(overlap)
    unique_planar_rotations = planar_rows_with_overlap - overlap_planar_rotations

    assert_equal("sample cases", sorted(sample_case_set), [(821205, 0), (821205, 1), (852969, 0), (852969, 1), (1000301, 0), (1000301, 1)])
    assert_equal(
        "slice cases",
        sorted(slice_case_set),
        [
            (1000301, 0),
            (1000301, 1),
            (1000788, 0),
            (1000788, 1),
            (1001293, 0),
            (1001293, 1),
        ],
    )
    assert_equal("overlapping radial-order cases", sorted(overlap), [(1000301, 0), (1000301, 1)])
    assert_equal("row coverage sample cases", sorted(row_coverage_sample_cases), sorted(sample_case_set))
    assert_equal(
        "row coverage slice 1000302 cases",
        sorted(row_coverage_slice1000302_cases),
        [(1000788, 0), (1000788, 1)],
    )
    assert_equal(
        "row coverage slice 1001289 cases",
        sorted(row_coverage_slice1001289_cases),
        [(1001293, 0), (1001293, 1)],
    )
    assert_equal(
        "row coverage certificate cases",
        [tuple(certificate["case"]) for certificate in row_coverage_certificates],
        [
            (821205, 0),
            (821205, 1),
            (852969, 0),
            (852969, 1),
            (1000301, 0),
            (1000301, 1),
            (1000788, 0),
            (1000788, 1),
            (1001293, 0),
            (1001293, 1),
        ],
    )
    assert_equal("sample radial-order case count", len(sample_cases), 6)
    assert_equal("slice radial-order case count", len(slice_cases), 6)
    assert_equal("row coverage certificate count", len(row_coverage_certificates), 10)
    assert_equal("archive rows with overlap", rows_with_overlap, 12)
    assert_equal("unique audited radial-order case count", len(unique_cases), 10)
    assert_equal("unique audited patch topology count", len(unique_patch_indices), 5)
    assert_equal("sample enumerated rotations", sample_enumerated_rotations, 1_572_864)
    assert_equal("slice enumerated rotations", slice_enumerated_rotations, 1_572_864)
    assert_equal("sample planar rotations", sample_planar_rotations, 48)
    assert_equal("slice planar rotations", slice_planar_rotations, 48)
    assert_equal("planar rows with overlap", planar_rows_with_overlap, 96)
    assert_equal("unique planar rotations", unique_planar_rotations, 80)
    assert_equal("sample coherent rotations", sample_coherent_rotations, 0)
    assert_equal("slice coherent rotations", slice_coherent_rotations, 0)
    assert_equal("archive coherent rotations", sample_coherent_rotations + slice_coherent_rotations, 0)
    assert_equal("sample template blockers", sample_template_blockers, 6)
    assert_equal("slice template blockers", slice_template_blockers, 6)
    assert_equal("slice template histogram", dict(slice_template_hist), {REVERSE_TEMPLATE_KEY: 6})
    assert_equal("max radial-cut histogram", dict(max_radial_cut_hist), {"2": 96})

    return {
        "schema": "fourcolor-section-9-2-closed-collar-winding-simple-patch-n6-radial-face-archive-audit-v1",
        "source": "Artifact audit for radial-face annular embedding verdicts",
        "sample_archive_files": list(RADIAL_FACE_SAMPLE_FILES),
        "slice_archive_files": list(RADIAL_FACE_SLICE_FILES),
        "sample_archive_json_file_count": len(RADIAL_FACE_SAMPLE_FILES),
        "slice_archive_json_file_count": len(RADIAL_FACE_SLICE_FILES),
        "total_archive_json_file_count": len(RADIAL_FACE_SAMPLE_FILES) + len(RADIAL_FACE_SLICE_FILES),
        "sample_cases": sorted(sample_case_set),
        "slice_cases": sorted(slice_case_set),
        "overlapping_cases": sorted(overlap),
        "sample_row_certificates": sorted(
            sample_row_certificates, key=lambda certificate: tuple(certificate["case"])
        ),
        "slice_row_certificates": sorted(
            slice_row_certificates, key=lambda certificate: tuple(certificate["case"])
        ),
        "row_coverage_sample_cases": sorted(row_coverage_sample_cases),
        "row_coverage_slice_cases": sorted(row_coverage_slice_cases),
        "row_coverage_slice1000302_cases": sorted(row_coverage_slice1000302_cases),
        "row_coverage_slice1001289_cases": sorted(row_coverage_slice1001289_cases),
        "row_coverage_certificates": row_coverage_certificates,
        "row_coverage_certificate_count": len(row_coverage_certificates),
        "row_coverage_verdict": "radial_face_row_coverage_all_planar_rotations_incoherent",
        "sample_archive_radial_order_case_count": len(sample_cases),
        "slice_archive_radial_order_case_count": len(slice_cases),
        "archive_radial_order_rows_with_overlap": rows_with_overlap,
        "overlapping_radial_order_case_count": len(overlap),
        "unique_audited_radial_order_case_count": len(unique_cases),
        "unique_audited_patch_topology_count": len(unique_patch_indices),
        "sample_enumerated_rotation_system_count": sample_enumerated_rotations,
        "slice_enumerated_rotation_system_count": slice_enumerated_rotations,
        "sample_planar_rotation_system_count": sample_planar_rotations,
        "slice_planar_rotation_system_count": slice_planar_rotations,
        "planar_rotation_system_rows_with_overlap": planar_rows_with_overlap,
        "unique_planar_rotation_system_count": unique_planar_rotations,
        "archive_radial_face_coherent_rotation_count": sample_coherent_rotations + slice_coherent_rotations,
        "sample_exact_template_blocker_count": sample_template_blockers,
        "slice_exact_template_blocker_count": slice_template_blockers,
        "slice_exact_template_histogram": dict(slice_template_hist),
        "max_radial_cut_edges_on_single_face_histogram": dict(max_radial_cut_hist),
        "verdict": "radial_face_archive_all_planar_rotations_incoherent",
    }


def audit_n8_frontier(prefix_results_dir: Path, stratified_results_dir: Path) -> dict[str, object]:
    prefix_totals: Counter[str] = Counter()
    prefix_files: list[str] = []
    prefix_ranges: list[dict[str, int]] = []

    for filename in N8_TEMPLATE_BLOCKER_FILES:
        data = read_json(prefix_results_dir / filename)
        search = object_field(data, filename, "search")
        block = summary(data, filename)
        assert_equal(
            f"{filename}: internal vertex count",
            int_field(search, filename, "internal_vertex_count"),
            8,
        )
        assert_equal(
            f"{filename}: verdict",
            block.get("verdict"),
            "template_exclusion_slice_found_no_profile_preserving_patch",
        )
        processed = int_field(block, filename, "processed_patch_topology_count")
        radial = int_field(block, filename, "radial_order_case_count")
        profile = int_field(block, filename, "profile_preserving_case_count")
        structural = int_field(block, filename, "structural_first_blocker_count")
        exact = int_field(block, filename, "exact_template_blocker_count")
        non_template = int_field(block, filename, "non_template_cyclic_cut_blocker_count")
        cap5 = int_field(block, filename, "cap5_like_blocker_count")
        passing = int_field(block, filename, "normal_form_after_template_exclusion_passing_count")
        assert_equal(f"{filename}: radial count", radial, 2 * processed)
        assert_equal(f"{filename}: profile-preserving count", profile, 0)
        assert_equal(f"{filename}: structural blocker count", structural, 0)
        assert_equal(f"{filename}: exact-template blocker count", exact, 0)
        assert_equal(f"{filename}: non-template cyclic-cut blocker count", non_template, 0)
        assert_equal(f"{filename}: cap5-like blocker count", cap5, 0)
        assert_equal(f"{filename}: post-template pass count", passing, 0)
        assert_equal(
            f"{filename}: exact template histogram",
            dict_field(block, filename, "exact_template_histogram"),
            {},
        )
        assert_equal(
            f"{filename}: post-template failure histogram",
            dict_field(block, filename, "first_failed_after_template_exclusion_histogram"),
            {},
        )
        start = int_field(search, filename, "patch_start_index")
        next_start = int_field(search, filename, "next_patch_start_index")
        assert_equal(f"{filename}: next start", start + processed, next_start)
        prefix_files.append(filename)
        prefix_ranges.append(
            {
                "patch_start_index": start,
                "next_patch_start_index": next_start,
                "processed_patch_topology_count": processed,
            }
        )
        prefix_totals["processed_patch_topology_count"] += processed
        prefix_totals["radial_order_case_count"] += radial
        prefix_totals["profile_preserving_case_count"] += profile
        prefix_totals["structural_first_blocker_count"] += structural
        prefix_totals["exact_template_blocker_count"] += exact
        prefix_totals["non_template_cyclic_cut_blocker_count"] += non_template
        prefix_totals["cap5_like_blocker_count"] += cap5
        prefix_totals["normal_form_after_template_exclusion_passing_count"] += passing

    assert_equal("n8 prefix first start", prefix_ranges[0]["patch_start_index"], 0)
    for left, right in zip(prefix_ranges, prefix_ranges[1:]):
        assert_equal(
            "n8 prefix contiguous slices",
            left["next_patch_start_index"],
            right["patch_start_index"],
        )
    assert_equal("n8 prefix end", prefix_ranges[-1]["next_patch_start_index"], 2_000_000)
    assert_equal("n8 prefix processed count", prefix_totals["processed_patch_topology_count"], 2_000_000)
    assert_equal("n8 prefix radial-order count", prefix_totals["radial_order_case_count"], 4_000_000)
    assert_equal("n8 prefix profile-preserving count", prefix_totals["profile_preserving_case_count"], 0)
    assert_equal(
        "n8 prefix post-template pass count",
        prefix_totals["normal_form_after_template_exclusion_passing_count"],
        0,
    )
    if not prefix_totals["processed_patch_topology_count"] < N8_EXACT_PATCH_TOPOLOGY_COUNT:
        raise AssertionError("n8 prefix unexpectedly exhausts the exact topology space")

    stratified_data = read_json(stratified_results_dir / N8_STRATIFIED_SAMPLE_FILE)
    stratified_search = object_field(stratified_data, N8_STRATIFIED_SAMPLE_FILE, "search")
    stratified_summary = summary(stratified_data, N8_STRATIFIED_SAMPLE_FILE)
    assert_equal(
        "n8 stratified internal vertex count",
        int_field(stratified_search, N8_STRATIFIED_SAMPLE_FILE, "internal_vertex_count"),
        8,
    )
    assert_equal(
        "n8 stratified exact patch count",
        int_field(stratified_search, N8_STRATIFIED_SAMPLE_FILE, "exact_patch_topology_count"),
        N8_EXACT_PATCH_TOPOLOGY_COUNT,
    )
    sampled_indices = stratified_search.get("sampled_patch_indices")
    if not isinstance(sampled_indices, list) or not all(
        isinstance(index, int) for index in sampled_indices
    ):
        raise ValueError("n8 stratified sample indices are not an integer list")
    assert_equal("n8 stratified sample count", len(sampled_indices), 33)
    assert_equal("n8 stratified first sample", sampled_indices[0], 0)
    assert_equal(
        "n8 stratified last sample",
        sampled_indices[-1],
        N8_EXACT_PATCH_TOPOLOGY_COUNT - 1,
    )
    assert_equal(
        "n8 stratified verdict",
        stratified_summary.get("verdict"),
        "template_exclusion_index_sample_found_no_profile_preserving_patch",
    )
    assert_equal(
        "n8 stratified radial-order count",
        int_field(stratified_summary, N8_STRATIFIED_SAMPLE_FILE, "radial_order_case_count"),
        66,
    )
    assert_equal(
        "n8 stratified profile-preserving count",
        int_field(stratified_summary, N8_STRATIFIED_SAMPLE_FILE, "profile_preserving_case_count"),
        0,
    )
    assert_equal(
        "n8 stratified post-template pass count",
        int_field(
            stratified_summary,
            N8_STRATIFIED_SAMPLE_FILE,
            "normal_form_after_template_exclusion_passing_count",
        ),
        0,
    )
    assert_equal(
        "n8 stratified exact template histogram",
        dict_field(stratified_summary, N8_STRATIFIED_SAMPLE_FILE, "exact_template_histogram"),
        {},
    )
    assert_equal(
        "n8 stratified post-template failure histogram",
        dict_field(
            stratified_summary,
            N8_STRATIFIED_SAMPLE_FILE,
            "first_failed_after_template_exclusion_histogram",
        ),
        {},
    )

    return {
        "schema": "fourcolor-section-9-2-closed-collar-winding-simple-patch-n8-frontier-audit-v1",
        "source": "Artifact audit for n8 closed-collar winding simple-patch frontier verdicts",
        "n8_exact_patch_topology_count": N8_EXACT_PATCH_TOPOLOGY_COUNT,
        "prefix_template_blocker_files": prefix_files,
        "prefix_ranges": prefix_ranges,
        "prefix": {
            **dict(prefix_totals),
            "verdict": "n8_first_2000000_found_no_profile_preserving_patch",
        },
        "stratified_sample_file": N8_STRATIFIED_SAMPLE_FILE,
        "stratified_sample": {
            "sampled_patch_indices": sampled_indices,
            "sampled_patch_topology_count": len(sampled_indices),
            "radial_order_case_count": int_field(
                stratified_summary, N8_STRATIFIED_SAMPLE_FILE, "radial_order_case_count"
            ),
            "profile_preserving_case_count": int_field(
                stratified_summary,
                N8_STRATIFIED_SAMPLE_FILE,
                "profile_preserving_case_count",
            ),
            "normal_form_after_template_exclusion_passing_count": int_field(
                stratified_summary,
                N8_STRATIFIED_SAMPLE_FILE,
                "normal_form_after_template_exclusion_passing_count",
            ),
            "verdict": "n8_stratified_33_found_no_profile_preserving_patch",
        },
        "remaining_prefix_unprocessed_patch_topology_count": (
            N8_EXACT_PATCH_TOPOLOGY_COUNT
            - prefix_totals["processed_patch_topology_count"]
        ),
        "verdict": "n8_frontier_no_profile_preserving_cases_in_checked_prefix_or_stratified_sample",
    }


def write_json(path: Path, data: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    os.replace(tmp, path)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--mode",
        choices=("taxonomy", "radial-face", "n8", "all"),
        default="taxonomy",
        help="which archived verdict family to audit",
    )
    parser.add_argument(
        "--results-dir",
        type=Path,
        default=DEFAULT_TAXONOMY_RESULTS_DIR,
        help="directory containing archived taxonomy verdict JSON files",
    )
    parser.add_argument(
        "--radial-face-results-dir",
        type=Path,
        default=DEFAULT_RADIAL_FACE_RESULTS_DIR,
        help="directory containing archived radial-face verdict JSON files",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_TAXONOMY_OUTPUT,
        help="write the audited taxonomy JSON",
    )
    parser.add_argument(
        "--radial-face-output",
        type=Path,
        default=DEFAULT_RADIAL_FACE_OUTPUT,
        help="write the audited radial-face archive JSON",
    )
    parser.add_argument(
        "--n8-stratified-results-dir",
        type=Path,
        default=DEFAULT_RADIAL_FACE_RESULTS_DIR,
        help="directory containing the archived n8 stratified verdict JSON file",
    )
    parser.add_argument(
        "--n8-output",
        type=Path,
        default=DEFAULT_N8_OUTPUT,
        help="write the audited n8 frontier JSON",
    )
    parser.add_argument("--check-only", action="store_true", help="skip writing output")
    args = parser.parse_args()

    reports: dict[str, object] = {}
    if args.mode in ("taxonomy", "all"):
        taxonomy_report = audit(args.results_dir)
        reports["taxonomy"] = taxonomy_report
        if not args.check_only:
            write_json(args.output, taxonomy_report)
    if args.mode in ("radial-face", "all"):
        radial_face_report = audit_radial_face_archive(args.radial_face_results_dir)
        reports["radial_face_archive"] = radial_face_report
        if not args.check_only:
            write_json(args.radial_face_output, radial_face_report)
    if args.mode in ("n8", "all"):
        n8_report = audit_n8_frontier(args.results_dir, args.n8_stratified_results_dir)
        reports["n8_frontier"] = n8_report
        if not args.check_only:
            write_json(args.n8_output, n8_report)

    if args.mode == "taxonomy":
        print(json.dumps(reports["taxonomy"], indent=2, sort_keys=True))
    elif args.mode == "radial-face":
        print(json.dumps(reports["radial_face_archive"], indent=2, sort_keys=True))
    elif args.mode == "n8":
        print(json.dumps(reports["n8_frontier"], indent=2, sort_keys=True))
    else:
        print(json.dumps(reports, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
