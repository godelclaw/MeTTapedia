#!/usr/bin/env python3
"""Audit archived closed-collar winding simple-patch verdict artifacts."""

from __future__ import annotations

from collections import Counter
from pathlib import Path
import argparse
import json
import os


N6_EXACT_PATCH_TOPOLOGY_COUNT = 1_858_980
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


def write_json(path: Path, data: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    os.replace(tmp, path)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--results-dir",
        type=Path,
        default=Path("results/fourcolor"),
        help="directory containing archived verdict JSON files",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(
            "results/fourcolor/"
            "section92_closed_collar_winding_simple_patch_n6_detailed_taxonomy_audit.json"
        ),
        help="write the audited taxonomy JSON",
    )
    parser.add_argument("--check-only", action="store_true", help="skip writing output")
    args = parser.parse_args()

    report = audit(args.results_dir)
    if not args.check_only:
        write_json(args.output, report)
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
