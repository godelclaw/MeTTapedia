#!/usr/bin/env python3
"""Verify the committed n8 finite-frontier archive for the winding witness."""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_INPUT = Path(
    "results/fourcolor/"
    "section92_closed_collar_winding_simple_patch_n8_frontier_audit.json"
)
DEFAULT_OUTPUT = Path(
    "results/fourcolor/"
    "section92_closed_collar_winding_realizability_n8_frontier_verdict.json"
)
DEFAULT_SOURCE_RESULTS_DIR = (
    REPO_ROOT / "lean" / "mettapedia" / "results" / "fourcolor"
)
DEFAULT_STRATIFIED_RESULTS_DIR = REPO_ROOT / "results" / "fourcolor"
EXPECTED_SCHEMA = (
    "fourcolor-section-9-2-closed-collar-winding-simple-patch-n8-"
    "frontier-audit-v1"
)
EXPECTED_SAMPLE_SCHEMA = (
    "fourcolor-section-9-2-closed-collar-winding-simple-patch-"
    "template-blocker-index-sample-v1"
)
EXPECTED_FRONTIER_VERDICT = (
    "n8_frontier_no_profile_preserving_cases_in_checked_prefix_or_"
    "stratified_sample"
)
EXPECTED_PREFIX_VERDICT = "n8_first_6000000_found_no_profile_preserving_patch"
EXPECTED_SAMPLE_VERDICT = "n8_stratified_65_found_no_profile_preserving_patch"
EXPECTED_SAMPLE_FILE_VERDICT = "template_exclusion_index_sample_found_no_profile_preserving_patch"
EXPECTED_CASE_VERDICT = "no_profile_preserving_extension"
EXPECTED_PROFILE_FAILURE_KINDS = {
    "terminal_precolor_conflict",
    "no_proper_tait_extension",
    "proper_extensions_wrong_profile",
}
OUTPUT_SCHEMA = "fourcolor-section-9-2-winding-realizability-n8-frontier-verdict-v1"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Validate internal consistency of the n8 winding finite-frontier "
            "archive and report which source payloads are present."
        )
    )
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument(
        "--source-results-dir",
        type=Path,
        default=DEFAULT_SOURCE_RESULTS_DIR,
        help="directory containing the prefix source payload JSON files named by the archive",
    )
    parser.add_argument(
        "--stratified-results-dir",
        type=Path,
        default=DEFAULT_STRATIFIED_RESULTS_DIR,
        help="directory containing the stratified-sample source payload JSON file",
    )
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


def fail(failures: list[str], label: str, detail: str) -> None:
    failures.append(f"{label}: {detail}")


def gap(gaps: list[str], label: str, detail: str) -> None:
    gaps.append(f"{label}: {detail}")


def require_zero_counts(counts: dict[str, Any], names: list[str], failures: list[str], label: str) -> None:
    for name in names:
        if int(counts.get(name, -1)) != 0:
            fail(failures, label, f"{name} is nonzero")


def sorted_counter(counter: Counter[str]) -> dict[str, int]:
    return dict(sorted(counter.items()))


def verify_no_profile_case_verdicts(
    case_verdicts: Any,
    sampled_indices: list[int],
    radial_cases: int,
    failures: list[str],
    gaps: list[str],
    label: str,
) -> dict[str, Any] | None:
    if case_verdicts is None:
        gap(gaps, label, "stratified source has no per-case verdict payloads")
        return None
    if not isinstance(case_verdicts, list):
        fail(failures, label, "case_verdicts is not a list")
        return None
    if len(case_verdicts) != radial_cases:
        fail(failures, label, "case verdict count does not match radial cases")

    sampled_index_set = set(sampled_indices)
    expected_pairs = {
        (patch_index, radial_order_index)
        for patch_index in sampled_indices
        for radial_order_index in (0, 1)
    }
    seen_pairs: set[tuple[int, int]] = set()
    profile_failure_kind_histogram: Counter[str] = Counter()
    first_blocking_state_index_histogram: Counter[str] = Counter()
    wrong_profile_proper_extension_count_histogram: Counter[str] = Counter()
    for index, item in enumerate(case_verdicts):
        if not isinstance(item, dict):
            fail(failures, label, f"case_verdicts[{index}] is not an object")
            continue
        patch_index = item.get("patch_index")
        radial_order_index = item.get("radial_order_index")
        if not isinstance(patch_index, int) or not isinstance(radial_order_index, int):
            fail(failures, label, f"case_verdicts[{index}] has non-integer index")
            continue
        pair = (patch_index, radial_order_index)
        if pair in seen_pairs:
            fail(failures, label, f"duplicate case verdict for {pair}")
        seen_pairs.add(pair)
        if patch_index not in sampled_index_set:
            fail(failures, label, f"case verdict patch index {patch_index} not sampled")
        if radial_order_index not in (0, 1):
            fail(failures, label, f"invalid radial order index {radial_order_index}")
        radial_order = item.get("radial_order")
        if (
            not isinstance(radial_order, list)
            or len(radial_order) != 2
            or not all(isinstance(edge, str) for edge in radial_order)
        ):
            fail(failures, label, f"case_verdicts[{index}] has invalid radial_order")
        if item.get("profile_preserving") is not False:
            fail(failures, label, f"case_verdicts[{index}] is profile-preserving")
        if item.get("verdict") != EXPECTED_CASE_VERDICT:
            fail(failures, label, f"case_verdicts[{index}] has unexpected verdict")
        first_blocking_state_index = item.get("first_blocking_state_index")
        if not isinstance(first_blocking_state_index, int):
            fail(failures, label, f"case_verdicts[{index}] has invalid blocking state")
        else:
            first_blocking_state_index_histogram[str(first_blocking_state_index)] += 1
        failure_kind = item.get("profile_failure_kind")
        if not isinstance(failure_kind, str) or failure_kind not in EXPECTED_PROFILE_FAILURE_KINDS:
            fail(failures, label, f"case_verdicts[{index}] has invalid failure kind")
            failure_kind = ""
        else:
            profile_failure_kind_histogram[failure_kind] += 1
        proper_count = item.get("proper_tait_extension_count")
        matching_count = item.get("matching_profile_extension_count")
        variant_count = item.get("profile_variant_count")
        if not isinstance(proper_count, int) or proper_count < 0:
            fail(failures, label, f"case_verdicts[{index}] has invalid proper count")
            proper_count = -1
        if matching_count != 0:
            fail(failures, label, f"case_verdicts[{index}] has nonzero matching count")
        if not isinstance(variant_count, int) or variant_count < 0:
            fail(failures, label, f"case_verdicts[{index}] has invalid profile variant count")
            variant_count = -1
        conflicts = item.get("terminal_precolor_conflict_vertices")
        if not isinstance(conflicts, list) or not all(
            isinstance(vertex, str) for vertex in conflicts
        ):
            fail(failures, label, f"case_verdicts[{index}] has invalid conflict vertices")
            conflicts = []
        if failure_kind == "terminal_precolor_conflict":
            if not conflicts:
                fail(failures, label, f"case_verdicts[{index}] lacks conflict vertices")
            if proper_count != 0 or variant_count != 0:
                fail(failures, label, f"case_verdicts[{index}] terminal conflict has extensions")
        elif failure_kind == "no_proper_tait_extension":
            if conflicts:
                fail(failures, label, f"case_verdicts[{index}] no-proper case has conflicts")
            if proper_count != 0 or variant_count != 0:
                fail(failures, label, f"case_verdicts[{index}] no-proper case has extensions")
        elif failure_kind == "proper_extensions_wrong_profile":
            if conflicts:
                fail(failures, label, f"case_verdicts[{index}] wrong-profile case has conflicts")
            if proper_count <= 0:
                fail(failures, label, f"case_verdicts[{index}] wrong-profile case lacks extensions")
            if variant_count <= 0:
                fail(failures, label, f"case_verdicts[{index}] wrong-profile case lacks profiles")
            if proper_count > 0:
                wrong_profile_proper_extension_count_histogram[str(proper_count)] += 1

    if seen_pairs != expected_pairs:
        missing = expected_pairs - seen_pairs
        extra = seen_pairs - expected_pairs
        if missing:
            fail(failures, label, f"missing {len(missing)} sampled radial-order verdicts")
        if extra:
            fail(failures, label, f"found {len(extra)} unexpected radial-order verdicts")
    return {
        "source_case_verdict_count": len(case_verdicts),
        "profile_failure_kind_histogram":
            sorted_counter(profile_failure_kind_histogram),
        "first_blocking_state_index_histogram":
            sorted_counter(first_blocking_state_index_histogram),
        "wrong_profile_proper_extension_count_histogram":
            sorted_counter(wrong_profile_proper_extension_count_histogram),
    }


def verify_prefix(frontier: dict[str, Any], results_dir: Path, failures: list[str], gaps: list[str]) -> dict[str, Any]:
    prefix = frontier.get("prefix", {})
    ranges = frontier.get("prefix_ranges", [])
    blocker_files = frontier.get("prefix_template_blocker_files", [])
    label = "prefix"

    if prefix.get("verdict") != EXPECTED_PREFIX_VERDICT:
        fail(failures, label, "unexpected prefix verdict")
    require_zero_counts(
        prefix,
        [
            "profile_preserving_case_count",
            "normal_form_after_template_exclusion_passing_count",
            "structural_first_blocker_count",
            "exact_template_blocker_count",
            "non_template_cyclic_cut_blocker_count",
            "cap5_like_blocker_count",
        ],
        failures,
        label,
    )

    if not isinstance(ranges, list) or not ranges:
        fail(failures, label, "missing prefix ranges")
        ranges = []
    processed_sum = 0
    expected_start = 0
    for index, item in enumerate(ranges):
        start = int(item.get("patch_start_index", -1))
        next_start = int(item.get("next_patch_start_index", -1))
        processed = int(item.get("processed_patch_topology_count", -1))
        if start != expected_start:
            fail(failures, label, f"range {index} is not contiguous")
        if next_start - start != processed:
            fail(failures, label, f"range {index} processed count mismatch")
        expected_start = next_start
        processed_sum += processed

    processed_total = int(prefix.get("processed_patch_topology_count", -1))
    if processed_sum != processed_total:
        fail(failures, label, "prefix range sum mismatch")
    if int(prefix.get("radial_order_case_count", -1)) != 2 * processed_total:
        fail(failures, label, "radial order case count is not twice processed patches")

    exact_total = int(frontier.get("n8_exact_patch_topology_count", -1))
    remaining = int(frontier.get("remaining_prefix_unprocessed_patch_topology_count", -1))
    if exact_total - processed_total != remaining:
        fail(failures, label, "remaining prefix count mismatch")

    missing_files: list[str] = []
    present_files: list[str] = []
    if not isinstance(blocker_files, list):
        fail(failures, label, "prefix blocker file list is not a list")
        blocker_files = []
    if len(blocker_files) != len(ranges):
        fail(failures, label, "prefix blocker file count does not match ranges")
    for name in blocker_files:
        if not isinstance(name, str):
            fail(failures, label, "prefix blocker file entry is not a string")
            continue
        if (results_dir / name).exists():
            present_files.append(name)
        else:
            missing_files.append(name)
    if missing_files:
        gap(gaps, label, f"{len(missing_files)} prefix source files are absent")

    return {
        "processed_patch_topology_count": processed_total,
        "radial_order_case_count": prefix.get("radial_order_case_count"),
        "range_count": len(ranges),
        "present_source_file_count": len(present_files),
        "missing_source_file_count": len(missing_files),
        "missing_source_files": missing_files,
    }


def verify_stratified_sample(
    frontier: dict[str, Any],
    results_dir: Path,
    failures: list[str],
    gaps: list[str],
) -> dict[str, Any]:
    label = "stratified_sample"
    sample = frontier.get("stratified_sample", {})
    sample_file_name = frontier.get("stratified_sample_file")
    if sample.get("verdict") != EXPECTED_SAMPLE_VERDICT:
        fail(failures, label, "unexpected frontier sample verdict")
    require_zero_counts(
        sample,
        [
            "profile_preserving_case_count",
            "normal_form_after_template_exclusion_passing_count",
        ],
        failures,
        label,
    )
    sampled_indices = sample.get("sampled_patch_indices", [])
    sampled_count = int(sample.get("sampled_patch_topology_count", -1))
    radial_cases = int(sample.get("radial_order_case_count", -1))
    if len(sampled_indices) != sampled_count:
        fail(failures, label, "sampled index count mismatch")
    if radial_cases != 2 * sampled_count:
        fail(failures, label, "radial order case count is not twice sampled patches")
    if len(set(sampled_indices)) != len(sampled_indices):
        fail(failures, label, "sampled indices are not unique")
    exact_total = int(frontier.get("n8_exact_patch_topology_count", -1))
    if any((not isinstance(index, int)) or index < 0 or index >= exact_total for index in sampled_indices):
        fail(failures, label, "sampled index outside exact topology range")

    sample_payload_present = False
    sample_payload_summary: dict[str, Any] | None = None
    sample_case_verdict_summary: dict[str, Any] | None = None
    if not isinstance(sample_file_name, str):
        fail(failures, label, "missing stratified_sample_file")
    elif not (results_dir / sample_file_name).exists():
        gap(gaps, label, "stratified sample source file is absent")
    else:
        sample_payload_present = True
        payload = load_json(results_dir / sample_file_name)
        if payload.get("schema") != EXPECTED_SAMPLE_SCHEMA:
            fail(failures, label, "unexpected stratified sample schema")
        summary = payload.get("summary", {})
        search = payload.get("search", {})
        samples = payload.get("samples", [])
        if summary.get("verdict") != EXPECTED_SAMPLE_FILE_VERDICT:
            fail(failures, label, "unexpected stratified sample file verdict")
        for key in [
            "sampled_patch_topology_count",
            "radial_order_case_count",
            "profile_preserving_case_count",
            "normal_form_after_template_exclusion_passing_count",
        ]:
            if summary.get(key) != sample.get(key):
                fail(failures, label, f"sample summary mismatch for {key}")
        if search.get("sampled_patch_indices") != sampled_indices:
            fail(failures, label, "sampled indices mismatch source file")
        if search.get("exact_patch_topology_count") != exact_total:
            fail(failures, label, "exact topology count mismatch source file")
        if summary.get("case_verdict_count") != radial_cases:
            fail(failures, label, "sample case verdict count mismatch")
        if samples != []:
            fail(failures, label, "expected empty per-sample payload list")
        sample_case_verdict_summary = verify_no_profile_case_verdicts(
            payload.get("case_verdicts"),
            sampled_indices,
            radial_cases,
            failures,
            gaps,
            label,
        )
        if sample_case_verdict_summary is not None:
            for key in [
                "profile_failure_kind_histogram",
                "first_blocking_state_index_histogram",
                "wrong_profile_proper_extension_count_histogram",
            ]:
                if summary.get(key) != sample_case_verdict_summary.get(key):
                    fail(failures, label, f"sample summary mismatch for {key}")
        sample_payload_summary = summary

    return {
        "sampled_patch_topology_count": sampled_count,
        "radial_order_case_count": radial_cases,
        "source_file": sample_file_name,
        "source_file_present": sample_payload_present,
        "source_summary": sample_payload_summary,
        "source_case_verdicts": sample_case_verdict_summary,
    }


def main() -> int:
    args = parse_args()
    frontier = load_json(args.input)
    failures: list[str] = []
    evidence_gaps: list[str] = []

    if frontier.get("schema") != EXPECTED_SCHEMA:
        fail(failures, "frontier", "unexpected schema")
    if frontier.get("verdict") != EXPECTED_FRONTIER_VERDICT:
        fail(failures, "frontier", "unexpected frontier verdict")

    prefix_summary = verify_prefix(
        frontier, args.source_results_dir, failures, evidence_gaps
    )
    sample_summary = verify_stratified_sample(
        frontier, args.stratified_results_dir, failures, evidence_gaps
    )

    if failures:
        verdict = "n8_frontier_archive_verification_failed"
    elif evidence_gaps:
        verdict = "n8_frontier_partially_verified_with_evidence_gaps"
    else:
        verdict = "n8_frontier_archive_fully_verified_from_sources"

    output = {
        "schema": OUTPUT_SCHEMA,
        "input_archive": args.input.name,
        "verdict": verdict,
        "frontier_verdict": frontier.get("verdict"),
        "prefix": prefix_summary,
        "stratified_sample": sample_summary,
        "evidence_gaps": evidence_gaps,
        "failures": failures,
    }
    write_json(args.output, output)
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
