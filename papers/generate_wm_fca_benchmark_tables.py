#!/usr/bin/env python3
"""Generate the WM/FCA paper tables from pinned CeTTa benchmark artifacts.

The generator fails closed: absent fields, drifted hashes, incomplete grids, or
disagreeing exact oracles prevent TeX emission.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from typing import Any


class ReceiptError(ValueError):
    """A required benchmark claim is absent or internally inconsistent."""


def require_dict(value: Any, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise ReceiptError(f"{label} must be an object")
    return value


def require_list(value: Any, label: str) -> list[Any]:
    if not isinstance(value, list):
        raise ReceiptError(f"{label} must be an array")
    return value


def require_number(value: Any, label: str) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise ReceiptError(f"{label} must be numeric")
    return float(value)


def require_int(value: Any, label: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise ReceiptError(f"{label} must be an integer")
    return value


def require_string(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise ReceiptError(f"{label} must be a nonempty string")
    return value


def load_json(path: Path) -> dict[str, Any]:
    try:
        return require_dict(json.loads(path.read_text(encoding="utf-8")), str(path))
    except FileNotFoundError as exc:
        raise ReceiptError(f"missing required artifact: {path}") from exc


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def relative_file(root: Path, value: Any, label: str) -> Path:
    relative = Path(require_string(value, label))
    if relative.is_absolute():
        raise ReceiptError(f"{label} must be relative")
    resolved = (root / relative).resolve()
    try:
        resolved.relative_to(root)
    except ValueError as exc:
        raise ReceiptError(f"{label} escapes the benchmark repository") from exc
    if not resolved.is_file():
        raise ReceiptError(f"missing pinned file for {label}: {relative}")
    return resolved


def read_ergonomics_receipt(benchmark_root: Path) -> dict[str, Any]:
    root = benchmark_root / "benchmarks" / "wm_fca"
    protocol_path = root / "ergonomics_protocol.json"
    receipt_path = root / "results" / "wm_fca_ergonomics_v1_receipt.json"
    protocol = load_json(protocol_path)
    receipt = load_json(receipt_path)
    if protocol.get("schema") != "wm-fca-ergonomics-protocol-v1":
        raise ReceiptError("unexpected ergonomics protocol schema")
    if receipt.get("schema") != "wm-fca-ergonomics-receipt-v1":
        raise ReceiptError("unexpected ergonomics receipt schema")
    if receipt.get("measurement_kind") != "descriptive_microbenchmark":
        raise ReceiptError("unexpected ergonomics measurement kind")
    if receipt.get("measurement_scope") != protocol.get("measurement_scope"):
        raise ReceiptError("ergonomics measurement scope drifted")
    expected_protocol_path = str(protocol_path.relative_to(benchmark_root))
    if receipt.get("protocol") != expected_protocol_path:
        raise ReceiptError("ergonomics protocol path drifted")
    if receipt.get("protocol_sha256") != digest(protocol_path):
        raise ReceiptError("ergonomics receipt does not pin its protocol")

    runner = require_dict(receipt.get("runner"), "ergonomics.runner")
    runner_path = relative_file(
        benchmark_root, runner.get("path"), "ergonomics.runner.path"
    )
    if runner.get("sha256") != digest(runner_path):
        raise ReceiptError("ergonomics receipt does not pin its runner")

    protocol_cases = require_list(protocol.get("cases"), "ergonomics cases")
    measurements = require_list(receipt.get("measurements"), "ergonomics measurements")
    warmups = require_int(
        protocol.get("warmup_runs_per_case"), "ergonomics warmup runs"
    )
    if warmups <= 0:
        raise ReceiptError("ergonomics warmup count must be positive")
    if len(protocol_cases) != len(measurements):
        raise ReceiptError("ergonomics measurement cardinality drifted")
    by_id: dict[str, dict[str, Any]] = {}
    for measurement_value in measurements:
        measurement = require_dict(measurement_value, "ergonomics measurement")
        case_id = require_string(measurement.get("id"), "ergonomics measurement id")
        if case_id in by_id:
            raise ReceiptError(f"duplicate ergonomics measurement: {case_id}")
        by_id[case_id] = measurement

    for case_value in protocol_cases:
        case = require_dict(case_value, "ergonomics case")
        case_id = require_string(case.get("id"), "ergonomics case id")
        measurement = by_id.get(case_id)
        if measurement is None:
            raise ReceiptError(f"missing ergonomics measurement: {case_id}")
        program = relative_file(
            benchmark_root, case.get("program"), f"{case_id}.program"
        )
        expected = relative_file(
            benchmark_root, case.get("expected"), f"{case_id}.expected"
        )
        if measurement.get("program") != case.get("program"):
            raise ReceiptError(f"{case_id} program path drifted")
        if measurement.get("expected") != case.get("expected"):
            raise ReceiptError(f"{case_id} expected path drifted")
        if measurement.get("program_sha256") != digest(program):
            raise ReceiptError(f"{case_id} program hash drifted")
        if measurement.get("expected_sha256") != digest(expected):
            raise ReceiptError(f"{case_id} golden hash drifted")
        if measurement.get("golden_output_bytes") != expected.stat().st_size:
            raise ReceiptError(f"{case_id} golden byte count drifted")
        if measurement.get("golden_output_rows") != len(expected.read_bytes().splitlines()):
            raise ReceiptError(f"{case_id} golden row count drifted")
        if measurement.get("all_runs_golden_equal") is not True:
            raise ReceiptError(f"{case_id} did not remain golden-equal")
        count = require_int(case.get("work_unit_count"), f"{case_id}.work_unit_count")
        if count <= 0 or measurement.get("work_unit_count") != count:
            raise ReceiptError(f"{case_id} work-unit count drifted")
        if measurement.get("work_unit") != case.get("work_unit"):
            raise ReceiptError(f"{case_id} work-unit label drifted")
        if require_int(measurement.get("measured_runs"), f"{case_id}.runs") <= 0:
            raise ReceiptError(f"{case_id} has no measured runs")
        if measurement.get("warmup_runs") != warmups:
            raise ReceiptError(f"{case_id} warmup count drifted")
        elapsed = require_dict(measurement.get("elapsed_seconds"), f"{case_id}.elapsed")
        minimum = require_number(elapsed.get("minimum"), f"{case_id}.minimum")
        median = require_number(elapsed.get("median"), f"{case_id}.median")
        maximum = require_number(elapsed.get("maximum"), f"{case_id}.maximum")
        if not 0 < minimum <= median <= maximum:
            raise ReceiptError(f"{case_id} elapsed order is invalid")
        rate = require_number(
            measurement.get("end_to_end_work_units_per_second_at_median"),
            f"{case_id}.rate",
        )
        expected_rate = count / median
        if abs(rate - expected_rate) > max(1e-9, expected_rate * 1e-12):
            raise ReceiptError(f"{case_id} rate is inconsistent with its median")

    coverage = require_list(protocol.get("certificate_coverage"), "certificate coverage")
    if receipt.get("certificate_coverage") != coverage:
        raise ReceiptError("certificate coverage drifted from the protocol")
    peak = require_int(receipt.get("campaign_peak_child_rss_kib"), "peak RSS")
    if peak <= 0:
        raise ReceiptError("peak RSS must be positive")
    for measurement in by_id.values():
        case_peak = require_int(
            measurement.get("campaign_peak_child_rss_kib_after_case"),
            "case peak RSS",
        )
        if not 0 < case_peak <= peak:
            raise ReceiptError("case peak RSS is inconsistent with campaign peak")

    library = require_dict(receipt.get("wm_fca_library"), "wm_fca_library")
    library_path = benchmark_root / "lib" / "lib_wm_fca.metta"
    library_text = library_path.read_text(encoding="utf-8")
    library_lines = library_text.splitlines()
    expected_library = {
        "path": library_path.name,
        "sha256": digest(library_path),
        "bytes": library_path.stat().st_size,
        "lines": len(library_lines),
        "type_declarations": sum(line.startswith("(: ") for line in library_lines),
        "equation_definitions": sum(line.startswith("(= ") for line in library_lines),
    }
    if library != expected_library:
        raise ReceiptError("ergonomics receipt does not pin the current WM/FCA library")

    receipt["artifact_sha256"] = digest(receipt_path)
    return receipt


def read_planets_receipt(root: Path) -> dict[str, Any]:
    process = subprocess.run(
        [sys.executable, str(root / "planets_oracle.py")],
        check=True,
        capture_output=True,
        text=True,
    )
    receipt = require_dict(json.loads(process.stdout), "Planets receipt")
    if receipt.get("schema") != "wm-fca-planets-oracle-v1":
        raise ReceiptError("unexpected Planets receipt schema")
    if receipt.get("published_intents_equal") is not True:
        raise ReceiptError("Planets intents do not match the published oracle")
    if receipt.get("published_basis_equal") is not True:
        raise ReceiptError("Planets basis does not match the published oracle")
    return receipt


def replay_corruption_analysis(
    root: Path,
    protocol_path: Path,
    receipt_path: Path,
    expected: dict[str, Any],
) -> None:
    analyzer = root / "analyze_corruption_receipt.py"
    if not analyzer.is_file():
        raise ReceiptError(f"missing corruption analyzer: {analyzer}")
    if expected.get("analysis_script_sha256") != digest(analyzer):
        raise ReceiptError("analysis does not pin the current corruption analyzer")
    with tempfile.TemporaryDirectory(prefix="wm-fca-analysis-") as directory:
        replay_path = Path(directory) / "analysis.json"
        process = subprocess.run(
            [
                sys.executable,
                str(analyzer),
                "--protocol",
                str(protocol_path),
                "--receipt",
                str(receipt_path),
                "--output",
                str(replay_path),
            ],
            check=False,
            capture_output=True,
            text=True,
        )
        if process.returncode != 0:
            raise ReceiptError(
                "corruption analysis replay failed: " + process.stderr[-1000:]
            )
        replayed = load_json(replay_path)
    if replayed != expected:
        raise ReceiptError("checked-in corruption analysis differs from exact replay")


def replay_incomplete_context_analysis(
    root: Path,
    protocol_path: Path,
    receipt_path: Path,
    expected: dict[str, Any],
) -> None:
    analyzer = root / "analyze_incomplete_context_baseline.py"
    if not analyzer.is_file():
        raise ReceiptError(f"missing incomplete-context analyzer: {analyzer}")
    if expected.get("analysis_script_sha256") != digest(analyzer):
        raise ReceiptError(
            "incomplete-context analysis does not pin the current analyzer"
        )
    with tempfile.TemporaryDirectory(prefix="wm-fca-incomplete-analysis-") as directory:
        replay_path = Path(directory) / "analysis.json"
        process = subprocess.run(
            [
                sys.executable,
                str(analyzer),
                "--protocol",
                str(protocol_path),
                "--receipt",
                str(receipt_path),
                "--output",
                str(replay_path),
            ],
            check=False,
            capture_output=True,
            text=True,
        )
        if process.returncode != 0:
            raise ReceiptError(
                "incomplete-context analysis replay failed: "
                + process.stderr[-1000:]
            )
        replayed = load_json(replay_path)
    if replayed != expected:
        raise ReceiptError(
            "checked-in incomplete-context analysis differs from exact replay"
        )


def read_exact_receipts(paths: list[Path]) -> list[dict[str, Any]]:
    if not paths:
        raise ReceiptError("an exact-oracle family is empty")
    receipts = [load_json(path) for path in paths]
    for receipt in receipts:
        if receipt.get("schema") != "wm-fca-cxt-oracle-v1":
            raise ReceiptError("unexpected exact-oracle schema")
        agreement = require_dict(receipt.get("oracle_agreement"), "oracle_agreement")
        if not agreement or not all(value is True for value in agreement.values()):
            raise ReceiptError("an exact oracle reports disagreement")
    return receipts


def exact_family_row(label: str, receipts: list[dict[str, Any]]) -> str:
    def integers(field: str) -> list[int]:
        return [require_int(receipt.get(field), field) for receipt in receipts]

    objects = integers("object_count")
    attributes = integers("attribute_count")
    concepts = integers("concept_count")
    bases = integers("canonical_basis_count")
    covers = integers("cover_count")
    object_span = (
        str(objects[0])
        if min(objects) == max(objects)
        else f"{min(objects)}--{max(objects)}"
    )
    attribute_span = (
        str(attributes[0])
        if min(attributes) == max(attributes)
        else f"{min(attributes)}--{max(attributes)}"
    )
    size = f"{object_span} $\\times$ {attribute_span}"
    return (
        f"{label} & {len(receipts)} & {size} & {sum(concepts):,} & "
        f"{sum(bases):,} & {sum(covers):,} \\\\"
    )


def comparison(
    analysis: dict[str, Any], model: str, metric: str
) -> dict[str, Any]:
    comparisons = require_dict(
        analysis.get("comparisons_against_crisp_single_source"), "comparisons"
    )
    model_value = require_dict(comparisons.get(model), f"comparisons.{model}")
    return require_dict(model_value.get(metric), f"comparisons.{model}.{metric}")


def metric_value(entry: dict[str, Any], field: str, label: str) -> float:
    return require_number(entry.get(field), label)


def f3(value: float) -> str:
    return f"{value:.3f}"


def signed3(value: float) -> str:
    return f"{value:+.3f}"


def render(benchmark_root: Path) -> str:
    root = benchmark_root / "benchmarks" / "wm_fca"
    analysis_path = root / "results" / "wm_fca_corruption_full_v1_analysis.json"
    receipt_path = root / "results" / "wm_fca_corruption_full_v1_receipt.json.gz"
    protocol_path = root / "corruption_protocol.json"
    incomplete_analysis_path = (
        root / "results" / "wm_fca_incomplete_context_baseline_v1_analysis.json"
    )
    incomplete_receipt_path = (
        root / "results" / "wm_fca_incomplete_context_baseline_v1_receipt.json.gz"
    )
    incomplete_protocol_path = root / "incomplete_context_baseline_protocol.json"
    analysis = load_json(analysis_path)
    protocol = load_json(protocol_path)
    incomplete_analysis = load_json(incomplete_analysis_path)
    incomplete_protocol = load_json(incomplete_protocol_path)
    ergonomics = read_ergonomics_receipt(benchmark_root)

    if analysis.get("schema") != "wm-fca-corruption-analysis-v1":
        raise ReceiptError("unexpected analysis schema")
    if protocol.get("schema") != "wm-fca-corruption-protocol-v1":
        raise ReceiptError("unexpected corruption protocol schema")
    if analysis.get("protocol_sha256") != digest(protocol_path):
        raise ReceiptError("analysis does not pin the current corruption protocol")
    if analysis.get("source_receipt_artifact_sha256") != digest(receipt_path):
        raise ReceiptError("analysis does not pin the current compressed receipt")
    replay_corruption_analysis(root, protocol_path, receipt_path, analysis)
    if (
        incomplete_analysis.get("schema")
        != "wm-fca-incomplete-context-baseline-analysis-v1"
    ):
        raise ReceiptError("unexpected incomplete-context analysis schema")
    if (
        incomplete_protocol.get("schema")
        != "wm-fca-incomplete-context-baseline-protocol-v1"
    ):
        raise ReceiptError("unexpected incomplete-context protocol schema")
    if incomplete_analysis.get("protocol_sha256") != digest(
        incomplete_protocol_path
    ):
        raise ReceiptError(
            "incomplete-context analysis does not pin its current protocol"
        )
    if incomplete_analysis.get("baseline_receipt_artifact_sha256") != digest(
        incomplete_receipt_path
    ):
        raise ReceiptError(
            "incomplete-context analysis does not pin its compressed receipt"
        )
    if incomplete_analysis.get("source_receipt_artifact_sha256") != digest(
        receipt_path
    ):
        raise ReceiptError(
            "incomplete-context analysis does not join the main corruption receipt"
        )
    replay_incomplete_context_analysis(
        root,
        incomplete_protocol_path,
        incomplete_receipt_path,
        incomplete_analysis,
    )

    contexts = require_list(protocol.get("contexts"), "contexts")
    seeds = require_list(protocol.get("seeds"), "seeds")
    corruption = require_dict(protocol.get("corruption_grid"), "corruption_grid")
    missing = require_list(corruption.get("missing_rates"), "missing_rates")
    flips = require_list(corruption.get("flip_rates"), "flip_rates")
    expected_cases = len(contexts) * len(seeds) * len(missing) * len(flips)
    case_count = require_int(analysis.get("case_count"), "case_count")
    if case_count != expected_cases:
        raise ReceiptError("analysis is not the complete frozen Cartesian grid")
    if require_int(
        incomplete_analysis.get("case_count"), "incomplete case_count"
    ) != case_count:
        raise ReceiptError("incomplete-context and WM case universes differ")

    planets = read_planets_receipt(root)
    published = [planets] + read_exact_receipts(
        sorted((root / "oracles").glob("*_oracle.json"))
    )
    mizar = read_exact_receipts(sorted((root / "mizar_oracles").glob("*.json")))
    fcapy_exact = read_exact_receipts(
        sorted((root / "scale_oracles").glob("random_*_exact_oracle.json"))
    )
    if (len(published), len(mizar), len(fcapy_exact)) != (6, 13, 9):
        raise ReceiptError("exact-validation family cardinalities drifted")

    query_receipts = [
        load_json(path)
        for path in sorted((root / "scale_oracles").glob("*_query_oracle.json"))
    ]
    for receipt in query_receipts:
        if receipt.get("schema") != "wm-fca-scale-query-oracle-v1":
            raise ReceiptError("unexpected query-oracle schema")
        agreement = require_dict(receipt.get("oracle_agreement"), "query agreement")
        if not agreement or not all(value is True for value in agreement.values()):
            raise ReceiptError("a query oracle reports disagreement")
    fcapy_queries = [r for r in query_receipts if r.get("context_id") != "bob_ross"]
    bob_queries = [r for r in query_receipts if r.get("context_id") == "bob_ross"]
    if (len(fcapy_queries), len(bob_queries)) != (18, 1):
        raise ReceiptError("query-validation family cardinalities drifted")

    event_receipts = [
        load_json(path)
        for path in sorted((root / "scale_oracles").glob("*_event_oracle.json"))
    ]
    if len(event_receipts) != 2:
        raise ReceiptError("event-oracle family cardinality drifted")
    event_prefixes = 0
    for receipt in event_receipts:
        agreement = require_dict(receipt.get("oracle_agreement"), "event agreement")
        if not agreement or not all(value is True for value in agreement.values()):
            raise ReceiptError("an event oracle reports disagreement")
        event_prefixes += len(require_list(receipt.get("prefixes"), "event prefixes"))

    exact_rows = "\n".join(
        [
            exact_family_row("Published FCA examples", published),
            exact_family_row("Mizar family", mizar),
            exact_family_row("FCApy controlled random", fcapy_exact),
        ]
    )
    exact_receipts = published + mizar + fcapy_exact
    exact_context_count = len(exact_receipts)
    exact_concept_count = sum(
        require_int(receipt.get("concept_count"), "concept_count")
        for receipt in exact_receipts
    )
    exact_basis_count = sum(
        require_int(receipt.get("canonical_basis_count"), "canonical_basis_count")
        for receipt in exact_receipts
    )
    exact_cover_count = sum(
        require_int(receipt.get("cover_count"), "cover_count")
        for receipt in exact_receipts
    )

    query_rows = []
    for label, receipts in [
        ("FCApy controlled random", fcapy_queries),
        ("Bob Ross", bob_queries),
    ]:
        query_count = sum(require_int(r.get("query_count"), "query_count") for r in receipts)
        max_objects = max(require_int(r.get("object_count"), "object_count") for r in receipts)
        max_attributes = max(
            require_int(r.get("attribute_count"), "attribute_count") for r in receipts
        )
        query_rows.append(
            f"{label} & {len(receipts)} & {max_objects} $\\times$ {max_attributes} & "
            f"{query_count:,} \\\\"
        )

    ergonomics_labels = {
        "bob_ross_query_batch": "Bob Ross query batch",
        "bob_ross_event_replay": "Immutable event replay",
        "query_certificates": "Certificate checks",
    }
    ergonomics_units = {
        "closure_query": "closure queries",
        "event_operation": "event operations",
        "verified_assertion": "verified assertions",
    }
    ergonomics_rows = []
    for measurement_value in require_list(
        ergonomics.get("measurements"), "ergonomics measurements"
    ):
        measurement = require_dict(measurement_value, "ergonomics measurement")
        case_id = require_string(measurement.get("id"), "ergonomics id")
        unit = require_string(measurement.get("work_unit"), f"{case_id}.unit")
        if case_id not in ergonomics_labels or unit not in ergonomics_units:
            raise ReceiptError("unrecognized ergonomics row label")
        count = require_int(measurement.get("work_unit_count"), f"{case_id}.count")
        elapsed = require_dict(measurement.get("elapsed_seconds"), f"{case_id}.elapsed")
        median_ms = require_number(elapsed.get("median"), f"{case_id}.median") * 1000
        rate = require_number(
            measurement.get("end_to_end_work_units_per_second_at_median"),
            f"{case_id}.rate",
        )
        ergonomics_rows.append(
            f"{ergonomics_labels[case_id]} & {count} {ergonomics_units[unit]} & "
            f"{median_ms:.3f} & {round(rate):,} & yes \\\\"
        )

    metrics = [
        ("Cell F1", "cell_f1"),
        ("Closure exact", "closure_exact_accuracy"),
        ("Canonical-basis F1", "basis_f1"),
        ("Concept F1", "concept_f1"),
        ("Cover-edge F1", "cover_f1"),
    ]
    models = [
        ("Crisp single source", None),
        ("Raw majority (2)", "raw-majority-2"),
        ("Source majority (2)", "source-majority-2"),
        ("WM permissive (1 group)", "wm-permissive-group-1"),
        ("WM robust (2 groups)", "wm-robust-group-2"),
        ("WM exact consensus", "wm-exact-consensus"),
    ]
    baseline_reference = comparison(analysis, "wm-permissive-group-1", "cell_f1")
    model_rows = []
    for label, model in models:
        values = []
        for _, metric in metrics:
            entry = comparison(analysis, model or "wm-permissive-group-1", metric)
            field = "baseline_mean" if model is None else "contender_mean"
            values.append(f3(metric_value(entry, field, f"{model}.{metric}.{field}")))
        model_rows.append(f"{label} & " + " & ".join(values) + " \\\\")
    require_number(baseline_reference.get("baseline_mean"), "baseline mean")

    incomplete_aggregate = require_dict(
        incomplete_analysis.get("baseline_aggregate"), "incomplete aggregate"
    )
    if require_int(
        incomplete_aggregate.get("case_count"), "incomplete aggregate case_count"
    ) != case_count:
        raise ReceiptError("incomplete aggregate case count drifted")
    incomplete_baselines = require_dict(
        incomplete_aggregate.get("baselines"), "incomplete baselines"
    )
    if set(incomplete_baselines) != {
        "incomplete-lower-completion",
        "incomplete-upper-completion",
    }:
        raise ReceiptError("incomplete baseline family drifted")
    incomplete_source_means = require_dict(
        incomplete_analysis.get("source_model_means"), "incomplete source means"
    )
    source_crisp_means = require_dict(
        incomplete_source_means.get("crisp-single-source"), "source crisp means"
    )
    source_permissive_means = require_dict(
        incomplete_source_means.get("wm-permissive-group-1"),
        "source permissive means",
    )

    def incomplete_mean(baseline_id: str, metric: str) -> float:
        baseline = require_dict(incomplete_baselines.get(baseline_id), baseline_id)
        entry = require_dict(baseline.get(metric), f"{baseline_id}.{metric}")
        return require_number(entry.get("mean"), f"{baseline_id}.{metric}.mean")

    incomplete_rows = []
    for label, baseline_id in [
        ("Incomplete lower completion", "incomplete-lower-completion"),
        ("Incomplete upper completion", "incomplete-upper-completion"),
    ]:
        values = [f3(incomplete_mean(baseline_id, metric)) for _, metric in metrics]
        incomplete_rows.append(f"{label} & " + " & ".join(values) + " \\\\")
    incomplete_rows.append(
        "WM permissive (1 group) & "
        + " & ".join(
            f3(require_number(source_permissive_means.get(metric), metric))
            for _, metric in metrics
        )
        + " \\\\"
    )
    for _, metric in metrics:
        lower = incomplete_mean("incomplete-lower-completion", metric)
        crisp = require_number(source_crisp_means.get(metric), f"crisp.{metric}")
        if lower != crisp:
            raise ReceiptError(
                f"lower completion no longer equals crisp single-source for {metric}"
            )
        main_permissive = metric_value(
            comparison(analysis, "wm-permissive-group-1", metric),
            "contender_mean",
            f"main permissive {metric}",
        )
        if require_number(
            source_permissive_means.get(metric), f"source permissive {metric}"
        ) != main_permissive:
            raise ReceiptError(
                f"incomplete comparator and main analysis disagree for {metric}"
            )

    permissive_rows = []
    for label, metric in metrics:
        entry = comparison(analysis, "wm-permissive-group-1", metric)
        permissive_rows.append(
            f"{label} & {signed3(metric_value(entry, 'mean_delta', metric))} & "
            f"{require_int(entry.get('wins'), metric + '.wins')}/"
            f"{require_int(entry.get('ties'), metric + '.ties')}/"
            f"{require_int(entry.get('losses'), metric + '.losses')} \\\\"
        )

    hypotheses = require_dict(analysis.get("hypothesis_evaluation"), "hypotheses")
    duplicate = require_dict(hypotheses.get("exact_duplicate_invariance"), "duplicate")
    dependence = require_dict(
        hypotheses.get("declared_dependence_group_invariance"), "dependence"
    )
    envelope = require_dict(hypotheses.get("wm_envelope_coverage"), "envelope")
    if duplicate.get("passed") is not True or dependence.get("passed") is not True:
        raise ReceiptError("a preregistered invariance hypothesis failed")
    if envelope.get("passed") is not True:
        raise ReceiptError("the preregistered envelope hypothesis failed")

    duplicate_rates = require_dict(duplicate.get("rates"), "duplicate rates")
    if not duplicate_rates or any(require_number(v, "duplicate rate") != 1.0 for v in duplicate_rates.values()):
        raise ReceiptError("exact-duplicate invariance is not universal")
    group_rates = require_dict(dependence.get("dependence_group_model_rates"), "group rates")
    raw_rates = require_dict(dependence.get("raw_or_source_counting_rates"), "raw rates")
    group_rate = min(require_number(v, "group rate") for v in group_rates.values())
    raw_rate = max(require_number(v, "raw rate") for v in raw_rates.values())

    coverage = require_dict(envelope.get("coverage_and_width"), "coverage")
    envelope_rows = []
    for label, key, width_key in [
        ("Cells", "cell", "mean_width"),
        ("Closures", "closure", "mean_normalized_width"),
    ]:
        value = require_dict(coverage.get(key), f"coverage.{key}")
        envelope_rows.append(
            f"{label} & {f3(require_number(value.get('crisp_singleton_coverage'), key))} & "
            f"{f3(require_number(value.get('wm_envelope_coverage'), key))} & "
            f"{signed3(require_number(value.get('coverage_gain'), key))} & "
            f"{f3(require_number(value.get(width_key), width_key))} \\\\"
        )

    calibration = require_dict(
        analysis.get("calibration_evaluation"), "calibration_evaluation"
    )
    crisp_calibration = require_dict(
        calibration.get("crisp_hard_point"), "crisp_hard_point"
    )
    midpoint_calibration = require_dict(
        calibration.get("wm_envelope_midpoint"), "wm_envelope_midpoint"
    )
    calibration_delta = require_dict(
        calibration.get("midpoint_minus_crisp"), "midpoint_minus_crisp"
    )
    if crisp_calibration.get("forecast_values") != [0.0, 1.0]:
        raise ReceiptError("crisp calibration forecast support drifted")
    if midpoint_calibration.get("forecast_values") != [0.0, 0.5, 1.0]:
        raise ReceiptError("midpoint calibration forecast support drifted")
    crisp_brier = require_number(crisp_calibration.get("brier"), "crisp brier")
    crisp_ece = require_number(crisp_calibration.get("ece"), "crisp ece")
    midpoint_brier = require_number(
        midpoint_calibration.get("brier"), "midpoint brier"
    )
    midpoint_ece = require_number(midpoint_calibration.get("ece"), "midpoint ece")
    brier_delta = require_number(calibration_delta.get("brier"), "brier delta")
    ece_delta = require_number(calibration_delta.get("ece"), "ece delta")
    if abs((midpoint_brier - crisp_brier) - brier_delta) > 1e-15:
        raise ReceiptError("Brier calibration delta is inconsistent")
    if abs((midpoint_ece - crisp_ece) - ece_delta) > 1e-15:
        raise ReceiptError("ECE calibration delta is inconsistent")
    incomplete_calibration = require_dict(
        incomplete_analysis.get("calibration_and_coverage"),
        "incomplete calibration and coverage",
    )
    comparator_calibration = require_dict(
        incomplete_calibration.get("incomplete_completion_midpoint"),
        "incomplete completion midpoint",
    )
    joined_crisp_calibration = require_dict(
        incomplete_calibration.get("crisp_hard_point"), "joined crisp calibration"
    )
    joined_wm_calibration = require_dict(
        incomplete_calibration.get("wm_model_family_midpoint"),
        "joined WM calibration",
    )
    if require_number(
        joined_crisp_calibration.get("brier"), "joined crisp brier"
    ) != crisp_brier:
        raise ReceiptError(
            "incomplete comparator and main analysis disagree on crisp Brier"
        )
    if require_number(
        joined_crisp_calibration.get("ece"), "joined crisp ECE"
    ) != crisp_ece:
        raise ReceiptError(
            "incomplete comparator and main analysis disagree on crisp ECE"
        )
    if require_number(
        joined_wm_calibration.get("brier"), "joined WM brier"
    ) != midpoint_brier:
        raise ReceiptError(
            "incomplete comparator and main analysis disagree on WM Brier"
        )
    if require_number(
        joined_wm_calibration.get("ece"), "joined WM ECE"
    ) != midpoint_ece:
        raise ReceiptError(
            "incomplete comparator and main analysis disagree on WM ECE"
        )

    def uncertainty_row(label: str, support: str, value: dict[str, Any]) -> str:
        return (
            f"{label} & {support} & "
            f"{f3(require_number(value.get('brier'), label + '.brier'))} & "
            f"{f3(require_number(value.get('ece'), label + '.ece'))} & "
            f"{f3(require_number(value.get('interval_coverage'), label + '.coverage'))} & "
            f"{f3(require_number(value.get('mean_width'), label + '.width'))} \\\\"
        )

    calibration_rows = "\n".join(
        [
            uncertainty_row(
                "Crisp hard point", "$\\{0,1\\}$", joined_crisp_calibration
            ),
            uncertainty_row(
                "Incomplete completion midpoint",
                "$\\{0,0.5,1\\}$",
                comparator_calibration,
            ),
            uncertainty_row(
                "WM model-family midpoint",
                "$\\{0,0.5,1\\}$",
                joined_wm_calibration,
            ),
        ]
    )
    calibration_strata = require_dict(calibration.get("strata"), "calibration strata")
    calibration_stratum_count = 0
    for factor in ("flip_rate", "missing_rate"):
        strata = require_dict(calibration_strata.get(factor), f"calibration.{factor}")
        if len(strata) != 3:
            raise ReceiptError(f"calibration {factor} cardinality drifted")
        for label, value in strata.items():
            entry = require_dict(value, f"calibration.{factor}.{label}")
            if require_number(entry.get("brier_delta"), "stratum brier delta") >= 0:
                raise ReceiptError("a calibration stratum has nonnegative Brier delta")
            if require_number(entry.get("ece_delta"), "stratum ECE delta") >= 0:
                raise ReceiptError("a calibration stratum has nonnegative ECE delta")
            calibration_stratum_count += 1

    artifact_hash = str(analysis["source_receipt_artifact_sha256"])
    content_hash = str(analysis["source_receipt_content_sha256"])
    protocol_hash = str(analysis["protocol_sha256"])
    incomplete_artifact_hash = require_string(
        incomplete_analysis.get("baseline_receipt_artifact_sha256"),
        "incomplete receipt artifact hash",
    )
    incomplete_content_hash = require_string(
        incomplete_analysis.get("baseline_receipt_content_sha256"),
        "incomplete receipt content hash",
    )
    incomplete_protocol_hash = require_string(
        incomplete_analysis.get("protocol_sha256"), "incomplete protocol hash"
    )
    ergonomics_library = require_dict(
        ergonomics.get("wm_fca_library"), "ergonomics library"
    )
    ergonomics_peak_mib = (
        require_int(ergonomics.get("campaign_peak_child_rss_kib"), "peak RSS")
        / 1024
    )
    return f"""% Generated by generate_wm_fca_benchmark_tables.py; do not edit.
\\newcommand{{\\WMFCACaseCount}}{{{case_count}}}
\\newcommand{{\\WMFCAAssertionCount}}{{{case_count * 30:,}}}
\\newcommand{{\\WMFCAEventPrefixCount}}{{{event_prefixes}}}
\\newcommand{{\\WMFCAExactContextCount}}{{{exact_context_count}}}
\\newcommand{{\\WMFCAExactConceptCount}}{{{exact_concept_count:,}}}
\\newcommand{{\\WMFCAExactBasisCount}}{{{exact_basis_count:,}}}
\\newcommand{{\\WMFCAExactCoverCount}}{{{exact_cover_count:,}}}
\\newcommand{{\\WMFCAQueryContextCount}}{{{len(query_receipts)}}}
\\newcommand{{\\WMFCAQueryCount}}{{{sum(require_int(r.get("query_count"), "query_count") for r in query_receipts):,}}}
\\newcommand{{\\WMFCACorruptionContextCount}}{{{len(contexts)}}}
\\newcommand{{\\WMFCASeedCount}}{{{len(seeds)}}}
\\newcommand{{\\WMFCAMissingRates}}{{{", ".join(f"{require_number(value, 'missing rate'):.2f}" for value in missing)}}}
\\newcommand{{\\WMFCAFlipRates}}{{{", ".join(f"{require_number(value, 'flip rate'):.2f}" for value in flips)}}}
\\newcommand{{\\WMFCAUnknownRate}}{{{require_number(corruption.get("unknown_rate"), "unknown_rate"):.2f}}}
\\newcommand{{\\WMFCAProtocolHash}}{{\\texttt{{{protocol_hash[:12]}...}}}}
\\newcommand{{\\WMFCAReceiptHash}}{{\\texttt{{{artifact_hash[:12]}...}}}}
\\newcommand{{\\WMFCAReceiptContentHash}}{{\\texttt{{{content_hash[:12]}...}}}}
\\newcommand{{\\WMFCAIncompleteProtocolHash}}{{\\texttt{{{incomplete_protocol_hash[:12]}...}}}}
\\newcommand{{\\WMFCAIncompleteReceiptHash}}{{\\texttt{{{incomplete_artifact_hash[:12]}...}}}}
\\newcommand{{\\WMFCAIncompleteReceiptContentHash}}{{\\texttt{{{incomplete_content_hash[:12]}...}}}}
\\newcommand{{\\WMFCAErgonomicsReceiptHash}}{{\\texttt{{{require_string(ergonomics.get("artifact_sha256"), "ergonomics hash")[:12]}...}}}}
\\newcommand{{\\WMFCAErgonomicsPeakMiB}}{{{ergonomics_peak_mib:.1f}}}
\\newcommand{{\\WMFCALibraryLines}}{{{require_int(ergonomics_library.get("lines"), "library lines"):,}}}
\\newcommand{{\\WMFCALibraryBytes}}{{{require_int(ergonomics_library.get("bytes"), "library bytes"):,}}}
\\newcommand{{\\WMFCALibraryTypeDeclarations}}{{{require_int(ergonomics_library.get("type_declarations"), "library type declarations")}}}
\\newcommand{{\\WMFCALibraryEquations}}{{{require_int(ergonomics_library.get("equation_definitions"), "library equations")}}}
\\newcommand{{\\WMFCACertificateCoverageCount}}{{{len(require_list(ergonomics.get("certificate_coverage"), "certificate coverage"))}}}
\\newcommand{{\\WMFCACalibrationStratumCount}}{{{calibration_stratum_count}}}

\\newcommand{{\\WMFCAExactValidationRows}}{{%
{exact_rows}
}}

\\newcommand{{\\WMFCAQueryValidationRows}}{{%
{chr(10).join(query_rows)}
}}

\\newcommand{{\\WMFCAErgonomicsRows}}{{%
{chr(10).join(ergonomics_rows)}
}}

\\newcommand{{\\WMFCAModelResultRows}}{{%
{chr(10).join(model_rows)}
}}

\\newcommand{{\\WMFCAIncompleteBaselineRows}}{{%
{chr(10).join(incomplete_rows)}
}}

\\newcommand{{\\WMFCAPermissiveDeltaRows}}{{%
{chr(10).join(permissive_rows)}
}}

\\newcommand{{\\WMFCAEnvelopeRows}}{{%
{chr(10).join(envelope_rows)}
}}

\\newcommand{{\\WMFCACalibrationRows}}{{%
{calibration_rows}
}}

\\newcommand{{\\WMFCADuplicateInvariantRate}}{{{f3(1.0)}}}
\\newcommand{{\\WMFCAGroupCopyInvariantRate}}{{{f3(group_rate)}}}
\\newcommand{{\\WMFCARawCopyInvariantRate}}{{{f3(raw_rate)}}}
"""


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--benchmark-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    rendered = render(args.benchmark_root.resolve())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(rendered, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
