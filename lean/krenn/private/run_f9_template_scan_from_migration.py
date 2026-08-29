#!/usr/bin/env python3
"""Run the exact template scan using every distinct migrated certificate.

This wrapper derives the template inventory from the fail-closed migration
manifest, verifies each certificate hash, removes duplicate proof shapes, and
then calls the exact CAS-free scanner. It prevents later waves from silently
forgetting a previously discovered template.
"""

from __future__ import annotations

import os
import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def certificate_for(case: int, root: Path, expected: str) -> Path:
    if case == 1:
        candidates = [
            Path(os.environ.get("KRENN_ARTIFACTS", "artifacts")) / "x5_0415_trace_prototype/frozen_case1"
            / "lift_direct/lift.stdout"
        ]
    else:
        artifact = root / f"case{case}"
        candidates = [
            artifact / "certificate_template.txt",
            artifact / "certificate_strict.txt",
            artifact / "lift_direct/lift.stdout",
        ]
    for candidate in candidates:
        if candidate.is_file() and digest(candidate) == expected:
            return candidate
    raise ValueError(f"case {case} has no certificate matching its receipt")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--migration-manifest", type=Path, required=True)
    parser.add_argument("--artifact-root", type=Path, required=True)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--historical-log", type=Path)
    source.add_argument("--case-manifest", type=Path)
    parser.add_argument("--prior-coverage", type=Path)
    parser.add_argument("--pending-only", action="store_true")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    manifest = json.loads(args.migration_manifest.read_text(encoding="utf-8"))
    rows = manifest.get("cases")
    if not isinstance(rows, list) or manifest.get("historical_closed_count") != 317:
        raise ValueError("migration manifest is not the 317-case inventory")
    templates: dict[str, tuple[Path, Path]] = {}
    for row in rows:
        if row.get("migration_status") != "official_normalized_case_zero_sorry_lean":
            continue
        case = int(row["case_index"])
        # Exhaustive-tree migrations have one certificate per terminal leaf,
        # not a single parent certificate whose multiplier vector can be
        # replayed as a template on another frozen parent system.
        expected_value = row.get("certificate_file_sha256")
        if not isinstance(expected_value, str):
            continue
        expected = expected_value
        certificate = certificate_for(case, args.artifact_root, expected)
        system = (Path(os.environ.get("KRENN_ARTIFACTS", "artifacts")) / "x5_0415_trace_prototype/frozen_case1"
                  / "system.json" if case == 1 else
                  args.artifact_root / f"case{case}/system.json")
        templates.setdefault(expected, (certificate, system))

    prior_hashes: set[str] = set()
    if args.prior_coverage is not None:
        prior = json.loads(args.prior_coverage.read_text(encoding="utf-8"))
        if prior.get("format") != "krenn-f9-template-coverage-v1" or \
                prior.get("cases_examined") != 317:
            raise ValueError("prior coverage is not a full 317-case scan")
        if prior.get("historical_log_sha256") != \
                manifest.get("historical_log_sha256"):
            raise ValueError("prior coverage binds a different historical log")
        prior_cases = prior.get("cases")
        expected_cases = {int(row["case_index"]) for row in rows}
        if not isinstance(prior_cases, list) or len(prior_cases) != 317 or \
                {row.get("case_index") for row in prior_cases} != expected_cases:
            raise ValueError("prior coverage does not enumerate the same 317 cases")
        prior_rows = prior.get("templates")
        if not isinstance(prior_rows, list):
            raise ValueError("prior coverage has no template inventory")
        for row in prior_rows:
            value = row.get("certificate_sha256")
            if not isinstance(value, str):
                raise ValueError("prior coverage has a malformed certificate digest")
            prior_hashes.add(value)
        if not prior_hashes <= set(templates):
            raise ValueError("prior coverage contains a template absent from migration")
        templates = {
            key: value for key, value in templates.items()
            if key not in prior_hashes
        }
        if not templates:
            raise ValueError("prior coverage already contains every template")

    scanner = Path(__file__).with_name("scan_f9_template_certificate_coverage.py")
    command = [
        sys.executable, str(scanner),
        "--output", str(args.output),
    ]
    if args.historical_log is not None:
        command += ["--log", str(args.historical_log)]
    else:
        command += ["--case-manifest", str(args.case_manifest)]
    if args.pending_only:
        if args.case_manifest is None:
            raise ValueError("--pending-only requires --case-manifest")
        command.append("--pending-only")
    for certificate, system in templates.values():
        command += ["--template", str(certificate), "--template-system", str(system)]
    print(
        f"distinct_templates={len(templates)} prior_templates={len(prior_hashes)}",
        flush=True,
    )
    return subprocess.run(command, check=False).returncode


if __name__ == "__main__":
    raise SystemExit(main())
