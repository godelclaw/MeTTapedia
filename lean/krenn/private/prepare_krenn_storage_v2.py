#!/usr/bin/env python3
"""Prepare a fail-closed, content-addressed Krenn archive plan.

The plan has two retained closures:

* the previously audited authoritative all-collapse component closure;
* chart-0 strict certificate/system pairs plus compact provenance.

Everything else under the three explicitly named expansion trees is classified
as generated scratch.  This program only writes manifests; it never deletes or
rewrites corpus files.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys
from typing import Any, NoReturn


STRICT_END = b"C4_LIFT_CERTIFICATE_END"
EXPANSION_ROOTS = (
    "allcollapse_case_artifacts",
    "chart0_attack_v1",
    ".ladder_scratch",
)


def fail(message: str) -> NoReturn:
    raise SystemExit("KRENN STORAGE V2 FAILED: " + message)


def digest(path: Path) -> str:
    result = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(4 * 1024 * 1024), b""):
            result.update(block)
    return result.hexdigest()


def load_jsonl(path: Path) -> list[dict[str, Any]]:
    result = []
    with path.open(encoding="utf-8") as stream:
        for line_number, line in enumerate(stream, 1):
            try:
                value = json.loads(line)
            except json.JSONDecodeError as error:
                fail(f"{path}:{line_number}: {error}")
            if not isinstance(value, dict):
                fail(f"{path}:{line_number}: row is not an object")
            result.append(value)
    return result


def safe_relative(corpus: Path, path: Path) -> str:
    try:
        relative = str(path.resolve().relative_to(corpus))
    except ValueError:
        fail(f"path escapes corpus: {path}")
    if not relative or relative.startswith("../") or "\n" in relative or "\0" in relative:
        fail(f"unsafe archive path: {relative!r}")
    return relative


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--corpus", type=Path, required=True)
    parser.add_argument("--prior-keep", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    corpus = args.corpus.resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    if corpus in output.parents or output == corpus:
        # Output beneath the corpus is fine, but never beneath a tree scheduled
        # for removal.
        relative_output = output.relative_to(corpus)
        if relative_output.parts and relative_output.parts[0] in EXPANSION_ROOTS:
            fail("output directory lies inside an expansion tree")

    retained: dict[str, dict[str, Any]] = {}

    def retain(path: Path, closure: str, reason: str, expected: str | None = None) -> None:
        relative = safe_relative(corpus, path)
        if not path.is_file():
            fail(f"missing retained file: {relative}")
        actual = digest(path)
        if expected is not None and actual != expected:
            fail(f"hash mismatch for {relative}: expected {expected}, got {actual}")
        row = retained.setdefault(relative, {
            "path": relative,
            "bytes": path.stat().st_size,
            "sha256": actual,
            "closures": [],
            "reasons": [],
        })
        if row["sha256"] != actual or row["bytes"] != path.stat().st_size:
            fail(f"retained file changed during audit: {relative}")
        if closure not in row["closures"]:
            row["closures"].append(closure)
        if reason not in row["reasons"]:
            row["reasons"].append(reason)

    prior = load_jsonl(args.prior_keep)
    for row in prior:
        relative = row.get("path")
        expected = row.get("sha256")
        if not isinstance(relative, str) or not isinstance(expected, str):
            fail("prior keep row lacks path or SHA-256")
        if not relative.startswith("allcollapse_case_artifacts/"):
            fail(f"unexpected prior-keep prefix: {relative}")
        retain(corpus / relative, "allcollapse", "selected authoritative closure", expected)

    chart0 = corpus / "chart0_attack_v1"
    if not chart0.is_dir():
        fail("chart0 expansion tree is absent")
    chart0_candidates: set[Path] = set()
    for path in chart0.rglob("*"):
        if not path.is_file():
            continue
        relative = path.relative_to(chart0)
        # Compact provenance and proof traces, excluding the huge expanded
        # system fleet unless a strict certificate below selects the system.
        if path.name != "system.json" and path.suffix in {
            ".json", ".sh", ".py", ".cnf", ".lrat", ".drat"
        }:
            chart0_candidates.add(path)
        # The three authoritative face roots are small and are needed to
        # reproduce the branching constructions.
        if path.name == "system.json" and len(relative.parts) <= 2:
            chart0_candidates.add(path)
        if len(relative.parts) == 1 and path.suffix in {".sing", ".sh"}:
            chart0_candidates.add(path)

    strict_certificates = 0
    for certificate in chart0.rglob("*.stdout"):
        try:
            content = certificate.read_bytes()
        except OSError as error:
            fail(f"cannot inspect {certificate}: {error}")
        if STRICT_END not in content:
            continue
        strict_certificates += 1
        chart0_candidates.add(certificate)
        system = certificate.parent / "system.json"
        if not system.is_file():
            fail(f"strict chart-0 certificate lacks sibling system: {certificate}")
        chart0_candidates.add(system)

    for path in sorted(chart0_candidates):
        reason = "chart0 compact provenance"
        if path.name == "system.json":
            reason = "chart0 strict-certificate source or authoritative face root"
        elif path.suffix == ".stdout":
            reason = "chart0 strict certificate"
        retain(path, "chart0", reason)

    by_closure: dict[str, list[dict[str, Any]]] = {"allcollapse": [], "chart0": []}
    for row in sorted(retained.values(), key=lambda item: item["path"]):
        for closure in row["closures"]:
            by_closure[closure].append(row)

    for closure, rows in by_closure.items():
        manifest = output / f"{closure}-keep.jsonl"
        paths = output / f"{closure}-paths.txt"
        with manifest.open("w", encoding="utf-8") as stream:
            for row in rows:
                stream.write(json.dumps(row, sort_keys=True) + "\n")
        paths.write_text("".join(row["path"] + "\n" for row in rows), encoding="utf-8")

    delete_rows = 0
    delete_bytes = 0
    delete_by_root: Counter[str] = Counter()
    delete_bytes_by_root: Counter[str] = Counter()
    delete_manifest = output / "delete.jsonl"
    with delete_manifest.open("w", encoding="utf-8") as stream:
        for root_name in EXPANSION_ROOTS:
            root = corpus / root_name
            if not root.is_dir():
                fail(f"expansion root is absent: {root_name}")
            for path in sorted(root.rglob("*")):
                if not path.is_file():
                    continue
                relative = safe_relative(corpus, path)
                if relative in retained:
                    continue
                size = path.stat().st_size
                stream.write(json.dumps({
                    "path": relative,
                    "bytes": size,
                    "classification": "generated expansion scratch",
                }, sort_keys=True) + "\n")
                delete_rows += 1
                delete_bytes += size
                delete_by_root[root_name] += 1
                delete_bytes_by_root[root_name] += size

    summary = {
        "format": "krenn-storage-archive-plan-v2",
        "corpus": str(corpus),
        "retained_files": len(retained),
        "retained_logical_bytes": sum(row["bytes"] for row in retained.values()),
        "allcollapse_files": len(by_closure["allcollapse"]),
        "allcollapse_logical_bytes": sum(row["bytes"] for row in by_closure["allcollapse"]),
        "chart0_files": len(by_closure["chart0"]),
        "chart0_logical_bytes": sum(row["bytes"] for row in by_closure["chart0"]),
        "chart0_strict_certificates": strict_certificates,
        "delete_files": delete_rows,
        "delete_logical_bytes": delete_bytes,
        "delete_by_root": dict(delete_by_root),
        "delete_bytes_by_root": dict(delete_bytes_by_root),
        "ambiguities": [],
    }
    (output / "plan-summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
