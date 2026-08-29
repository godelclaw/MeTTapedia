#!/usr/bin/env python3
"""Apply a verified Krenn storage archive plan, failing closed.

This is intentionally separate from planning and archive construction.  It
requires streaming verification receipts for both retained closures, checks
that every current file in each expansion root is classified, atomically moves
the roots into a narrowly named quarantine, and only then removes that
quarantine.  The archives are the recovery path.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
from typing import NoReturn


ROOTS = ("allcollapse_case_artifacts", "chart0_attack_v1", ".ladder_scratch")


def fail(message: str) -> NoReturn:
    raise SystemExit("KRENN STORAGE V2 APPLY FAILED: " + message)


def digest(path: Path) -> str:
    result = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(4 * 1024 * 1024), b""):
            result.update(block)
    return result.hexdigest()


def jsonl_paths(path: Path) -> set[str]:
    result = set()
    with path.open(encoding="utf-8") as stream:
        for line in stream:
            row = json.loads(line)
            name = row.get("path")
            if not isinstance(name, str) or name in result:
                fail(f"invalid or duplicate path in {path}: {name!r}")
            result.add(name)
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--corpus", type=Path, required=True)
    parser.add_argument("--plan", type=Path, required=True)
    parser.add_argument("--verifier", type=Path, required=True)
    args = parser.parse_args()

    corpus = args.corpus.resolve()
    plan = args.plan.resolve()
    summary = json.loads((plan / "plan-summary.json").read_text(encoding="utf-8"))
    if summary.get("format") != "krenn-storage-archive-plan-v2":
        fail("unexpected plan format")
    if summary.get("ambiguities") != []:
        fail("plan contains ambiguities")

    retained = set()
    for closure in ("allcollapse", "chart0"):
        manifest = plan / f"{closure}-keep.jsonl"
        archive = plan / f"{closure}.tar.zst"
        receipt_path = plan / f"{closure}-archive-verification.json"
        if not archive.is_file() or not receipt_path.is_file():
            fail(f"{closure}: archive or verification receipt is absent")
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        if receipt.get("archive_sha256") != digest(archive):
            fail(f"{closure}: archive hash differs from verification receipt")
        if receipt.get("manifest_sha256") != digest(manifest):
            fail(f"{closure}: manifest hash differs from verification receipt")
        # Re-run the independent streaming verifier immediately before deletion.
        replay = subprocess.run(
            [sys.executable, str(args.verifier), str(archive), str(manifest)],
            check=False,
            capture_output=True,
            text=True,
        )
        if replay.returncode != 0:
            fail(f"{closure}: pre-delete archive replay failed: {replay.stderr or replay.stdout}")
        fresh = json.loads(replay.stdout)
        if fresh != receipt:
            fail(f"{closure}: pre-delete verification differs from recorded receipt")
        retained |= jsonl_paths(manifest)

    deleted = jsonl_paths(plan / "delete.jsonl")
    if retained & deleted:
        fail("retained and deleted path sets overlap")
    classified = retained | deleted

    current = set()
    for root_name in ROOTS:
        root = corpus / root_name
        if not root.is_dir() or root.parent != corpus:
            fail(f"unsafe or absent expansion root: {root}")
        for path in root.rglob("*"):
            if path.is_file():
                current.add(str(path.relative_to(corpus)))
    unknown = current - classified
    missing = classified - current
    if unknown:
        fail(f"{len(unknown)} current files are unclassified; first: {sorted(unknown)[:3]}")
    if missing:
        fail(f"{len(missing)} classified files disappeared; first: {sorted(missing)[:3]}")

    quarantine = corpus / ".storage-v2-quarantine"
    if quarantine.exists():
        fail(f"quarantine already exists: {quarantine}")
    quarantine.mkdir(mode=0o2770)
    moved = []
    try:
        for root_name in ROOTS:
            source = corpus / root_name
            destination = quarantine / root_name
            os.rename(source, destination)
            moved.append((source, destination))
    except OSError as error:
        for source, destination in reversed(moved):
            if destination.exists() and not source.exists():
                os.rename(destination, source)
        fail(f"atomic quarantine move failed and was rolled back: {error}")

    # The exact quarantine contains only roots already covered by the verified
    # archives and explicit delete manifest.
    shutil.rmtree(quarantine)
    print(json.dumps({
        "removed_roots": list(ROOTS),
        "classified_files": len(classified),
        "retained_archive_members": len(retained),
        "discarded_generated_files": len(deleted),
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
