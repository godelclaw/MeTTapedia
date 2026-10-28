#!/usr/bin/env python3
"""Check that a curated snapshot accounts for every changed upstream file.

The ledger records source identities and reasons for changes. This check
verifies those identities; semantic replacements and proof hypotheses are
documented in the ledger's review entries.
"""

from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path


def git(root: Path, *args: str) -> bytes:
    return subprocess.check_output(["git", *args], cwd=root)


def entries(root: Path, revision: str) -> dict[str, tuple[str, str]]:
    result = {}
    for row in git(root, "ls-tree", "-r", "-z", revision).split(b"\0"):
        if not row:
            continue
        metadata, path = row.split(b"\t", 1)
        mode, _, oid = metadata.decode().split()
        result[path.decode()] = (mode, oid)
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--revision", default="HEAD")
    parser.add_argument("--ledger", default="lean/mettapedia/artifacts/integration-20261028/preservation.json")
    args = parser.parse_args()
    root = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip())
    ledger = json.loads((root / args.ledger).read_text())
    baseline = entries(root, ledger["upstream_baseline"])
    candidate = entries(root, args.revision)
    recorded = ledger["upstream_changes"]
    failures = []
    changed = 0
    for path, old in baseline.items():
        new = candidate.get(path)
        if new == old:
            if path in recorded:
                failures.append(f"ledger describes an unchanged file: {path}")
            continue
        changed += 1
        record = recorded.get(path)
        if record is None:
            failures.append(f"unaccounted upstream change: {path}")
            continue
        if record["upstream_blob"] != old[1]:
            failures.append(f"wrong upstream identity: {path}")
        if record["curated_blob"] != (new[1] if new else None):
            failures.append(f"curated identity changed: {path}")
        if record.get("upstream_mode") != old[0]:
            failures.append(f"wrong upstream file mode: {path}")
        if record.get("curated_mode") != (new[0] if new else None):
            failures.append(f"curated file mode changed: {path}")
        if not record.get("reason"):
            failures.append(f"missing preservation reason: {path}")
        if path.endswith(".lean") and new is None:
            failures.append(f"upstream Lean source removed: {path}")
    for path in recorded:
        if path not in baseline:
            failures.append(f"ledger path absent from upstream: {path}")
    if failures:
        for failure in failures:
            print(failure)
        return 1
    print(f"Preservation ledger verified: {changed} accounted changes; every upstream Lean file remains present.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
