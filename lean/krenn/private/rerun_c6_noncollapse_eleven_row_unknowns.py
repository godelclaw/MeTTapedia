#!/usr/bin/env python3
"""Give only the first-pass unknown eleven-row transports one standard rerun.

This does not rewrite the original transport manifest.  It reads its explicitly
recorded timeout rows, reruns each exactly once with the established 30-second
exact-Q bound, and stores the new receipts under distinct names.  A unit
result is still accepted only after a fresh strict exact lift/replay.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path

from test_c6_noncollapse_eleven_row_transport import exact_lift, msolve_probe


def sha256_path(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--msolve-timeout", type=int, default=30)
    parser.add_argument("--lift-timeout", type=int, default=30)
    args = parser.parse_args()
    if args.msolve_timeout <= 0 or args.lift_timeout <= 0:
        parser.error("timeouts must be positive")
    if args.output.exists():
        parser.error("output receipt must not already exist")

    initial_manifest = args.root / "manifest.json"
    initial = json.loads(initial_manifest.read_text())
    selected = [
        row for row in initial["rows"]
        if row["msolve"]["verdict"] == "timeout_unknown"
    ]
    rows = []
    for row in selected:
        candidate = args.root / row["tag"]
        probe = msolve_probe(
            candidate, args.msolve_timeout, basis_name="basis_standard30s.out"
        )
        lift = None
        if probe["verdict"] == "unit_ideal":
            lift = exact_lift(
                candidate, args.lift_timeout, output_name="lift_tracked_standard30s"
            )
        outcome = {
            "tag": row["tag"],
            "system_file_sha256": row["system_file_sha256"],
            "initial_msolve": row["msolve"],
            "standard_msolve": probe,
            "lift": lift,
        }
        rows.append(outcome)
        print(json.dumps({
            "tag": row["tag"],
            "msolve": probe["verdict"],
            "lift": None if lift is None else lift["verdict"],
        }, sort_keys=True), flush=True)

    counts = Counter(
        "strict_exact_identity" if row["lift"] and
        row["lift"]["verdict"] == "strict_exact_identity"
        else row["standard_msolve"]["verdict"]
        for row in rows
    )
    payload = {
        "format": "krenn-c6-noncollapse-eleven-row-standard30s-rerun-v1",
        "initial_manifest_sha256": sha256_path(initial_manifest),
        "candidate_count": len(rows),
        "msolve_timeout_seconds": args.msolve_timeout,
        "lift_timeout_seconds": args.lift_timeout,
        "counts": dict(sorted(counts.items())),
        "rows": rows,
    }
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print("manifest_sha256=" + sha256_path(args.output))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
