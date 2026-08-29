#!/usr/bin/env python3
"""Verify and rehydrate a Krenn proof-evidence archive into an empty directory."""

from __future__ import annotations

import argparse
from pathlib import Path
import subprocess
import sys


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("archive", type=Path)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("destination", type=Path)
    parser.add_argument("--verifier", type=Path, required=True)
    args = parser.parse_args()

    destination = args.destination.resolve()
    if destination.exists() and any(destination.iterdir()):
        raise SystemExit("destination must be absent or empty")
    destination.mkdir(parents=True, exist_ok=True)

    subprocess.run(
        [sys.executable, str(args.verifier), str(args.archive), str(args.manifest)],
        check=True,
    )
    decompressor = subprocess.Popen(["zstd", "-qdc", str(args.archive)], stdout=subprocess.PIPE)
    assert decompressor.stdout is not None
    extractor = subprocess.run(
        ["tar", "-xpf", "-", "-C", str(destination)],
        stdin=decompressor.stdout,
        check=False,
    )
    decompressor.stdout.close()
    decompressor_status = decompressor.wait()
    if extractor.returncode != 0 or decompressor_status != 0:
        raise SystemExit(
            f"rehydration failed: tar={extractor.returncode}, zstd={decompressor_status}"
        )
    print(destination)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
