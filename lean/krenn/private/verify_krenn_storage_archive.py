#!/usr/bin/env python3
"""Stream-verify a compressed tar archive against its content manifest."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tarfile


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("archive", type=Path)
    parser.add_argument("manifest", type=Path)
    args = parser.parse_args()

    expected = {}
    for line in args.manifest.read_text(encoding="utf-8").splitlines():
        row = json.loads(line)
        expected[row["path"]] = (row["bytes"], row["sha256"])

    seen = set()
    process = subprocess.Popen(["zstd", "-qdc", str(args.archive)], stdout=subprocess.PIPE)
    assert process.stdout is not None
    try:
        with tarfile.open(fileobj=process.stdout, mode="r|") as archive:
            for member in archive:
                if not member.isfile():
                    raise SystemExit(f"unexpected non-file archive member: {member.name}")
                if member.name not in expected:
                    raise SystemExit(f"unexpected archive member: {member.name}")
                if member.name in seen:
                    raise SystemExit(f"duplicate archive member: {member.name}")
                size, wanted = expected[member.name]
                if member.size != size:
                    raise SystemExit(f"size mismatch for {member.name}")
                extracted = archive.extractfile(member)
                if extracted is None:
                    raise SystemExit(f"cannot read archive member: {member.name}")
                digest = hashlib.sha256()
                for block in iter(lambda: extracted.read(4 * 1024 * 1024), b""):
                    digest.update(block)
                if digest.hexdigest() != wanted:
                    raise SystemExit(f"SHA-256 mismatch for {member.name}")
                seen.add(member.name)
    finally:
        process.stdout.close()
    status = process.wait()
    if status != 0:
        raise SystemExit(f"zstd exited with status {status}")
    missing = set(expected) - seen
    if missing:
        raise SystemExit(f"archive omits {len(missing)} manifest members")
    print(json.dumps({
        "archive_sha256": hashlib.sha256(args.archive.read_bytes()).hexdigest(),
        "manifest_sha256": hashlib.sha256(args.manifest.read_bytes()).hexdigest(),
        "verified_files": len(seen),
        "verified_logical_bytes": sum(size for size, _ in expected.values()),
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
