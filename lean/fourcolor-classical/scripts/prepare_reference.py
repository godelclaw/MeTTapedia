#!/usr/bin/env python3
"""Apply the single import compatibility edit to the pinned reference source."""

import argparse
from pathlib import Path
import subprocess

REVISION = "3db71e0a786a1f19be04c5266fe3d06fed216885"
SOURCE = "FourColor/Finitize.lean"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference", type=Path,
                        default=Path(__file__).resolve().parents[2] / "externals/fourcolor")
    args = parser.parse_args()
    reference = args.reference.resolve()
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"],
                                       cwd=reference, text=True).strip()
    if revision != REVISION:
        raise SystemExit("Reference revision differs from the integration pin")
    original = subprocess.check_output(["git", "show", REVISION + ":" + SOURCE],
                                       cwd=reference)
    old = b"import Mathlib.Basic.Denumerable"
    new = b"import Mathlib.Logic.Denumerable"
    if original.count(old) != 1:
        raise SystemExit("The pinned source has an unexpected import layout")
    compatible = original.replace(old, new)
    source = reference / SOURCE
    current = source.read_bytes()
    if current not in (original, compatible):
        raise SystemExit("Preserving a reference file with unrelated edits")
    if current != compatible:
        source.write_bytes(compatible)
    print("Pinned reference import compatibility verified; proof bodies unchanged.")


if __name__ == "__main__":
    main()
