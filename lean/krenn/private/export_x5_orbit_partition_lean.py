#!/usr/bin/env python3
"""Export the audited 317/19 representative partition as decidable Lean data."""

from __future__ import annotations

import os
import argparse
import hashlib
import json
import sys
from pathlib import Path


KRENN_ROOT = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
sys.path.insert(0, str(KRENN_ROOT))

from audit_x5_0415_closure import (  # noqa: E402
    LOG,
    RESIDUAL,
    exact_case_representatives,
    parse_historical_partition,
)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lean_list(values: list[int], indent: str = "  ") -> list[str]:
    lines: list[str] = []
    width = 78
    current = indent + "["
    for offset, value in enumerate(values):
        token = str(value) + ("," if offset + 1 < len(values) else "]")
        if len(current) + 1 + len(token) > width:
            lines.append(current)
            current = indent + " " + token
        else:
            if not current.endswith("["):
                current += " "
            current += token
    lines.append(current)
    return lines


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()

    representatives, _cover = exact_case_representatives()
    exact = sorted(row[0] for row in representatives)
    closed_set, residual_set = parse_historical_partition(LOG.read_text())
    closed = sorted(closed_set)
    residual = sorted(residual_set)
    if len(exact) != 336 or len(closed) != 317 or len(residual) != 19:
        raise ValueError("audited partition cardinality drift")
    if set(exact) != set(closed) | set(residual) or set(closed) & set(residual):
        raise ValueError("audited partition set drift")
    frozen_residual = json.loads(RESIDUAL.read_text())
    if sorted(int(row["case"]) for row in frozen_residual["rows"]) != residual:
        raise ValueError("frozen residual inventory drift")

    lines = [
        "import Mathlib",
        "",
        "/-!",
        "Exact finite partition for the 336 normalized representatives of the",
        "`X = {01,02,03,04,15}` support orbit.",
        "",
        "This module checks the finite bookkeeping only: 317 historical",
        "multilinear closures and 19 strictly reflected residual closures are",
        "distinct and exhaust the audited representative list.  The semantic",
        "symmetry/normalization action remains a separate theorem.",
        "-/",
        "",
        "namespace Krenn.X5OrbitPartition",
        "",
        f'def historicalLogSHA256 : String := "{digest(LOG)}"',
        f'def residualManifestSHA256 : String := "{digest(RESIDUAL)}"',
        "",
        "def exactRepresentativeIndices : List Nat :=",
        *lean_list(exact),
        "",
        "def historicalClosedIndices : List Nat :=",
        *lean_list(closed),
        "",
        "def residualIndices : List Nat :=",
        *lean_list(residual),
        "",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 5000000",
        "",
        "theorem exactRepresentativeIndices_length :",
        "    exactRepresentativeIndices.length = 336 := by decide",
        "",
        "theorem historicalClosedIndices_length :",
        "    historicalClosedIndices.length = 317 := by decide",
        "",
        "theorem residualIndices_length : residualIndices.length = 19 := by decide",
        "",
        "theorem exactRepresentativeIndices_nodup :",
        "    exactRepresentativeIndices.Nodup := by decide",
        "",
        "theorem historicalClosedIndices_nodup : historicalClosedIndices.Nodup := by decide",
        "",
        "theorem residualIndices_nodup : residualIndices.Nodup := by decide",
        "",
        "theorem closed_residual_disjoint :",
        "    Disjoint historicalClosedIndices.toFinset residualIndices.toFinset := by decide",
        "",
        "theorem representative_partition :",
        "    exactRepresentativeIndices.toFinset =",
        "      historicalClosedIndices.toFinset ∪ residualIndices.toFinset := by decide",
        "",
        "#print axioms Krenn.X5OrbitPartition.representative_partition",
        "",
        "end Krenn.X5OrbitPartition",
        "",
    ]
    args.output.write_text("\n".join(lines), encoding="utf-8")
    receipt = {
        "format": "krenn-x5-orbit-partition-lean-export-v1",
        "exact_representatives": len(exact),
        "historical_closed": len(closed),
        "strict_residual": len(residual),
        "historical_log_sha256": digest(LOG),
        "residual_manifest_sha256": digest(RESIDUAL),
        "output_sha256": digest(args.output),
        "exporter_sha256": digest(Path(__file__)),
    }
    if args.receipt is not None:
        args.receipt.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps(receipt, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
