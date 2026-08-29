#!/usr/bin/env python3
"""Separate genuine factor-probe closures from already-inverted coordinates.

The chart-0 factor experiment branches on three coordinates per quadratic row.
If the frozen parent already contains ``u * x - 1``, every child setting ``x``
to zero is contradictory before the selected factor row is used.  This audit
identifies those children, verifies the recorded branch bytes and strict lift
framing, and reports the remaining nontrivial closures separately.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys
from typing import Any, NoReturn


EXPECTED_FORMAT = "krenn-frozen-coordinate-branch-inventory-v1"
CERTIFICATE_END = "C4_LIFT_CERTIFICATE_END"


def fail(message: str) -> NoReturn:
    raise SystemExit("CHART0 FACTOR BASELINE AUDIT FAILED: " + message)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def load_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        fail(f"cannot read {path}: {error}")


def section_first_line(text: str, begin: str, end: str) -> str | None:
    lines = text.splitlines()
    try:
        start = lines.index(begin)
        stop = lines.index(end, start + 1)
    except ValueError:
        return None
    body = lines[start + 1 : stop]
    return body[0].strip() if body else None


def strict_certificate(path: Path) -> bool:
    try:
        text = path.read_text(encoding="utf-8", errors="strict")
    except (OSError, UnicodeError):
        return False
    return (
        text.rstrip().endswith(CERTIFICATE_END)
        and section_first_line(text, "C4_LIFT_BASIS_BEGIN", "C4_LIFT_BASIS_END")
        == "1"
        and section_first_line(text, "C4_LIFT_CHECK_BEGIN", "C4_LIFT_CHECK_END")
        == "1"
    )


def directly_inverted_coordinates(system: dict[str, Any]) -> dict[str, dict[str, Any]]:
    variables = system["variables"]
    result: dict[str, dict[str, Any]] = {}
    for equation_index, equation in enumerate(system["equations"]):
        if len(equation) != 2:
            continue
        constant_terms = [(coefficient, exponents) for coefficient, exponents in equation if sum(exponents) == 0]
        nonconstant_terms = [(coefficient, exponents) for coefficient, exponents in equation if sum(exponents) != 0]
        if len(constant_terms) != 1 or len(nonconstant_terms) != 1:
            continue
        coefficient, exponents = nonconstant_terms[0]
        nonzero = [index for index, exponent in enumerate(exponents) if exponent]
        if coefficient not in (-1, 1) or len(nonzero) != 2:
            continue
        if any(exponents[index] != 1 for index in nonzero):
            continue
        names = [variables[index] for index in nonzero]
        inverses = [name for name in names if "inv" in name]
        coordinates = [name for name in names if "inv" not in name]
        if len(inverses) == 1 and len(coordinates) == 1:
            result[coordinates[0]] = {
                "equation": equation_index,
                "inverse": inverses[0],
            }
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("system", type=Path)
    parser.add_argument("rows", type=Path)
    parser.add_argument("probe_root", type=Path)
    parser.add_argument("--stage2-log", type=Path)
    args = parser.parse_args()

    system = load_json(args.system)
    rows = load_json(args.rows)
    system_file_sha256 = sha256(args.system)
    inverted = directly_inverted_coordinates(system)
    if not inverted:
        fail("parent system has no directly inverted coordinates")

    row_results: list[dict[str, Any]] = []
    for row in rows:
        equation = row["eq"]
        expected_coordinates = row["coords"]
        row_root = args.probe_root / f"row{equation}_split"
        inventory_path = row_root / "inventory.json"
        inventory = load_json(inventory_path)
        if inventory.get("format") != EXPECTED_FORMAT:
            fail(f"row {equation}: unexpected inventory format")
        if inventory.get("source_system_file_sha256") != system_file_sha256:
            fail(f"row {equation}: parent-system hash mismatch")
        if inventory.get("coordinates") != expected_coordinates:
            fail(f"row {equation}: coordinate list mismatch")
        branches = inventory.get("branches")
        if not isinstance(branches, list) or len(branches) != 8:
            fail(f"row {equation}: expected eight branches")

        closed: list[int] = []
        trivial: list[int] = []
        nontrivial_closed: list[int] = []
        for branch in branches:
            index = branch["branch"]
            bits = branch["nonzero_bits"]
            if len(bits) != len(expected_coordinates):
                fail(f"row {equation} branch {index}: bit-vector length mismatch")
            branch_root = row_root / f"branch_{index}"
            branch_system = branch_root / "system.json"
            if sha256(branch_system) != branch["system_file_sha256"]:
                fail(f"row {equation} branch {index}: branch-system hash mismatch")
            is_trivial = any(
                bit == 0 and coordinate in inverted
                for bit, coordinate in zip(bits, expected_coordinates, strict=True)
            )
            is_closed = strict_certificate(branch_root / "lift.stdout")
            if is_trivial:
                trivial.append(index)
            if is_closed:
                closed.append(index)
                if not is_trivial:
                    nontrivial_closed.append(index)

        missing_trivial = sorted(set(trivial) - set(closed))
        if missing_trivial:
            fail(
                f"row {equation}: already-inverted branches lack strict certificates: "
                + ", ".join(map(str, missing_trivial))
            )
        row_results.append(
            {
                "equation": equation,
                "coordinates": expected_coordinates,
                "closed": closed,
                "trivial_inverse_closures": trivial,
                "nontrivial_closures": nontrivial_closed,
            }
        )

    superior = [row["equation"] for row in row_results if len(row["closed"]) >= 4]
    nontrivial_superior = [
        row["equation"] for row in row_results if len(row["nontrivial_closures"]) >= 4
    ]
    output: dict[str, Any] = {
        "format": "krenn-chart0-factor-inverse-baseline-audit-v1",
        "system_file_sha256": system_file_sha256,
        "directly_inverted_coordinates": inverted,
        "rows": row_results,
        "sealed_superior_rows": superior,
        "rows_with_at_least_four_nontrivial_closures": nontrivial_superior,
    }
    if args.stage2_log is not None:
        try:
            stage2 = args.stage2_log.read_text(encoding="utf-8", errors="strict")
        except (OSError, UnicodeError) as error:
            fail(f"cannot read stage-2 log: {error}")
        output["stage2_probe"] = {
            "log_sha256": sha256(args.stage2_log),
            "discovery_timeouts": stage2.count("DISCOVERY_FAILED rc=124"),
            "strict_certificates": stage2.count("STRICT_CERTIFICATE PASS"),
            "complete": "=== COMPLETE " in stage2,
        }
    json.dump(output, sys.stdout, indent=2, sort_keys=True)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
