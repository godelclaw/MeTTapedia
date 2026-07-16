#!/usr/bin/env python3
"""Exact finite transport census for charged public disagreements.

Worlds are Boolean public strings.  A nonconstant truth table is the target
bit, a mask selects charged public coordinates, and the complementary
coordinates are required to agree across a coupling.  The left and right
marginals are the uniform laws conditioned on target false and target true.

The transportation problem is scaled to an integral assignment problem.
Every left world is repeated once for each right-phase world and conversely,
so one unit of assignment mass represents ``1 / (|L| |R|)``.  The objective
is charged Hamming disagreement.  Selected sharp primal assignments are
paired with the universal dual certificate ``u = 1, v = 0``.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from collections import Counter
from fractions import Fraction
from pathlib import Path
from typing import Any

from scipy.optimize import linear_sum_assignment


def bit(table: int, world: int) -> int:
    return (table >> world) & 1


def charged_distance(left: int, right: int, charged_mask: int) -> int:
    return ((left ^ right) & charged_mask).bit_count()


def solve_transport(n: int, table: int, charged_mask: int) -> dict[str, Any] | None:
    worlds = range(1 << n)
    left = [w for w in worlds if bit(table, w) == 0]
    right = [w for w in worlds if bit(table, w) == 1]
    if not left or not right:
        return None

    neutral_mask = ((1 << n) - 1) ^ charged_mask
    left_fibers = Counter(w & neutral_mask for w in left)
    right_fibers = Counter(w & neutral_mask for w in right)
    left_count = len(left)
    right_count = len(right)

    fibers = set(left_fibers) | set(right_fibers)
    if any(
        left_fibers[z] * right_count != right_fibers[z] * left_count
        for z in fibers
    ):
        return None

    left_slots = [w for w in left for _ in range(right_count)]
    right_slots = [w for w in right for _ in range(left_count)]
    forbidden = n + 1
    costs = [
        [
            charged_distance(x, y, charged_mask)
            if (x & neutral_mask) == (y & neutral_mask)
            else forbidden
            for y in right_slots
        ]
        for x in left_slots
    ]
    row_index, column_index = linear_sum_assignment(costs)

    flow: Counter[tuple[int, int]] = Counter()
    numerator = 0
    for row, column in zip(row_index.tolist(), column_index.tolist(), strict=True):
        x = left_slots[row]
        y = right_slots[column]
        cost = costs[row][column]
        if cost == forbidden:
            raise AssertionError("balanced neutral fibers produced a forbidden assignment")
        flow[x, y] += 1
        numerator += cost

    denominator = left_count * right_count

    for x in left:
        if sum(amount for (a, _), amount in flow.items() if a == x) != right_count:
            raise AssertionError("incorrect scaled left marginal")
    for y in right:
        if sum(amount for (_, b), amount in flow.items() if b == y) != left_count:
            raise AssertionError("incorrect scaled right marginal")
    for (x, y), amount in flow.items():
        if amount <= 0 or (x & neutral_mask) != (y & neutral_mask):
            raise AssertionError("invalid coupling support")

    allowed_costs = [
        charged_distance(x, y, charged_mask)
        for x in left
        for y in right
        if (x & neutral_mask) == (y & neutral_mask)
    ]
    if not allowed_costs or min(allowed_costs) < 1:
        raise AssertionError("opposite targets crossed without charged disagreement")

    dual_numerator = denominator
    if dual_numerator > numerator:
        raise AssertionError("dual lower bound exceeds primal value")

    return {
        "n": n,
        "target_table": table,
        "charged_mask": charged_mask,
        "neutral_mask": neutral_mask,
        "left_worlds": left,
        "right_worlds": right,
        "scale": denominator,
        "flow": [
            {"left": x, "right": y, "amount": amount}
            for (x, y), amount in sorted(flow.items())
        ],
        "objective_numerator": numerator,
        "objective_denominator": denominator,
        "dual_left_potential": 1,
        "dual_right_potential": 0,
        "dual_numerator": dual_numerator,
    }


def census_dimension(n: int) -> tuple[dict[str, Any], dict[str, Any]]:
    full_table_mask = (1 << (1 << n)) - 1
    cases: list[tuple[int, int, int, int]] = []
    sharp_certificate: dict[str, Any] | None = None
    feasible = 0
    sharp = 0
    minimum: Fraction | None = None
    maximum: Fraction | None = None

    for table in range(1, full_table_mask):
        for charged_mask in range(1 << n):
            solution = solve_transport(n, table, charged_mask)
            if solution is None:
                continue
            feasible += 1
            value = Fraction(
                solution["objective_numerator"], solution["objective_denominator"]
            )
            if value < 1:
                raise AssertionError("charged disagreement optimum below one")
            minimum = value if minimum is None else min(minimum, value)
            maximum = value if maximum is None else max(maximum, value)
            if value == 1:
                sharp += 1
                if sharp_certificate is None:
                    sharp_certificate = solution
            cases.append(
                (
                    table,
                    charged_mask,
                    solution["objective_numerator"],
                    solution["objective_denominator"],
                )
            )

    if sharp_certificate is None or minimum is None or maximum is None:
        raise AssertionError("dimension has no sharp admissible transport")

    digest_payload = json.dumps(cases, separators=(",", ":"), sort_keys=False).encode()
    summary = {
        "n": n,
        "truth_tables_checked": full_table_mask - 1,
        "charged_masks_per_table": 1 << n,
        "candidate_pairs_checked": (full_table_mask - 1) * (1 << n),
        "admissible_transports": feasible,
        "sharp_transports": sharp,
        "minimum_optimum": str(minimum),
        "maximum_optimum": str(maximum),
        "case_digest_sha256": hashlib.sha256(digest_payload).hexdigest(),
    }
    return summary, sharp_certificate


def shared_localization_family(max_size: int) -> list[dict[str, int]]:
    return [
        {
            "target_count": size,
            "public_bit_count": 1,
            "charged_bit_count": 1,
            "per_target_optimum": 1,
            "coordinate_summed_optimum": size,
            "distinct_charged_atoms": 1,
        }
        for size in range(1, max_size + 1)
    ]


def write_atomic(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    os.replace(temporary, path)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-bits", type=int, default=3)
    parser.add_argument("--shared-targets", type=int, default=8)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--resume", action="store_true")
    args = parser.parse_args()
    if args.max_bits < 1:
        raise SystemExit("--max-bits must be positive")

    if args.resume and args.output.exists():
        payload = json.loads(args.output.read_text())
    else:
        payload = {
            "schema": "pnp-charged-public-budget-certificate-v1",
            "census": [],
            "sharp_certificates": [],
        }

    completed = {row["n"] for row in payload["census"]}
    for n in range(1, args.max_bits + 1):
        if n in completed:
            continue
        summary, certificate = census_dimension(n)
        payload["census"].append(summary)
        payload["sharp_certificates"].append(certificate)
        payload["census"].sort(key=lambda row: row["n"])
        payload["sharp_certificates"].sort(key=lambda row: row["n"])
        payload["shared_localization_family"] = shared_localization_family(
            args.shared_targets
        )
        write_atomic(args.output, payload)

    payload["shared_localization_family"] = shared_localization_family(
        args.shared_targets
    )
    write_atomic(args.output, payload)


if __name__ == "__main__":
    main()
