#!/usr/bin/env python3
"""Expose the factor-forced ``w_05_21`` inverse on one chart-0 face.

On the chart-0 branch ``w_24_11 != 0, w_25_11 = 0``, the frozen
``Gb`` inverse equation becomes

    (delta_0_1 + w_04_21) * w_24_11 * factor_gb_inv - 1 = 0.

Thus ``w_05_21 = delta_0_1 + w_04_21`` has the explicit inverse
``w_24_11 * factor_gb_inv``.  The extension below is checked by exact
polynomial equality against that inherited frozen row before it is
written.  It is a provenance-preserving enrichment, not a solver
inference.
"""

from __future__ import annotations

import os
import hashlib
import json
import sys
from pathlib import Path

import sympy as sp


SHARED = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
if str(SHARED) not in sys.path:
    sys.path.insert(0, str(SHARED))

from c4_crux_freeze import canonical_polynomial, write_msolve, write_singular_lift
from strict_certificate_checker import frozen_poly, symbols_for, validate_variable_names


PARENT = Path("private/chart0_x24_split_v1/live_x25zero/system.json")
PARENT_SOURCE = Path("private/chart0_x24_split_v1/live/system.json")
ROOT_SOURCE = Path(
    Path(os.environ.get("KRENN_ARTIFACTS", "artifacts")) / "noncollapse_case_artifacts/"
    "pair_type01_pivot_cover_reflected_factor_v1/chart_0_pivot_w23/system.json"
)
TARGET = Path("private/chart0_x24_split_v1/live_x25zero_enriched")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def semantic_hash(variables: list[str], equations: list[object]) -> str:
    return hashlib.sha256(json.dumps(
        {"variables": variables, "equations": equations},
        sort_keys=True, separators=(",", ":"),
    ).encode()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def main() -> int:
    require(not TARGET.exists(), f"refusing to overwrite {TARGET}")
    parent = json.loads(PARENT.read_text())
    require(parent["source_system_file_sha256"] == sha256(PARENT_SOURCE),
            "parent/immediate-source hash mismatch")
    immediate = json.loads(PARENT_SOURCE.read_text())
    require(immediate["source_system_file_sha256"] == sha256(ROOT_SOURCE),
            "immediate/root-source hash mismatch")
    require(parent["zero_coordinates"] == ["w_25_11"],
            "not the expected x24-live/x25-zero face")

    names = validate_variable_names(parent["variables"])
    symbols = symbols_for(names)
    table = dict(zip(names, symbols, strict=True))
    needed = {"delta_0_1", "w_04_21", "w_24_11", "factor_gb_inv",
              "leaf_inv_0_w_24_11"}
    require(needed <= set(names), "required factor variables absent")
    rows = [frozen_poly(row, symbols).as_expr() for row in parent["equations"]]
    delta, w04, w24, gb_inv, x24_inv = (table[name] for name in
                                        ("delta_0_1", "w_04_21", "w_24_11",
                                         "factor_gb_inv", "leaf_inv_0_w_24_11"))
    w05 = delta + w04
    factor_row_index = parent["parent_and_branch_row_to_generator_zero_based"][736]
    require(factor_row_index is not None,
            "factor-Gb inverse unexpectedly vanished")
    # The inherited factor row is exactly w05*w24*gb_inv - 1 on this
    # x25-zero face.  Since the live parent also carries w24*x24_inv - 1,
    # this makes w05 invertible with witness w24*gb_inv.
    factor_row = rows[int(factor_row_index)]
    expected_factor = sp.expand(w05 * w24 * gb_inv - 1)
    require(sp.expand(factor_row - expected_factor) == 0,
            "x25-zero image of factor-Gb inverse drift")
    w24_relation = next(
        (row for row in rows
         if sp.expand(row - (w24 * x24_inv - 1)) == 0),
        None,
    )
    require(w24_relation is not None, "w24 live relation missing")
    w05_inv = sp.Symbol("chart0_x24live_x25zero_w05_inv")
    extra = w05 * w05_inv - 1
    witness = w24 * gb_inv
    require(sp.expand(extra.xreplace({w05_inv: witness}) - factor_row) == 0,
            "w05 inverse witness is not the inherited factor row")
    require(sp.expand(w24_relation - (w24 * x24_inv - 1)) == 0,
            "w24 inverse relation drift")

    variables = (*symbols, w05_inv)
    equations = [canonical_polynomial(row, variables) for row in (*rows, extra)]
    payload = {
        "format": "krenn-chart0-x24live-x25zero-w05-inverse-v1",
        "parent_system_file_sha256": sha256(PARENT),
        "source_system_file_sha256": sha256(ROOT_SOURCE),
        "immediate_source_system_file_sha256": sha256(PARENT_SOURCE),
        "factor_gb_parent_row_zero_based": 736,
        "factor_gb_child_generator_zero_based": factor_row_index,
        "extension_witnesses": {
            "chart0_x24live_x25zero_w05_inv": str(witness),
        },
        "variables": [str(symbol) for symbol in variables],
        "equations": equations,
        "statistics": {
            "parent_generators": len(rows),
            "added_inverse_generators": 1,
            "variables": len(variables),
        },
    }
    payload["system_sha256"] = semantic_hash(payload["variables"], equations)
    TARGET.mkdir(parents=True)
    system = TARGET / "system.json"
    system.write_text(json.dumps(payload, sort_keys=True, indent=2) + "\n")
    polynomials = [frozen_poly(row, variables).as_expr() for row in equations]
    write_msolve(TARGET / "input_q.ms", variables, polynomials, 0)
    write_msolve(TARGET / "input_p32003.ms", variables, polynomials, 32003)
    write_singular_lift(TARGET / "lift.sing", variables, polynomials)
    manifest = {
        "format": "krenn-chart0-x24live-x25zero-w05-inverse-manifest-v1",
        "generator_sha256": sha256(Path(__file__)),
        "system_file_sha256": sha256(system),
        "system_sha256": payload["system_sha256"],
        "parent_system_file_sha256": payload["parent_system_file_sha256"],
        "source_system_file_sha256": payload["source_system_file_sha256"],
        "immediate_source_system_file_sha256": payload["immediate_source_system_file_sha256"],
    }
    manifest_path = TARGET / "manifest.json"
    manifest_path.write_text(json.dumps(manifest, sort_keys=True, indent=2) + "\n")
    print(json.dumps(manifest, sort_keys=True))
    print("manifest_sha256=" + sha256(manifest_path))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
