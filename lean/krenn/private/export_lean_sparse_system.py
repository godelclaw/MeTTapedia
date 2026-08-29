#!/usr/bin/env python3
"""Serialize one frozen sparse system as a shared Lean root family.

Carrier-tree leaves can cite this one definition instead of each embedding a
copy of the common root equations.  This is intentionally data-only: Lean
reconstructs the polynomials from the integer term lists at use sites.
"""

from __future__ import annotations

import os
import argparse
import sys
from pathlib import Path

SHARED_KRENN = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
if str(SHARED_KRENN) not in sys.path:
    sys.path.insert(0, str(SHARED_KRENN))

from export_lean_sparse_certificate import lean_poly, sha256, vector_definition
from strict_certificate_checker import frozen_poly, load_json_strict, symbols_for, validate_variable_names


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("system", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--namespace", default="Krenn.SharedRoot")
    args = parser.parse_args()
    args.system = args.system.resolve()
    args.output = args.output.resolve()

    payload = load_json_strict(args.system)
    names = validate_variable_names(payload["variables"])
    symbols = symbols_for(names)
    equations = [frozen_poly(row, symbols) for row in payload["equations"]]
    lines = [
        "import KrennSparseCertificate",
        "",
        "/-! A frozen shared root system, reflected from integer sparse data. -/",
        "",
        f"namespace {args.namespace}",
        "",
        "open Krenn.SparseCertificate",
        "open MvPolynomial",
        "",
        f'def systemSHA256 : String := "{sha256(args.system)}"',
        "",
        *vector_definition(
            "rootEquations", len(equations), f"SparsePoly (Fin {len(names)})",
            [lean_poly(row) for row in equations],
        ),
        "",
        "def RootCommonZero {R : Type*} [CommRing R]",
        f"    (values : Fin {len(names)} → R) : Prop :=",
        "  ∀ index, eval₂Hom (Int.castRingHom R) values",
        "    (rootEquations index).toPoly = 0",
        "",
        f"end {args.namespace}",
        "",
    ]
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("\n".join(lines))
    print(
        f'{{"system_sha256":"{sha256(args.system)}","variables":{len(names)},'
        f'"equations":{len(equations)},"output_sha256":"{sha256(args.output)}"}}'
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
