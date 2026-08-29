#!/usr/bin/env python3
"""Export a frozen integer polynomial system as Lean sparse data.

The resulting module contains a kernel-reconstructible copy of every input
polynomial, plus both byte and semantic digests.  It intentionally does not
claim that either digest is checked inside Lean; the sparse literal equality is
the actual proof-facing object.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lean_term(term: object, variables: int) -> str:
    if not isinstance(term, list) or len(term) != 2:
        raise ValueError("term must be [integer coefficient, exponent vector]")
    coefficient, exponents = term
    if not isinstance(coefficient, int):
        raise ValueError("coefficient is not an integer")
    if not isinstance(exponents, list) or len(exponents) != variables:
        raise ValueError("exponent-vector length drift")
    powers: list[str] = []
    for index, exponent in enumerate(exponents):
        if not isinstance(exponent, int) or exponent < 0:
            raise ValueError("exponent is not a natural number")
        if exponent:
            powers.append(f"({index}, {exponent})")
    return "{ coefficient := %d, powers := [%s] }" % (
        coefficient, ", ".join(powers))


def lean_poly(polynomial: object, variables: int) -> str:
    if not isinstance(polynomial, list) or not polynomial:
        raise ValueError("equation must be a nonempty term list")
    return "[" + ", ".join(lean_term(term, variables) for term in polynomial) + "]"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("system", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--namespace", default="Krenn.FrozenCase0System")
    args = parser.parse_args()
    system_path = args.system.resolve()
    payload = json.loads(system_path.read_text(encoding="utf-8"))
    if payload.get("format") != "krenn-frozen-polynomial-system-v1":
        raise ValueError("unexpected frozen-system format")
    variables = payload.get("variables")
    equations = payload.get("equations")
    if not isinstance(variables, list) or not all(isinstance(name, str) for name in variables):
        raise ValueError("invalid variable inventory")
    if not isinstance(equations, list) or not equations:
        raise ValueError("invalid equation inventory")
    rendered = [lean_poly(polynomial, len(variables)) for polynomial in equations]
    semantic = payload.get("system_sha256")
    if not isinstance(semantic, str):
        raise ValueError("missing semantic system digest")
    lines = [
        "import KrennSparseCertificate",
        "",
        "/-!",
        "Kernel-facing sparse copy of the frozen C6 case-0 full equation system.",
        "The explicit term data—not the hashes below—is the proof-facing object.",
        "-/",
        "",
        f"namespace {args.namespace}",
        "",
        "open MvPolynomial",
        "open Krenn.SparseCertificate",
        "",
        f'def systemFileSHA256 : String := "{sha256(system_path)}"',
        f'def systemSHA256 : String := "{semantic}"',
        f"def variableCount : Nat := {len(variables)}",
        f"def equationCount : Nat := {len(equations)}",
        "",
        "set_option maxRecDepth 100000 in",
        "set_option maxHeartbeats 5000000 in",
        f"def equations : Fin {len(equations)} → SparsePoly (Fin {len(variables)}) := ![",
    ]
    lines.extend("  " + polynomial + ("," if index + 1 < len(rendered) else "")
                 for index, polynomial in enumerate(rendered))
    lines.extend([
        "]",
        "",
        "noncomputable def CommonZero {R : Type*} [CommRing R]",
        f"    (values : Fin {len(variables)} → R) : Prop :=",
        "  ∀ index, eval₂Hom (Int.castRingHom R) values",
        "    (equations index).toPoly = 0",
        "",
        f"end {args.namespace}",
        "",
    ])
    args.output.write_text("\n".join(lines), encoding="utf-8")
    print(json.dumps({
        "format": "krenn-lean-frozen-system-export-v1",
        "input_file_sha256": sha256(system_path),
        "semantic_system_sha256": semantic,
        "output_sha256": sha256(args.output),
        "variables": len(variables),
        "equations": len(equations),
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
