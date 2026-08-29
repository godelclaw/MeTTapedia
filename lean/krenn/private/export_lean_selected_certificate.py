#!/usr/bin/env python3
"""Export the selected core of a strict exact unit certificate to Lean.

The complete frozen system and complete multiplier list are first replayed by
the strict checker.  Lean then needs only the nonzero multiplier subfamily;
the frozen file and semantic hashes preserve provenance without embedding
hundreds of unused zero-multiplier rows in every module.
"""

from __future__ import annotations

import os
import argparse
import hashlib
import json
import sys
from pathlib import Path

KRENN_ROOT = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
sys.path.insert(0, str(KRENN_ROOT))

from export_lean_sparse_certificate import (  # noqa: E402
    certificate_multipliers,
    lean_poly,
    vector_definition,
)
from strict_certificate_checker import (  # noqa: E402
    check_c4,
    frozen_poly,
    load_json_strict,
    symbols_for,
    validate_variable_names,
)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("system", type=Path)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--namespace", required=True)
    args = parser.parse_args()

    verdict = check_c4(args.system, args.certificate)
    constant = int(verdict["basis"])
    if constant == 0:
        raise ValueError("zero certificate constant is not a contradiction")
    system = load_json_strict(args.system)
    names = validate_variable_names(system["variables"])
    symbols = symbols_for(names)
    equations = [frozen_poly(row, symbols) for row in system["equations"]]
    multipliers = certificate_multipliers(args.certificate, symbols)
    if len(equations) != len(multipliers):
        raise ValueError("system/certificate equation count drift")
    selected = [index for index, value in enumerate(multipliers) if not value.is_zero]
    if selected != [value - 1 for value in verdict["nonzero_multiplier_indices_1based"]]:
        raise ValueError("strict checker/exporter selected-row drift")

    lines = [
        "import KrennSparseCertificate",
        "",
        "/-! Selected core of a strict exact certificate over a frozen system. -/",
        "",
        f"namespace {args.namespace}",
        "",
        "open Krenn.SparseCertificate",
        "open MvPolynomial",
        "",
        f'def sourceSystemFileSHA256 : String := "{digest(args.system)}"',
        f'def sourceSystemSemanticSHA256 : String := "{system["system_sha256"]}"',
        f'def certificateSHA256 : String := "{digest(args.certificate)}"',
        f"def sourceEquationCount : Nat := {len(equations)}",
        "",
    ]
    lines.extend(vector_definition(
        "selectedIndices", len(selected), f"Fin {len(equations)}",
        [str(index) for index in selected],
    ))
    lines.extend(["", *vector_definition(
        "selectedEquations", len(selected),
        f"SparsePoly (Fin {len(symbols)})",
        [lean_poly(equations[index]) for index in selected],
    )])
    lines.extend(["", *vector_definition(
        "multipliers", len(selected),
        f"SparsePoly (Fin {len(symbols)})",
        [lean_poly(multipliers[index]) for index in selected],
    )])
    lines.extend([
        "",
        "set_option maxRecDepth 100000 in",
        "set_option maxHeartbeats 5000000 in",
        "theorem constantIdentity :",
        "    ∑ index, (multipliers index).toPoly *",
        f"      (selectedEquations index).toPoly = C ({constant} : ℤ) := by",
        "  simp (config := { maxSteps := 1000000 })",
        "    [Fin.sum_univ_succ, multipliers, selectedEquations,",
        "      SparsePoly.toPoly, SparseTerm.toPoly]",
        "  ring",
        "",
        "theorem selectedHasNoCommonZero {R : Type*}",
        "    [CommRing R] [Nontrivial R] [CharZero R]",
        f"    (values : Fin {len(symbols)} → R) :",
        f"    ¬ ∀ index : Fin {len(selected)},",
        "      eval₂Hom (Int.castRingHom R) values",
        "        (selectedEquations index).toPoly = 0 := by",
        f"  have constantNonzero : (({constant} : ℤ) : R) ≠ 0 := by",
        f"    exact_mod_cast (show ({constant} : ℤ) ≠ 0 by decide)",
        "  exact noCommonZero_of_sparseConstantCertificate",
        f"    selectedEquations multipliers ({constant} : ℤ)",
        "    constantIdentity constantNonzero values",
        "",
        f"#print axioms {args.namespace}.selectedHasNoCommonZero",
        "",
        f"end {args.namespace}",
        "",
    ])
    args.output.write_text("\n".join(lines), encoding="utf-8")
    print(json.dumps({
        "certificate_file_sha256": verdict["certificate_file_sha256"],
        "output_file_sha256": digest(args.output),
        "selected_rows": selected,
        "source_equations": len(equations),
        "source_system_file_sha256": verdict["system_file_sha256"],
        "source_system_semantic_sha256": system["system_sha256"],
        "variables": len(symbols),
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
