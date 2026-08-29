#!/usr/bin/env python3
"""Export the selected rows of a strict certificate without duplicating its parent.

The ordinary sparse-certificate exporter serializes every parent equation into
each leaf module.  Carrier trees share a large root family, so that is correct
but needlessly expensive to elaborate hundreds of times.  This exporter keeps
only the rows whose multipliers are nonzero.  A tree wrapper must separately
prove each selected row from the shared root family and its branch equations;
Lean checks those equalities at the wrapper boundary.

It is a private scaling prototype.  The strict Python checker is still run
before serialization, and Lean still replays the exact integer identity.
"""

from __future__ import annotations

import os
import argparse
import sys
from pathlib import Path

SHARED_KRENN = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
if str(SHARED_KRENN) not in sys.path:
    sys.path.insert(0, str(SHARED_KRENN))

from export_lean_sparse_certificate import (
    certificate_multipliers,
    lean_poly,
    sha256,
    vector_definition,
)
from strict_certificate_checker import (
    check_c4,
    frozen_poly,
    load_json_strict,
    symbols_for,
    validate_variable_names,
)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("system", type=Path)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--namespace", default="Krenn.SelectedCertificate")
    args = parser.parse_args()
    args.system = args.system.resolve()
    args.certificate = args.certificate.resolve()
    args.output = args.output.resolve()

    verdict = check_c4(args.system, args.certificate)
    try:
        constant = int(verdict["basis"])
    except (KeyError, TypeError, ValueError) as error:
        raise ValueError("certificate basis is not an integer constant") from error
    if constant == 0:
        raise ValueError("zero certificate constant does not prove inconsistency")

    system = load_json_strict(args.system)
    names = validate_variable_names(system["variables"])
    symbols = symbols_for(names)
    equations = [frozen_poly(row, symbols) for row in system["equations"]]
    multipliers = certificate_multipliers(args.certificate, symbols)
    if len(equations) != len(multipliers):
        raise ValueError("system/certificate equation count drift")
    selected_indices = [index for index, multiplier in enumerate(multipliers)
                        if not multiplier.is_zero]
    selected_equations = [equations[index] for index in selected_indices]
    selected_multipliers = [multipliers[index] for index in selected_indices]

    lines = [
        "import KrennSparseCertificate",
        "",
        "/-!",
        "A selected-row reflection of a strict frozen certificate.",
        "The surrounding carrier tree supplies the semantic route from these",
        "rows to the shared root system and the chart assumptions.",
        "-/",
        "",
        f"namespace {args.namespace}",
        "",
        "open Krenn.SparseCertificate",
        "open MvPolynomial",
        "",
        f'def systemSHA256 : String := "{sha256(args.system)}"',
        f'def certificateSHA256 : String := "{sha256(args.certificate)}"',
        "",
    ]
    lines.extend(vector_definition(
        "selectedSourceIndices", len(selected_indices), f"Fin {len(equations)}",
        [str(index) for index in selected_indices],
    ))
    lines.extend(["", *vector_definition(
        "selectedEquations", len(selected_equations),
        f"SparsePoly (Fin {len(symbols)})",
        [lean_poly(row) for row in selected_equations],
    )])
    lines.extend(["", *vector_definition(
        "multipliers", len(selected_multipliers),
        f"SparsePoly (Fin {len(symbols)})",
        [lean_poly(row) for row in selected_multipliers],
    )])
    lines.extend([
        "",
        "set_option maxRecDepth 100000 in",
        "set_option maxHeartbeats 5000000 in",
        "/-- Lean replays the exact selected-row integer certificate. -/",
        "theorem constantIdentity :",
        "    ∑ index, (multipliers index).toPoly *",
        f"      (selectedEquations index).toPoly = C ({constant} : ℤ) := by",
        "  simp (config := { maxSteps := 1000000 })",
        "    [Fin.sum_univ_succ, multipliers, selectedEquations,",
        "    SparsePoly.toPoly, SparseTerm.toPoly]",
        "  ring",
        "",
        "/-- The selected rows have no common zero in a characteristic-zero ring. -/",
        "theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]",
        f"    (values : Fin {len(symbols)} → R) :",
        f"    ¬ ∀ index : Fin {len(selected_equations)},",
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
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("\n".join(lines))
    print(
        "{" + ", ".join([
            f'\"system_sha256\": \"{sha256(args.system)}\"',
            f'\"certificate_sha256\": \"{sha256(args.certificate)}\"',
            f'\"selected_equations\": {len(selected_equations)}',
            f'\"parent_equations_omitted\": {len(equations) - len(selected_equations)}',
            f'\"output_sha256\": \"{sha256(args.output)}\"',
        ]) + "}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
