#!/usr/bin/env python3
"""Generate the exact frozen case-0 adjugate connector for Lean.

The generator is deliberately a checker-backed serializer, not a solver.  It
reconstructs the six-cycle case-0 gauge substitution from the canonical
source, checks that the reconstructed 747 generators agree term-for-term with
``system.json``, and emits Lean definitions for the eighteen two-by-two
one-defect systems.  The generated Lean proof then verifies every displayed
polynomial equality with ``ring`` against the frozen source equations.
"""

from __future__ import annotations

import os
import argparse
import hashlib
import json
import sys
from pathlib import Path

import sympy as sp


SHARED = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
if str(SHARED) not in sys.path:
    sys.path.insert(0, str(SHARED))

import c6_collapse_attack as c6  # noqa: E402
import f9_pipeline as pipeline  # noqa: E402


def digest_json(value: object) -> str:
    return hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def read_system(path: Path) -> tuple[dict, list[sp.Symbol], list[sp.Expr]]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    symbols = [sp.Symbol(name) for name in payload["variables"]]
    equations = [
        sp.Poly.from_dict(
            {tuple(exponents): int(coefficient) for coefficient, exponents in row},
            *symbols,
            domain=sp.ZZ,
        ).as_expr()
        for row in payload["equations"]
    ]
    canonical = {"variables": payload["variables"], "equations": payload["equations"]}
    if digest_json(canonical) != payload["system_sha256"]:
        raise ValueError("frozen system hash mismatch")
    return payload, symbols, equations


def lean_expr(expr: sp.Expr, positions: dict[sp.Symbol, int]) -> str:
    poly = sp.Poly(sp.expand(expr), *positions, domain=sp.ZZ)
    rendered: list[str] = []
    for exponents, coefficient in poly.terms():
        factors: list[str] = []
        absolute = abs(int(coefficient))
        if absolute != 1 or not any(exponents):
            factors.append(str(absolute))
        for symbol, exponent in zip(positions, exponents):
            if exponent:
                atom = f"values {positions[symbol]}"
                factors.append(atom if exponent == 1 else f"({atom}) ^ {exponent}")
        term = " * ".join(factors) if factors else "1"
        rendered.append(("- " if coefficient < 0 else "+ ") + f"({term})")
    if not rendered:
        return "0"
    first = rendered[0]
    if first.startswith("+ "):
        first = first[2:]
    elif first.startswith("- "):
        first = "-" + first[2:]
    return " ".join([first, *rendered[1:]])


def vector(rows: list[str], indent: str = "  ") -> str:
    return "![\n" + ",\n".join(indent + row for row in rows) + "\n]"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()

    source = SHARED / "allcollapse_case_artifacts/case_0/system.json"
    payload, symbols, frozen_equations = read_system(source)
    if len(symbols) != 75 or len(frozen_equations) != 747:
        raise ValueError("unexpected frozen case-0 dimensions")
    positions = {symbol: index for index, symbol in enumerate(symbols)}

    case = pipeline.cases_for(c6.X)[0]
    chosen = [(c6.X[index], colours[0], colours[1])
              for index, colours in enumerate(case)]
    fixed = pipeline.max_fixable(chosen)
    substitution = {c6.VAR[key]: sp.Integer(1) for key in fixed}
    base_reconstructed = sorted(
        {sp.expand(poly.xreplace(substitution)) for poly in c6.system()
         if sp.expand(poly.xreplace(substitution)) != 0},
        key=sp.default_sort_key,
    )
    determinant_reconstructed = [
        sp.expand(c6.theta_det(vertex, colour).xreplace(substitution))
        for vertex in range(6) for colour in range(3)
    ]
    reconstructed = sorted(
        set(base_reconstructed) | set(determinant_reconstructed),
        key=sp.default_sort_key,
    )
    if reconstructed != frozen_equations:
        raise ValueError("reconstructed system does not match frozen system")
    generator_index = {poly: index for index, poly in enumerate(reconstructed)}

    slots: list[dict[str, object]] = []
    for vertex in range(6):
        for colour in range(3):
            left_neighbour, right_neighbour = c6.NBR[vertex]
            first, second = [other for other in range(3) if other != colour]
            a1 = sp.expand(c6.ch(vertex, left_neighbour, first, colour)
                           .xreplace(substitution))
            b1 = sp.expand(c6.ch(vertex, right_neighbour, first, colour)
                           .xreplace(substitution))
            a2 = sp.expand(c6.ch(vertex, left_neighbour, second, colour)
                           .xreplace(substitution))
            b2 = sp.expand(c6.ch(vertex, right_neighbour, second, colour)
                           .xreplace(substitution))
            left = sp.expand(c6.P(vertex, left_neighbour, colour)
                             .xreplace(substitution))
            right = sp.expand(c6.P(vertex, right_neighbour, colour)
                              .xreplace(substitution))
            l1 = sp.expand(c6.L1eq(vertex, colour, first).xreplace(substitution))
            l2 = sp.expand(c6.L1eq(vertex, colour, second).xreplace(substitution))
            determinant = sp.expand(c6.theta_det(vertex, colour)
                                    .xreplace(substitution))
            if sp.expand(l1 - (a1 * left + b1 * right)) != 0:
                raise ValueError(f"first L1 decomposition failed at {vertex}/{colour}")
            if sp.expand(l2 - (a2 * left + b2 * right)) != 0:
                raise ValueError(f"second L1 decomposition failed at {vertex}/{colour}")
            if sp.expand(determinant - (a1 * b2 - a2 * b1)) != 0:
                raise ValueError(f"determinant decomposition failed at {vertex}/{colour}")
            slots.append({
                "vertex": vertex,
                "colour": colour,
                "l1_first_source_index": generator_index[l1],
                "l1_second_source_index": generator_index[l2],
                "determinant_source_index": generator_index[determinant],
                "a1": a1, "b1": b1, "a2": a2, "b2": b2,
                "left": left, "right": right,
            })
    if len(slots) != 18:
        raise AssertionError("slot count drift")
    determinant_sources = {int(slot["determinant_source_index"]) for slot in slots}
    if len(determinant_sources) != 18:
        raise ValueError("collapse determinants do not have distinct source rows")
    base_sources = [index for index in range(len(reconstructed))
                    if index not in determinant_sources]
    if [reconstructed[index] for index in base_sources] != base_reconstructed:
        raise ValueError("dropping determinant rows does not recover the base system")

    def entries(key: str) -> list[str]:
        return [lean_expr(slot[key], positions) for slot in slots]

    l1_indices = [
        f"![{slot['l1_first_source_index']}, {slot['l1_second_source_index']}]"
        for slot in slots
    ]
    det_indices = [str(slot["determinant_source_index"]) for slot in slots]
    first_simp = (
        "sourceValue, l1SourceIndex, slotA1, slotB1, slotLeft, slotRight, "
        "Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly"
    )
    second_simp = (
        "sourceValue, l1SourceIndex, slotA2, slotB2, slotLeft, slotRight, "
        "Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly"
    )
    determinant_simp = (
        "sourceValue, determinantSourceIndex, slotA1, slotB1, slotA2, slotB2, "
        "Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly"
    )
    lines = [
        "import KrennAdjugateDichotomy",
        "import KrennFrozenCase0System",
        "import Mathlib",
        "",
        "/-!",
        "Exact case-0 C6 connector for the non-collapse split.",
        "",
        "This file is generated only after term-for-term reconstruction of the",
        "canonical 747-generator frozen system.  Each of the eighteen slots has",
        "two actual one-defect equations in that system.  Lean expands those",
        "source equations and checks their adjugate decompositions with `ring`.",
        "The base system is the same frozen source with exactly those eighteen",
        "determinant positions omitted; adding every determinant back recovers",
        "the all-collapse system consumed by the certificate corpus.",
        "-/",
        "",
        "namespace Krenn.FrozenCase0AdjugateLayer",
        "",
        "open MvPolynomial",
        "open Krenn.SparseCertificate",
        "",
        "noncomputable def sourceValue {R : Type*} [CommRing R]",
        "    (values : Fin 75 → R) (source : Fin 747) : R :=",
        "  eval₂Hom (Int.castRingHom R) values",
        "    (Krenn.FrozenCase0System.equations source).toPoly",
        "",
        "/-- Two one-defect source equations for every `(vertex, colour)` slot. -/",
        "def l1SourceIndex : Fin 18 → Fin 2 → Fin 747 := " + vector(l1_indices, "  "),
        "",
        "/-- The actual frozen source position of the corresponding determinant. -/",
        "def determinantSourceIndex : Fin 18 → Fin 747 := " + vector(det_indices, "  "),
        "",
        "/-- The original, pre-all-collapse C6 equations: all frozen source rows",
        "except the eighteen recorded determinant rows. -/",
        "noncomputable def BaseCommonZero {R : Type*} [CommRing R]",
        "    (values : Fin 75 → R) : Prop :=",
        "  ∀ source, (∀ slot, determinantSourceIndex slot ≠ source) →",
        "    sourceValue values source = 0",
        "",
    ]
    for name, key, doc in [
        ("slotA1", "a1", "First left-neighbour coefficient."),
        ("slotB1", "b1", "First right-neighbour coefficient."),
        ("slotA2", "a2", "Second left-neighbour coefficient."),
        ("slotB2", "b2", "Second right-neighbour coefficient."),
        ("slotLeft", "left", "First deflated amplitude."),
        ("slotRight", "right", "Second deflated amplitude."),
    ]:
        lines.extend([
            f"/-- {doc} -/",
            f"def {name} {{R : Type*}} [CommRing R] (values : Fin 75 → R) : Fin 18 → R := " + vector(entries(key), "  "),
            "",
        ])
    lines.extend([
        "/-- The literal two-by-two determinant in each frozen slot. -/",
        "def slotDeterminant {R : Type*} [CommRing R] (values : Fin 75 → R)",
        "    (slot : Fin 18) : R :=",
        "  slotA1 values slot * slotB2 values slot -",
        "    slotA2 values slot * slotB1 values slot",
        "",
        "set_option maxRecDepth 100000 in",
        "set_option maxHeartbeats 5000000 in",
        "theorem first_l1_source_eq {R : Type*} [CommRing R]",
        "    (values : Fin 75 → R) (slot : Fin 18) :",
        "    sourceValue values (l1SourceIndex slot 0) =",
        "      slotA1 values slot * slotLeft values slot +",
        "        slotB1 values slot * slotRight values slot := by",
        f"  fin_cases slot <;> simp [{first_simp}] <;> ring",
        "",
        "set_option maxRecDepth 100000 in",
        "set_option maxHeartbeats 5000000 in",
        "theorem second_l1_source_eq {R : Type*} [CommRing R]",
        "    (values : Fin 75 → R) (slot : Fin 18) :",
        "    sourceValue values (l1SourceIndex slot 1) =",
        "      slotA2 values slot * slotLeft values slot +",
        "        slotB2 values slot * slotRight values slot := by",
        f"  fin_cases slot <;> simp [{second_simp}] <;> ring",
        "",
        "set_option maxRecDepth 100000 in",
        "set_option maxHeartbeats 5000000 in",
        "theorem determinant_source_eq {R : Type*} [CommRing R]",
        "    (values : Fin 75 → R) (slot : Fin 18) :",
        "    sourceValue values (determinantSourceIndex slot) =",
        "      slotDeterminant values slot := by",
        f"  fin_cases slot <;> simp [{determinant_simp}, slotDeterminant] <;> ring",
        "",
        "/-- A one-defect row is never mistaken for one of the added collapse",
        "determinants.  This finite disjointness check is part of the bridge. -/",
        "theorem l1_source_not_determinant (slot : Fin 18) (row : Fin 2)",
        "    (determinant : Fin 18) :",
        "    determinantSourceIndex determinant ≠ l1SourceIndex slot row := by",
        "  fin_cases slot <;> fin_cases row <;> fin_cases determinant <;> decide",
        "",
        "/-- Every common zero of the original pre-collapse case-0 system lies on",
        "the all-collapse locus or has a concrete left deflated-amplitude kill. -/",
        "theorem left_kill_or_collapse {R : Type*} [CommRing R] [NoZeroDivisors R]",
        "    (values : Fin 75 → R)",
        "    (base : BaseCommonZero values) (slot : Fin 18) :",
        "    slotDeterminant values slot = 0 ∨ slotLeft values slot = 0 := by",
        "  change slotA1 values slot * slotB2 values slot -",
        "      slotA2 values slot * slotB1 values slot = 0 ∨",
        "        slotLeft values slot = 0",
        "  refine Krenn.AdjugateDichotomy.left_kill_or_collapse",
        "    (slotA1 values slot) (slotB1 values slot)",
        "    (slotA2 values slot) (slotB2 values slot)",
        "    (slotLeft values slot) (slotRight values slot) ?_ ?_",
        "  · have h := base (l1SourceIndex slot 0)",
        "      (fun determinant => l1_source_not_determinant slot 0 determinant)",
        "    rw [first_l1_source_eq] at h",
        "    exact h",
        "  · have h := base (l1SourceIndex slot 1)",
        "      (fun determinant => l1_source_not_determinant slot 1 determinant)",
        "    rw [second_l1_source_eq] at h",
        "    exact h",
        "",
        "/-- The symmetric right deflated-amplitude alternative. -/",
        "theorem right_kill_or_collapse {R : Type*} [CommRing R] [NoZeroDivisors R]",
        "    (values : Fin 75 → R)",
        "    (base : BaseCommonZero values) (slot : Fin 18) :",
        "    slotDeterminant values slot = 0 ∨ slotRight values slot = 0 := by",
        "  change slotA1 values slot * slotB2 values slot -",
        "      slotA2 values slot * slotB1 values slot = 0 ∨",
        "        slotRight values slot = 0",
        "  refine Krenn.AdjugateDichotomy.right_kill_or_collapse",
        "    (slotA1 values slot) (slotB1 values slot)",
        "    (slotA2 values slot) (slotB2 values slot)",
        "    (slotLeft values slot) (slotRight values slot) ?_ ?_",
        "  · have h := base (l1SourceIndex slot 0)",
        "      (fun determinant => l1_source_not_determinant slot 0 determinant)",
        "    rw [first_l1_source_eq] at h",
        "    exact h",
        "  · have h := base (l1SourceIndex slot 1)",
        "      (fun determinant => l1_source_not_determinant slot 1 determinant)",
        "    rw [second_l1_source_eq] at h",
        "    exact h",
        "",
        "/-- Adding every slot determinant to a base common zero recovers the",
        "complete frozen all-collapse system. -/",
        "theorem full_common_zero_of_base_and_all_collapse",
        "    {R : Type*} [CommRing R] (values : Fin 75 → R)",
        "    (base : BaseCommonZero values)",
        "    (collapse : ∀ slot, slotDeterminant values slot = 0) :",
        "    Krenn.FrozenCase0System.CommonZero values := by",
        "  intro source",
        "  by_cases hdet : ∃ slot, determinantSourceIndex slot = source",
        "  · rcases hdet with ⟨slot, hslot⟩",
        "    rw [← hslot]",
        "    change sourceValue values (determinantSourceIndex slot) = 0",
        "    rw [determinant_source_eq]",
        "    exact collapse slot",
        "  · exact base source (fun slot equal => hdet ⟨slot, equal⟩)",
        "",
        "/-- The full exact split of the original case-0 C6 system: either it",
        "enters the already-certified all-collapse system, or an explicit left",
        "deflated amplitude is zero. -/",
        "theorem base_all_collapse_or_exists_left_kill",
        "    {R : Type*} [CommRing R] [NoZeroDivisors R]",
        "    (values : Fin 75 → R) (base : BaseCommonZero values) :",
        "    Krenn.FrozenCase0System.CommonZero values ∨",
        "      ∃ slot, slotLeft values slot = 0 := by",
        "  rcases Krenn.AdjugateDichotomy.all_collapse_or_exists_kill",
        "      (slotDeterminant values) (slotLeft values)",
        "      (left_kill_or_collapse values base) with collapse | kill",
        "  · exact Or.inl (full_common_zero_of_base_and_all_collapse values base collapse)",
        "  · exact Or.inr kill",
        "",
        "#print axioms Krenn.FrozenCase0AdjugateLayer.left_kill_or_collapse",
        "#print axioms Krenn.FrozenCase0AdjugateLayer.right_kill_or_collapse",
        "#print axioms Krenn.FrozenCase0AdjugateLayer.base_all_collapse_or_exists_left_kill",
        "",
        "end Krenn.FrozenCase0AdjugateLayer",
        "",
    ])
    text = "\n".join(lines)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(text, encoding="utf-8")
    receipt = {
        "format": "krenn-case0-adjugate-layer-v1",
        "frozen_system_file_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "frozen_system_sha256": payload["system_sha256"],
        "slot_count": len(slots),
        "base_source_row_count": len(base_sources),
        "base_source_indices_sha256": digest_json(base_sources),
        "mapping": [
            {
                "vertex": slot["vertex"], "colour": slot["colour"],
                "l1_first_source_index": slot["l1_first_source_index"],
                "l1_second_source_index": slot["l1_second_source_index"],
                "determinant_source_index": slot["determinant_source_index"],
            }
            for slot in slots
        ],
        "mapping_sha256": digest_json([
            {
                "vertex": slot["vertex"], "colour": slot["colour"],
                "l1_first_source_index": slot["l1_first_source_index"],
                "l1_second_source_index": slot["l1_second_source_index"],
                "determinant_source_index": slot["determinant_source_index"],
            }
            for slot in slots
        ]),
        "output_sha256": hashlib.sha256(text.encode()).hexdigest(),
    }
    if args.receipt is not None:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps(receipt, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
