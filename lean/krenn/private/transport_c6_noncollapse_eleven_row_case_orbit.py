#!/usr/bin/env python3
"""Strictly transport the C6 eleven-row certificate across case-0 symmetry.

Unlike a colour-pattern guess, this program transports the *physical*
gauge-normalized equations by an explicitly checked vertex--colour symmetry of
the C6 support.  It maps the selected amplitude rows, both P-kills, the theta
inverse (including its determinant sign), and every certificate multiplier.
Each target then receives an independent strict replay; no CAS discovery is
run here.
"""

from __future__ import annotations

import os
import argparse
import hashlib
import itertools
import json
import sys
from pathlib import Path
from typing import Any

import sympy as sp


SHARED = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
if str(SHARED) not in sys.path:
    sys.path.insert(0, str(SHARED))

import c6_collapse_attack as c6
import f9_pipeline as pipeline
from c4_crux_freeze import canonical_polynomial
from engine_fingerprint import ROOT, source_manifest
from strict_certificate_checker import (
    check_c4,
    framed_body,
    frozen_poly,
    load_json_strict,
    parse_multiplier,
    symbols_for,
    validate_variable_names,
)


def sha256_path(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def digest(value: object) -> str:
    return hashlib.sha256(json.dumps(
        value, sort_keys=True, separators=(",", ":")
    ).encode()).hexdigest()


def action_case(
    sigma: dict[int, int], tau: dict[int, int], case: tuple[tuple[int, int], ...]
) -> tuple[tuple[int, int], ...]:
    moved: dict[tuple[int, int], tuple[int, int]] = {}
    for index, edge in enumerate(c6.X):
        edge2, left, right = pipeline.vertex_perm_on_entry(
            sigma, edge, *case[index]
        )
        moved[edge2] = (tau[left], tau[right])
    return tuple(moved[edge] for edge in c6.X)


def fixed_substitution(
    case: tuple[tuple[int, int], ...]
) -> tuple[dict[sp.Symbol, sp.Expr], list[tuple[tuple[int, int], int, int]]]:
    entries = [(c6.X[index], colours[0], colours[1])
               for index, colours in enumerate(case)]
    fixed = pipeline.max_fixable(entries)
    if len(fixed) != len(entries):
        raise RuntimeError("case-0 orbit unexpectedly lost full gauge rank")
    return {c6.VAR[entry]: sp.Integer(1) for entry in fixed}, fixed


def transformed_word(
    word: str, sigma: dict[int, int], tau: dict[int, int]
) -> str:
    out = [""] * 6
    for vertex, colour in enumerate(word):
        out[sigma[vertex]] = str(tau[int(colour)])
    if any(not value for value in out):
        raise RuntimeError("vertex permutation did not define a colouring")
    return "".join(out)


def load_certificate(
    system_path: Path, certificate_path: Path
) -> tuple[dict[str, Any], tuple[sp.Symbol, ...], list[sp.Poly]]:
    system = load_json_strict(system_path)
    names = validate_variable_names(system.get("variables"))
    symbols = symbols_for(names)
    lines = certificate_path.read_text(encoding="utf-8").splitlines()
    body = framed_body(lines, "C4_LIFT_CERTIFICATE_BEGIN", "C4_LIFT_CERTIFICATE_END")
    if len(body) % 3:
        raise RuntimeError("certificate framing drift")
    multipliers: list[sp.Poly] = []
    for offset in range(0, len(body), 3):
        if body[offset] != "C4_LIFT_ENTRY":
            raise RuntimeError("certificate entry marker drift")
        index = int(body[offset + 1])
        if index != len(multipliers) + 1:
            raise RuntimeError("certificate multiplier index drift")
        multipliers.append(parse_multiplier(body[offset + 2], symbols))
    if len(multipliers) != len(system["equations"]):
        raise RuntimeError("certificate/system equation count drift")
    return system, symbols, multipliers


def serialise_certificate(multipliers: list[sp.Poly]) -> str:
    lines = [
        "C4_LIFT_BASIS_BEGIN", "1", "C4_LIFT_BASIS_END",
        "C4_LIFT_CERTIFICATE_BEGIN",
    ]
    for index, multiplier in enumerate(multipliers, 1):
        lines.extend(["C4_LIFT_ENTRY", str(index), str(multiplier.as_expr())])
    lines.extend(["C4_LIFT_CERTIFICATE_END", ""])
    return "\n".join(lines)


def source_words(source: dict[str, Any]) -> list[str]:
    indices = source.get("selected_source_indices_1based")
    labels = source.get("source_labels")
    if not isinstance(indices, list) or not isinstance(labels, dict) or len(indices) != 11:
        raise RuntimeError("strict eleven-row source provenance drift")
    words = [labels.get(str(index)) for index in indices[:8]]
    if any(not isinstance(word, str) or len(word) != 6 or not word.isdigit()
           for word in words):
        raise RuntimeError("strict eleven-row amplitude labels drift")
    return words


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument(
        "--source-system", type=Path,
        default=SHARED / "noncollapse_case_artifacts" /
        "slot0_profile321_strict11_v1" / "system.json",
    )
    parser.add_argument(
        "--source-certificate", type=Path,
        default=SHARED / "noncollapse_case_artifacts" /
        "slot0_profile321_strict11_v1" / "lift_tracked" / "lift.stdout",
    )
    args = parser.parse_args()
    if args.output.exists():
        parser.error("output directory must not already exist")

    source, source_symbols, source_multipliers = load_certificate(
        args.source_system, args.source_certificate
    )
    source_equations = [
        frozen_poly(raw, source_symbols) for raw in source["equations"]
    ]
    words = source_words(source)
    source_case = pipeline.cases_for(c6.X)[0]
    source_substitution, source_fixed = fixed_substitution(source_case)
    source_vertex, source_colour = 0, 0
    source_neighbours = tuple(c6.NBR[source_vertex])
    source_theta = sp.expand(
        c6.theta_det(source_vertex, source_colour).xreplace(source_substitution)
    )

    c6_by_name = {str(symbol): symbol for symbol in c6.VAR.values()}
    source_inverse_name = "theta_0_0_inv"
    if source_inverse_name not in {str(symbol) for symbol in source_symbols}:
        raise RuntimeError("source inverse name drift")

    sources = source_manifest(
        "transport_c6_noncollapse_eleven_row_case_orbit",
        sources=[ROOT / "c6_collapse_attack.py", ROOT / "f9_pipeline.py",
                 ROOT / "krenn_exact.py", ROOT / "c4_crux_freeze.py",
                 SHARED / "strict_certificate_checker.py", Path(__file__)],
    )
    args.output.mkdir(parents=True, exist_ok=False)
    seen: dict[tuple[tuple[int, int], ...], tuple[dict[int, int], dict[int, int]]] = {}
    for sigma in pipeline.stabilizer(c6.X):
        for permutation in itertools.permutations(range(3)):
            tau = dict(enumerate(permutation))
            target_case = action_case(sigma, tau, source_case)
            seen.setdefault(target_case, (sigma, tau))
    if len(seen) != 36:
        raise RuntimeError(f"unexpected case-0 orbit size: {len(seen)}")

    rows: list[dict[str, Any]] = []
    for number, (target_case, (sigma, tau)) in enumerate(sorted(seen.items())):
        target_substitution, target_fixed = fixed_substitution(target_case)
        variable_map: dict[sp.Symbol, sp.Expr] = {}
        for (edge, left, right), symbol in c6.VAR.items():
            edge2, left2, right2 = pipeline.vertex_perm_on_entry(
                sigma, edge, left, right
            )
            variable_map[symbol] = c6.VAR[(edge2, tau[left2], tau[right2])]
        target_vertex, target_colour = sigma[source_vertex], tau[source_colour]
        target_theta = sp.expand(
            c6.theta_det(target_vertex, target_colour).xreplace(target_substitution)
        )
        image_theta = sp.expand(source_theta.xreplace(variable_map))
        if sp.expand(image_theta - target_theta) == 0:
            determinant_sign = 1
        elif sp.expand(image_theta + target_theta) == 0:
            determinant_sign = -1
        else:
            raise RuntimeError("theta determinant transport drift")
        target_inverse = sp.Symbol(f"theta_{target_vertex}_{target_colour}_inv")
        source_map: dict[sp.Symbol, sp.Expr] = {}
        for symbol in source_symbols:
            if str(symbol) == source_inverse_name:
                source_map[symbol] = determinant_sign * target_inverse
            else:
                raw = c6_by_name.get(str(symbol))
                if raw is None:
                    raise RuntimeError(f"undeclared source certificate symbol {symbol}")
                source_map[symbol] = variable_map[raw]
        target_symbols: list[sp.Symbol] = []
        for symbol in source_symbols:
            image = source_map[symbol]
            base = -image if image.could_extract_minus_sign() else image
            if not isinstance(base, sp.Symbol):
                raise RuntimeError("source variable transport ceased to be monomial")
            target_symbols.append(base)
        if len(set(target_symbols)) != len(target_symbols):
            raise RuntimeError("target variable transport is not injective")
        if any(symbol in target_substitution for symbol in target_symbols):
            raise RuntimeError("target certificate retained a gauge-fixed variable")
        image_fixed = {
            variable_map[c6.VAR[entry]] for entry in source_fixed
        }
        expected_fixed = {c6.VAR[entry] for entry in target_fixed}
        if image_fixed != expected_fixed:
            raise RuntimeError("gauge-fixing transport drift")

        target_words = [transformed_word(word, sigma, tau) for word in words]
        target_amplitudes = [
            sp.expand(c6.pm_sum(dict(enumerate(map(int, word))))
                      .xreplace(target_substitution))
            for word in target_words
        ]
        target_pkills = [
            sp.expand(c6.P(target_vertex, sigma[neighbour], target_colour)
                      .xreplace(target_substitution))
            for neighbour in source_neighbours
        ]
        target_equations_expr = target_amplitudes + target_pkills + [
            sp.expand(target_theta * target_inverse - 1)
        ]
        image_equations = [
            sp.expand(equation.as_expr().xreplace(source_map))
            for equation in source_equations
        ]
        if any(sp.expand(image - target) != 0
               for image, target in zip(image_equations, target_equations_expr,
                                        strict=True)):
            raise RuntimeError("selected physical equation transport drift")
        target_symbol_set = set(target_symbols)
        if any(not equation.free_symbols <= target_symbol_set
               for equation in target_equations_expr):
            raise RuntimeError("target equations escaped certificate variable frame")

        target_multipliers = [
            sp.Poly(multiplier.as_expr().xreplace(source_map), *target_symbols,
                    domain=sp.QQ)
            for multiplier in source_multipliers
        ]
        directory = args.output / f"case_{number:02d}"
        directory.mkdir()
        system = {
            "variables": [str(symbol) for symbol in target_symbols],
            "equations": [
                canonical_polynomial(expression, target_symbols)
                for expression in target_equations_expr
            ],
        }
        payload = {
            "format": "krenn-c6-noncollapse-eleven-row-symmetry-transport-v1",
            "source_system_file_sha256": sha256_path(args.source_system),
            "source_certificate_sha256": sha256_path(args.source_certificate),
            "source_case": list(map(list, source_case)),
            "target_case": list(map(list, target_case)),
            "source_slot": {"vertex": source_vertex, "colour": source_colour},
            "target_slot": {"vertex": target_vertex, "colour": target_colour},
            "sigma": [sigma[index] for index in range(6)],
            "tau": [tau[index] for index in range(3)],
            "determinant_sign": determinant_sign,
            "source_words": words,
            "target_words": target_words,
            "source_manifest": sources,
            "statistics": {"generators": 11, "variables": len(target_symbols)},
            "system_sha256": digest(system),
            **system,
        }
        system_path = directory / "system.json"
        system_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        certificate_path = directory / "certificate.txt"
        certificate_path.write_text(serialise_certificate(target_multipliers))
        strict = check_c4(system_path, certificate_path)
        row = {
            "directory": directory.name,
            "target_case": payload["target_case"],
            "target_slot": payload["target_slot"],
            "determinant_sign": determinant_sign,
            "system_file_sha256": sha256_path(system_path),
            "certificate_sha256": sha256_path(certificate_path),
            "strict_replay": strict,
        }
        rows.append(row)
        print(json.dumps({
            "case": number,
            "slot": payload["target_slot"],
            "sign": determinant_sign,
            "basis": strict["basis"],
        }, sort_keys=True), flush=True)

    manifest = {
        "format": "krenn-c6-noncollapse-eleven-row-symmetry-transport-manifest-v1",
        "source_manifest": sources,
        "source_system_file_sha256": sha256_path(args.source_system),
        "source_certificate_sha256": sha256_path(args.source_certificate),
        "case_orbit_size": len(rows),
        "all_strict": all(row["strict_replay"]["basis"] != "0" for row in rows),
        "rows": rows,
    }
    manifest_path = args.output / "manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print("manifest_sha256=" + sha256_path(manifest_path))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
