#!/usr/bin/env python3
"""Classify the exact first-stage charts of the 12 C6 non-collapse types.

This is a falsification-oriented structural audit.  It starts with the exact
12-orbit quotient of `(raw case, theta-slot)` pairs, works on its case-0
representatives, and asks a deliberately narrow question:

Can the two adjugate P-kills and four low-profile amplitude rows force two
cofactors to vanish by an inverted generic theta minor, in the same *first
stage* shape as the strict eleven-row seed certificate?

For a generic four-variable theta chart the answer is certified by direct
polynomial reduction modulo the two P-kills.  The later `(3,2,1)` tail is
then scanned only for literal variable kills after those cofactors vanish.
This does not decide the full ideal.  In particular, failure to find a linear
tail kill is a limitation of this exact template, not a nonexistence result.
"""

from __future__ import annotations

import os
import hashlib
import itertools
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

import sympy as sp


ROOT = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import c6_collapse_attack as c6  # noqa: E402
import f9_pipeline as pipeline  # noqa: E402


FIRST_PROFILES = {(4, 2), (4, 1, 1), (3, 2, 1)}
TAIL_PROFILE = (3, 2, 1)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def profile(colours: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(sorted(Counter(colours).values(), reverse=True))


def expression_degree(expression: sp.Expr, variables: list[sp.Symbol]) -> int:
    return sp.Poly(expression, *variables, domain=sp.ZZ).total_degree()


def main() -> int:
    pair_audit_path = (
        ROOT / "noncollapse_case_artifacts" / "noncollapse_pair_orbit_audit_v1.json"
    )
    pair_audit = json.loads(pair_audit_path.read_text())
    if pair_audit.get("pair_orbit_count") != 12:
        raise RuntimeError("pair-orbit audit drift")
    case0 = tuple(tuple(entry) for entry in pair_audit["pair_orbits"][0]
                  ["representative"]["case"])
    if case0 != ((0, 1),) * 6:
        raise RuntimeError("case-0 gauge receipt drift")
    fixed = pipeline.max_fixable([
        (c6.X[index], left, right)
        for index, (left, right) in enumerate(case0)
    ])
    substitution = {c6.VAR[entry]: sp.Integer(1) for entry in fixed}
    variables = sorted(
        {symbol for equation in c6.system() for symbol in equation.free_symbols
         if symbol not in substitution},
        key=sp.default_sort_key,
    )
    first_rows: list[tuple[str, tuple[int, ...], sp.Expr]] = []
    tail_rows: list[tuple[str, sp.Expr]] = []
    for colours in itertools.product(range(3), repeat=6):
        kind = profile(colours)
        word = "".join(map(str, colours))
        if kind not in FIRST_PROFILES:
            continue
        polynomial = sp.expand(
            c6.pm_sum(dict(enumerate(colours))).xreplace(substitution)
        )
        first_rows.append((word, kind, polynomial))
        if kind == TAIL_PROFILE:
            tail_rows.append((word, polynomial))
    if len(first_rows) != 540 or len(tail_rows) != 360:
        raise RuntimeError("profile row census drift")

    records: list[dict[str, Any]] = []
    for type_index, pair_type in enumerate(pair_audit["pair_orbits"]):
        representative = pair_type["representative"]
        u, k = representative["vertex"], representative["colour"]
        left, right = c6.NBR[u]
        other = [colour for colour in range(3) if colour != k]
        entries = [
            sp.expand(c6.ch(u, left, colour, k).xreplace(substitution))
            for colour in other
        ] + [
            sp.expand(c6.ch(u, right, colour, k).xreplace(substitution))
            for colour in other
        ]
        theta = sp.expand(c6.theta_det(u, k).xreplace(substitution))
        p_left = sp.expand(c6.P(u, left, k).xreplace(substitution))
        p_right = sp.expand(c6.P(u, right, k).xreplace(substitution))
        fixed_entries = [str(entry) for entry in entries if entry == 1]
        record: dict[str, Any] = {
            "pair_orbit_index": type_index,
            "representative": representative,
            "theta_entries": [str(entry) for entry in entries],
            "theta": str(theta),
            "gauge_fixed_theta_entry_count": len(fixed_entries),
            "gauge_fixed_theta_entries": fixed_entries,
            "p_kills": {"left": str(p_left), "right": str(p_right)},
        }
        if any(not isinstance(entry, sp.Symbol) for entry in entries):
            record["chart_kind"] = "affine_or_partially_fixed"
            record["first_stage_template"] = {
                "applicable": False,
                "reason": (
                    "The seed template assumes a four-variable 2x2 minor; "
                    "this gauge chart has one or more entries fixed to 1."
                ),
            }
            records.append(record)
            continue

        record["chart_kind"] = "generic_four_variable"
        groebner = sp.groebner([p_left, p_right], *variables, order="lex")
        candidates: list[dict[str, list[dict[str, Any]]]] = [defaultdict(list)
                                                               for _ in range(4)]
        for word, kind, polynomial in first_rows:
            quotients, remainder = groebner.reduce(polynomial)
            reduced = sp.Poly(remainder, *variables, domain=sp.ZZ)
            if len(reduced.terms()) != 1:
                continue
            powers, coefficient = reduced.terms()[0]
            if coefficient not in (1, -1):
                continue
            monomial = sp.Mul(*[
                variable ** exponent
                for variable, exponent in zip(variables, powers, strict=True)
                if exponent
            ])
            for entry_index, entry in enumerate(entries):
                var_index = variables.index(entry)
                if powers[var_index] != 1:
                    continue
                cofactor = sp.cancel(monomial / entry)
                if cofactor.has(entry):
                    continue
                if sp.expand(
                    polynomial - remainder - sum(
                        quotient * basis.as_expr()
                        for quotient, basis in zip(quotients, groebner.polys, strict=True)
                    )
                ) != 0:
                    raise RuntimeError("exact P-kill reduction replay drift")
                candidates[entry_index][str(cofactor)].append({
                    "word": word,
                    "profile": list(kind),
                    "remainder": str(remainder),
                    "groebner_quotients": [str(value) for value in quotients],
                })

        def select_shared(first: int, second: int) -> tuple[sp.Expr, str] | None:
            shared = set(candidates[first]) & set(candidates[second])
            if not shared:
                return None
            return min(
                ((sp.sympify(key), key) for key in shared),
                key=lambda pair: (expression_degree(pair[0], variables), pair[1]),
            )

        x_pair = select_shared(0, 1)
        y_pair = select_shared(2, 3)
        if x_pair is None or y_pair is None:
            record["first_stage_template"] = {
                "applicable": False,
                "reason": "No shared cofactor pair was found by the seed first-stage matcher.",
                "candidate_cofactor_counts": [len(group) for group in candidates],
            }
            records.append(record)
            continue
        x, x_key = x_pair
        y, y_key = y_pair
        selected = []
        for entry_index, key in ((0, x_key), (1, x_key), (2, y_key), (3, y_key)):
            selected.append(min(candidates[entry_index][key], key=lambda row: row["word"]))
        record["first_stage_template"] = {
            "applicable": True,
            "cofactor_x": str(x),
            "cofactor_x_degree": expression_degree(x, variables),
            "cofactor_y": str(y),
            "cofactor_y_degree": expression_degree(y, variables),
            "selected_rows": selected,
            "derivation": (
                "The four selected remainders are a*x, b*x, c*y, d*y "
                "modulo the two P-kills.  With theta=a*d-b*c invertible, "
                "x=y=0 follows in the branch."
            ),
        }

        # Test only the seed's simple tail pattern: iteratively add literal
        # variables forced by a single `(3,2,1)` row after the proven
        # cofactor kills.  Products are intentionally not split here.
        known = [p_left, p_right, x, y]
        known_variables: set[sp.Symbol] = set()
        levels: list[dict[str, Any]] = []
        for level in range(3):
            tail_groebner = sp.groebner(known, *variables, order="lex")
            new: dict[sp.Symbol, str] = {}
            for word, polynomial in tail_rows:
                _quotients, remainder = tail_groebner.reduce(polynomial)
                reduced = sp.Poly(remainder, *variables, domain=sp.ZZ)
                if len(reduced.terms()) != 1:
                    continue
                powers, coefficient = reduced.terms()[0]
                if coefficient not in (1, -1) or sum(powers) != 1:
                    continue
                variable = variables[powers.index(1)]
                if variable not in known_variables:
                    new.setdefault(variable, word)
            levels.append({
                "level": level,
                "groebner_generator_count": len(tail_groebner.polys),
                "new_literal_kills": [
                    {"variable": str(variable), "word": word}
                    for variable, word in sorted(new.items(), key=lambda row: str(row[0]))
                ],
            })
            if not new:
                break
            known.extend(new)
            known_variables |= set(new)
        record["seed_style_tail_scan"] = {
            "levels": levels,
            "theta_entries_forced_literal_zero": [
                str(entry) for entry in entries if entry in known_variables
            ],
            "theta_forced_zero_by_literal_row_kill": (
                (entries[0] in known_variables and entries[2] in known_variables)
                or (entries[1] in known_variables and entries[3] in known_variables)
            ),
            "scope": (
                "This is only a literal-kill scan.  It does not rule out "
                "nonlinear, product-split, or profile-adaptive tail proofs."
            ),
        }
        records.append(record)

    if len(records) != 12:
        raise RuntimeError("chart record count drift")
    seed = records[0]
    seed_reproduces = bool(
        seed["first_stage_template"]["applicable"]
        and seed["seed_style_tail_scan"]["theta_forced_zero_by_literal_row_kill"]
    )
    if not seed_reproduces:
        raise RuntimeError("eleven-row seed mechanism stopped reproducing")

    payload = {
        "format": "krenn-c6-noncollapse-chart-template-audit-v1",
        "sources": {
            "pair_orbit_audit_sha256": sha256(pair_audit_path),
            "c6_collapse_attack_sha256": sha256(ROOT / "c6_collapse_attack.py"),
            "f9_pipeline_sha256": sha256(ROOT / "f9_pipeline.py"),
            "audit_script_sha256": sha256(Path(__file__)),
        },
        "profile_row_counts": {"first_stage_pool": len(first_rows), "tail_321": len(tail_rows)},
        "type_count": len(records),
        "types": records,
        "summary": {
            "generic_four_variable_types": sum(
                row["chart_kind"] == "generic_four_variable" for row in records
            ),
            "affine_or_partially_fixed_types": sum(
                row["chart_kind"] == "affine_or_partially_fixed" for row in records
            ),
            "seed_style_first_stage_types": sum(
                bool(row["first_stage_template"].get("applicable"))
                for row in records
            ),
            "seed_style_literal_tail_closures": sum(
                bool(row.get("seed_style_tail_scan", {}).get(
                    "theta_forced_zero_by_literal_row_kill", False
                )) for row in records
            ),
            "elevenrow_seed_literal_tail_reproduces": seed_reproduces,
        },
        "conclusion": {
            "established": (
                "The seed mechanism is chart-sensitive already at its exact "
                "first-stage cofactors; a uniform unqualified 321 template "
                "cannot be inferred from its one successful instance."
            ),
            "not_established": (
                "This audit does not decide any full non-collapse component "
                "or rule out a different profile-adaptive certificate."
            ),
        },
    }
    target = ROOT / "noncollapse_case_artifacts" / "noncollapse_pair_chart_audit_v1.json"
    target.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(
        "C6 NON-COLLAPSE CHART TEMPLATE AUDIT VERIFIED: "
        f"{payload['summary']['generic_four_variable_types']} generic, "
        f"{payload['summary']['affine_or_partially_fixed_types']} affine; "
        f"seed-style literal tails close "
        f"{payload['summary']['seed_style_literal_tail_closures']} type(s)"
    )
    print("manifest_sha256=" + sha256(target))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
