#!/usr/bin/env python3
"""Freeze a structural tail target for a generic C6 non-collapse slot.

For a slot whose four theta entries are not gauge-fixed constants, the two
adjugate P-kills admit a small, exact first-stage construction.  Four low
profile amplitude rows reduce modulo those P-kills to

``a*x, b*x, c*y, d*y``,

where ``a*d - b*c`` is the inverted theta minor.  Hence ``x = y = 0`` on the
branch.  This program finds that construction by exact polynomial reduction,
then freezes the remaining `(3,2,1)` tail together with those two derived
cofactor kills.

The output is a *structural discovery target*, not directly a strict leaf:
the two added cofactor equations carry their derivation transcript and need
the elementary minor lemma when assembled into a proof.  A unit/certificate
for the frozen tail would therefore be a meaningful next proof object rather
than a blind full-system solve.
"""

from __future__ import annotations

import os
import argparse
import hashlib
import itertools
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

import sympy as sp


SHARED = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
if str(SHARED) not in sys.path:
    sys.path.insert(0, str(SHARED))

import c6_collapse_attack as c6  # noqa: E402
import f9_pipeline as pipeline  # noqa: E402
from c4_crux_freeze import canonical_polynomial, write_msolve, write_singular_lift  # noqa: E402
from engine_fingerprint import ROOT, source_manifest  # noqa: E402


FIRST_PROFILES = {(4, 2), (4, 1, 1), (3, 2, 1)}
TAIL_PROFILE = (3, 2, 1)


def digest(value: object) -> str:
    return hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def profile(colours: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(sorted(Counter(colours).values(), reverse=True))


def expression_degree(expression: sp.Expr, variables: list[sp.Symbol]) -> int:
    return sp.Poly(expression, *variables, domain=sp.ZZ).total_degree()


def row_record(
    word: str,
    kind: tuple[int, ...],
    polynomial: sp.Expr,
    quotient: list[sp.Expr],
    remainder: sp.Expr,
) -> dict[str, Any]:
    return {
        "word": word,
        "profile": list(kind),
        "polynomial": str(polynomial),
        "groebner_quotients": [str(value) for value in quotient],
        "remainder": str(remainder),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument("--vertex", type=int, choices=range(6), required=True)
    parser.add_argument("--colour", type=int, choices=range(3), required=True)
    parser.add_argument("--x-factor", type=int, default=None)
    parser.add_argument("--y-factor", type=int, default=None)
    args = parser.parse_args()
    if args.output.exists() and any(args.output.iterdir()):
        parser.error("output must be new or empty")

    u, k = args.vertex, args.colour
    case0 = pipeline.cases_for(c6.X)[0]
    fixed = pipeline.max_fixable([
        (c6.X[index], left, right)
        for index, (left, right) in enumerate(case0)
    ])
    substitution = {c6.VAR[entry]: sp.Integer(1) for entry in fixed}
    all_variables = sorted(
        {symbol for equation in c6.system() for symbol in equation.free_symbols
         if symbol not in substitution},
        key=sp.default_sort_key,
    )

    left, right = c6.NBR[u]
    other = [colour for colour in range(3) if colour != k]
    theta_entries = [
        sp.expand(c6.ch(u, left, colour, k).xreplace(substitution))
        for colour in other
    ] + [
        sp.expand(c6.ch(u, right, colour, k).xreplace(substitution))
        for colour in other
    ]
    if any(not isinstance(entry, sp.Symbol) for entry in theta_entries):
        raise ValueError(
            "slot is not a generic four-variable theta chart; "
            f"entries={list(map(str, theta_entries))}"
        )
    theta = sp.expand(c6.theta_det(u, k).xreplace(substitution))
    expected_theta = sp.expand(
        theta_entries[0] * theta_entries[3]
        - theta_entries[1] * theta_entries[2]
    )
    if theta != expected_theta:
        raise RuntimeError("theta-entry order drift")
    p_left = sp.expand(c6.P(u, left, k).xreplace(substitution))
    p_right = sp.expand(c6.P(u, right, k).xreplace(substitution))
    groebner = sp.groebner([p_left, p_right], *all_variables, order="lex")

    rows: list[tuple[str, tuple[int, ...], sp.Expr]] = []
    for colours in itertools.product(range(3), repeat=6):
        kind = profile(colours)
        if kind not in FIRST_PROFILES:
            continue
        word = "".join(map(str, colours))
        polynomial = sp.expand(
            c6.pm_sum(dict(enumerate(colours))).xreplace(substitution)
        )
        rows.append((word, kind, polynomial))

    # For each theta entry, retain every amplitude whose P-kill normal form is
    # precisely that entry times a cofactor.  This is a finite exact matching
    # calculation, not a Gröbner-basis contradiction search.
    candidates: list[dict[str, list[dict[str, Any]]]] = [defaultdict(list) for _ in range(4)]
    for word, kind, polynomial in rows:
        quotients, remainder = groebner.reduce(polynomial)
        reduced = sp.Poly(remainder, *all_variables, domain=sp.ZZ)
        if len(reduced.terms()) != 1:
            continue
        powers, coefficient = reduced.terms()[0]
        if coefficient not in (1, -1):
            continue
        monomial = sp.Mul(*[
            variable ** exponent
            for variable, exponent in zip(all_variables, powers, strict=True)
            if exponent
        ])
        for index, entry in enumerate(theta_entries):
            entry_index = all_variables.index(entry)
            if powers[entry_index] != 1:
                continue
            cofactor = sp.cancel(monomial / entry)
            if cofactor.has(entry):
                continue
            relation = sp.expand(
                polynomial - remainder
                - sum(q * g.as_expr() for q, g in zip(quotients, groebner.polys, strict=True))
            )
            if relation != 0:
                raise RuntimeError("Groebner quotient replay drift")
            key = str(cofactor)
            candidates[index][key].append(row_record(
                word, kind, polynomial, list(quotients), remainder
            ))

    def choose_common(first: int, second: int) -> tuple[sp.Expr, str]:
        shared = set(candidates[first]) & set(candidates[second])
        if not shared:
            raise RuntimeError(
                f"no shared cofactor for theta entries {first} and {second}"
            )
        return min(
            ((sp.sympify(key), key) for key in shared),
            key=lambda pair: (expression_degree(pair[0], all_variables), pair[1]),
        )

    x, x_key = choose_common(0, 1)
    y, y_key = choose_common(2, 3)
    if (args.x_factor is None) != (args.y_factor is None):
        parser.error("--x-factor and --y-factor must be supplied together")

    def squarefree_factors(expression: sp.Expr) -> list[sp.Expr]:
        _constant, factors = sp.factor_list(expression)
        answer: list[sp.Expr] = []
        for factor, exponent in factors:
            answer.extend([factor] * exponent)
        return answer

    factor_branch: dict[str, Any] | None = None
    branch_generators: list[sp.Expr] = []
    if args.x_factor is not None:
        x_factors = squarefree_factors(x)
        y_factors = squarefree_factors(y)
        if not 0 <= args.x_factor < len(x_factors):
            parser.error("--x-factor is outside the factor list")
        if not 0 <= args.y_factor < len(y_factors):
            parser.error("--y-factor is outside the factor list")
        branch_generators = [x_factors[args.x_factor], y_factors[args.y_factor]]
        factor_branch = {
            "x_factors": [str(factor) for factor in x_factors],
            "y_factors": [str(factor) for factor in y_factors],
            "selected": {
                "x_index": args.x_factor,
                "x_factor": str(branch_generators[0]),
                "y_index": args.y_factor,
                "y_factor": str(branch_generators[1]),
            },
            "scope": (
                "This is one product-zero subbranch after the derived "
                "cofactor kills; it is not the whole generic slot."
            ),
        }
    selected_first = [
        min(candidates[index][key], key=lambda row: row["word"])
        for index, key in ((0, x_key), (1, x_key), (2, y_key), (3, y_key))
    ]
    first_polynomials = [sp.sympify(row["polynomial"]) for row in selected_first]

    tail_rows = [
        (word, polynomial)
        for word, kind, polynomial in rows
        if kind == TAIL_PROFILE
    ]
    inverse = sp.Symbol(f"theta_{u}_{k}_inv")
    generators = first_polynomials + [p_left, p_right, theta * inverse - 1, x, y]
    generator_labels = [
        f"first_stage_{index}_{row['word']}" for index, row in enumerate(selected_first)
    ] + [
        "adjugate_P_kill_left",
        "adjugate_P_kill_right",
        "theta_inverse_branch",
        "derived_minor_cofactor_x",
        "derived_minor_cofactor_y",
    ]
    if factor_branch is not None:
        generators.extend(branch_generators)
        generator_labels.extend([
            "factor_branch_x",
            "factor_branch_y",
        ])
    generators.extend(polynomial for _word, polynomial in tail_rows)
    generator_labels.extend(f"tail_321_{word}" for word, _polynomial in tail_rows)
    variables = sorted(
        {symbol for polynomial in generators for symbol in polynomial.free_symbols},
        key=sp.default_sort_key,
    )
    system = {
        "variables": [str(symbol) for symbol in variables],
        "equations": [canonical_polynomial(polynomial, variables)
                      for polynomial in generators],
    }
    payload = {
        "format": "krenn-c6-noncollapse-generic-slot-tail-v1",
        "slot": {
            "vertex": u,
            "colour": k,
            "neighbours": [left, right],
            "other_colours": other,
        },
        "gauge_case": [list(entry) for entry in case0],
        "theta_entries": [str(entry) for entry in theta_entries],
        "theta": str(theta),
        "p_kills": {"left": str(p_left), "right": str(p_right)},
        "first_stage": {
            "cofactor_x": str(x),
            "cofactor_y": str(y),
            "selected_rows": selected_first,
            "derivation": (
                "After the two P-kills, the four displayed rows force "
                "a*x=b*x=c*y=d*y=0.  The inverse of a*d-b*c then forces "
                "x=y=0."
            ),
        },
        "factor_branch": factor_branch,
        "tail": {
            "profile": list(TAIL_PROFILE),
            "row_count": len(tail_rows),
            "words_sha256": digest([word for word, _polynomial in tail_rows]),
        },
        "generator_labels": generator_labels,
        "statistics": {
            "first_stage_rows": len(selected_first),
            "branch_rows": 5 + len(branch_generators),
            "tail_rows": len(tail_rows),
            "generators": len(generators),
            "variables": len(variables),
        },
        "system_sha256": digest(system),
        "source_manifest": source_manifest(
            "freeze_c6_noncollapse_generic_tail",
            sources=[ROOT / "c6_collapse_attack.py", ROOT / "f9_pipeline.py",
                     ROOT / "krenn_exact.py", ROOT / "c4_crux_freeze.py",
                     Path(__file__)],
        ),
        **system,
    }
    args.output.mkdir(parents=True, exist_ok=True)
    system_path = args.output / "system.json"
    system_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    write_msolve(args.output / "input_q.ms", variables, generators, 0)
    write_singular_lift(args.output / "lift.sing", variables, generators)
    print(json.dumps({
        "slot": payload["slot"],
        "theta": payload["theta"],
        "cofactor_x": payload["first_stage"]["cofactor_x"],
        "cofactor_y": payload["first_stage"]["cofactor_y"],
        "statistics": payload["statistics"],
        "system_sha256": payload["system_sha256"],
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
