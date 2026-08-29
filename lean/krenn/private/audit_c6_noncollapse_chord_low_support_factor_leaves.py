#!/usr/bin/env python3
"""Exhaust the one/two-row scalar chord-P harvests on hard factor leaves.

This is a deliberately small follow-up to the factor-leaf adjugate audit.
For the hard generic C6 non-collapse chart `(vertex 0, colour 2)`, the two
incident P-kills are already known.  The finite doily calculation shows that
on each of its four exact factor leaves, no one or two further P-kills can
reach a contradiction: three are minimal.  In three leaves the unique
minimal triple is the remaining vertex-star chords `(01,02,03)`.

For each such required chord target, reduce all 729 original frozen amplitude
rows modulo the two known P-kills and the leaf's two factor-zero generators.
Then exhaust every exact rational span of at most two reduced rows.  A match
would give `P(0,chord,2)=0` directly, with a tiny replayable identity.  It is
not a Gröbner search and it makes no claim about three-or-more-row syzygies.
"""

from __future__ import annotations

import os
import hashlib
import itertools
import json
import sys
from collections import Counter, defaultdict
from fractions import Fraction
from pathlib import Path
from typing import Any

import sympy as sp


ROOT = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
PRIVATE = Path(__file__).resolve().parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
if str(PRIVATE) not in sys.path:
    sys.path.insert(0, str(PRIVATE))

import c6_collapse_attack as c6  # noqa: E402
import f9_pipeline as pipeline  # noqa: E402
from audit_c6_noncollapse_factor_frontier import total_forced_zero  # noqa: E402


FRONTIER = ROOT / "noncollapse_case_artifacts" / "noncollapse_factor_frontier_audit_v1.json"
PAIR_AUDIT = ROOT / "noncollapse_case_artifacts" / "noncollapse_chord_adjugate_pair_audit_v1.json"
FACTOR_ADJUGATE_AUDIT = ROOT / "noncollapse_case_artifacts" / "noncollapse_chord_adjugate_factor_leaf_audit_v1.json"
TARGET = ROOT / "noncollapse_case_artifacts" / "noncollapse_chord_low_support_factor_leaf_audit_v1.json"


Sparse = dict[tuple[int, ...], int]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def digest(value: object) -> str:
    return hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def profile(colours: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(sorted(Counter(colours).values(), reverse=True))


def sparse(expression: sp.Expr, variables: list[sp.Symbol]) -> Sparse:
    polynomial = sp.Poly(expression, *variables, domain=sp.ZZ)
    return {
        powers: int(coefficient)
        for powers, coefficient in polynomial.terms()
        if coefficient
    }


def scalar_multiple(left: Sparse, right: Sparse) -> Fraction | None:
    """Return `q` with left = q * right, including exact support checking."""
    if not right:
        raise ValueError("zero target")
    if set(left) != set(right):
        return None
    pivot = next(iter(right))
    quotient = Fraction(left[pivot], right[pivot])
    if quotient == 0:
        return None
    if all(Fraction(left[key], right[key]) == quotient for key in right):
        return quotient
    return None


def projective_outside(remainder: Sparse, target: Sparse) -> tuple[tuple[tuple[int, ...], Fraction], ...] | None:
    """Projective class of terms outside target support, or None if empty."""
    outside = {powers: coefficient for powers, coefficient in remainder.items()
               if powers not in target}
    if not outside:
        return None
    pivot = min(outside)
    pivot_coefficient = outside[pivot]
    return tuple(
        (powers, Fraction(coefficient, pivot_coefficient))
        for powers, coefficient in sorted(outside.items())
    )


def factor_symbol(record: dict[str, Any]) -> sp.Symbol:
    if record.get("kind") not in {"diagonal", "offdiagonal"}:
        raise RuntimeError("factor frontier supplied a non-weight factor")
    return sp.Symbol(record["symbol"])


def serial_sparse(value: Sparse) -> list[dict[str, Any]]:
    return [
        {"powers": list(powers), "coefficient": coefficient}
        for powers, coefficient in sorted(value.items())
    ]


def finite_completion_sets(
    base: set[tuple[int, int]], zeros: set[tuple[int, int]]
) -> list[tuple[tuple[int, int], ...]]:
    all_edges = [(a, b) for a in range(6) for b in range(a + 1, 6)]
    available = [edge for edge in all_edges if edge not in base]
    for size in range(1, len(available) + 1):
        hits = [
            candidate for candidate in itertools.combinations(available, size)
            if total_forced_zero(base | set(candidate), zeros)
        ]
        if hits:
            return hits
    raise RuntimeError("all fifteen P-kills should force a doily contradiction")


def main() -> int:
    frontier = json.loads(FRONTIER.read_text())
    if frontier.get("format") != "krenn-c6-noncollapse-factor-frontier-audit-v1":
        raise RuntimeError("factor-frontier format drift")
    hard = next(row for row in frontier["frontier"] if row["pair_orbit_index"] == 2)
    if hard["factor_branch_count"] != 4:
        raise RuntimeError("hard chart factor frontier drift")

    vertex, colour = 0, 2
    left, right = c6.NBR[vertex]
    case0 = pipeline.cases_for(c6.X)[0]
    fixed = pipeline.max_fixable([
        (c6.X[index], source, target)
        for index, (source, target) in enumerate(case0)
    ])
    substitution = {c6.VAR[key]: sp.Integer(1) for key in fixed}
    p_left = sp.expand(c6.P(vertex, left, colour).xreplace(substitution))
    p_right = sp.expand(c6.P(vertex, right, colour).xreplace(substitution))

    rows: list[dict[str, Any]] = []
    for colours in itertools.product(range(3), repeat=6):
        kind = profile(colours)
        equation = sp.expand(
            c6.pm_sum(dict(enumerate(colours))).xreplace(substitution)
            - (1 if kind == (6,) else 0)
        )
        if equation != 0:
            rows.append({
                "word": "".join(map(str, colours)),
                "profile": list(kind),
                "equation": equation,
            })
    if len(rows) != 729:
        raise RuntimeError("frozen C6 row census drift")
    variables = sorted(
        {symbol for row in rows for symbol in row["equation"].free_symbols}
        | p_left.free_symbols | p_right.free_symbols,
        key=sp.default_sort_key,
    )

    leaf_records: list[dict[str, Any]] = []
    all_matches: list[dict[str, Any]] = []
    for branch_index, branch in enumerate(hard["branches"]):
        constraint = branch["doily_constraints_by_colour"]
        if len(constraint) != 1 or constraint[0]["colour"] != colour:
            raise RuntimeError("unexpected hard leaf doily data")
        base = {tuple(edge) for edge in constraint[0]["dead_p_edges"]}
        zeros = {tuple(edge) for edge in constraint[0]["diagonal_zero_edges"]}
        completions = finite_completion_sets(base, zeros)
        if len(completions[0]) != 3:
            raise RuntimeError("hard type-2 completion threshold drift")
        factors = [factor_symbol(branch["x_factor"]), factor_symbol(branch["y_factor"])]
        groebner = sp.groebner([p_left, p_right, *factors], *variables, order="lex")
        reduced_rows = []
        for row in rows:
            quotients, remainder = groebner.reduce(row["equation"])
            replay = sp.expand(
                row["equation"] - remainder
                - sum(quotient * basis.as_expr()
                      for quotient, basis in zip(quotients, groebner.polys, strict=True)))
            if replay != 0:
                raise RuntimeError("leaf reduction replay drift")
            reduced_rows.append({
                "word": row["word"],
                "profile": row["profile"],
                "remainder": sparse(remainder, variables),
                "groebner_quotients": [str(value) for value in quotients],
            })

        target_edges = sorted({edge for completion in completions for edge in completion})
        targets = []
        for edge in target_edges:
            target = sparse(
                sp.expand(c6.P(edge[0], edge[1], colour).xreplace(substitution)),
                variables,
            )
            direct = []
            groups: dict[tuple[tuple[tuple[int, ...], Fraction], ...], list[dict[str, Any]]] = defaultdict(list)
            for row_index, row in enumerate(reduced_rows):
                quotient = scalar_multiple(row["remainder"], target)
                if quotient is not None:
                    direct.append({
                        "row_index": row_index,
                        "word": row["word"],
                        "profile": row["profile"],
                        "row_equals_scalar_times_target": str(quotient),
                        "groebner_quotients": row["groebner_quotients"],
                    })
                    continue
                key = projective_outside(row["remainder"], target)
                if key is not None:
                    pivot = key[0][0]
                    groups[key].append({
                        "row_index": row_index,
                        "row": row,
                        "outside_pivot": row["remainder"][pivot],
                    })
            pairs = []
            for group in groups.values():
                for first, second in itertools.combinations(group, 2):
                    alpha_raw = second["outside_pivot"]
                    beta_raw = -first["outside_pivot"]
                    combination: Sparse = {}
                    for powers, coefficient in first["row"]["remainder"].items():
                        combination[powers] = combination.get(powers, 0) + alpha_raw * coefficient
                    for powers, coefficient in second["row"]["remainder"].items():
                        combination[powers] = combination.get(powers, 0) + beta_raw * coefficient
                    combination = {powers: coefficient for powers, coefficient in combination.items() if coefficient}
                    scale = scalar_multiple(combination, target)
                    if scale is None:
                        continue
                    pairs.append({
                        "left_row_index": first["row_index"],
                        "right_row_index": second["row_index"],
                        "left": {
                            "word": first["row"]["word"],
                            "profile": first["row"]["profile"],
                            "groebner_quotients": first["row"]["groebner_quotients"],
                        },
                        "right": {
                            "word": second["row"]["word"],
                            "profile": second["row"]["profile"],
                            "groebner_quotients": second["row"]["groebner_quotients"],
                        },
                        "raw_coefficients": [alpha_raw, beta_raw],
                        "raw_combination_equals_scalar_times_target": str(scale),
                    })
            targets.append({
                "edge": list(edge),
                "target": serial_sparse(target),
                "direct_matches": direct,
                "two_row_scalar_matches": pairs,
            })
            for match in direct:
                all_matches.append({"branch_index": branch_index, "edge": list(edge), "kind": "direct", **match})
            for match in pairs:
                all_matches.append({"branch_index": branch_index, "edge": list(edge), "kind": "two_row", **match})
        leaf_records.append({
            "branch_index": branch_index,
            "factor_zero_generators": [str(factor) for factor in factors],
            "base_dead_p_edges": [list(edge) for edge in sorted(base)],
            "diagonal_zero_edges": [list(edge) for edge in sorted(zeros)],
            "minimal_doily_completion_size": len(completions[0]),
            "minimal_doily_completions": [[list(edge) for edge in completion] for completion in completions],
            "targets": targets,
        })

    payload = {
        "format": "krenn-c6-noncollapse-chord-low-support-factor-leaf-audit-v1",
        "scope": {
            "pair_orbit_index": 2,
            "slot": {"vertex": vertex, "colour": colour, "neighbours": [left, right]},
            "known_p_kills": [str(p_left), str(p_right)],
            "row_census": len(rows),
        },
        "candidate_family": (
            "One original frozen amplitude row, or the exact rational span of two such rows, "
            "after reduction by the two slot P-kills and an exhaustive factor leaf, equals a "
            "required additional P-line target."
        ),
        "factor_leaves": leaf_records,
        "summary": {
            "factor_leaves": len(leaf_records),
            "minimal_completion_size": 3,
            "low_support_p_kill_matches": len(all_matches),
        },
        "conclusion": {
            "established": (
                "No required chord P-kill has the stated one/two-row low-support identity "
                "on any hard factor leaf."
                if not all_matches else
                "A stated low-support chord P-kill identity occurs; promote it to a framed "
                "strict certificate."
            ),
            "not_established": (
                "Three-or-more-row syzygies, identities with nonconstant multipliers, and "
                "other non-collapse chart types remain outside this audit."
            ),
        },
        "sources": {
            "factor_frontier_sha256": sha256(FRONTIER),
            "base_pair_audit_sha256": sha256(PAIR_AUDIT),
            "factor_adjugate_audit_sha256": sha256(FACTOR_ADJUGATE_AUDIT),
            "c6_collapse_attack_sha256": sha256(ROOT / "c6_collapse_attack.py"),
            "f9_pipeline_sha256": sha256(ROOT / "f9_pipeline.py"),
            "audit_script_sha256": sha256(Path(__file__)),
        },
        "receipt_payload_sha256": digest({
            "factor_leaves": leaf_records,
            "matches": all_matches,
        }),
    }
    TARGET.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    if all_matches:
        print("C6 LOW-SUPPORT FACTOR-LEAF AUDIT FOUND MATCHES: " + str(len(all_matches)))
        return 2
    print(
        "C6 LOW-SUPPORT FACTOR-LEAF AUDIT VERIFIED: "
        f"{len(leaf_records)} leaves, no one/two-row chord-P matches"
    )
    print("manifest_sha256=" + sha256(TARGET))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
