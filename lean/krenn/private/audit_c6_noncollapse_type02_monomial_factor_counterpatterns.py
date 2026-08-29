#!/usr/bin/env python3
"""Falsify pure monomial-factor propagation on the hard C6 factor leaves.

After a hard type-2 factor leaf is substituted, many normalized amplitude
equations become single monomials.  Over a domain each gives a Boolean clause:
at least one of its factors is zero.  It is tempting to branch on those
clauses until a support drop, all-collapse, or doily obstruction appears.

This audit tests that *specific* proof strategy before building its tree.  For
each of the four leaves it finds a concrete zero/nonzero pattern satisfying
every such monomial clause while:

* retaining a possible nonzero designated theta determinant;
* retaining at least one off-diagonal channel on every C6 mixed edge; and
* avoiding the exact diagonal/doily contradiction supplied by the two known
  incident P-kills.

The patterns are independently rechecked with ordinary finite Python logic;
Z3 is used only to discover them.  They are not algebraic witnesses for the
full equations.  They prove only that monomial-factor propagation alone
cannot close these leaves.
"""

from __future__ import annotations

import os
import hashlib
import itertools
import json
import sys
from pathlib import Path
from typing import Any

import sympy as sp
import z3


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
TARGET = ROOT / "noncollapse_case_artifacts" / "noncollapse_type02_monomial_factor_counterpatterns_v1.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def digest(value: object) -> str:
    return hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def factors_of_monomial(poly: sp.Expr) -> tuple[sp.Symbol, ...] | None:
    if poly == 0:
        return None
    expanded = sp.Poly(poly)
    terms = expanded.terms()
    if len(terms) != 1 or terms[0][1] == 0:
        return None
    exponents, _coefficient = terms[0]
    factors: list[sp.Symbol] = []
    for symbol, exponent in zip(expanded.gens, exponents, strict=True):
        factors.extend([symbol] * exponent)
    return tuple(factors)


def forced_zero_monomial(factors: tuple[sp.Symbol, ...], dead: set[sp.Symbol]) -> bool:
    return any(factor in dead for factor in factors)


def main() -> int:
    frontier = json.loads(FRONTIER.read_text())
    if frontier.get("format") != "krenn-c6-noncollapse-factor-frontier-audit-v1":
        raise RuntimeError("factor-frontier format drift")
    hard = next(row for row in frontier["frontier"] if row["pair_orbit_index"] == 2)
    if hard["factor_branch_count"] != 4:
        raise RuntimeError("hard factor-leaf inventory drift")

    vertex, colour = 0, 2
    case0 = pipeline.cases_for(c6.X)[0]
    fixed = pipeline.max_fixable([
        (c6.X[index], source, target)
        for index, (source, target) in enumerate(case0)
    ])
    gauge = {c6.VAR[key]: sp.Integer(1) for key in fixed}
    theta = sp.expand(c6.theta_det(vertex, colour).xreplace(gauge))
    theta_terms = sp.Poly(theta).terms()
    theta_monomials: list[tuple[sp.Symbol, ...]] = []
    for exponents, _coefficient in theta_terms:
        factors: list[sp.Symbol] = []
        for symbol, exponent in zip(sp.Poly(theta).gens, exponents, strict=True):
            factors.extend([symbol] * exponent)
        theta_monomials.append(tuple(factors))
    if len(theta_monomials) != 2:
        raise RuntimeError("designated theta shape drift")

    source_rows = []
    for colours in itertools.product(range(3), repeat=6):
        equation = sp.expand(
            c6.pm_sum(dict(enumerate(colours))).xreplace(gauge)
            - (1 if len(set(colours)) == 1 else 0)
        )
        source_rows.append(("".join(map(str, colours)), equation))
    if len(source_rows) != 729:
        raise RuntimeError("frozen source-row census drift")

    offdiagonal_by_edge = {
        edge: tuple(
            symbol for (candidate, source, target), symbol in c6.VAR.items()
            if candidate == edge and source != target
        )
        for edge in c6.X
    }
    records = []
    for leaf_index, branch in enumerate(hard["branches"]):
        factor_symbols = {
            sp.Symbol(branch["x_factor"]["symbol"]),
            sp.Symbol(branch["y_factor"]["symbol"]),
        }
        substitution = {symbol: sp.Integer(0) for symbol in factor_symbols}
        clauses = set()
        zero_rows = 0
        for word, equation in source_rows:
            reduced = sp.expand(equation.xreplace(substitution))
            if reduced == 0:
                zero_rows += 1
                continue
            factors = factors_of_monomial(reduced)
            if factors == ():
                raise RuntimeError("factor leaf has a direct nonzero constant contradiction")
            if factors:
                clauses.add(tuple(sorted(set(factors), key=str)))
        clauses = sorted(clauses, key=lambda clause: (len(clause), tuple(map(str, clause))))
        symbols = sorted(
            set().union(*clauses, factor_symbols, *theta_monomials,
                        *(set(values) for values in offdiagonal_by_edge.values())),
            key=str,
        )
        dead = {symbol: z3.Bool(str(symbol)) for symbol in symbols}
        solver = z3.Solver()
        for factor in factor_symbols:
            solver.add(dead[factor])
        for clause in clauses:
            solver.add(z3.Or(*[dead[factor] for factor in clause]))
        # At least one theta monomial remains nonzero, so the determinant is
        # not forced to zero by this zero-pattern information.
        solver.add(z3.Or(*[
            z3.And(*[z3.Not(dead[factor]) for factor in monomial])
            for monomial in theta_monomials
        ]))
        # No mixed edge is forced fully diagonal.
        for edge, channels in offdiagonal_by_edge.items():
            solver.add(z3.Or(*[z3.Not(dead[channel]) for channel in channels]))
        if solver.check() != z3.sat:
            raise RuntimeError(
                "no Boolean counterpattern: this leaf may justify a certified propagation tree"
            )
        model = solver.model()
        dead_set = {
            symbol for symbol in symbols
            if z3.is_true(model.eval(dead[symbol], model_completion=True))
        }
        # Independent, solver-free validation of every claimed property.
        if not factor_symbols <= dead_set:
            raise RuntimeError("counterpattern omitted a leaf factor")
        if not all(forced_zero_monomial(clause, dead_set) for clause in clauses):
            raise RuntimeError("counterpattern misses a monomial clause")
        if not any(not forced_zero_monomial(monomial, dead_set)
                   for monomial in theta_monomials):
            raise RuntimeError("counterpattern forces designated theta zero")
        if any(all(channel in dead_set for channel in channels)
               for channels in offdiagonal_by_edge.values()):
            raise RuntimeError("counterpattern forces a support drop")
        doily = branch["doily_constraints_by_colour"]
        if len(doily) != 1 or doily[0]["colour"] != colour:
            raise RuntimeError("hard leaf doily data drift")
        p_edges = {tuple(edge) for edge in doily[0]["dead_p_edges"]}
        diagonal_zeros = {
            edge for (edge, source, target), symbol in c6.VAR.items()
            if source == target == colour and symbol in dead_set
        }
        if total_forced_zero(p_edges, diagonal_zeros):
            raise RuntimeError("counterpattern accidentally meets the doily obstruction")
        records.append({
            "leaf_index": leaf_index,
            "factor_zero_generators": sorted(map(str, factor_symbols)),
            "zero_source_rows_after_factor_substitution": zero_rows,
            "distinct_monomial_clauses": [list(map(str, clause)) for clause in clauses],
            "counterpattern_dead_variables": sorted(map(str, dead_set)),
            "counterpattern_checks": {
                "all_monomial_clauses_hit": True,
                "designated_theta_not_forced_zero": True,
                "every_C6_mixed_edge_retains_an_offdiagonal": True,
                "doily_total_not_forced_zero": True,
                "doily_diagonal_zero_edges": [list(edge) for edge in sorted(diagonal_zeros)],
            },
        })

    payload = {
        "format": "krenn-c6-noncollapse-type02-monomial-factor-counterpatterns-v1",
        "scope": (
            "Boolean consequences of normalized amplitude rows that become monomials after "
            "one hard type-2 factor leaf; nonmonomial P relations and inverse-sensitive algebra "
            "are intentionally outside scope."
        ),
        "slot": {"vertex": vertex, "colour": colour, "theta": str(theta)},
        "records": records,
        "summary": {
            "factor_leaves": len(records),
            "all_leaves_have_counterpatterns": len(records) == 4,
        },
        "conclusion": {
            "established": (
                "Pure propagation from monomialized balanced rows cannot alone force a support "
                "drop, all-collapse, or the current doily contradiction on any hard type-2 leaf."
            ),
            "not_established": (
                "These Boolean counterpatterns are not solutions of the full polynomial system; "
                "they do not address nonmonomial source relations, P-line identities, or theta localization."
            ),
        },
        "sources": {
            "factor_frontier_sha256": sha256(FRONTIER),
            "c6_collapse_attack_sha256": sha256(ROOT / "c6_collapse_attack.py"),
            "f9_pipeline_sha256": sha256(ROOT / "f9_pipeline.py"),
            "audit_script_sha256": sha256(Path(__file__)),
        },
        "receipt_payload_sha256": digest(records),
    }
    TARGET.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print("C6 TYPE-2 MONOMIAL FACTOR COUNTERPATTERNS VERIFIED: 4/4 leaves")
    print("manifest_sha256=" + sha256(TARGET))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
