#!/usr/bin/env python3
"""Bounded Macaulay-degree probe for a non-collapse unit certificate.

For a frozen branch whose only constant-bearing generator is ``q - 1``, a
certificate of total degree ``D`` has the form

    sum_i h_i f_i - (q - 1) = 1.

This script asks whether a target lies in the span of frozen generators after
multiplication by monomials of the allowed degree.  By default it derives the
target from that ``q - 1`` branch.  A payload with a top-level canonical
``target`` polynomial instead runs a direct ideal-membership probe.  A
positive result records its sparse multiplier inventory for subsequent exact
replay; a finite-field negative is merely diagnostic and never treated as a
proof of non-membership over Q.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from itertools import combinations_with_replacement
from pathlib import Path

import sympy as sp
from sympy.polys.domains import GF, QQ
from sympy.polys.matrices.sdm import SDM


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def total_degree(exponent: tuple[int, ...]) -> int:
    return sum(exponent)


def multiplier_monomials(nvars: int, maximum_degree: int):
    zero = (0,) * nvars
    yield zero
    for degree in range(1, maximum_degree + 1):
        for positions in combinations_with_replacement(range(nvars), degree):
            exponent = [0] * nvars
            for position in positions:
                exponent[position] += 1
            yield tuple(exponent)


def add_exponents(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(a + b for a, b in zip(left, right, strict=True))


def as_terms(raw: list[list[object]]) -> dict[tuple[int, ...], int]:
    answer: dict[tuple[int, ...], int] = {}
    for coefficient, exponent in raw:
        monomial = tuple(int(value) for value in exponent)
        answer[monomial] = answer.get(monomial, 0) + int(coefficient)
    return {monomial: coefficient for monomial, coefficient in answer.items()
            if coefficient}


def constant_term(terms: dict[tuple[int, ...], int]) -> int:
    zero = (0,) * len(next(iter(terms)))
    return terms.get(zero, 0)


def sparse_column(
    terms: dict[tuple[int, ...], int], multiplier: tuple[int, ...],
) -> dict[tuple[int, ...], int]:
    return {add_exponents(monomial, multiplier): coefficient
            for monomial, coefficient in terms.items()}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("system", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--degree", type=int, required=True)
    parser.add_argument("--prime", type=int, default=32003)
    parser.add_argument("--exact", action="store_true")
    args = parser.parse_args()

    source = json.loads(args.system.read_text())
    names = source["variables"]
    equations = [as_terms(raw) for raw in source["equations"]]
    nvars = len(names)
    mode = "membership" if "target" in source else "unit_branch"
    branch_index: int | None = None
    if mode == "membership":
        target = as_terms(source["target"])
    else:
        constant_indices = [index for index, terms in enumerate(equations)
                            if constant_term(terms)]
        if len(constant_indices) != 1:
            raise ValueError(
                f"expected one constant-bearing branch, got {constant_indices}"
            )
        branch_index = constant_indices[0]
        branch = equations[branch_index]
        if constant_term(branch) != -1:
            raise ValueError("expected branch generator q - 1")
        zero = (0,) * nvars
        target = dict(branch)
        del target[zero]
    if max(map(total_degree, target)) > args.degree:
        raise ValueError("requested certificate degree is smaller than target")

    columns: list[tuple[int, tuple[int, ...], dict[tuple[int, ...], int]]] = []
    for equation_index, terms in enumerate(equations):
        if equation_index == branch_index:
            continue
        budget = args.degree - max(map(total_degree, terms))
        if budget < 0:
            continue
        for multiplier in multiplier_monomials(nvars, budget):
            columns.append((equation_index, multiplier, sparse_column(terms, multiplier)))
    zero = (0,) * nvars
    # Append -target, so a null vector whose final entry is nonzero encodes
    # A*x=target.
    columns.append((-1, zero, {monomial: -coefficient
                               for monomial, coefficient in target.items()}))

    rows: dict[tuple[int, ...], int] = {}
    entries: dict[int, dict[int, object]] = {}
    domain = QQ if args.exact else GF(args.prime)
    for column_index, (_source_index, _multiplier, column) in enumerate(columns):
        for monomial, coefficient in column.items():
            row_index = rows.setdefault(monomial, len(rows))
            entries.setdefault(row_index, {})[column_index] = domain.convert(coefficient)
    matrix = SDM(entries, (len(rows), len(columns)), domain)
    nullspace, _pivots = matrix.nullspace()
    target_column = len(columns) - 1
    witness: dict[int, object] | None = None
    for _basis_index, vector in nullspace.items():
        if vector.get(target_column, domain.zero) != domain.zero:
            witness = vector
            break

    payload = {
        "format": "krenn-noncollapse-linear-certificate-probe-v1",
        "source_system_file_sha256": sha256(args.system),
        "degree": args.degree,
        "field": "Q" if args.exact else f"GF({args.prime})",
        "variables": nvars,
        "rows": len(rows),
        "candidate_columns": len(columns) - 1,
        "mode": mode,
        "branch_equation_index_1based": (branch_index + 1
                                           if branch_index is not None else None),
        "verdict": "span_found" if witness is not None else "span_not_found",
    }
    if witness is not None:
        scale = witness[target_column]
        selected = []
        for column_index, value in witness.items():
            if column_index == target_column or value == domain.zero:
                continue
            equation_index, multiplier, _column = columns[column_index]
            selected.append({
                "equation_index_1based": equation_index + 1,
                "multiplier_exponents": list(multiplier),
                "coefficient": str(value / scale),
            })
        payload["nonzero_terms"] = len(selected)
        payload["selected"] = selected
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: payload[key] for key in payload if key != "selected"},
                     sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
