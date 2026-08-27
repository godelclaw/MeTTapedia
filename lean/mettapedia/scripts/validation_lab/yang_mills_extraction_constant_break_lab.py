#!/usr/bin/env python3
"""Finite audit for the Yang-Mills extended-extraction constant.

The manuscript bounds the extraction projection by a displayed series of the
form

    sum_d count(d) * (r1 / r0)^(-d)

and then asserts a small value at r1/r0 = 1/2 and dmax = 16.  This lab computes
that displayed series bound.  It does not pretend to reconstruct the missing
analytic operator-norm proof; when the exact jet basis/count is underspecified,
the one-variable series is a conservative lower-bound scenario.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from math import comb
from pathlib import Path
from typing import Literal

import numpy as np


CountModel = Literal["multiindex", "ordinary_binomial"]


@dataclass(frozen=True)
class ExtractionCase:
    dmax: int
    b: int
    radius_ratio_r1_over_r0: float
    count_model: str
    variables: int
    displayed_series_cextract: float
    asserted_cextract: float
    series_c1: float
    advertised_c1: float
    lambda_irr: float
    series_lambda: float
    advertised_lambda: float
    contraction_threshold_c1: float
    series_over_asserted_cextract: float
    series_over_contraction_threshold: float
    series_contracts: bool
    advertised_contracts: bool


def count_for_degree(variables: int, degree: int, model: CountModel) -> int:
    if model == "multiindex":
        return comb(variables + degree - 1, degree)
    if model == "ordinary_binomial":
        return comb(variables, degree) if degree <= variables else 0
    raise ValueError(f"unknown count model: {model}")


def displayed_series_cextract(
    dmax: int,
    radius_ratio: float,
    variables: int,
    model: CountModel,
) -> float:
    degrees = np.arange(dmax + 1, dtype=np.float64)
    counts = np.array(
        [count_for_degree(variables, int(degree), model) for degree in degrees],
        dtype=np.float64,
    )
    terms = counts * np.power(radius_ratio, -degrees)
    return float(np.sum(terms))


def c1_from_cextract(cextract: float, b: int) -> float:
    return 1.65 * (3.0 * (b**4)) * 14.0 * cextract


def lambda_irr(b: int, dmax: int) -> float:
    return float(b ** (3 - dmax))


def case_row(
    dmax: int,
    *,
    b: int,
    radius_ratio: float,
    variables: int,
    model: CountModel,
    asserted_cextract: float,
    advertised_c1: float,
) -> ExtractionCase:
    cextract = displayed_series_cextract(dmax, radius_ratio, variables, model)
    series_c1 = c1_from_cextract(cextract, b)
    lam = lambda_irr(b, dmax)
    threshold = float(b ** (dmax - 3))
    series_lambda = series_c1 * lam
    advertised_lambda = advertised_c1 * lam
    return ExtractionCase(
        dmax=dmax,
        b=b,
        radius_ratio_r1_over_r0=radius_ratio,
        count_model=model,
        variables=variables,
        displayed_series_cextract=cextract,
        asserted_cextract=asserted_cextract,
        series_c1=series_c1,
        advertised_c1=advertised_c1,
        lambda_irr=lam,
        series_lambda=series_lambda,
        advertised_lambda=advertised_lambda,
        contraction_threshold_c1=threshold,
        series_over_asserted_cextract=cextract / asserted_cextract,
        series_over_contraction_threshold=series_c1 / threshold,
        series_contracts=series_lambda < 1.0,
        advertised_contracts=advertised_lambda < 1.0,
    )


def make_payload(args: argparse.Namespace) -> dict[str, object]:
    dmax_values = [int(part) for part in args.dmax_values.split(",") if part.strip()]
    if not dmax_values or any(dmax < 0 for dmax in dmax_values):
        raise ValueError("dmax-values must contain nonnegative integers")

    primary = [
        case_row(
            dmax,
            b=args.b,
            radius_ratio=args.radius_ratio,
            variables=1,
            model="multiindex",
            asserted_cextract=args.asserted_cextract,
            advertised_c1=args.advertised_c1,
        )
        for dmax in dmax_values
    ]
    sensitivity = [
        case_row(
            args.operative_dmax,
            b=args.b,
            radius_ratio=args.radius_ratio,
            variables=variables,
            model=model,
            asserted_cextract=args.asserted_cextract,
            advertised_c1=args.advertised_c1,
        )
        for model in ("multiindex", "ordinary_binomial")
        for variables in args.variables
    ]
    operative = case_row(
        args.operative_dmax,
        b=args.b,
        radius_ratio=args.radius_ratio,
        variables=1,
        model="multiindex",
        asserted_cextract=args.asserted_cextract,
        advertised_c1=args.advertised_c1,
    )
    status = (
        "pass"
        if operative.displayed_series_cextract > args.asserted_cextract
        and operative.series_lambda > 1.0
        and operative.advertised_lambda < 1.0
        else "fail"
    )
    return {
        "status": status,
        "interpretation": (
            "The manuscript-displayed extraction series grows at r1/r0=1/2. "
            "Even the one-variable multiindex lower-bound scenario contradicts "
            "Cextract <= 2 and makes the extended RG gain exceed 1 at dmax=16."
        ),
        "honesty_note": (
            "This computes the displayed series bound. The exact analytic "
            "operator norm of P_le_dmax is not fully specified by the PDF text."
        ),
        "manuscript_claims": {
            "b": args.b,
            "operative_dmax": args.operative_dmax,
            "radius_ratio_r1_over_r0": args.radius_ratio,
            "asserted_cextract": args.asserted_cextract,
            "advertised_c1": args.advertised_c1,
        },
        "primary_one_variable_lower_bound": [asdict(row) for row in primary],
        "operative_variable_sensitivity": [asdict(row) for row in sensitivity],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--dmax-values", default="4,10,12,14,16,18")
    parser.add_argument("--operative-dmax", type=int, default=16)
    parser.add_argument("--b", type=int, default=2)
    parser.add_argument("--radius-ratio", type=float, default=0.5)
    parser.add_argument("--asserted-cextract", type=float, default=2.0)
    parser.add_argument("--advertised-c1", type=float, default=2224.0)
    parser.add_argument("--variables", type=int, nargs="+", default=[1, 2, 4, 6, 16])
    args = parser.parse_args()

    payload = make_payload(args)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    operative = next(
        row
        for row in payload["primary_one_variable_lower_bound"]
        if row["dmax"] == args.operative_dmax
    )
    print(
        json.dumps(
            {
                "status": payload["status"],
                "operative_dmax": args.operative_dmax,
                "series_cextract": operative["displayed_series_cextract"],
                "asserted_cextract": operative["asserted_cextract"],
                "series_lambda": operative["series_lambda"],
                "advertised_lambda": operative["advertised_lambda"],
                "series_contracts": operative["series_contracts"],
                "advertised_contracts": operative["advertised_contracts"],
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
