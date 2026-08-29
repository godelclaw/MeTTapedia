#!/usr/bin/env python3
"""Try the transported 11-row non-collapse core on the four hard factor leaves.

The seed non-collapse chart `(v0,c0)` has a strict 11-generator unit
certificate: eight (3,2,1) source rows, two adjugate P-kills, and the theta
inverse equation.  Its two frozen transports to the hard `(v0,c2)` chart are
not units by themselves.  The hard chart additionally has four exhaustive
domain leaves from its first-stage cofactor products.  This script makes that
precise finite experiment:

* two pre-existing frozen `(v0,c2)` transports;
* four pairs of factor-zero generators;
* one bounded exact-Q unit screen per resulting 13-generator system;
* a strict Singular lift only if that screen returns a unit basis.

It does not infer anything from a non-unit or timeout screen.  A successful
strict replay is a genuine subset certificate for that factor leaf.
"""

from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys
import time
from pathlib import Path
from typing import Any

import sympy as sp


ROOT = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
PRIVATE = Path(__file__).resolve().parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from c4_crux_freeze import write_msolve, write_singular_lift  # noqa: E402
from run_frozen_msolve import unit_basis  # noqa: E402


FRONTIER = ROOT / "noncollapse_case_artifacts" / "noncollapse_factor_frontier_audit_v1.json"
TRANSPORT = ROOT / "noncollapse_case_artifacts" / "elevenrow_transport_v1"
TARGET = ROOT / "noncollapse_case_artifacts" / "type02_factorized_eleven_core_v2"
MSOLVE = Path(os.environ.get("MSOLVE", "msolve"))
LIFT_RUNNER = ROOT / "run_exact_lift.py"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical(poly: sp.Expr, symbols: list[sp.Symbol]) -> list[list[object]]:
    return [
        [int(coefficient), list(exponents)]
        for exponents, coefficient in sp.Poly(poly, *symbols, domain=sp.ZZ).terms()
    ]


def decode(terms: list[list[object]], symbols: list[sp.Symbol]) -> sp.Expr:
    expression = sp.Integer(0)
    for coefficient, exponents in terms:
        if type(coefficient) is not int or not isinstance(exponents, list):
            raise RuntimeError("frozen equation encoding drift")
        if len(exponents) != len(symbols) or any(type(power) is not int or power < 0 for power in exponents):
            raise RuntimeError("frozen exponent encoding drift")
        monomial = sp.Integer(coefficient)
        for symbol, power in zip(symbols, exponents, strict=True):
            monomial *= symbol ** power
        expression += monomial
    return sp.expand(expression)


def run_msolve(input_path: Path, output: Path, timeout: int) -> dict[str, Any]:
    output.mkdir(parents=True, exist_ok=True)
    basis = output / "basis.out"
    basis.unlink(missing_ok=True)
    started = time.monotonic()
    try:
        result = subprocess.run(
            [str(MSOLVE), "-g", "1", "-t", "1", "-f", str(input_path), "-o", str(basis)],
            capture_output=True, text=True, timeout=timeout,
        )
    except subprocess.TimeoutExpired as error:
        stdout = error.stdout.decode() if isinstance(error.stdout, bytes) else error.stdout or ""
        stderr = error.stderr.decode() if isinstance(error.stderr, bytes) else error.stderr or ""
        (output / "stdout").write_text(stdout)
        (output / "stderr").write_text(stderr)
        return {
            "verdict": "timeout_no_verdict",
            "seconds": round(time.monotonic() - started, 6),
            "timeout_seconds": timeout,
        }
    (output / "stdout").write_text(result.stdout)
    (output / "stderr").write_text(result.stderr)
    basis_text = basis.read_text() if basis.exists() else ""
    is_unit, constant = unit_basis(basis_text)
    verdict = "unit_ideal" if result.returncode == 0 and is_unit else "not_unit_or_unparsed"
    return {
        "verdict": verdict,
        "seconds": round(time.monotonic() - started, 6),
        "timeout_seconds": timeout,
        "returncode": result.returncode,
        "basis_constant": constant,
        "basis_sha256": sha256(basis) if basis.exists() else None,
        "stdout_sha256": sha256(output / "stdout"),
        "stderr_sha256": sha256(output / "stderr"),
    }


def run_lift(system: Path, lift: Path, output: Path, timeout: int) -> dict[str, Any]:
    started = time.monotonic()
    result = subprocess.run(
        [sys.executable, str(LIFT_RUNNER), str(system), str(lift), str(output),
         "--method", "tracked", "--timeout", str(timeout)],
        capture_output=True, text=True,
    )
    (output / "runner.stdout").write_text(result.stdout)
    (output / "runner.stderr").write_text(result.stderr)
    manifest = output / "manifest.json"
    if not manifest.exists():
        return {
            "verdict": "lift_runner_failure_no_certificate",
            "returncode": result.returncode,
            "seconds_including_runner": round(time.monotonic() - started, 6),
            "runner_stdout_sha256": sha256(output / "runner.stdout"),
            "runner_stderr_sha256": sha256(output / "runner.stderr"),
        }
    payload = json.loads(manifest.read_text())
    return {
        "verdict": payload.get("verdict"),
        "returncode": result.returncode,
        "seconds_including_runner": round(time.monotonic() - started, 6),
        "manifest_sha256": sha256(manifest),
        "runner_stdout_sha256": sha256(output / "runner.stdout"),
        "runner_stderr_sha256": sha256(output / "runner.stderr"),
        "strict_replay": payload.get("strict_replay"),
    }


def main() -> int:
    if not MSOLVE.is_file() or not LIFT_RUNNER.is_file():
        raise RuntimeError("required bounded-certificate tools missing")
    frontier = json.loads(FRONTIER.read_text())
    if frontier.get("format") != "krenn-c6-noncollapse-factor-frontier-audit-v1":
        raise RuntimeError("factor-frontier format drift")
    hard = next(row for row in frontier["frontier"] if row["pair_orbit_index"] == 2)
    if hard["factor_branch_count"] != 4:
        raise RuntimeError("hard factor-leaf inventory drift")
    base_tags = ("v0_c2_p201", "v0_c2_p210")
    TARGET.mkdir(parents=True, exist_ok=True)
    records = []
    strict_successes = 0
    for tag in base_tags:
        base_dir = TRANSPORT / tag
        base_system = base_dir / "system.json"
        base = json.loads(base_system.read_text())
        if base.get("format") != "krenn-c6-noncollapse-eleven-row-transport-v1":
            raise RuntimeError("transport system format drift")
        base_names = base["variables"]
        if not isinstance(base_names, list) or len(base_names) != len(set(base_names)):
            raise RuntimeError("transport variable inventory drift")
        base_symbols = list(sp.symbols(" ".join(base_names), seq=True))
        source_equations = [decode(equation, base_symbols) for equation in base["equations"]]
        if len(source_equations) != 11:
            raise RuntimeError("transport generator count drift")
        all_factor_names = sorted({
            factor["symbol"]
            for branch in hard["branches"]
            for factor in (branch["x_factor"], branch["y_factor"])
        })
        names = [*base_names, *(name for name in all_factor_names if name not in base_names)]
        symbols = list(sp.symbols(" ".join(names), seq=True))
        symbol_by_name = dict(zip(names, symbols, strict=True))
        for leaf_index, branch in enumerate(hard["branches"]):
            factor_names = [branch["x_factor"]["symbol"], branch["y_factor"]["symbol"]]
            output = TARGET / f"{tag}_leaf{leaf_index}"
            output.mkdir(parents=True, exist_ok=True)
            factors = [symbol_by_name[name] for name in factor_names]
            equations = [*source_equations, *factors]
            system_payload = {
                "format": "krenn-c6-noncollapse-factorized-eleven-core-v1",
                "parent_system_file_sha256": sha256(base_system),
                "parent_system_sha256": base.get("system_sha256"),
                "factor_frontier_sha256": sha256(FRONTIER),
                "transport_tag": tag,
                "factor_leaf_index": leaf_index,
                "factor_zero_generators": factor_names,
                "variables": names,
                "equations": [canonical(equation, symbols) for equation in equations],
                "statistics": {
                    "variables": len(symbols),
                    "generators": len(equations),
                    "variables_added_for_leaf_factors": len(names) - len(base_names),
                },
            }
            system = output / "system.json"
            system.write_text(json.dumps(system_payload, indent=2, sort_keys=True) + "\n")
            input_q = output / "input_q.ms"
            lift = output / "lift.sing"
            write_msolve(input_q, symbols, equations, 0)
            write_singular_lift(lift, symbols, equations)
            msolve = run_msolve(input_q, output / "msolve_q", timeout=10)
            lift_result = None
            if msolve["verdict"] == "unit_ideal":
                lift_result = run_lift(system, lift, output / "lift_tracked", timeout=30)
                strict_successes += int(lift_result["verdict"] == "strict_exact_identity")
            records.append({
                "tag": tag,
                "factor_leaf_index": leaf_index,
                "system_file_sha256": sha256(system),
                "input_q_sha256": sha256(input_q),
                "lift_script_sha256": sha256(lift),
                "msolve": msolve,
                "lift": lift_result,
            })
            print(f"{tag} leaf{leaf_index}: {msolve['verdict']}", flush=True)
    payload = {
        "format": "krenn-c6-noncollapse-factorized-eleven-core-probe-v1",
        "candidate_family": (
            "The two frozen 11-row transports to hard type `(v0,c2)`, augmented only "
            "by one of the four domain factor leaves."
        ),
        "summary": {
            "candidate_systems": len(records),
            "strict_exact_identities": strict_successes,
            "msolve_units": sum(row["msolve"]["verdict"] == "unit_ideal" for row in records),
        },
        "records": records,
        "sources": {
            "factor_frontier_sha256": sha256(FRONTIER),
            "transport_manifest_sha256": sha256(TRANSPORT / "manifest.json"),
            "probe_script_sha256": sha256(Path(__file__)),
        },
    }
    manifest = TARGET / "manifest.json"
    manifest.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print("manifest_sha256=" + sha256(manifest))
    return 0 if strict_successes else 2


if __name__ == "__main__":
    raise SystemExit(main())
