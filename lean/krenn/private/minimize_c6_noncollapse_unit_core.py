#!/usr/bin/env python3
"""Deterministically shrink the exact C6 non-collapse branch to a 1-minimal core.

This is a discovery tool, never a proof checker.  It preserves the two
adjugate P-kills and the determinant inverse, then uses bounded exact-Q
``msolve`` calls to discard other generators whenever the remaining ideal is
still a unit ideal.  A timeout or any unparsed result is treated as unknown
and therefore *kept*: the resulting core is conservative.

The output remains a canonical polynomial system with source indices and a
full call transcript.  It is intended to make a subsequent short
``liftstd`` run feasible; only a strict exact replay can certify that later
identity.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Any

import sympy as sp


SHARED = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
if str(SHARED) not in sys.path:
    sys.path.insert(0, str(SHARED))

from c4_crux_freeze import write_msolve
from run_frozen_msolve import unit_basis


def sha256_path(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical_digest(value: object) -> str:
    return hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def as_polynomial(raw: list[list[object]], symbols: list[sp.Symbol]) -> sp.Expr:
    terms: dict[tuple[int, ...], int] = {}
    for coefficient, exponents in raw:
        key = tuple(int(value) for value in exponents)
        terms[key] = terms.get(key, 0) + int(coefficient)
    return sp.Poly.from_dict(terms, *symbols, domain=sp.ZZ).as_expr()


def chunks(values: list[int], count: int) -> list[list[int]]:
    count = min(max(count, 1), len(values))
    quotient, remainder = divmod(len(values), count)
    answer = []
    start = 0
    for index in range(count):
        width = quotient + (1 if index < remainder else 0)
        answer.append(values[start:start + width])
        start += width
    return [part for part in answer if part]


def profile_label(index: int) -> str | None:
    """Recover the source colouring label for the known 579-row input shape."""
    import itertools
    from collections import Counter as LocalCounter

    lower = {(6,), (5, 1), (4, 2), (4, 1, 1), (3, 2, 1)}
    rows = []
    for colouring in itertools.product(range(3), repeat=6):
        kind = tuple(sorted(LocalCounter(colouring).values(), reverse=True))
        if kind in lower:
            rows.append("".join(map(str, colouring)))
    return rows[index] if index < len(rows) else None


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("system", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument(
        "--msolve", type=Path,
        default=Path(os.environ.get("MSOLVE", "msolve")),
    )
    parser.add_argument("--timeout", type=int, default=30)
    parser.add_argument("--max-calls", type=int, default=12)
    parser.add_argument("--threads", type=int, default=1)
    args = parser.parse_args()
    if args.timeout <= 0 or args.max_calls < 2 or args.threads <= 0:
        parser.error("timeout and threads must be positive; max-calls must be at least 2")

    source = json.loads(args.system.read_text())
    names = source["variables"]
    symbols = [sp.Symbol(name) for name in names]
    raw_equations: list[list[list[object]]] = source["equations"]
    polynomials = [as_polynomial(raw, symbols) for raw in raw_equations]
    if len(polynomials) < 4:
        raise ValueError("need at least one non-branch generator and three branch rows")
    required = list(range(len(polynomials) - 3, len(polynomials)))
    candidates = list(range(0, len(polynomials) - 3))
    original_indices = source.get("original_equation_indices_1based")
    if original_indices is None:
        original_indices = list(range(1, len(polynomials) + 1))
    if len(original_indices) != len(polynomials):
        raise ValueError("original equation-index provenance length drift")

    args.output.mkdir(parents=True, exist_ok=True)
    trial_input = args.output / "trial.ms"
    trial_basis = args.output / "trial.basis"
    calls: list[dict[str, Any]] = []
    # The userspace msolve installation is deliberately not globally linked.
    # Keep this discovery tool self-contained rather than relying on the
    # caller's shell profile to find its bundled FLINT/NeoGB libraries.
    library = args.msolve.parents[1] / "lib" / "x86_64-linux-gnu"
    if not library.is_dir():
        raise FileNotFoundError(f"msolve library directory missing: {library}")
    environment = os.environ.copy()
    inherited_library_path = environment.get("LD_LIBRARY_PATH")
    environment["LD_LIBRARY_PATH"] = (
        str(library) if not inherited_library_path else
        str(library) + ":" + inherited_library_path
    )

    def unit(indices: list[int], purpose: str) -> bool:
        if len(calls) >= args.max_calls:
            return False
        ordered = sorted(set(indices))
        trial_basis.unlink(missing_ok=True)
        write_msolve(trial_input, symbols, [polynomials[index] for index in ordered], 0)
        started = time.monotonic()
        try:
            result = subprocess.run(
                [str(args.msolve), "-g", "1", "-t", str(args.threads),
                 "-f", str(trial_input), "-o", str(trial_basis)],
                capture_output=True, text=True, timeout=args.timeout,
                env=environment,
            )
            timed_out = False
        except subprocess.TimeoutExpired as error:
            result = None
            timed_out = True
            stdout = ((error.stdout or b"").decode()
                      if isinstance(error.stdout, bytes) else error.stdout or "")
            stderr = ((error.stderr or b"").decode()
                      if isinstance(error.stderr, bytes) else error.stderr or "")
        else:
            stdout, stderr = result.stdout, result.stderr
        basis = trial_basis.read_text() if trial_basis.exists() else ""
        is_unit, constant = unit_basis(basis)
        verdict = ("timeout_unknown" if timed_out else
                   "process_failure_unknown" if result is None or result.returncode != 0 else
                   "unit" if is_unit else "not_unit_or_unparsed")
        calls.append({
            "purpose": purpose,
            "generator_count": len(ordered),
            "indices_sha256": canonical_digest(ordered),
            "seconds": round(time.monotonic() - started, 6),
            "returncode": None if result is None else result.returncode,
            "verdict": verdict,
            "basis_constant": constant,
            "stdout_sha256": hashlib.sha256(stdout.encode()).hexdigest(),
            "stderr_sha256": hashlib.sha256(stderr.encode()).hexdigest(),
        })
        return verdict == "unit"

    if not unit(candidates + required, "initial"):
        (args.output / "preflight_failure.json").write_text(json.dumps({
            "format": "krenn-c6-noncollapse-core-preflight-failure-v1",
            "source_system_file_sha256": sha256_path(args.system),
            "calls": calls,
        }, indent=2, sort_keys=True) + "\n")
        raise RuntimeError("source branch no longer has a bounded exact-Q unit verdict")

    current = candidates
    split_count = 2
    # Reserve one bounded call for the final positive recheck.
    while current and len(calls) < args.max_calls - 1:
        changed = False
        for part in chunks(current, split_count):
            dropped = set(part)
            proposed = [index for index in current if index not in dropped]
            if unit(proposed + required, f"drop_{len(part)}_of_{len(current)}"):
                current = proposed
                split_count = max(2, split_count - 1)
                changed = True
                break
        if changed:
            continue
        if split_count >= len(current):
            break
        split_count = min(len(current), split_count * 2)

    selected = sorted(current + required)
    # Recheck after the final branch so the receipt always has a positive result.
    if not unit(selected, "final_recheck"):
        raise RuntimeError("final retained core lost its exact-Q unit verdict")

    core = {
        "variables": names,
        "equations": [raw_equations[index] for index in selected],
    }
    labels = {}
    for index in selected:
        original_index = int(original_indices[index])
        if index == required[0]:
            label = "adjugate_P_kill_left"
        elif index == required[1]:
            label = "adjugate_P_kill_right"
        elif index == required[2]:
            label = "theta_inverse_branch"
        else:
            label = profile_label(original_index - 1)
        labels[str(original_index)] = label
    payload = {
        "format": "krenn-c6-noncollapse-1minimal-core-v1",
        "source_system_file_sha256": sha256_path(args.system),
        "source_system_sha256": source.get("system_sha256"),
        "msolve_executable_sha256": sha256_path(args.msolve),
        "search_policy": {
            "algorithm": "deterministic-conservative-ddmin",
            "timeout_seconds_per_call": args.timeout,
            "max_calls": args.max_calls,
            "threads": args.threads,
            "unknown_is_kept": True,
            "required_source_indices_1based": [int(original_indices[index])
                                                for index in required],
        },
        "statistics": {
            "source_generators": len(polynomials),
            "retained_generators": len(selected),
            "retained_nonbranch_generators": len(current),
            "calls": len(calls),
            "call_verdicts": dict(Counter(call["verdict"] for call in calls)),
        },
        "selected_local_indices_1based": [index + 1 for index in selected],
        "selected_source_indices_1based": [int(original_indices[index])
                                             for index in selected],
        "source_labels": labels,
        "core_system_sha256": canonical_digest(core),
        "calls": calls,
        **core,
    }
    core_path = args.output / "system.json"
    core_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    write_msolve(args.output / "input_q.ms", symbols,
                 [polynomials[index] for index in selected], 0)
    manifest_path = args.output / "manifest.json"
    manifest = {
        "format": "krenn-c6-noncollapse-1minimal-core-manifest-v1",
        "core_system_file_sha256": sha256_path(core_path),
        "core_system_sha256": payload["core_system_sha256"],
        "input_q_sha256": sha256_path(args.output / "input_q.ms"),
        "source_system_file_sha256": payload["source_system_file_sha256"],
        "statistics": payload["statistics"],
    }
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "retained": len(selected),
        "calls": len(calls),
        "verdicts": payload["statistics"]["call_verdicts"],
        "core_system_sha256": payload["core_system_sha256"],
        "manifest_sha256": sha256_path(manifest_path),
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
