#!/usr/bin/env python3
"""Test one small non-collapse certificate shape across the 18 C6 slots.

The seed is the eleven-row strict certificate found at the gauge-fixed
case-0 slot ``(vertex=0, colour=0)``.  For each vertex, distinguished colour,
and the two orientations of the other colours, this program freezes the
corresponding physical eleven-row subsystem:

* eight fixed-profile amplitude equations;
* the two adjacent P-kills for that slot; and
* the Rabinowitsch inverse of that slot's theta determinant.

This is a finite mutation-and-transport test, not an assumed symmetry.  Each
candidate is an independently frozen system.  A positive result is accepted
only when Singular emits an exact identity that the strict checker replays.
All calls are sequential and bounded; a timeout is recorded as unknown.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import os
import re
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

import c6_collapse_attack as c6
import f9_pipeline as pipeline
from c4_crux_freeze import canonical_polynomial, write_msolve, write_singular_lift
from engine_fingerprint import ROOT, source_manifest
from run_exact_lift import environment as singular_environment
from run_frozen_msolve import unit_basis


MSOLVE = Path(os.environ.get("MSOLVE", "msolve"))
MSOLVE_LIB = Path(os.environ.get("MSOLVE_LIB", ""))

# These are the eight amplitude rows in the proved slot-0 core.  They contain
# two 4-2, two 4-1-1, and five 3-2-1 profiles.
SEED_WORDS = (
    "100001", "100010", "200001", "200010",
    "200101", "200111", "201010", "201011",
)


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def digest(value: object) -> str:
    return sha256_bytes(json.dumps(
        value, sort_keys=True, separators=(",", ":")
    ).encode())


def transform_word(word: str, permutation: tuple[int, int, int]) -> str:
    return "".join(str(permutation[int(colour)]) for colour in word)


def msolve_environment() -> dict[str, str]:
    if not MSOLVE.is_file() or not MSOLVE_LIB.is_dir():
        raise FileNotFoundError("userspace msolve installation is incomplete")
    result = os.environ.copy()
    old = result.get("LD_LIBRARY_PATH", "")
    result["LD_LIBRARY_PATH"] = str(MSOLVE_LIB) + (":" + old if old else "")
    return result


def freeze_candidate(
    output: Path,
    substitution: dict[sp.Symbol, sp.Expr],
    vertex: int,
    colour: int,
    permutation: tuple[int, int, int],
    sources: dict[str, Any],
) -> tuple[Path, dict[str, Any]]:
    words = tuple(transform_word(word, permutation) for word in SEED_WORDS)
    amplitudes = [
        sp.expand(c6.pm_sum(dict(enumerate(map(int, word)))).xreplace(substitution))
        for word in words
    ]
    left, right = c6.NBR[vertex]
    theta = sp.expand(c6.theta_det(vertex, colour).xreplace(substitution))
    inverse = sp.Symbol(f"theta_{vertex}_{colour}_inv")
    generators = amplitudes + [
        sp.expand(c6.P(vertex, left, colour).xreplace(substitution)),
        sp.expand(c6.P(vertex, right, colour).xreplace(substitution)),
        sp.expand(theta * inverse - 1),
    ]
    if any(poly == 0 for poly in generators):
        raise RuntimeError("candidate contains an unexpectedly zero generator")
    variables = sorted(
        {symbol for poly in generators for symbol in poly.free_symbols},
        key=sp.default_sort_key,
    )
    system = {
        "variables": [str(symbol) for symbol in variables],
        "equations": [canonical_polynomial(poly, variables) for poly in generators],
    }
    payload = {
        "format": "krenn-c6-noncollapse-eleven-row-transport-v1",
        "seed_slot": {"vertex": 0, "colour": 0},
        "slot": {
            "vertex": vertex,
            "colour": colour,
            "neighbours": [left, right],
        },
        "colour_permutation": list(permutation),
        "seed_words": list(SEED_WORDS),
        "selected_words": list(words),
        "equation_labels": list(words) + [
            "adjugate_P_kill_left",
            "adjugate_P_kill_right",
            "theta_inverse_branch",
        ],
        "profile_signature": {
            "4-2": 2,
            "4-1-1": 2,
            "3-2-1": 5,
        },
        "source_manifest": sources,
        "statistics": {"generators": len(generators), "variables": len(variables)},
        "system_sha256": digest(system),
        **system,
    }
    output.mkdir(parents=True, exist_ok=False)
    system_path = output / "system.json"
    system_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    write_msolve(output / "input_q.ms", variables, generators, 0)
    write_singular_lift(output / "lift.sing", variables, generators)
    return system_path, payload


def msolve_probe(
    system_dir: Path, timeout: int, basis_name: str = "basis.out"
) -> dict[str, Any]:
    basis = system_dir / basis_name
    started = time.monotonic()
    try:
        result = subprocess.run(
            [str(MSOLVE), "-g", "1", "-t", "1", "-f",
             str(system_dir / "input_q.ms"), "-o", str(basis)],
            capture_output=True, text=True, timeout=timeout, env=msolve_environment(),
        )
    except subprocess.TimeoutExpired as error:
        stdout = ((error.stdout or b"").decode()
                  if isinstance(error.stdout, bytes) else error.stdout or "")
        stderr = ((error.stderr or b"").decode()
                  if isinstance(error.stderr, bytes) else error.stderr or "")
        return {
            "verdict": "timeout_unknown",
            "seconds": round(time.monotonic() - started, 6),
            "stdout_sha256": sha256_bytes(stdout.encode()),
            "stderr_sha256": sha256_bytes(stderr.encode()),
        }
    text = basis.read_text() if basis.exists() else ""
    is_unit, constant = unit_basis(text)
    length_match = re.search(r"#length of basis:\s*(\d+)\s+elements?", text)
    if result.returncode != 0:
        verdict = "process_failure_unknown"
    elif is_unit:
        verdict = "unit_ideal"
    elif length_match and int(length_match.group(1)) > 1:
        verdict = "nonunit_basis"
    else:
        verdict = "unparsed_basis_unknown"
    return {
        "verdict": verdict,
        "basis_constant": constant,
        "returncode": result.returncode,
        "seconds": round(time.monotonic() - started, 6),
        "basis_sha256": sha256_bytes(text.encode()),
        "stdout_sha256": sha256_bytes(result.stdout.encode()),
        "stderr_sha256": sha256_bytes(result.stderr.encode()),
    }


def exact_lift(
    system_dir: Path, timeout: int, output_name: str = "lift_tracked"
) -> dict[str, Any]:
    lift_dir = system_dir / output_name
    started = time.monotonic()
    result = subprocess.run(
        [sys.executable, str(SHARED / "run_exact_lift.py"),
         str(system_dir / "system.json"), str(system_dir / "lift.sing"),
         str(lift_dir), "--method", "tracked", "--timeout", str(timeout)],
        capture_output=True, text=True, env=singular_environment(),
    )
    manifest = lift_dir / "manifest.json"
    if not manifest.exists():
        raise RuntimeError("exact-lift runner produced no manifest")
    payload = json.loads(manifest.read_text())
    return {
        "returncode": result.returncode,
        "seconds_including_runner": round(time.monotonic() - started, 6),
        "manifest_sha256": sha256_path(manifest),
        "verdict": payload.get("verdict"),
        "strict_replay": payload.get("strict_replay"),
        "runner_stdout_sha256": sha256_bytes(result.stdout.encode()),
        "runner_stderr_sha256": sha256_bytes(result.stderr.encode()),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument("--msolve-timeout", type=int, default=2)
    parser.add_argument("--lift-timeout", type=int, default=10)
    args = parser.parse_args()
    if args.msolve_timeout <= 0 or args.lift_timeout <= 0:
        parser.error("timeouts must be positive")
    if args.output.exists() and any(args.output.iterdir()):
        parser.error("output must be a new or empty directory")
    args.output.mkdir(parents=True, exist_ok=True)

    case = pipeline.cases_for(c6.X)[0]
    chosen = [(c6.X[index], colours[0], colours[1])
              for index, colours in enumerate(case)]
    fixed = pipeline.max_fixable(chosen)
    substitution = {c6.VAR[key]: sp.Integer(1) for key in fixed}
    sources = source_manifest(
        "test_c6_noncollapse_eleven_row_transport",
        sources=[ROOT / "c6_collapse_attack.py", ROOT / "f9_pipeline.py",
                 ROOT / "krenn_exact.py", ROOT / "c4_crux_freeze.py",
                 SHARED / "run_exact_lift.py", Path(__file__)],
    )

    rows: list[dict[str, Any]] = []
    permutations = tuple(itertools.permutations(range(3)))
    for vertex in range(6):
        for colour in range(3):
            for permutation in permutations:
                if permutation[0] != colour:
                    continue
                tag = f"v{vertex}_c{colour}_p{''.join(map(str, permutation))}"
                candidate_dir = args.output / tag
                system_path, payload = freeze_candidate(
                    candidate_dir, substitution, vertex, colour, permutation, sources
                )
                probe = msolve_probe(candidate_dir, args.msolve_timeout)
                lift: dict[str, Any] | None = None
                if probe["verdict"] == "unit_ideal":
                    lift = exact_lift(candidate_dir, args.lift_timeout)
                row = {
                    "tag": tag,
                    "slot": payload["slot"],
                    "colour_permutation": payload["colour_permutation"],
                    "system_file_sha256": sha256_path(system_path),
                    "system_sha256": payload["system_sha256"],
                    "msolve": probe,
                    "lift": lift,
                }
                rows.append(row)
                print(json.dumps({
                    "tag": tag,
                    "msolve": probe["verdict"],
                    "lift": None if lift is None else lift["verdict"],
                }, sort_keys=True), flush=True)

    counts = Counter(
        "strict_exact_identity" if row["lift"] and
        row["lift"]["verdict"] == "strict_exact_identity"
        else row["msolve"]["verdict"]
        for row in rows
    )
    payload = {
        "format": "krenn-c6-noncollapse-eleven-row-transport-manifest-v1",
        "source_manifest": sources,
        "seed_words": list(SEED_WORDS),
        "candidate_count": len(rows),
        "counts": dict(sorted(counts.items())),
        "rows": rows,
    }
    manifest = args.output / "manifest.json"
    manifest.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print("manifest_sha256=" + sha256_path(manifest))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
