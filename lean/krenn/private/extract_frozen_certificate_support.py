#!/usr/bin/env python3
"""Extract a source-bound frozen subsystem used by a strict lift identity.

The resulting system preserves the original variable order and records both
the parent-local and ultimate source equation indices.  It is useful for
turning a sparse strict certificate into a small independently replayable
core without treating an untrusted discovery solver as evidence.
"""

from __future__ import annotations

import os
import argparse
import hashlib
import json
import sys
from pathlib import Path

import sympy as sp


SHARED = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
if str(SHARED) not in sys.path:
    sys.path.insert(0, str(SHARED))

from c4_crux_freeze import write_msolve, write_singular_lift
from strict_certificate_checker import frozen_poly, symbols_for


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical_digest(value: object) -> str:
    return hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("parent", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("indices", nargs="+", type=int,
                        help="one-based parent equation indices")
    args = parser.parse_args()
    if len(args.indices) != len(set(args.indices)) or any(index <= 0 for index in args.indices):
        parser.error("indices must be distinct positive one-based positions")

    parent = json.loads(args.parent.read_text())
    equations = parent["equations"]
    if any(index > len(equations) for index in args.indices):
        parser.error("an index exceeds the parent equation count")
    selected = sorted(index - 1 for index in args.indices)
    names = parent["variables"]
    source_indices = parent.get("selected_source_indices_1based")
    if source_indices is None:
        source_indices = list(range(1, len(equations) + 1))
    if len(source_indices) != len(equations):
        raise ValueError("source-index provenance length drift")
    parent_labels = parent.get("source_labels", {})
    selected_source_indices = [int(source_indices[index]) for index in selected]
    source_labels = {
        str(source_index): parent_labels.get(str(source_index))
        for source_index in selected_source_indices
    }
    core = {
        "variables": names,
        "equations": [equations[index] for index in selected],
    }
    payload = {
        "format": "krenn-frozen-certificate-support-core-v1",
        "parent_system_file_sha256": sha256(args.parent),
        "parent_system_sha256": parent.get("system_sha256"),
        "ultimate_source_system_file_sha256": parent.get("source_system_file_sha256"),
        "selected_parent_indices_1based": [index + 1 for index in selected],
        "selected_source_indices_1based": selected_source_indices,
        "source_labels": source_labels,
        "statistics": {"variables": len(names), "generators": len(selected)},
        "system_sha256": canonical_digest(core),
        **core,
    }
    args.output.mkdir(parents=True, exist_ok=True)
    system_path = args.output / "system.json"
    system_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    symbols = symbols_for(names)
    polynomials = [frozen_poly(equations[index], symbols).as_expr()
                   for index in selected]
    write_msolve(args.output / "input_q.ms", symbols, polynomials, 0)
    write_singular_lift(args.output / "lift.sing", symbols, polynomials)
    manifest = {
        "format": "krenn-frozen-certificate-support-core-manifest-v1",
        "system_file_sha256": sha256(system_path),
        "system_sha256": payload["system_sha256"],
        "input_q_sha256": sha256(args.output / "input_q.ms"),
        "lift_script_sha256": sha256(args.output / "lift.sing"),
        "parent_system_file_sha256": payload["parent_system_file_sha256"],
    }
    manifest_path = args.output / "manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "generators": len(selected),
        "system_sha256": payload["system_sha256"],
        "manifest_sha256": sha256(manifest_path),
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
