#!/usr/bin/env python3
"""Serially kernel-check one selected carrier-tree leaf and its bridge.

This is a deliberately narrow scaling test.  It checks exactly one frozen
leaf, its shared root system, and the generated semantic root-to-leaf bridge;
it does not claim that the full carrier tree or component has been imported.
The three Lean files are compiled one at a time with one Lean thread.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import time
from pathlib import Path


HERE = Path(__file__).resolve()
LEAN_ROOT = HERE.parents[1]
SHARED = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
LAKE = Path.home() / ".elan" / "bin" / "lake"

if str(SHARED) not in sys.path:
    sys.path.insert(0, str(SHARED))

from certify_carrier_tree import expand  # noqa: E402


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def suffix(tag: str) -> str:
    return tag.upper().replace(".", "_")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def source_paths(component: int, tag: str) -> tuple[Path, Path, Path]:
    directory = LEAN_ROOT / f"KrennComponent{component}"
    stem = suffix(tag)
    return (
        directory / "Root.lean",
        directory / f"SelectedLeaf{stem}.lean",
        directory / f"SelectedBridge{stem}.lean",
    )


def build_source(source: Path, timeout_seconds: int) -> dict[str, object]:
    relative = source.relative_to(LEAN_ROOT)
    output = LEAN_ROOT / ".lake" / "build" / "lib" / "lean" / relative
    output = output.with_suffix(".olean")
    ilean = output.with_suffix(".ilean")
    output.parent.mkdir(parents=True, exist_ok=True)
    environment = os.environ.copy()
    environment["LEAN_NUM_THREADS"] = "1"
    started = time.monotonic()
    completed = subprocess.run(
        [str(LAKE), "env", "lean", str(relative), "-o", str(output), "-i", str(ilean)],
        cwd=LEAN_ROOT,
        env=environment,
        text=True,
        capture_output=True,
        timeout=timeout_seconds,
        preexec_fn=lambda: os.nice(19),
    )
    elapsed = time.monotonic() - started
    output_text = completed.stdout + completed.stderr
    if completed.returncode != 0:
        raise RuntimeError(
            f"Lean failed for {relative} (exit {completed.returncode}):\n"
            + output_text[-8000:]
        )
    require(output.is_file(), f"Lean did not emit {output}")
    return {
        "source": str(relative),
        "source_sha256": sha256(source),
        "olean": str(output.relative_to(LEAN_ROOT)),
        "olean_sha256": sha256(output),
        "elapsed_seconds": round(elapsed, 3),
        "lean_output": output_text.strip(),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("component", type=int)
    parser.add_argument("tag")
    parser.add_argument("--build", action="store_true")
    parser.add_argument("--timeout-seconds", type=int, default=600)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    require(args.timeout_seconds > 0, "timeout must be positive")
    require(LAKE.is_file(), "lake executable is absent")

    case = SHARED / "allcollapse_case_artifacts" / "case_0"
    slug = f"component{args.component:02d}"
    spec_path = case / f"{slug}_tree_spec.json"
    manifest_path = case / f"{slug}_tree_manifest.json"
    spec = json.loads(spec_path.read_text())
    manifest = json.loads(manifest_path.read_text())
    require(manifest.get("summary", {}).get("complete") is True,
            "tree manifest is incomplete")
    leaves, coverage = expand(spec_path)
    require(manifest.get("coverage") == coverage, "tree manifest/spec coverage drift")
    leaf_dirs = dict(leaves)
    rows = {row["tag"]: row for row in manifest["leaves"]}
    require(args.tag in leaf_dirs and args.tag in rows, "tag is not a terminal leaf")
    row = rows[args.tag]
    leaf_dir = leaf_dirs[args.tag]
    certificate = leaf_dir / row["certificate_file"]
    system = leaf_dir / "system.json"
    replay = row.get("strict_replay", {})
    require(sha256(certificate) == row["certificate_sha256"],
            "certificate hash differs from tree manifest")
    require(sha256(system) == row["system_file_sha256"],
            "leaf system hash differs from tree manifest")
    require(replay.get("certificate_file_sha256") == sha256(certificate),
            "strict replay/certificate hash drift")
    require(replay.get("system_file_sha256") == sha256(system),
            "strict replay/system hash drift")

    root_path = (SHARED / spec["source_system"]).resolve()
    root, leaf, bridge = source_paths(args.component, args.tag)
    for source in (root, leaf, bridge):
        require(source.is_file(), f"generated Lean source missing: {source}")
    root_text, leaf_text, bridge_text = (
        root.read_text(), leaf.read_text(), bridge.read_text()
    )
    root_hash = sha256(root_path)
    require(root_hash in root_text, "Lean root source does not bind root system SHA")
    require(sha256(system) in leaf_text, "Lean leaf source does not bind leaf system SHA")
    require(sha256(certificate) in leaf_text,
            "Lean leaf source does not bind certificate SHA")
    require(f"Krenn.Component{args.component}.Root" in bridge_text,
            "Lean bridge does not name the shared root")
    require(f"Krenn.Component{args.component}.SelectedLeaf{suffix(args.tag)}" in bridge_text,
            "Lean bridge does not name the selected leaf")

    result: dict[str, object] = {
        "format": "krenn-selected-leaf-serial-build-v1",
        "scope": {
            "component": args.component,
            "terminal_tag": args.tag,
            "claim": "only one selected leaf plus its shared-root bridge",
        },
        "tree_spec_sha256": sha256(spec_path),
        "tree_manifest_sha256": sha256(manifest_path),
        "root_system_file_sha256": root_hash,
        "leaf_system_file_sha256": sha256(system),
        "certificate_sha256": sha256(certificate),
        "strict_replay": {
            "basis": replay.get("basis"),
            "equations": replay.get("equations"),
            "selected_equations": len(replay.get("nonzero_multiplier_indices_1based", [])),
            "max_multiplier_degree": replay.get("max_multiplier_degree"),
        },
        "generated_sources": [
            {"path": str(source.relative_to(LEAN_ROOT)), "sha256": sha256(source)}
            for source in (root, leaf, bridge)
        ],
        "mode": "source-audit-only",
    }
    if args.build:
        checks = [build_source(source, args.timeout_seconds) for source in (root, leaf, bridge)]
        bridge_output = str(checks[-1]["lean_output"])
        require("depends on axioms:" in bridge_output,
                "bridge did not emit its axiom audit")
        require("native_decide" not in bridge_output,
                "bridge axiom audit contains native_decide")
        result["mode"] = "fresh-serial-kernel-check"
        result["module_checks"] = checks
        result["total_elapsed_seconds"] = round(
            sum(float(check["elapsed_seconds"]) for check in checks), 3
        )
        result["axiom_audit"] = bridge_output

    encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.receipt is not None:
        receipt = args.receipt.resolve()
        receipt.parent.mkdir(parents=True, exist_ok=True)
        receipt.write_text(encoded)
        print(f"wrote {receipt}")
    print(encoded, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
