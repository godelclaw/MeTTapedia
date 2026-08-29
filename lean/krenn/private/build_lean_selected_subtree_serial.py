#!/usr/bin/env python3
"""Sequentially check one generated Krenn selected-carrier subtree.

The selected-subtree exporter deliberately proves a named subtree rather
than a whole component.  This companion runner preserves that scope and
invokes `lake env lean` one source module at a time: root, leaves, bridges,
then the recursive wrapper.  It never calls `lake build`, whose dependency
scheduler may elaborate many large certificate modules concurrently.

The emitted receipt binds the exact selected leaf list and generated source
hashes.  A successful run means precisely the named subtree checked; it does
not assert that the surrounding component or the Krenn theorem is closed.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
import time
from pathlib import Path


HERE = Path(__file__).resolve()
LEAN_ROOT = HERE.parents[1]
LAKE = Path.home() / ".elan" / "bin" / "lake"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def suffix(tag: str) -> str:
    return tag.upper().replace(".", "_")


def subtree_suffix(tag: str) -> str:
    return "ROOT" if not tag else suffix(tag)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def lean_source(component: int, kind: str, tag: str | None = None) -> Path:
    stem = kind if tag is None else kind + suffix(tag)
    return LEAN_ROOT / f"KrennComponent{component}" / f"{stem}.lean"


def olean_path(component: int, kind: str, tag: str | None = None) -> Path:
    stem = kind if tag is None else kind + suffix(tag)
    return LEAN_ROOT / ".lake" / "build" / "lib" / "lean" / (
        f"KrennComponent{component}") / f"{stem}.olean"


def subtree_source(component: int, prefix: str) -> Path:
    return LEAN_ROOT / f"KrennComponent{component}" / (
        f"SelectedSubtree{subtree_suffix(prefix)}.lean"
    )


def run_module(component: int, source: Path, timeout_seconds: int) -> dict[str, object]:
    relative_source = source.relative_to(LEAN_ROOT)
    output = LEAN_ROOT / ".lake" / "build" / "lib" / "lean" / relative_source
    output = output.with_suffix(".olean")
    ilean = output.with_suffix(".ilean")
    output.parent.mkdir(parents=True, exist_ok=True)
    environment = os.environ.copy()
    environment["LEAN_NUM_THREADS"] = "1"
    command = [str(LAKE), "env", "lean", str(relative_source), "-o", str(output),
               "-i", str(ilean)]
    started = time.monotonic()
    completed = subprocess.run(
        command, cwd=LEAN_ROOT, env=environment, text=True,
        capture_output=True, timeout=timeout_seconds,
    )
    elapsed = time.monotonic() - started
    if completed.returncode != 0:
        detail = (completed.stdout + completed.stderr)[-8000:]
        raise RuntimeError(
            f"Lean failed for {relative_source} (exit {completed.returncode}):\n{detail}"
        )
    require(output.is_file(), f"Lean did not produce {output}")
    return {
        "source": str(relative_source),
        "source_sha256": sha256(source),
        "olean": str(output.relative_to(LEAN_ROOT)),
        "olean_sha256": sha256(output),
        "elapsed_seconds": round(elapsed, 3),
    }


def source_record(source: Path) -> dict[str, str]:
    require(source.is_file(), f"missing generated Lean source: {source}")
    return {
        "source": str(source.relative_to(LEAN_ROOT)),
        "source_sha256": sha256(source),
    }


def atomic_json_write(path: Path, payload: dict[str, object]) -> None:
    """Write a resumable build checkpoint without leaving a partial JSON file."""
    path.parent.mkdir(parents=True, exist_ok=True)
    encoded = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    with tempfile.NamedTemporaryFile(
        mode="w", encoding="utf-8", dir=path.parent, prefix=path.name + ".",
        suffix=".tmp", delete=False,
    ) as handle:
        handle.write(encoded)
        temporary = Path(handle.name)
    temporary.replace(path)


def validated_checkpoint(
    path: Path, manifest_sha256: str, sources: list[dict[str, str]],
) -> list[dict[str, object]]:
    """Return only prior module checks whose complete provenance still matches.

    An existing checkpoint with a different manifest or generated source is a
    hard error, rather than an invitation to mix incomparable proof runs.
    Likewise, a missing or changed `.olean` is rebuilt instead of trusted.
    """
    if not path.exists():
        return []
    payload = json.loads(path.read_text())
    if payload.get("format") != "krenn-selected-subtree-build-checkpoint-v1":
        raise RuntimeError("checkpoint format drift")
    if payload.get("manifest_sha256") != manifest_sha256:
        raise RuntimeError("checkpoint/manifest hash mismatch")
    if payload.get("source_records") != sources:
        raise RuntimeError("checkpoint/generated-source provenance mismatch")
    source_paths = {record["source"] for record in sources}
    checks = payload.get("module_checks")
    if not isinstance(checks, list):
        raise RuntimeError("checkpoint module checks malformed")
    accepted: list[dict[str, object]] = []
    seen: set[str] = set()
    for check in checks:
        if not isinstance(check, dict):
            raise RuntimeError("checkpoint module check is not an object")
        source = check.get("source")
        olean = check.get("olean")
        source_sha256 = check.get("source_sha256")
        olean_sha256 = check.get("olean_sha256")
        if not all(isinstance(item, str)
                   for item in (source, olean, source_sha256, olean_sha256)):
            raise RuntimeError("checkpoint module check fields malformed")
        if source not in source_paths or source in seen:
            raise RuntimeError("checkpoint module source coverage malformed")
        seen.add(source)
        current_source = LEAN_ROOT / source
        current_olean = LEAN_ROOT / olean
        if sha256(current_source) != source_sha256:
            raise RuntimeError(f"checkpoint source hash drift: {source}")
        # An `.olean` can be absent after cache cleanup; rebuild that one
        # module, but never accept a different object as an old check.
        if current_olean.is_file() and sha256(current_olean) == olean_sha256:
            accepted.append(check)
    return accepted


def write_checkpoint(
    path: Path, manifest_sha256: str, sources: list[dict[str, str]],
    checks: list[dict[str, object]], complete: bool,
) -> None:
    atomic_json_write(path, {
        "format": "krenn-selected-subtree-build-checkpoint-v1",
        "manifest_sha256": manifest_sha256,
        "source_records": sources,
        "module_checks": checks,
        "complete": complete,
    })


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("component", type=int)
    parser.add_argument(
        "prefix",
        help="selected nonterminal chart prefix, e.g. b6.2; use root for the whole tree",
    )
    parser.add_argument("--manifest", type=Path, required=True,
                        help="selected-subtree exporter receipt")
    parser.add_argument("--build", action="store_true",
                        help="perform fresh sequential kernel checks")
    parser.add_argument("--timeout-seconds", type=int, default=120)
    parser.add_argument("--receipt", type=Path)
    parser.add_argument(
        "--checkpoint", type=Path,
        help="optional fail-closed resumable receipt, updated after every module",
    )
    args = parser.parse_args()
    require(args.timeout_seconds > 0, "timeout must be positive")
    require(LAKE.is_file(), f"lake executable is absent: {LAKE}")
    prefix = "" if args.prefix == "root" else args.prefix

    manifest_path = args.manifest.resolve()
    manifest = json.loads(manifest_path.read_text())
    require(manifest.get("format") == "krenn-selected-subtree-export-v1",
            "selected-subtree manifest format drift")
    require(manifest.get("component") == args.component,
            "component/manifest mismatch")
    require(manifest.get("prefix") == prefix, "prefix/manifest mismatch")
    tags = manifest.get("terminal_leaves")
    require(isinstance(tags, list) and tags and all(isinstance(tag, str) for tag in tags),
            "manifest terminal leaves malformed")
    require(len(set(tags)) == len(tags), "manifest repeats a terminal leaf")
    wrapper = subtree_source(args.component, prefix)
    require(str(wrapper) == manifest.get("wrapper"), "wrapper path drift")
    require(sha256(wrapper) == manifest.get("wrapper_sha256"), "wrapper hash drift")

    root = lean_source(args.component, "Root")
    leaves = [lean_source(args.component, "SelectedLeaf", tag) for tag in tags]
    bridges = [lean_source(args.component, "SelectedBridge", tag) for tag in tags]
    sources = [root, *leaves, *bridges, wrapper]
    for source in sources:
        source_record(source)

    records = [source_record(source) for source in sources]
    result: dict[str, object] = {
        "format": "krenn-selected-subtree-serial-build-v1",
        "scope": {
            "component": args.component,
            "prefix": "root" if not prefix else prefix,
            "terminal_leaf_count": len(tags),
            "claim": "only the named selected subtree",
        },
        "selected_subtree_manifest": str(manifest_path),
        "selected_subtree_manifest_sha256": sha256(manifest_path),
        "tree_manifest_sha256": manifest.get("manifest_sha256"),
        "tree_spec_sha256": manifest.get("spec_sha256"),
        "root_system_file_sha256": manifest.get("root_system_file_sha256"),
        "terminal_leaves": tags,
        "source_records": records,
        "mode": "source-audit-only",
    }
    if args.build:
        checkpoint = args.checkpoint.resolve() if args.checkpoint is not None else None
        manifest_sha256 = sha256(manifest_path)
        checked = (validated_checkpoint(checkpoint, manifest_sha256, records)
                   if checkpoint is not None else [])
        reused_count = len(checked)
        fresh_checks: list[dict[str, object]] = []
        checked_sources = {str(row["source"]) for row in checked}
        if checkpoint is not None:
            write_checkpoint(checkpoint, manifest_sha256, records, checked, False)
        for source in sources:
            relative_source = str(source.relative_to(LEAN_ROOT))
            if relative_source in checked_sources:
                print(f"reusing {relative_source}", flush=True)
                continue
            print(f"checking {source.relative_to(LEAN_ROOT)}", flush=True)
            fresh = run_module(args.component, source, args.timeout_seconds)
            checked.append(fresh)
            fresh_checks.append(fresh)
            if checkpoint is not None:
                write_checkpoint(checkpoint, manifest_sha256, records, checked, False)
        if checkpoint is not None:
            write_checkpoint(checkpoint, manifest_sha256, records, checked, True)
        result["mode"] = "fresh-sequential-kernel-check"
        result["module_checks"] = checked
        result["reused_module_count"] = reused_count
        result["fresh_module_count"] = len(fresh_checks)
        result["fresh_elapsed_seconds"] = round(
            sum(float(row["elapsed_seconds"]) for row in fresh_checks), 3
        )
        result["complete_check_elapsed_seconds"] = round(
            sum(float(row["elapsed_seconds"]) for row in checked), 3
        )
        if checkpoint is not None:
            result["checkpoint"] = str(checkpoint)
            result["checkpoint_complete"] = True

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
