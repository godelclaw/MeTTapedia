#!/usr/bin/env python3
"""Fail-closed audit for promoting generated Krenn components into an aggregate.

The audit resolves artifacts in the current checkout.  Absolute paths recorded
by an originating worktree are provenance text, not authority.  Content hashes,
component indices, build receipts, and the current aggregate source are the
authority checked here.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import tempfile
from pathlib import Path


HERE = Path(__file__).resolve()
LEAN_ROOT = HERE.parents[1]
PRIVATE = LEAN_ROOT / "private"

REQUIRED_RECEIPTS = (
    "fulltree_manifest",
    "fulltree_serial_audit",
    "import_preflight",
    "normalization_export",
    "root_bridge_export",
    "root_chunks_export",
    "root_connector_serial_audit",
    "table_entry_export",
    "tree_adapter_manifest",
)
FORBIDDEN = re.compile(r"\b(?:sorry|admit|native_decide)\b|^\s*axiom\b", re.MULTILINE)
EXPECTED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path: Path) -> dict[str, object]:
    require(path.is_file(), f"missing artifact: {path.relative_to(LEAN_ROOT)}")
    payload = json.loads(path.read_text())
    require(isinstance(payload, dict), f"JSON object required: {path.name}")
    return payload


def local_source(recorded: str) -> Path:
    """Resolve a receipt's source in this checkout, ignoring old worktree roots."""
    path = Path(recorded)
    if path.is_absolute():
        path = Path(path.name)
    candidate = LEAN_ROOT / path
    require(candidate.is_file(), f"missing recorded source: {path}")
    return candidate


def local_olean(recorded: str) -> Path:
    path = Path(recorded)
    if path.is_absolute():
        marker = ".lake/build/lib/lean"
        text = path.as_posix()
        require(marker in text, f"unrecognized recorded OLean path: {recorded}")
        path = Path(marker + text.split(marker, 1)[1])
    candidate = LEAN_ROOT / path
    require(candidate.is_file(), f"missing recorded OLean: {path}")
    return candidate


def audit_build(component: int, name: str, expected_format: str) -> tuple[dict[str, object], int]:
    path = PRIVATE / f"component{component}_{name}.json"
    payload = read_json(path)
    require(payload.get("format") == expected_format, f"c{component} {name}: format drift")
    require(payload.get("checkpoint_complete") is True, f"c{component} {name}: incomplete")
    require(payload.get("reused_module_count") == 0, f"c{component} {name}: reused modules")
    checks = payload.get("module_checks")
    records = payload.get("source_records")
    require(isinstance(checks, list) and isinstance(records, list),
            f"c{component} {name}: malformed module records")
    require(payload.get("fresh_module_count") == len(checks),
            f"c{component} {name}: fresh count mismatch")

    checked_sources: set[str] = set()
    for row in checks:
        require(isinstance(row, dict), f"c{component} {name}: malformed module check")
        source = row.get("source")
        olean = row.get("olean")
        require(isinstance(source, str) and isinstance(olean, str),
                f"c{component} {name}: path fields malformed")
        source_path = local_source(source)
        olean_path = local_olean(olean)
        require(sha256(source_path) == row.get("source_sha256"),
                f"c{component} {name}: source hash drift: {source}")
        require(sha256(olean_path) == row.get("olean_sha256"),
                f"c{component} {name}: OLean hash drift: {olean}")
        require(source not in checked_sources, f"c{component} {name}: duplicate source check")
        checked_sources.add(source)

    recorded_sources: set[str] = set()
    for row in records:
        require(isinstance(row, dict) and isinstance(row.get("source"), str),
                f"c{component} {name}: malformed source record")
        source = str(row["source"])
        path = local_source(source)
        require(sha256(path) == row.get("source_sha256"),
                f"c{component} {name}: source-record hash drift: {source}")
        recorded_sources.add(source)
    require(checked_sources == recorded_sources,
            f"c{component} {name}: checked/source-record coverage mismatch")
    return payload, len(checks)


def component_sources(component: int) -> list[Path]:
    directory = LEAN_ROOT / f"KrennComponent{component}"
    require(directory.is_dir(), f"c{component}: selected-tree source directory missing")
    sources = sorted(directory.rglob("*.lean"))
    sources.extend(sorted(LEAN_ROOT.glob(f"KrennComponent{component}*.lean")))
    require(sources, f"c{component}: no Lean sources")
    return sources


def audit_component(component: int) -> dict[str, object]:
    for stem in REQUIRED_RECEIPTS:
        require((PRIVATE / f"component{component}_{stem}.json").is_file(),
                f"c{component}: missing {stem} receipt")

    preflight = read_json(PRIVATE / f"component{component}_import_preflight.json")
    require(preflight.get("format") == "krenn-component-lean-import-preflight-v2",
            f"c{component}: preflight format drift")
    require(preflight.get("component_1based") == component,
            f"c{component}: preflight component mismatch")
    require(preflight.get("connector_row_0based") == component - 1,
            f"c{component}: preflight table-slot mismatch")
    checks = preflight.get("checks")
    require(isinstance(checks, dict) and checks and all(value is True for value in checks.values()),
            f"c{component}: preflight check failed")

    tree, tree_modules = audit_build(
        component, "fulltree_serial_audit", "krenn-selected-subtree-serial-build-v1")
    connector, connector_modules = audit_build(
        component, "root_connector_serial_audit",
        "krenn-component-root-connector-serial-build-v1")
    require(tree.get("scope", {}).get("component") == component,
            f"c{component}: tree scope mismatch")
    require(connector.get("scope", {}).get("component") == component,
            f"c{component}: connector scope mismatch")

    context = connector.get("context")
    require(isinstance(context, dict), f"c{component}: connector context missing")
    bindings = {
        "adapter_manifest_sha256": "tree_adapter_manifest",
        "normalization_manifest_sha256": "normalization_export",
        "root_bridge_manifest_sha256": "root_bridge_export",
        "root_chunks_manifest_sha256": "root_chunks_export",
        "selected_tree_audit_sha256": "fulltree_serial_audit",
    }
    for field, stem in bindings.items():
        artifact = PRIVATE / f"component{component}_{stem}.json"
        require(context.get(field) == sha256(artifact),
                f"c{component}: connector context drift for {stem}")

    table = read_json(PRIVATE / f"component{component}_table_entry_export.json")
    require(table.get("format") == "krenn-component-table-entry-export-v1",
            f"c{component}: table receipt format drift")
    require(table.get("component") == component and table.get("lean_table_index") == component - 1,
            f"c{component}: table receipt index mismatch")
    table_source = LEAN_ROOT / f"KrennComponent{component}TableEntry.lean"
    require(table.get("output_sha256") == sha256(table_source),
            f"c{component}: table-entry hash drift")
    connector_path = PRIVATE / f"component{component}_root_connector_serial_audit.json"
    require(table.get("root_connector_audit_sha256") == sha256(connector_path),
            f"c{component}: table/connector binding drift")
    root_source = LEAN_ROOT / f"KrennComponent{component}RootCommonZero.lean"
    require(table.get("root_source_sha256") == sha256(root_source),
            f"c{component}: table/root-source binding drift")
    root_olean = local_olean(str(table.get("root_olean")))
    require(table.get("root_olean_sha256") == sha256(root_olean),
            f"c{component}: table/root-OLean binding drift")

    table_text = table_source.read_text()
    require(re.search(
        rf"RefutesSelectedComponent \(R := R\) \({component - 1} : Fin 67\)", table_text),
        f"c{component}: theorem targets wrong table slot")
    sources = component_sources(component)
    forbidden = [str(path.relative_to(LEAN_ROOT)) for path in sources
                 if FORBIDDEN.search(path.read_text(errors="replace"))]
    require(not forbidden, f"c{component}: forbidden proof token in {forbidden}")

    return {
        "component": component,
        "lean_table_index": component - 1,
        "tree_modules_fresh": tree_modules,
        "connector_modules_fresh": connector_modules,
        "lean_source_count": len(sources),
        "table_entry_sha256": sha256(table_source),
        "tree_audit_sha256": sha256(PRIVATE / f"component{component}_fulltree_serial_audit.json"),
        "connector_audit_sha256": sha256(connector_path),
    }


def audit_aggregate(path: Path, components: list[int]) -> dict[str, object]:
    require(path.is_file(), f"aggregate missing: {path}")
    text = path.read_text()
    imports = re.findall(r"^import KrennComponent(\d+)(?:TableEntry|RootCommonZero)$", text, re.MULTILINE)
    prints = re.findall(r"^#print axioms .*\.component(\d+)_refutes_selected$", text, re.MULTILINE)
    require(len(imports) == len(set(imports)), "aggregate repeats a component import")
    require(len(prints) == len(set(prints)), "aggregate repeats an axiom print")
    for component in components:
        require(imports.count(str(component)) == 1, f"aggregate does not import c{component} exactly once")
        require(prints.count(str(component)) == 1, f"aggregate does not print c{component} exactly once")
    return {
        "file": str(path.relative_to(LEAN_ROOT)),
        "sha256": sha256(path),
        "imported_components": sorted(map(int, imports)),
        "axiom_print_components": sorted(map(int, prints)),
    }


def audit_aggregate_axioms(
    path: Path, expected_components: list[int], timeout_seconds: int
) -> dict[str, object]:
    """Compile the aggregate and require the exact accepted axiom footprint.

    Run this script from an uncapped process: this function invokes Lean, whose
    runtime creates threads and must not inherit an exporter memory limit.
    """
    relative = path.relative_to(LEAN_ROOT)
    result = subprocess.run(
        ["lake", "env", "lean", str(relative)],
        cwd=LEAN_ROOT,
        capture_output=True,
        text=True,
        timeout=timeout_seconds,
        check=False,
    )
    require(result.returncode == 0,
            f"aggregate Lean build failed with exit {result.returncode}: "
            f"{result.stderr[-500:]}")
    pattern = re.compile(
        r"'Krenn\.FrozenCase0AllCollapseAssembly\.component(\d+)_refutes_selected' "
        r"depends on axioms: \[([^\]]*)\]",
        re.MULTILINE,
    )
    observed: dict[int, list[str]] = {}
    for component_text, body in pattern.findall(result.stdout + "\n" + result.stderr):
        component = int(component_text)
        require(component not in observed, f"duplicate axiom report for c{component}")
        axioms = sorted(part.strip() for part in body.replace("\n", " ").split(",")
                        if part.strip())
        require(set(axioms) == EXPECTED_AXIOMS,
                f"c{component}: unexpected axiom footprint {axioms}")
        observed[component] = axioms
    require(sorted(observed) == sorted(expected_components),
            "aggregate axiom output does not cover exactly the imported components: "
            f"observed={sorted(observed)} expected={sorted(expected_components)}")
    return {
        "command": ["lake", "env", "lean", str(relative)],
        "component_count": len(observed),
        "components": [
            {"component": component, "axioms": observed[component]}
            for component in sorted(observed)
        ],
        "expected_axioms": sorted(EXPECTED_AXIOMS),
        "stdout_sha256": hashlib.sha256(result.stdout.encode()).hexdigest(),
        "stderr_sha256": hashlib.sha256(result.stderr.encode()).hexdigest(),
    }


def atomic_write(path: Path, payload: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    encoded = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    with tempfile.NamedTemporaryFile(
        mode="w", encoding="utf-8", dir=path.parent, prefix=path.name + ".",
        suffix=".tmp", delete=False,
    ) as handle:
        handle.write(encoded)
        temporary = Path(handle.name)
    temporary.replace(path)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("components", nargs="+", type=int)
    parser.add_argument("--aggregate", type=Path)
    parser.add_argument("--check-aggregate-axioms", action="store_true")
    parser.add_argument("--lean-timeout-seconds", type=int, default=3600)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    require(len(set(args.components)) == len(args.components), "component list contains duplicates")
    require(all(1 <= component <= 67 for component in args.components),
            "component indices must lie in 1..67")

    component_results = [audit_component(component) for component in sorted(args.components)]
    result: dict[str, object] = {
        "format": "krenn-component-promotion-audit-v1",
        "components": component_results,
        "component_count": len(component_results),
        "tree_modules_fresh": sum(int(row["tree_modules_fresh"]) for row in component_results),
        "connector_modules_fresh": sum(int(row["connector_modules_fresh"]) for row in component_results),
        "all_checks_pass": True,
    }
    if args.aggregate is not None:
        aggregate = args.aggregate
        if not aggregate.is_absolute():
            aggregate = LEAN_ROOT / aggregate
        aggregate_result = audit_aggregate(aggregate, sorted(args.components))
        result["aggregate"] = aggregate_result
        if args.check_aggregate_axioms:
            result["aggregate_axiom_audit"] = audit_aggregate_axioms(
                aggregate,
                list(aggregate_result["imported_components"]),
                args.lean_timeout_seconds,
            )
    else:
        require(not args.check_aggregate_axioms,
                "--check-aggregate-axioms requires --aggregate")
    if args.output is not None:
        output = args.output
        if not output.is_absolute():
            output = PRIVATE / output
        atomic_write(output, result)
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
