#!/usr/bin/env python3
"""Validate the pinned SWI/PeTTa provenance manifest.

With --swi-tree and --petta-tree this also verifies the pinned Git commits and
the SHA-256 digest of every referenced source file.  Without source trees it
still fails closed on schema, identifiers, source coverage, and digest shape.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path


REQUIRED_COMPONENTS = {
    "runtime.term-graph",
    "runtime.unification",
    "runtime.query",
    "runtime.vm",
    "runtime.compiler",
    "runtime.clause-selection",
    "runtime.dynamic-database",
    "runtime.term-copy",
    "runtime.reader",
    "runtime.source-loader",
    "library.clpfd",
    "petta.compiler",
    "petta.runtime",
    "petta.reader",
}
IMPLEMENTATION_STATUSES = {"reference-only", "pinned-source", "adapted"}
PROOF_STATUSES = {"not-started", "partial", "proved"}
CONFORMANCE_STATUSES = {"not-measured", "partial", "matched", "divergent"}
HEX40 = re.compile(r"[0-9a-f]{40}\Z")
HEX64 = re.compile(r"[0-9a-f]{64}\Z")


class InvalidManifest(ValueError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise InvalidManifest(message)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def git_head(tree: Path) -> str:
    result = subprocess.run(
        ["git", "-C", str(tree), "rev-parse", "HEAD"],
        check=True,
        text=True,
        capture_output=True,
    )
    return result.stdout.strip()


def validate_xref(manifest: dict, petta_tree: Path, script: Path) -> None:
    result = subprocess.run(
        ["swipl", "-q", "-f", str(script), "--", str(petta_tree)],
        check=True,
        text=True,
        capture_output=True,
    )
    generated = json.loads(result.stdout)
    expected = manifest.get("dependency_inventory", {})
    require(generated.get("generator") == expected.get("generator"),
            "dependency inventory generator changed")
    require(generated.get("completeness") == expected.get("completeness"),
            "dependency inventory completeness claim changed")
    require([row["path"] for row in generated.get("sources", [])]
            == expected.get("source_files"),
            "dependency inventory source set changed")
    summary = generated.get("summary", {})
    require(summary.get("calls") == expected.get("call_sites"),
            f"xref call-site count changed: {summary.get('calls')}")
    require(summary.get("imports") == expected.get("imports"),
            f"xref import count changed: {summary.get('imports')}")
    actual_classes = {
        row["classification"]: row["count"]
        for row in summary.get("classifications", [])
    }
    require(actual_classes == expected.get("classifications"),
            f"xref classifications changed: {actual_classes}")
    unresolved = sorted({
        row["indicator"]
        for row in generated.get("calls", [])
        if row["classification"] == "external-or-dynamic"
    })
    require(unresolved == expected.get("unresolved_indicators"),
            f"xref unresolved indicators changed: {unresolved}")


def validate(manifest: dict, trees: dict[str, Path]) -> tuple[int, int]:
    require(manifest.get("schema_version") == 2, "schema_version must be 2")
    require(manifest.get("target") == "petta-core-plus-clpfd", "unexpected target")

    projects = manifest.get("projects")
    require(isinstance(projects, dict) and projects, "projects must be a nonempty object")
    for name, project in projects.items():
        require(HEX40.fullmatch(project.get("commit", "")) is not None,
                f"{name}: commit is not a lowercase 40-hex Git object")
        require(project.get("license") in {"BSD-2-Clause", "MIT"},
                f"{name}: unreviewed license")
        if name in trees:
            actual = git_head(trees[name])
            require(actual == project["commit"],
                    f"{name}: HEAD {actual} != pinned {project['commit']}")

    sources = manifest.get("source_files")
    require(isinstance(sources, list) and sources, "source_files must be nonempty")
    source_keys: set[tuple[str, str]] = set()
    source_map: dict[tuple[str, str], dict] = {}
    for source in sources:
        project = source.get("project")
        path_text = source.get("path")
        key = (project, path_text)
        require(project in projects, f"unknown source project: {project}")
        require(isinstance(path_text, str) and path_text and not Path(path_text).is_absolute(),
                f"{key}: source path must be nonempty and relative")
        require(".." not in Path(path_text).parts, f"{key}: source path escapes its tree")
        require(key not in source_keys, f"duplicate source entry: {key}")
        require(HEX64.fullmatch(source.get("sha256", "")) is not None,
                f"{key}: malformed SHA-256")
        source_keys.add(key)
        source_map[key] = source
        if project in trees:
            path = trees[project] / path_text
            require(path.is_file(), f"{key}: missing pinned source file")
            actual = sha256(path)
            require(actual == source["sha256"],
                    f"{key}: SHA-256 {actual} != pinned {source['sha256']}")

    components = manifest.get("semantic_components")
    require(isinstance(components, list) and components,
            "semantic_components must be nonempty")
    identifiers: set[str] = set()
    repository_root = Path(__file__).resolve().parents[1]
    for component in components:
        identifier = component.get("id")
        project = component.get("project")
        require(isinstance(identifier, str) and identifier, "component id must be nonempty")
        require(identifier not in identifiers, f"duplicate component id: {identifier}")
        require(project in projects, f"{identifier}: unknown project {project}")
        require("status" not in component,
                f"{identifier}: ambiguous legacy status field is forbidden")
        require(component.get("implementation_status") in IMPLEMENTATION_STATUSES,
                f"{identifier}: invalid implementation status "
                f"{component.get('implementation_status')}")
        require(component.get("proof_status") in PROOF_STATUSES,
                f"{identifier}: invalid proof status {component.get('proof_status')}")
        require(component.get("swi_conformance_status") in CONFORMANCE_STATUSES,
                f"{identifier}: invalid SWI conformance status "
                f"{component.get('swi_conformance_status')}")
        for field in (
            "implementation_evidence", "proof_evidence", "swi_conformance_evidence"
        ):
            evidence = component.get(field, [])
            require(isinstance(evidence, list)
                    and all(isinstance(path, str) and path for path in evidence),
                    f"{identifier}: {field} must be a list of nonempty paths")
            for path_text in evidence:
                evidence_path = Path(path_text)
                require(not evidence_path.is_absolute() and ".." not in evidence_path.parts,
                        f"{identifier}: {field} path must stay repository-relative")
                require((repository_root / evidence_path).is_file(),
                        f"{identifier}: missing {field} file {path_text}")
        if component["implementation_status"] == "adapted":
            require(component.get("implementation_evidence"),
                    f"{identifier}: adapted implementation lacks evidence")
        if component["proof_status"] != "not-started":
            require(component.get("proof_evidence"),
                    f"{identifier}: nonempty proof status lacks evidence")
        if component["swi_conformance_status"] != "not-measured":
            require(component.get("swi_conformance_evidence"),
                    f"{identifier}: measured conformance lacks evidence")
        anchors = component.get("anchors")
        require(isinstance(anchors, list) and all(isinstance(a, str) and a for a in anchors),
                f"{identifier}: anchors must be nonempty strings")
        component_sources = component.get("sources")
        require(isinstance(component_sources, list) and component_sources,
                f"{identifier}: sources must be nonempty")
        for path_text in component_sources:
            require((project, path_text) in source_map,
                    f"{identifier}: source {project}:{path_text} is not hash-pinned")
        if project in trees:
            source_text = "\n".join(
                (trees[project] / path_text).read_text(encoding="utf-8", errors="replace")
                for path_text in component_sources
            )
            for anchor in anchors:
                require(anchor in source_text,
                        f"{identifier}: anchor {anchor!r} absent from pinned sources")
        identifiers.add(identifier)

    missing = REQUIRED_COMPONENTS - identifiers
    require(not missing, f"missing required semantic components: {sorted(missing)}")

    policy = manifest.get("policy", {})
    require(policy.get("canonical_runtime") == "one Lean executable microstep machine",
            "canonical runtime policy changed")
    require(policy.get("unsupported_behavior") == "structured-error",
            "unsupported behavior must fail visibly")
    effects = policy.get("external_effects")
    require(isinstance(effects, list) and len(effects) == len(set(effects)),
            "external effects must be an explicit duplicate-free list")

    return len(sources), len(components)


def main() -> int:
    parser = argparse.ArgumentParser()
    default_manifest = (
        Path(__file__).resolve().parents[1]
        / "Mettapedia/Logic/Prolog/SWI/SWI_PROVENANCE.json"
    )
    parser.add_argument("--manifest", type=Path, default=default_manifest)
    parser.add_argument("--swi-tree", type=Path)
    parser.add_argument("--petta-tree", type=Path)
    parser.add_argument("--check-xref", action="store_true")
    args = parser.parse_args()

    trees = {}
    if args.swi_tree is not None:
        trees["swi-prolog"] = args.swi_tree.resolve()
    if args.petta_tree is not None:
        trees["petta"] = args.petta_tree.resolve()

    try:
        with args.manifest.open(encoding="utf-8") as stream:
            manifest = json.load(stream)
        source_count, component_count = validate(manifest, trees)
        if args.check_xref:
            require(args.petta_tree is not None, "--check-xref requires --petta-tree")
            validate_xref(
                manifest,
                args.petta_tree.resolve(),
                Path(__file__).resolve().with_name("petta_swi_inventory.pl"),
            )
    except (InvalidManifest, OSError, json.JSONDecodeError, subprocess.CalledProcessError) as error:
        print(f"SWI provenance check failed: {error}", file=sys.stderr)
        return 1

    checked_items = sorted(trees)
    if args.check_xref:
        checked_items.append("PeTTa xref")
    checked = ", ".join(checked_items) if checked_items else "manifest structure"
    print(
        f"SWI provenance OK: {source_count} pinned files, "
        f"{component_count} components; checked {checked}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
