#!/usr/bin/env python3
"""Fail-closed preflight for one frozen all-collapse component import.

This is a generic successor to the component-60 scale preflight.  It checks
that an external one-based minimal-prime component, its zero-based connector
row, its raw-to-reduced normalization, its carrier-tree root, and its complete
strict-tree manifest all describe the same frozen object.  It is deliberately
an input-contract audit: Lean still checks the generated semantic bridge.
"""

from __future__ import annotations

import os
import argparse
import hashlib
import json
import sys
from pathlib import Path

import sympy as sp


SHARED_KRENN = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
if str(SHARED_KRENN) not in sys.path:
    sys.path.insert(0, str(SHARED_KRENN))

from certify_carrier_tree import expand
from export_component46_root_bridge import parse_component_with_composed_substitutions
from freeze_collapse_components import parse_components
from replay_collapse_component_cover import derive_reduced_system
from strict_certificate_checker import symbols_for


CASE = SHARED_KRENN / "allcollapse_case_artifacts" / "case_0"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical_poly(expression: sp.Expr, variables: list[sp.Symbol]):
    return tuple(sorted(
        (tuple(exponents), int(coefficient))
        for exponents, coefficient in
        sp.Poly(expression, *variables, domain=sp.ZZ).terms()
    ))


def canonical_json_terms(terms: list[dict]):
    return tuple(sorted(
        (tuple(term["exponents"]), int(term["coefficient"]))
        for term in terms
    ))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("component", type=int, help="external one-based component index")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    component = args.component
    row = component - 1
    require(component >= 1, "component index must be positive")

    base = json.loads((CASE / "system.json").read_text())
    full_names = base["variables"]
    full_symbols = symbols_for(full_names)
    reduced_symbols, determinants, _, collapse_substitutions = derive_reduced_system()
    raw_symbols = sorted(
        {symbol for determinant in determinants for symbol in determinant.free_symbols},
        key=sp.default_sort_key,
    )
    components = parse_components(
        CASE / "minass.stdout", dict(zip(full_names, full_symbols, strict=True))
    )
    require(len(components) == 67, "minimal-prime component count drift")
    require(row < len(components), "component index exceeds frozen component count")

    connector_path = CASE / "lean_connector_v2" / "connector_certificate.json"
    connector = json.loads(connector_path.read_text())
    require(len(connector.get("components", [])) == len(components),
            "connector/component count drift")
    raw = components[row]
    residual, substitutions, _composed, pivots = (
        parse_component_with_composed_substitutions(raw)
    )

    root_path = CASE / "components_reduced_v2" / f"component_{component:02d}" / "system.json"
    require(root_path.is_file(), "reduced component root is absent")
    root = json.loads(root_path.read_text())
    freeze_path = root_path.with_name("freeze_manifest.json")
    freeze = json.loads(freeze_path.read_text())
    spec_path = CASE / f"component{component:02d}_tree_spec.json"
    manifest_path = CASE / f"component{component:02d}_tree_manifest.json"
    spec = json.loads(spec_path.read_text())
    manifest = json.loads(manifest_path.read_text())

    selected = connector["components"][row]
    generator_ids = {
        canonical_json_terms(generator): index
        for index, generator in enumerate(connector["generators"])
    }
    normalized: list[int | None] = []
    for generator in raw:
        reduced = sp.expand(generator.xreplace(collapse_substitutions))
        if reduced == 0:
            normalized.append(None)
        else:
            key = canonical_poly(reduced, reduced_symbols)
            require(key in generator_ids,
                    "normalized raw generator missing from connector")
            normalized.append(generator_ids[key])
    require([index for index in normalized if index is not None] == selected,
            "raw component does not normalize to its connector row")

    root_indices = [full_names.index(name) for name in root["variables"]]
    eliminated = sorted(set(range(len(full_names))) - set(root_indices))
    pivot_names = [str(variable) for variable, _ in substitutions]
    require(len(full_names) == 75 and len(raw_symbols) == 30,
            "frozen case-0 vocabulary drift")
    require(sorted(full_names.index(name) for name in pivot_names) == eliminated,
            "linear elimination does not match root vocabulary")

    root_hash = sha256(root_path)
    require(freeze.get("component_index") == component,
            "freeze manifest component label drift")
    require(freeze.get("system_file_sha256") == root_hash,
            "freeze manifest root hash drift")
    source = (SHARED_KRENN / spec["source_system"]).resolve()
    require(source == root_path.resolve(), "tree spec root source path drift")
    coverage = manifest.get("coverage")
    require(isinstance(coverage, dict), "tree manifest coverage is absent")
    require(coverage.get("source_system_file_sha256") == root_hash,
            "tree manifest root hash drift")
    require(manifest.get("summary", {}).get("complete") is True,
            "tree manifest is incomplete")
    leaves, derived_coverage = expand(spec_path)
    require(coverage == derived_coverage, "tree manifest/spec coverage drift")
    manifest_rows = manifest.get("leaves")
    require(isinstance(manifest_rows, list), "tree manifest leaves are absent")
    leaf_tags = [tag for tag, _directory in leaves]
    require({entry.get("tag") for entry in manifest_rows} == set(leaf_tags),
            "tree manifest terminal-leaf inventory drift")
    require(manifest["summary"].get("selected_leaf_count") == len(leaf_tags),
            "tree manifest selected leaf count drift")
    require(manifest["summary"].get("strict_exact_identities") == len(leaf_tags),
            "tree manifest strict identity count drift")

    payload = {
        "format": "krenn-component-lean-import-preflight-v2",
        "component_1based": component,
        "connector_row_0based": row,
        "raw_generators": len(raw),
        "normalized_connector_generators": selected,
        "linear_substitution_count": len(substitutions),
        "residual_generator_count": len(residual),
        "eliminated_full_coordinates": eliminated,
        "pivot_sources": [pivots[variable] for variable, _ in substitutions],
        "root_variables": len(root["variables"]),
        "root_equations": len(root["equations"]),
        "root_system_file_sha256": root_hash,
        "freeze_manifest_sha256": sha256(freeze_path),
        "tree_spec_sha256": sha256(spec_path),
        "tree_manifest_sha256": sha256(manifest_path),
        "strict_leaf_count": len(leaf_tags),
        "checks": {
            "external_component_to_connector_row": True,
            "raw_normalization_matches_connector_row": True,
            "linear_elimination_matches_root_vocabulary": True,
            "freeze_and_tree_bind_exact_root_file": True,
            "tree_manifest_is_complete": True,
        },
    }
    output = (args.output.resolve() if args.output is not None else
              Path(__file__).with_name(f"component{component:02d}_import_preflight.json"))
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps(payload, sort_keys=True))


if __name__ == "__main__":
    main()
