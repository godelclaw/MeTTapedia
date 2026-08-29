#!/usr/bin/env python3
"""Fail-closed preflight for the component-60 Lean scaling specimen.

This checks the external one-based component number, its zero-based connector
row, raw-to-reduced normalization, exact linear elimination, frozen root
hashes, and carrier-tree source binding before a semantic connector is
generated.  It does not replace the Lean proofs; it makes their input
contract explicit and reproducible.
"""

from __future__ import annotations

import os
import hashlib
import json
import sys
from pathlib import Path

import sympy as sp

SHARED_KRENN = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
if str(SHARED_KRENN) not in sys.path:
    sys.path.insert(0, str(SHARED_KRENN))

from export_component46_root_bridge import parse_component_with_composed_substitutions
from freeze_collapse_components import parse_components
from replay_collapse_component_cover import derive_reduced_system
from strict_certificate_checker import symbols_for


CASE = SHARED_KRENN / "allcollapse_case_artifacts" / "case_0"
COMPONENT_1BASED = 60
ROW_0BASED = COMPONENT_1BASED - 1


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical_poly(expression: sp.Expr, variables: list[sp.Symbol]):
    return tuple(sorted((tuple(exponents), int(coefficient))
                        for exponents, coefficient in
                        sp.Poly(expression, *variables, domain=sp.ZZ).terms()))


def canonical_json_terms(terms: list[dict]):
    return tuple(sorted((tuple(term["exponents"]), int(term["coefficient"]))
                        for term in terms))


def main() -> int:
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
    raw = components[ROW_0BASED]
    residual, substitutions, _composed, pivots = (
        parse_component_with_composed_substitutions(raw)
    )
    root_path = CASE / "components_reduced_v2" / "component_60" / "system.json"
    root = json.loads(root_path.read_text())
    freeze = json.loads(root_path.with_name("freeze_manifest.json").read_text())
    tree_spec = json.loads((CASE / "component60_tree_spec.json").read_text())
    tree_manifest = json.loads((CASE / "component60_tree_manifest.json").read_text())
    connector = json.loads((CASE / "lean_connector_v2" / "connector_certificate.json").read_text())

    if len(components) != 67:
        raise RuntimeError("minimal-prime component count drift")
    if ROW_0BASED != 59 or connector["components"][ROW_0BASED] == connector["components"][60]:
        raise RuntimeError("one-based/zero-based component gate drift")
    selected = connector["components"][ROW_0BASED]
    generator_ids = {
        canonical_json_terms(generator): index
        for index, generator in enumerate(connector["generators"])
    }
    normalized = []
    for generator in raw:
        reduced = sp.expand(generator.xreplace(collapse_substitutions))
        if reduced == 0:
            normalized.append(None)
        else:
            key = canonical_poly(reduced, reduced_symbols)
            if key not in generator_ids:
                raise RuntimeError("normalized raw generator missing from connector")
            normalized.append(generator_ids[key])
    if [index for index in normalized if index is not None] != selected:
        raise RuntimeError("raw component does not normalize to Lean row 59")

    root_indices = [full_names.index(name) for name in root["variables"]]
    eliminated = sorted(set(range(len(full_names))) - set(root_indices))
    pivot_names = [str(variable) for variable, _ in substitutions]
    if len(full_names) != 75 or len(raw_symbols) != 30:
        raise RuntimeError("frozen vocabulary drift")
    if len(raw) != 19 or len(substitutions) != 14 or len(residual) != 5:
        raise RuntimeError("component-60 elimination shape drift")
    if len(root["variables"]) != 61 or len(root["equations"]) != 656:
        raise RuntimeError("component-60 root shape drift")
    if sorted(full_names.index(name) for name in pivot_names) != eliminated:
        raise RuntimeError("linear elimination does not match root vocabulary")

    root_hash = sha256(root_path)
    if freeze["component_index"] != COMPONENT_1BASED:
        raise RuntimeError("freeze manifest component label drift")
    if freeze["system_file_sha256"] != root_hash:
        raise RuntimeError("freeze manifest root hash drift")
    if tree_spec["source_system"] != (
        "allcollapse_case_artifacts/case_0/components_reduced_v2/component_60/system.json"
    ):
        raise RuntimeError("tree spec root source path drift")
    coverage = tree_manifest["coverage"]
    if coverage["source_system_file_sha256"] != root_hash:
        raise RuntimeError("tree manifest root hash drift")
    if tree_manifest["summary"] != {
        "complete": True,
        "selected_leaf_count": 386,
        "strict_exact_identities": 386,
    }:
        raise RuntimeError("tree completeness summary drift")

    payload = {
        "format": "krenn-component60-lean-import-preflight-v1",
        "component_1based": COMPONENT_1BASED,
        "connector_row_0based": ROW_0BASED,
        "raw_generators": len(raw),
        "normalized_connector_generators": selected,
        "linear_substitution_count": len(substitutions),
        "residual_generator_count": len(residual),
        "eliminated_full_coordinates": eliminated,
        "pivot_sources": [pivots[variable] for variable, _ in substitutions],
        "root_variables": len(root["variables"]),
        "root_equations": len(root["equations"]),
        "root_system_file_sha256": root_hash,
        "freeze_manifest_sha256": sha256(root_path.with_name("freeze_manifest.json")),
        "tree_spec_sha256": sha256(CASE / "component60_tree_spec.json"),
        "tree_manifest_sha256": sha256(CASE / "component60_tree_manifest.json"),
        "strict_leaf_count": 386,
        "checks": {
            "external_component_to_connector_row": True,
            "raw_normalization_matches_connector_row": True,
            "linear_elimination_matches_root_vocabulary": True,
            "freeze_and_tree_bind_exact_root_file": True,
            "tree_manifest_is_complete": True,
        },
    }
    output = Path(__file__).with_name("component60_import_preflight.json")
    output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps(payload, sort_keys=True))


if __name__ == "__main__":
    main()
