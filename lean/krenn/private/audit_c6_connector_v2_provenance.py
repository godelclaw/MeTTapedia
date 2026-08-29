#!/usr/bin/env python3
"""Fail-closed provenance audit for the C6 collapse connector v2.

The Boolean support cover selects a zero-based component label.  This audit
binds that label to its actual algebraic content: each of the 67 external
minimal-prime rows is reduced through the recorded collapse substitution and
matched exactly to the corresponding connector-v2 generator-ID row.  It also
binds every row to the frozen component system file by SHA-256.

This is an artifact-level check, not a replacement for the Lean semantic
component-containment theorem.  Its role is to make a component-label swap
fail before an importer could silently attach the wrong carrier tree.
"""

from __future__ import annotations

import os
import copy
import hashlib
import json
import sys
from pathlib import Path

import sympy as sp


SHARED = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
if str(SHARED) not in sys.path:
    sys.path.insert(0, str(SHARED))

from export_component46_root_bridge import parse_component_with_composed_substitutions  # noqa: E402
from freeze_collapse_components import parse_components  # noqa: E402
from replay_collapse_component_cover import derive_reduced_system  # noqa: E402
from strict_certificate_checker import symbols_for  # noqa: E402


CASE = SHARED / "allcollapse_case_artifacts" / "case_0"
CONNECTOR_PATH = CASE / "lean_connector_v2" / "connector_certificate.json"
INVENTORY_PATH = CASE / "components_reduced_v2" / "inventory.json"
MINASS_PATH = CASE / "minass.stdout"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical_poly(expression: sp.Expr, variables: list[sp.Symbol]) -> tuple:
    return tuple(sorted(
        (tuple(exponents), int(coefficient))
        for exponents, coefficient in
        sp.Poly(expression, *variables, domain=sp.ZZ).terms()
    ))


def canonical_json_terms(terms: list[dict]) -> tuple:
    return tuple(sorted(
        (tuple(term["exponents"]), int(term["coefficient"]))
        for term in terms
    ))


def audit_rows(connector: dict, inventory: dict) -> list[dict]:
    """Return the exact 1-based component-to-connector binding or fail."""
    if connector.get("format") != "krenn-c6-collapse-cover-connector-v2":
        raise RuntimeError("connector v2 format drift")
    if inventory.get("format") != "krenn-c6-collapse-minimal-component-inventory-v1":
        raise RuntimeError("component inventory format drift")
    connector_rows = connector.get("components")
    inventory_rows = inventory.get("components")
    if not isinstance(connector_rows, list) or len(connector_rows) != 67:
        raise RuntimeError("connector does not contain 67 component rows")
    if not isinstance(inventory_rows, list) or len(inventory_rows) != 67:
        raise RuntimeError("inventory does not contain 67 component rows")
    if inventory.get("component_count") != 67:
        raise RuntimeError("inventory component count drift")
    if any(not (0 <= row["component_index"] < 67)
           for row in connector.get("strata", [])):
        raise RuntimeError("connector stratum has out-of-range component index")

    base = json.loads((CASE / "system.json").read_text())
    full_names = base["variables"]
    full_symbols = symbols_for(full_names)
    reduced_symbols, _determinants, _relations, collapse_substitutions = (
        derive_reduced_system()
    )
    components = parse_components(MINASS_PATH, dict(zip(
        full_names, full_symbols, strict=True
    )))
    if len(components) != 67:
        raise RuntimeError("minimal-prime source does not contain 67 components")

    generator_ids = {
        canonical_json_terms(generator): index
        for index, generator in enumerate(connector["generators"])
    }
    if len(generator_ids) != len(connector["generators"]):
        raise RuntimeError("connector generator vocabulary has duplicates")

    binding: list[dict] = []
    for zero_based, (raw, row, frozen) in enumerate(
        zip(components, connector_rows, inventory_rows, strict=True)
    ):
        one_based = zero_based + 1
        if frozen.get("component_index") != one_based:
            raise RuntimeError(f"inventory row {zero_based} has wrong component label")
        normalized_ids = []
        for generator in raw:
            reduced = sp.expand(generator.xreplace(collapse_substitutions))
            if reduced == 0:
                continue
            key = canonical_poly(reduced, reduced_symbols)
            if key not in generator_ids:
                raise RuntimeError(
                    f"component {one_based}: normalized generator missing from connector"
                )
            normalized_ids.append(generator_ids[key])
        if normalized_ids != row:
            raise RuntimeError(
                f"component {one_based}: connector row does not match normalized generators"
            )
        system_path = CASE / "components_reduced_v2" / f"component_{one_based:02d}" / "system.json"
        if not system_path.is_file():
            raise RuntimeError(f"component {one_based}: frozen system missing")
        system_hash = sha256(system_path)
        if frozen.get("system_file_sha256") != system_hash:
            raise RuntimeError(f"component {one_based}: frozen system SHA mismatch")
        # This parses the component's linear data too, so a malformed row does
        # not masquerade as a purely syntactic list of generators.
        residual, substitutions, _composed, _pivots = (
            parse_component_with_composed_substitutions(raw)
        )
        binding.append({
            "component_index_1based": one_based,
            "connector_index_0based": zero_based,
            "raw_generator_count": len(raw),
            "connector_generator_ids": normalized_ids,
            "linear_substitution_count": len(substitutions),
            "residual_generator_count": len(residual),
            "frozen_system_file_sha256": system_hash,
            "freeze_manifest_sha256": frozen["freeze_manifest_sha256"],
        })
    return binding


def main() -> int:
    connector = json.loads(CONNECTOR_PATH.read_text())
    inventory = json.loads(INVENTORY_PATH.read_text())
    binding = audit_rows(connector, inventory)

    # Negative control: Boolean labels alone cannot catch this, but the
    # algebra/provenance binding above must reject it at the first swapped row.
    mutant = copy.deepcopy(connector)
    mutant["components"][0], mutant["components"][1] = (
        mutant["components"][1], mutant["components"][0]
    )
    try:
        audit_rows(mutant, inventory)
    except RuntimeError as error:
        mutation_message = str(error)
    else:
        raise RuntimeError("swapped component-row mutation was accepted")
    if not mutation_message.startswith("component 1:"):
        raise RuntimeError("mutation failed at an unexpected audit boundary")

    payload = {
        "format": "krenn-c6-connector-v2-provenance-audit-v1",
        "sources": {
            "connector_certificate_sha256": sha256(CONNECTOR_PATH),
            "inventory_sha256": sha256(INVENTORY_PATH),
            "minimal_primes_sha256": sha256(MINASS_PATH),
            "case0_system_sha256": sha256(CASE / "system.json"),
            "audit_script_sha256": sha256(Path(__file__)),
        },
        "counts": {
            "components": len(binding),
            "connector_generators": len(connector["generators"]),
            "connector_strata": len(connector["strata"]),
            "relations": len(connector["relations"]),
        },
        "checks": {
            "all_raw_components_normalize_to_named_connector_rows": True,
            "all_connector_rows_bind_to_named_frozen_system_sha": True,
            "all_stratum_component_indices_are_in_range": True,
            "swapped_component_row_mutation_rejected": True,
            "mutation_rejection": mutation_message,
        },
        "component_binding": binding,
        "scope": (
            "Artifact provenance only. Lean's separate containment theorem is "
            "the semantic statement that raw collapse valuations satisfy the "
            "selected component generators."
        ),
    }
    target = CASE / "lean_connector_v2" / "connector_provenance_audit_v1.json"
    target.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(
        "CONNECTOR V2 PROVENANCE VERIFIED: 67 normalized component rows; "
        "swapped-label mutation rejected"
    )
    print("manifest_sha256=" + sha256(target))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
