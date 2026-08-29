#!/usr/bin/env python3
"""Fail-closed aggregate audit for the 19 reflected X=5 residual cases."""

from __future__ import annotations

import os
import argparse
import hashlib
import json
import re
from pathlib import Path


HERE = Path(__file__).resolve().parent
LEAN_ROOT = HERE.parent
ARTIFACTS = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts")) / "x5_frontier_artifacts"
RESIDUAL_MANIFEST = ARTIFACTS / "0415_residual_manifest.json"
TREE_CASES = [
    84, 86, 98, 102, 131, 170, 304, 316, 385, 388, 429, 516, 642,
    817, 861, 863, 1033,
]
DIRECT_CASES = [5, 1293]
EXPECTED_CASES = sorted(DIRECT_CASES + TREE_CASES)
EXPECTED_AXIOMS = "[propext, Classical.choice, Quot.sound]"


class AuditError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AuditError(message)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path: Path) -> dict:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as error:
        raise AuditError(f"cannot read {path}: {error}") from error
    require(isinstance(value, dict), f"expected JSON object: {path}")
    return value


def source_dir(case: int) -> Path:
    return ARTIFACTS / f"0415_case{case:03d}"


def module_dir(case: int) -> Path:
    return LEAN_ROOT / f"KrennX5ResidualCase{case}"


def olean_dir(case: int) -> Path:
    return LEAN_ROOT / ".lake/build/lib/lean" / f"KrennX5ResidualCase{case}"


def scan_source(path: Path) -> None:
    text = path.read_text(encoding="utf-8")
    require(not re.search(r"\b(sorry|admit|native_decide)\b", text),
            f"forbidden proof escape in {path}")


def require_built(source: Path, olean: Path) -> None:
    require(olean.is_file(), f"missing OLean: {olean}")
    require(olean.stat().st_mtime >= source.stat().st_mtime,
            f"stale OLean: {olean}")


def require_axiom_log(case: int) -> str:
    path = Path(f"/tmp/krenn-x5-case{case}-bridge-build.log")
    require(path.is_file(), f"missing top-theorem build log for case {case}")
    text = path.read_text(encoding="utf-8")
    needle = (
        f"'Krenn.X5ResidualCase{case}.Bridge.noNormalizedCase' "
        f"depends on axioms: {EXPECTED_AXIOMS}"
    )
    require(needle in text, f"unexpected/missing top axiom line for case {case}")
    require("error:" not in text and "sorryAx" not in text,
            f"case {case} top build log contains an error marker")
    return digest(path)


def audit() -> dict:
    residual = load(RESIDUAL_MANIFEST)
    rows = residual.get("rows")
    require(isinstance(rows, list), "residual manifest rows missing")
    by_case = {int(row["case"]): row for row in rows}
    require(sorted(by_case) == EXPECTED_CASES,
            "reflected cases do not equal the exact frozen residual")

    reflected = []
    generated_sources: list[Path] = []
    for case in DIRECT_CASES:
        directory = module_dir(case)
        certificate_source = directory / "Certificate.lean"
        bridge_source = directory / "Bridge.lean"
        certificate_receipt = load(HERE / f"x5_case{case}_certificate_receipt.json")
        bridge_receipt = load(HERE / f"x5_case{case}_bridge_receipt.json")
        source = source_dir(case) / "system.json"
        certificate = source_dir(case) / "strict_certificate.stdout"
        require(certificate_receipt.get("source_system_file_sha256") == digest(source),
                f"case {case} direct certificate/source drift")
        require(certificate_receipt.get("certificate_file_sha256") == digest(certificate),
                f"case {case} direct certificate hash drift")
        require(bridge_receipt.get("system_file_sha256") == digest(source),
                f"case {case} direct bridge/source drift")
        require(bridge_receipt.get("certificate_file_sha256") == digest(certificate),
                f"case {case} direct bridge/certificate drift")
        require(by_case[case].get("system_file_sha256") == digest(source),
                f"case {case} residual/source drift")
        require_built(certificate_source, olean_dir(case) / "Certificate.olean")
        require_built(bridge_source, olean_dir(case) / "Bridge.olean")
        generated_sources.extend([certificate_source, bridge_source])
        reflected.append({
            "case": case,
            "closure_kind": "strict_parent_identity",
            "source_system_file_sha256": digest(source),
            "certificate_file_sha256": digest(certificate),
            "top_axiom_log_sha256": require_axiom_log(case),
        })

    for case in TREE_CASES:
        directory = module_dir(case)
        receipt = load(HERE / f"x5_case{case}_reflection_receipt.json")
        source = source_dir(case) / "system.json"
        require(receipt.get("format") == "krenn-x5-residual-lean-reflection-v1",
                f"case {case} reflection receipt format drift")
        require(receipt.get("case") == case and receipt.get("leaf_count") == 8,
                f"case {case} reflection receipt count drift")
        require(receipt.get("source_system_file_sha256") == digest(source),
                f"case {case} reflection/source drift")
        require(by_case[case].get("system_file_sha256") == digest(source),
                f"case {case} residual/source drift")
        require(receipt.get("exporter_sha256") == digest(
            HERE / "export_x5_residual_tree_lean.py"
        ), f"case {case} was generated by a different exporter")
        sources = [directory / f"LeafB{branch}.lean" for branch in range(8)]
        sources.extend([directory / "Tree.lean", directory / "Bridge.lean"])
        for source_file in sources:
            require_built(source_file, olean_dir(case) / (source_file.stem + ".olean"))
        generated_sources.extend(sources)
        reflected.append({
            "case": case,
            "closure_kind": "strict_exhaustive_carrier_tree",
            "source_system_file_sha256": digest(source),
            "root_selected_count": receipt["root_selected_count"],
            "tree_spec_sha256": receipt["tree_spec_sha256"],
            "tree_manifest_sha256": receipt["tree_manifest_sha256"],
            "top_axiom_log_sha256": require_axiom_log(case),
        })

    registry = LEAN_ROOT / "KrennX5Residuals.lean"
    generated_sources.append(registry)
    for source in generated_sources:
        require(source.is_file(), f"missing generated source: {source}")
        scan_source(source)
    require(len(generated_sources) == 175,
            "generated source count is not 174 case modules plus registry")
    require_built(registry, LEAN_ROOT / ".lake/build/lib/lean/KrennX5Residuals.olean")

    return {
        "format": "krenn-x5-0415-residual-lean-audit-v1",
        "residual_manifest_sha256": digest(RESIDUAL_MANIFEST),
        "case_count": len(reflected),
        "direct_parent_identities": len(DIRECT_CASES),
        "carrier_trees": len(TREE_CASES),
        "strict_leaf_identities": 8 * len(TREE_CASES),
        "generated_lean_sources": len(generated_sources),
        "zero_forbidden_proof_escapes": True,
        "top_theorem_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "registry_sha256": digest(registry),
        "exporter_sha256": digest(HERE / "export_x5_residual_tree_lean.py"),
        "auditor_sha256": digest(Path(__file__)),
        "reflected": sorted(reflected, key=lambda row: row["case"]),
        "verdict": "all_19_residual_cases_reflected_into_official_lean",
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", type=Path)
    args = parser.parse_args()
    try:
        result = audit()
    except (AuditError, OSError, ValueError, TypeError) as error:
        print(f"FAIL: {error}")
        return 1
    encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.json is not None:
        args.json.write_text(encoded, encoding="utf-8")
        print("manifest_sha256=" + digest(args.json))
    print(json.dumps({
        "case_count": result["case_count"],
        "generated_lean_sources": result["generated_lean_sources"],
        "strict_leaf_identities": result["strict_leaf_identities"],
        "verdict": result["verdict"],
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
