#!/usr/bin/env python3
"""Transport a strict certificate across an explicit variable renaming.

This is a discovery transport, not a trusted shortcut.  The source identity
is strictly replayed first.  Identifier tokens are then renamed
simultaneously, and the resulting certificate must strictly replay against
the target frozen system.  The receipt binds both systems, both certificates,
the exact renaming, and both replay verdicts.
"""

from __future__ import annotations

import os
import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

KRENN_ROOT = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
sys.path.insert(0, str(KRENN_ROOT))

from strict_certificate_checker import (  # noqa: E402
    check_c4,
    load_json_strict,
    validate_variable_names,
)


IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse_mapping(raw: list[str]) -> dict[str, str]:
    result: dict[str, str] = {}
    for item in raw:
        if item.count("=") != 1:
            raise ValueError(f"renaming is not OLD=NEW: {item!r}")
        old, new = item.split("=", 1)
        if IDENTIFIER.fullmatch(old) is None or IDENTIFIER.fullmatch(new) is None:
            raise ValueError(f"renaming contains a malformed identifier: {item!r}")
        if old == new:
            raise ValueError(f"renaming is an identity: {item!r}")
        if old in result:
            raise ValueError(f"duplicate source identifier: {old}")
        result[old] = new
    if not result:
        raise ValueError("at least one renaming is required")
    if len(set(result.values())) != len(result):
        raise ValueError("target identifiers are not injective")
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("source_system", type=Path)
    parser.add_argument("source_certificate", type=Path)
    parser.add_argument("target_system", type=Path)
    parser.add_argument("output_certificate", type=Path)
    parser.add_argument("output_manifest", type=Path)
    parser.add_argument("renaming", nargs="+")
    args = parser.parse_args()
    mapping = parse_mapping(args.renaming)

    source = load_json_strict(args.source_system)
    target = load_json_strict(args.target_system)
    source_names = set(validate_variable_names(source.get("variables")))
    target_names = set(validate_variable_names(target.get("variables")))
    if not set(mapping).issubset(source_names):
        raise ValueError("renaming source is absent from the source inventory")
    if not set(mapping.values()).issubset(target_names):
        raise ValueError("renaming target is absent from the target inventory")

    source_replay = check_c4(args.source_system, args.source_certificate)
    text = args.source_certificate.read_text(encoding="utf-8")
    counts = {old: 0 for old in mapping}

    def replace(match: re.Match[str]) -> str:
        token = match.group(0)
        replacement = mapping.get(token)
        if replacement is None:
            return token
        counts[token] += 1
        return replacement

    transported = IDENTIFIER.sub(replace, text)
    unused = sorted(old for old, count in counts.items() if count == 0)
    if unused:
        raise ValueError(f"renaming sources absent from certificate: {unused}")
    args.output_certificate.parent.mkdir(parents=True, exist_ok=True)
    args.output_certificate.write_text(transported, encoding="utf-8")
    target_replay = check_c4(args.target_system, args.output_certificate)

    receipt = {
        "format": "krenn-certificate-variable-rename-v1",
        "script_sha256": sha256(Path(__file__)),
        "source_system_file_sha256": sha256(args.source_system),
        "source_certificate_sha256": sha256(args.source_certificate),
        "target_system_file_sha256": sha256(args.target_system),
        "output_certificate_sha256": sha256(args.output_certificate),
        "renaming": mapping,
        "replacement_counts": counts,
        "source_strict_replay": source_replay,
        "target_strict_replay": target_replay,
    }
    args.output_manifest.parent.mkdir(parents=True, exist_ok=True)
    args.output_manifest.write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps({
        "manifest_sha256": sha256(args.output_manifest),
        "max_multiplier_degree": target_replay["max_multiplier_degree"],
        "renamed_identifiers": len(mapping),
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
