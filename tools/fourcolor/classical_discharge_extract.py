#!/usr/bin/env python3
"""Extract the classical four-color discharging rules as finite patterns.

The source lists 38 base parts, including deliberate multiplicities, and then
adds a prescribed reflected copy whenever it is not already covered by the
base part.  This tool parses that data language, performs the same finite
symmetrization, and emits a source-hashed Lean module.
"""

from __future__ import annotations

import argparse
import hashlib
import re
from pathlib import Path

from classical_presentation_extract import (
    FaceRange,
    Pattern,
    Sector,
    mirror_pattern,
    pattern_subset,
    rotate_pattern,
)


RULE_RE = re.compile(
    r"Definition\s+(?P<name>drule[0-9]+'?)\s*:=\s*Part\s+"
    r"(?P<body>.*?)\.",
    re.DOTALL,
)
BASE_RE = re.compile(
    r"Definition\s+base_drules\s*:\s*drules\s*:=\s*"
    r"@seqn\s+part\s+(?P<count>[0-9]+)(?P<body>.*?)\.",
    re.DOTALL,
)
SECTOR_RE = re.compile(
    r"\$(?:\[(?P<ranges>[^]]*)\])?\s*"
    r"(?P<spoke>\*|[5-9](?:\s*(?:[+-]|\?\s*[5-9]))?)"
)
RANGE_RE = re.compile(r"\*|[5-9](?:\s*(?:[+-]|\?\s*[5-9]))?")
NAME_RE = re.compile(r"drule[0-9]+'?")


class DischargeSyntaxError(ValueError):
    """Raised when the discharging source is outside the checked language."""


def parse_range(text: str) -> FaceRange:
    token = "".join(text.split())
    if token == "*":
        return FaceRange(5, 9)
    if token.endswith("+"):
        return FaceRange(int(token[:-1]), 9)
    if token.endswith("-"):
        return FaceRange(5, int(token[:-1]))
    if "?" in token:
        lower, upper = token.split("?", maxsplit=1)
        return FaceRange(int(lower), int(upper))
    arity = int(token)
    return FaceRange(arity, arity)


def parse_ranges(text: str) -> tuple[FaceRange, ...]:
    matches = list(RANGE_RE.finditer(text))
    residue = RANGE_RE.sub("", text)
    if residue.strip():
        raise DischargeSyntaxError(f"unrecognized ranges {text!r}")
    return tuple(parse_range(match.group(0)) for match in matches)


def parse_part(text: str) -> Pattern:
    sectors: list[Sector] = []
    matches = list(SECTOR_RE.finditer(text))
    residue = SECTOR_RE.sub("", text)
    if residue.replace("$", "").strip():
        raise DischargeSyntaxError(f"unrecognized part text {residue!r}")
    if residue.count("$") != 1:
        raise DischargeSyntaxError("a part must have exactly one terminal `$`")
    for match in matches:
        spoke = parse_range(match.group("spoke"))
        bracket = match.group("ranges")
        if bracket is None:
            hat = FaceRange(5, 9)
            fans: tuple[FaceRange, ...] = ()
        else:
            ranges = parse_ranges(bracket)
            if not ranges:
                raise DischargeSyntaxError("an explicit sector needs a hat range")
            hat, *fan_list = ranges
            fans = tuple(fan_list)
        sector = Sector(spoke, hat, fans)
        if len(fans) > sector.fan_capacity():
            raise DischargeSyntaxError(
                f"too many fan ranges for spoke {match.group('spoke')!r}"
            )
        sectors.append(sector)
    if not sectors:
        raise DischargeSyntaxError("empty discharge rule")
    return tuple(sectors)


def reflected_rule(pattern: Pattern) -> Pattern:
    """The reflection word used by `symmetrize_drules` in `discharge.v`."""

    amount = len(pattern) - 1
    result = mirror_pattern(pattern)
    for _ in range(5):
        result = rotate_pattern(result, amount)
    return result


def symmetrize_rules(base_rules: tuple[Pattern, ...]) -> tuple[Pattern, ...]:
    result: list[Pattern] = []
    for pattern in base_rules:
        reflected = reflected_rule(pattern)
        if not pattern_subset(pattern, reflected):
            result.append(reflected)
        result.append(pattern)
    return tuple(result)


def extract(source_path: Path) -> tuple[str, tuple[Pattern, ...], tuple[Pattern, ...]]:
    source_bytes = source_path.read_bytes()
    source = source_bytes.decode("utf-8")
    definitions = {
        match.group("name"): parse_part(match.group("body"))
        for match in RULE_RE.finditer(source)
    }
    base_match = BASE_RE.search(source)
    if base_match is None:
        raise DischargeSyntaxError("missing `base_drules` definition")
    names = NAME_RE.findall(base_match.group("body"))
    declared_count = int(base_match.group("count"))
    if len(names) != declared_count:
        raise DischargeSyntaxError(
            f"base rule count is {len(names)}, declared {declared_count}"
        )
    missing = [name for name in names if name not in definitions]
    if missing:
        raise DischargeSyntaxError(f"undefined base rules: {missing!r}")
    base_rules = tuple(definitions[name] for name in names)
    return (
        hashlib.sha256(source_bytes).hexdigest(),
        base_rules,
        symmetrize_rules(base_rules),
    )


def lean_range(face_range: FaceRange) -> str:
    if face_range == FaceRange(5, 9):
        return "FaceRange.free"
    if face_range.lower == face_range.upper:
        return f"FaceRange.singleton {face_range.lower}"
    return f"⟨{face_range.lower}, {face_range.upper}⟩"


def lean_sector(sector: Sector) -> str:
    def argument(face_range: FaceRange) -> str:
        return f"({lean_range(face_range)})"

    hat = argument(sector.hat)
    fans = [argument(item) for item in sector.fans]
    if not fans:
        return f"Sector.plain {argument(sector.spoke)} {hat}"
    constructors = {1: "six", 2: "seven", 3: "eight"}
    constructor = constructors.get(len(fans))
    if constructor is None:
        raise DischargeSyntaxError("a sector has more than three fans")
    return f"Sector.{constructor} " + " ".join([hat, *fans])


def lean_pattern(pattern: Pattern) -> str:
    return "[" + ", ".join(lean_sector(sector) for sector in pattern) + "]"


def lean_rules(name: str, rules: tuple[Pattern, ...]) -> list[str]:
    lines = [f"def {name} : List Pattern := ["]
    for index, pattern in enumerate(rules):
        suffix = "," if index + 1 < len(rules) else ""
        lines.append(f"  {lean_pattern(pattern)}{suffix}")
    lines.append("]")
    return lines


def lean_module(
    source_hash: str,
    base_rules: tuple[Pattern, ...],
    rules: tuple[Pattern, ...],
) -> str:
    lines = [
        "import Mettapedia.GraphTheory.FourColor.ClassicalCertificatePresentationPattern",
        "",
        "/-! Generated classical discharging-rule data. -/",
        "",
        "set_option autoImplicit false",
        "",
        "namespace Mettapedia.GraphTheory.FourColor",
        "",
        "namespace ClassicalCertificateDischargeRuleData",
        "",
        "open ClassicalCertificatePresentationPattern",
        "",
        f'def sourceSha256 : String := "{source_hash}"',
        "",
    ]
    lines.extend(lean_rules("baseRules", base_rules))
    lines.append("")
    lines.extend(lean_rules("rules", rules))
    lines.extend(
        [
            "",
            f"theorem baseRules_length : baseRules.length = {len(base_rules)} := by",
            "  rfl",
            "",
            f"theorem rules_length : rules.length = {len(rules)} := by",
            "  rfl",
            "",
            "end ClassicalCertificateDischargeRuleData",
            "",
            "end Mettapedia.GraphTheory.FourColor",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("--lean-output", type=Path)
    args = parser.parse_args()

    source_hash, base_rules, rules = extract(args.source)
    output = lean_module(source_hash, base_rules, rules)
    if args.lean_output is None:
        print(output, end="")
    else:
        args.lean_output.write_text(output, encoding="utf-8")


if __name__ == "__main__":
    main()
