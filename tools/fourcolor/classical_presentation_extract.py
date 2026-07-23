#!/usr/bin/env python3
"""Extract the finite four-color unavoidability presentation language.

The presentation sources use a prefix proof script: every ``Pcase`` replaces
the current goal by two ordered subgoals, while ``Reducible``, ``Hubcap``, and
``Similar`` close the current subgoal.  This tool parses that small language,
checks its branch and label discipline, and emits a source-hashed JSON syntax
tree suitable for conversion to a proof-assistant certificate.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Sequence


sys.setrecursionlimit(100_000)


PCASE_RE = re.compile(
    r"^Pcase(?:\s+(?P<label>[A-Za-z][A-Za-z0-9_]*))?\s*:\s*"
    r"(?P<location>s|h|f1|f2|f3)\[(?P<index>[0-9]+)\]\s*"
    r"(?P<relation><=|>)\s*(?P<bound>[0-9]+)\.$"
)
SIMILAR_RE = re.compile(
    r"^Similar\s+to\s+(?P<mirror>\*)?"
    r"(?P<label>[A-Za-z][A-Za-z0-9_]*)\[(?P<rotation>[0-9]+)\]\.$"
)
HUBCAP_TERM_RE = re.compile(
    r"\$\[(?P<first>[0-9]+)(?:,(?P<second>[0-9]+))?\]"
    r"<=\s*(?P<bound>\(-[0-9]+\)|-?[0-9]+)"
)
EXCLUDE_RE = re.compile(r"^Lemma\s+exclude(?P<arity>[0-9]+)\s*:", re.MULTILINE)


class PresentationSyntaxError(ValueError):
    """Raised when a presentation source is not in the checked language."""


@dataclass(frozen=True)
class FaceRange:
    """One of the finite presentation intervals; upper nine means infinity."""

    lower: int
    upper: int

    def contains(self, arity: int) -> bool:
        return self.lower <= arity and (self.upper == 9 or arity <= self.upper)

    def good_split(self, bound: int) -> bool:
        return self.lower <= bound < self.upper and bound < 9

    def split(self, bound: int, lower_side: bool) -> FaceRange:
        if not self.good_split(bound):
            raise PresentationSyntaxError(
                f"cannot split [{self.lower},{self.upper}] at {bound}"
            )
        if lower_side:
            return FaceRange(self.lower, min(self.upper, bound))
        return FaceRange(max(self.lower, bound + 1), self.upper)

    def subset_of(self, other: FaceRange) -> bool:
        lower_ok = other.lower <= self.lower
        upper_ok = other.upper == 9 or (
            self.upper != 9 and self.upper <= other.upper
        )
        return lower_ok and upper_ok


FREE_RANGE = FaceRange(5, 9)


@dataclass(frozen=True)
class Sector:
    """A spoke, its preceding hat, and zero to three explicit fan ranges."""

    spoke: FaceRange
    hat: FaceRange
    fans: tuple[FaceRange, ...] = ()

    def fan_capacity(self) -> int:
        if self.spoke.lower == self.spoke.upper and self.spoke.lower in (6, 7, 8):
            return self.spoke.lower - 5
        return 0

    def range_at(self, location: str) -> FaceRange | None:
        if location == "s":
            return self.spoke
        if location == "h":
            return self.hat
        fan_index = {"f1": 0, "f2": 1, "f3": 2}[location]
        if fan_index < len(self.fans):
            return self.fans[fan_index]
        if not self.fans and fan_index < self.fan_capacity():
            return FREE_RANGE
        return None

    def split_at(self, location: str, bound: int, lower_side: bool) -> Sector:
        selected = self.range_at(location)
        if selected is None or not selected.good_split(bound):
            raise PresentationSyntaxError(
                f"invalid {location} split on sector {self!r} at {bound}"
            )
        replacement = selected.split(bound, lower_side)
        if location == "s":
            if self.fans:
                raise PresentationSyntaxError("explicit-fan sectors have fixed spokes")
            return Sector(replacement, self.hat)
        if location == "h":
            return Sector(self.spoke, replacement, self.fans)
        fan_index = {"f1": 0, "f2": 1, "f3": 2}[location]
        fans = list(self.fans)
        if not fans:
            fans = [FREE_RANGE] * self.fan_capacity()
        fans[fan_index] = replacement
        return Sector(self.spoke, self.hat, tuple(fans))

    def constraints(self) -> tuple[FaceRange, ...]:
        fans = self.fans + (FREE_RANGE,) * (3 - len(self.fans))
        return (self.spoke, self.hat, *fans)


Pattern = tuple[Sector, ...]


def free_pattern(arity: int) -> Pattern:
    return tuple(Sector(FREE_RANGE, FREE_RANGE) for _ in range(arity))


def split_pattern(
    pattern: Pattern, location: str, index: int, bound: int, lower_side: bool
) -> Pattern:
    if not 0 <= index < len(pattern):
        raise PresentationSyntaxError(f"sector index {index + 1} is out of range")
    result = list(pattern)
    result[index] = result[index].split_at(location, bound, lower_side)
    return tuple(result)


def good_pattern_split(pattern: Pattern, location: str, index: int, bound: int) -> bool:
    if not 0 <= index < len(pattern):
        return False
    selected = pattern[index].range_at(location)
    return selected is not None and selected.good_split(bound)


def rotate_pattern(pattern: Pattern, amount: int) -> Pattern:
    return pattern[amount:] + pattern[:amount]


def mirror_pattern(pattern: Pattern) -> Pattern:
    if not pattern:
        return pattern
    result: list[Sector] = []
    size = len(pattern)
    for index in range(size - 1, -1, -1):
        sector = pattern[index]
        next_hat = pattern[(index + 1) % size].hat
        result.append(Sector(sector.spoke, next_hat, tuple(reversed(sector.fans))))
    return tuple(result)


def pattern_subset(left: Pattern, right: Pattern) -> bool:
    """Whether every pentagonal profile fitting ``left`` also fits ``right``."""

    if len(left) != len(right):
        return False
    for left_sector, right_sector in zip(left, right, strict=True):
        left_constraints = left_sector.constraints()
        right_constraints = right_sector.constraints()
        if len(left_constraints) < len(right_constraints):
            return False
        if not all(
            left_range.subset_of(right_range)
            for left_range, right_range in zip(
                left_constraints[: len(right_constraints)],
                right_constraints,
                strict=True,
            )
        ):
            return False
    return True


@dataclass(frozen=True)
class Command:
    text: str
    line: int


@dataclass
class Slot:
    container: dict[str, Any]
    key: str
    labels: tuple[str, ...]


def normalized_commands(source: str) -> list[Command]:
    """Collect complete presentation commands and their first source line."""

    commands: list[Command] = []
    active = False
    hubcap_text: list[str] = []
    hubcap_line = 0

    for line_number, raw_line in enumerate(source.splitlines(), start=1):
        text = raw_line.strip()
        if not active:
            if text == "Presentation red.":
                active = True
            continue
        if text == "Qed.":
            if hubcap_text:
                raise PresentationSyntaxError(
                    f"line {hubcap_line}: unterminated Hubcap command"
                )
            break

        if hubcap_text:
            hubcap_text.append(text)
            joined = " ".join(hubcap_text)
            if joined.endswith("$."):
                commands.append(Command(joined, hubcap_line))
                hubcap_text = []
            continue

        if text.startswith("Hubcap "):
            hubcap_text = [text]
            hubcap_line = line_number
            if text.endswith("$."):
                commands.append(Command(text, line_number))
                hubcap_text = []
            continue

        if text.startswith(("Pcase", "Similar", "Reducible")):
            commands.append(Command(text, line_number))

    if not active:
        raise PresentationSyntaxError("missing `Presentation red.`")
    return commands


def parse_bound(text: str) -> int:
    if text.startswith("(") and text.endswith(")"):
        text = text[1:-1]
    return int(text)


def parse_hubcap(command: Command) -> dict[str, Any]:
    body = command.text[len("Hubcap ") :]
    terms: list[dict[str, Any]] = []
    cursor = 0
    for match in HUBCAP_TERM_RE.finditer(body):
        skipped = body[cursor : match.start()].strip()
        if skipped:
            raise PresentationSyntaxError(
                f"line {command.line}: unexpected Hubcap text {skipped!r}"
            )
        term: dict[str, Any] = {
            "first": int(match.group("first")),
            "bound": parse_bound(match.group("bound")),
        }
        if match.group("second") is not None:
            term["second"] = int(match.group("second"))
        terms.append(term)
        cursor = match.end()
    trailing = body[cursor:].strip()
    if trailing != "$." or not terms:
        raise PresentationSyntaxError(
            f"line {command.line}: malformed Hubcap terminator {trailing!r}"
        )
    return {"kind": "hubcap", "terms": terms, "line": command.line}


def label_depth(labels: Sequence[str], name: str, line: int) -> int:
    for depth, known in enumerate(reversed(labels)):
        if known == name:
            return depth
    raise PresentationSyntaxError(
        f"line {line}: similarity refers to unavailable label {name!r}"
    )


def parse_leaf(command: Command, labels: Sequence[str]) -> dict[str, Any]:
    if command.text == "Reducible.":
        return {"kind": "reducible", "line": command.line}
    if command.text.startswith("Hubcap "):
        return parse_hubcap(command)
    match = SIMILAR_RE.fullmatch(command.text)
    if match is None:
        raise PresentationSyntaxError(
            f"line {command.line}: unrecognized terminal {command.text!r}"
        )
    name = match.group("label")
    return {
        "kind": "similar",
        "label": name,
        "depth": label_depth(labels, name, command.line),
        "mirror": match.group("mirror") is not None,
        "rotation": int(match.group("rotation")),
        "line": command.line,
    }


def parse_tree(commands: Iterable[Command]) -> dict[str, Any]:
    """Parse the prefix subgoal stream and validate scoped label references."""

    holder: dict[str, Any] = {"root": None}
    current: Slot | None = Slot(holder, "root", ())
    pending: list[Slot] = []

    for command in commands:
        if current is None:
            raise PresentationSyntaxError(
                f"line {command.line}: command occurs after the root was closed"
            )

        match = PCASE_RE.fullmatch(command.text)
        if match is not None:
            label = match.group("label")
            node: dict[str, Any] = {
                "kind": "split",
                "location": match.group("location"),
                "index": int(match.group("index")),
                "lower": match.group("relation") == "<=",
                "bound": int(match.group("bound")),
                "line": command.line,
                "left": None,
                "right": None,
            }
            if label is not None:
                node["label"] = label
            current.container[current.key] = node
            right_labels = current.labels
            if label is not None:
                right_labels = right_labels + (label,)
            pending.append(Slot(node, "right", right_labels))
            current = Slot(node, "left", current.labels)
            continue

        current.container[current.key] = parse_leaf(command, current.labels)
        current = pending.pop() if pending else None

    if current is not None or pending:
        raise PresentationSyntaxError("presentation ended with open subgoals")
    root = holder["root"]
    if root is None:
        raise PresentationSyntaxError("presentation contains no proof commands")
    return root


def presentation_arity(source: str) -> int:
    match = EXCLUDE_RE.search(source)
    if match is None:
        raise PresentationSyntaxError("missing `Lemma excludeN` declaration")
    arity = int(match.group("arity"))
    if not 5 <= arity <= 11:
        raise PresentationSyntaxError(f"unsupported presentation arity {arity}")
    return arity


def validate_tree(
    node: dict[str, Any],
    context: Pattern,
    pattern: Pattern,
    labels: tuple[tuple[str, Pattern], ...] = (),
) -> None:
    """Execute all pattern operations and validate each scoped similarity."""

    kind = node["kind"]
    if kind == "split":
        location = node["location"]
        index = node["index"] - 1
        bound = node["bound"]
        lower_side = node["lower"]
        if not good_pattern_split(pattern, location, index, bound):
            raise PresentationSyntaxError(
                f"line {node['line']}: split is not nontrivial in its goal pattern"
            )
        left = split_pattern(pattern, location, index, bound, lower_side)
        right = split_pattern(pattern, location, index, bound, not lower_side)
        if good_pattern_split(context, location, index, bound):
            left_context = split_pattern(
                context, location, index, bound, lower_side
            )
        else:
            left_context = left
        validate_tree(node["left"], left_context, left, labels)
        right_labels = labels
        if "label" in node:
            right_labels = labels + ((node["label"], left_context),)
        validate_tree(node["right"], context, right, right_labels)
        return

    if kind != "similar":
        return
    depth = node["depth"]
    if depth >= len(labels):
        raise PresentationSyntaxError(
            f"line {node['line']}: similarity depth {depth} is out of scope"
        )
    label, known = labels[-1 - depth]
    if label != node["label"]:
        raise PresentationSyntaxError(
            f"line {node['line']}: similarity depth resolves to {label!r}, "
            f"not {node['label']!r}"
        )
    transformed = mirror_pattern(pattern) if node["mirror"] else pattern
    transformed = rotate_pattern(transformed, node["rotation"])
    if not pattern_subset(transformed, known):
        raise PresentationSyntaxError(
            f"line {node['line']}: transformed goal is not contained in "
            f"the referenced pattern {label!r}"
        )


def tree_statistics(root: dict[str, Any]) -> dict[str, int]:
    counts = {
        "splits": 0,
        "reducible": 0,
        "hubcap": 0,
        "similar": 0,
        "leaves": 0,
        "maximumDepth": 0,
    }
    stack: list[tuple[dict[str, Any], int]] = [(root, 0)]
    while stack:
        node, depth = stack.pop()
        counts["maximumDepth"] = max(counts["maximumDepth"], depth)
        kind = node["kind"]
        if kind == "split":
            counts["splits"] += 1
            stack.append((node["right"], depth + 1))
            stack.append((node["left"], depth + 1))
        else:
            counts[kind] += 1
            counts["leaves"] += 1
    if counts["leaves"] != counts["splits"] + 1:
        raise AssertionError("a full binary presentation has leaves = splits + 1")
    return counts


def extract(path: Path) -> dict[str, Any]:
    source_bytes = path.read_bytes()
    source = source_bytes.decode("utf-8")
    tree = parse_tree(normalized_commands(source))
    arity = presentation_arity(source)
    root = free_pattern(arity)
    validate_tree(tree, root, root)
    return {
        "source": path.name,
        "sha256": hashlib.sha256(source_bytes).hexdigest(),
        "arity": arity,
        "statistics": tree_statistics(tree),
        "tree": tree,
    }


LEAN_LOCATIONS = {
    "s": ".spoke",
    "h": ".hat",
    "f1": ".fan1",
    "f2": ".fan2",
    "f3": ".fan3",
}


def lean_hubcap_term(term: dict[str, Any]) -> str:
    first = term["first"] - 1
    if first < 0:
        raise PresentationSyntaxError("hubcap indices must be positive")
    if "second" in term:
        second_index = term["second"] - 1
        if second_index < 0:
            raise PresentationSyntaxError("hubcap indices must be positive")
        second = f"some {second_index}"
    else:
        second = "none"
    return f"⟨{first}, {second}, {term['bound']}⟩"


def lean_tree_lines(node: dict[str, Any], indent: int = 2) -> list[str]:
    pad = " " * indent
    kind = node["kind"]
    if kind == "reducible":
        return [f"{pad}(.terminal .reducible)"]
    if kind == "hubcap":
        terms = ", ".join(lean_hubcap_term(term) for term in node["terms"])
        return [f"{pad}(.terminal (.hubcap [{terms}]))"]
    if kind == "similar":
        mirror = "true" if node["mirror"] else "false"
        return [
            f"{pad}(.similar {node['depth']} ⟨{mirror}, {node['rotation']}⟩)"
        ]
    if kind != "split":
        raise AssertionError(f"unexpected presentation node {kind!r}")
    location = LEAN_LOCATIONS[node["location"]]
    index = node["index"] - 1
    if index < 0:
        raise PresentationSyntaxError("split indices must be positive")
    lower = "true" if node["lower"] else "false"
    retain = "true" if "label" in node else "false"
    lines = [
        f"{pad}(.split {retain} "
        f"⟨{location}, {index}, {node['bound']}, {lower}⟩"
    ]
    lines.extend(lean_tree_lines(node["left"], indent + 2))
    lines.extend(lean_tree_lines(node["right"], indent + 2))
    lines[-1] += ")"
    return lines


def lean_module(item: dict[str, Any]) -> tuple[str, str]:
    arity = item["arity"]
    namespace = f"ClassicalCertificatePresentationData{arity}"
    filename = f"{namespace}.lean"
    statistics = item["statistics"]
    lines = [
        "import Mettapedia.GraphTheory.FourColor."
        "ClassicalCertificatePresentationCertificate",
        "",
        "/-! Generated finite unavoidability presentation certificate. -/",
        "",
        "set_option autoImplicit false",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 200000000",
        "",
        "namespace Mettapedia.GraphTheory.FourColor",
        "",
        f"namespace {namespace}",
        "",
        "open ClassicalCertificatePresentationPattern",
        "open ClassicalCertificatePresentationCertificate",
        "",
        f'def sourceSha256 : String := "{item["sha256"]}"',
        f"def arity : Nat := {arity}",
        f"def splitCount : Nat := {statistics['splits']}",
        f"def leafCount : Nat := {statistics['leaves']}",
        "",
        "def code : Code :=",
    ]
    lines.extend(lean_tree_lines(item["tree"]))
    lines.extend(
        [
            "",
            "theorem structureCheck_eq_true :",
            "    structureCheck arity code = true := by",
            "  rfl",
            "",
            f"end {namespace}",
            "",
            "end Mettapedia.GraphTheory.FourColor",
            "",
        ]
    )
    return filename, "\n".join(lines)


def write_lean_modules(output: Path, presentations: Sequence[dict[str, Any]]) -> None:
    output.mkdir(parents=True, exist_ok=True)
    for item in presentations:
        filename, source = lean_module(item)
        (output / filename).write_text(source, encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("sources", nargs="+", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--stats-only", action="store_true")
    parser.add_argument("--lean-output", type=Path)
    args = parser.parse_args()

    presentations = [extract(path) for path in args.sources]
    if args.lean_output is not None:
        write_lean_modules(args.lean_output, presentations)
    if args.stats_only:
        result: Any = [
            {
                "source": item["source"],
                "sha256": item["sha256"],
                "arity": item["arity"],
                **item["statistics"],
            }
            for item in presentations
        ]
    else:
        result = {"format": "four-color-presentation-v1", "presentations": presentations}

    encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output is None:
        sys.stdout.write(encoded)
    else:
        args.output.write_text(encoded, encoding="utf-8")


if __name__ == "__main__":
    main()
