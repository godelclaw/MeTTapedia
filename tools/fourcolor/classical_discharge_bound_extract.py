#!/usr/bin/env python3
"""Generate a finite sharp-bound certificate for the discharging rules.

Six simultaneously applicable rules form a clique in the coordinatewise
interval-intersection graph.  Intersecting all six boxes and removing
duplicates gives the complete obstruction list.  A greedy binary range tree
then certifies that every other box leaves at most five rules possible.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path

from classical_discharge_extract import extract, lean_range
from classical_presentation_extract import FREE_RANGE, FaceRange, Pattern


Location = int
FullSector = tuple[FaceRange, FaceRange, FaceRange, FaceRange, FaceRange]
Box = tuple[FullSector, ...]

LOCATION_NAMES = ("spoke", "hat", "fan1", "fan2", "fan3")


def full_box(pattern: Pattern) -> Box:
    return tuple(sector.constraints() for sector in pattern)  # type: ignore[return-value]


def free_box(arity: int) -> Box:
    return tuple((FREE_RANGE,) * 5 for _ in range(arity))


def range_disjoint(left: FaceRange, right: FaceRange) -> bool:
    return (
        left.upper != 9 and left.upper < right.lower
    ) or (
        right.upper != 9 and right.upper < left.lower
    )


def box_disjoint(left: Box, right: Box) -> bool:
    if len(left) != len(right):
        return True
    return any(
        range_disjoint(left_range, right_range)
        for left_sector, right_sector in zip(left, right, strict=True)
        for left_range, right_range in zip(left_sector, right_sector, strict=True)
    )


def range_intersection(left: FaceRange, right: FaceRange) -> FaceRange:
    if range_disjoint(left, right):
        raise ValueError("cannot intersect disjoint face ranges")
    return FaceRange(max(left.lower, right.lower), min(left.upper, right.upper))


def box_intersection(left: Box, right: Box) -> Box:
    if len(left) != len(right):
        raise ValueError("cannot intersect boxes of different arities")
    return tuple(
        tuple(
            range_intersection(left_range, right_range)
            for left_range, right_range in zip(
                left_sector, right_sector, strict=True
            )
        )
        for left_sector, right_sector in zip(left, right, strict=True)
    )  # type: ignore[return-value]


def box_subset(left: Box, right: Box) -> bool:
    return len(left) == len(right) and all(
        left_range.subset_of(right_range)
        for left_sector, right_sector in zip(left, right, strict=True)
        for left_range, right_range in zip(left_sector, right_sector, strict=True)
    )


def six_clique_intersections(rules: tuple[Box, ...]) -> tuple[Box, ...]:
    """All distinct nonempty intersections of six compatible rules."""

    compatibility = tuple(
        frozenset(
            right
            for right in range(left + 1, len(rules))
            if not box_disjoint(rules[left], rules[right])
        )
        for left in range(len(rules))
    )
    intersections: set[Box] = set()

    def visit(chosen: tuple[int, ...], candidates: tuple[int, ...]) -> None:
        needed = 6 - len(chosen)
        if needed == 0:
            result = rules[chosen[0]]
            for index in chosen[1:]:
                result = box_intersection(result, rules[index])
            intersections.add(result)
            return
        if len(candidates) < needed:
            return
        for offset, index in enumerate(candidates):
            following = tuple(
                candidate
                for candidate in candidates[offset + 1 :]
                if candidate in compatibility[index]
            )
            visit((*chosen, index), following)

    visit((), tuple(range(len(rules))))
    return tuple(sorted(intersections, key=repr))


def split_box(
    box: Box, sector: int, location: Location, bound: int, lower: bool
) -> Box:
    result = [list(item) for item in box]
    result[sector][location] = result[sector][location].split(bound, lower)
    return tuple(tuple(item) for item in result)  # type: ignore[return-value]


def fan_available(sector: FullSector, location: Location) -> bool:
    if location < 2:
        return True
    spoke = sector[0]
    return (
        spoke.lower == spoke.upper
        and spoke.lower in (6, 7, 8)
        and location - 1 <= spoke.lower - 5
    )


def possible_count(rules: tuple[Box, ...], context: Box) -> int:
    return sum(not box_disjoint(context, rule) for rule in rules)


@dataclass(frozen=True)
class Bounded:
    pass


@dataclass(frozen=True)
class Obstruction:
    index: int


@dataclass(frozen=True)
class Split:
    sector: int
    location: Location
    bound: int
    left: "Tree"
    right: "Tree"


Tree = Bounded | Obstruction | Split


def build_tree(
    rules: tuple[Box, ...], obstructions: tuple[Box, ...], root: Box, limit: int
) -> Tree:
    cache: dict[Box, Tree] = {}

    def visit(context: Box) -> Tree:
        known = cache.get(context)
        if known is not None:
            return known
        if possible_count(rules, context) <= limit:
            result: Tree = Bounded()
            cache[context] = result
            return result
        for index, obstruction in enumerate(obstructions):
            if box_subset(context, obstruction):
                result = Obstruction(index)
                cache[context] = result
                return result

        choices: list[tuple[tuple[int, int, int, int], int, int, int, Box, Box]] = []
        for sector_index, sector in enumerate(context):
            for location, selected in enumerate(sector):
                if not fan_available(sector, location):
                    continue
                for bound in range(selected.lower, min(selected.upper, 9)):
                    left = split_box(context, sector_index, location, bound, True)
                    right = split_box(context, sector_index, location, bound, False)
                    left_count = possible_count(rules, left)
                    right_count = possible_count(rules, right)
                    closed = int(left_count <= limit or any(
                        box_subset(left, item) for item in obstructions
                    )) + int(right_count <= limit or any(
                        box_subset(right, item) for item in obstructions
                    ))
                    score = (
                        -closed,
                        max(left_count, right_count),
                        left_count + right_count,
                        abs(left_count - right_count),
                    )
                    choices.append(
                        (score, sector_index, location, bound, left, right)
                    )
        if not choices:
            raise RuntimeError(
                f"unclosed atomic context with {possible_count(rules, context)} rules"
            )
        _, sector_index, location, bound, left, right = min(choices)
        result = Split(
            sector_index,
            location,
            bound,
            visit(left),
            visit(right),
        )
        cache[context] = result
        return result

    return visit(root)


def tree_statistics(tree: Tree) -> tuple[int, int, int, int]:
    """Return split, bounded, obstruction, and maximum-depth counts."""

    if isinstance(tree, Bounded):
        return (0, 1, 0, 0)
    if isinstance(tree, Obstruction):
        return (0, 0, 1, 0)
    left = tree_statistics(tree.left)
    right = tree_statistics(tree.right)
    return (
        1 + left[0] + right[0],
        left[1] + right[1],
        left[2] + right[2],
        1 + max(left[3], right[3]),
    )


def lean_sector(sector: FullSector) -> str:
    return "⟨" + ", ".join(lean_range(item) for item in sector) + "⟩"


def lean_box(box: Box) -> str:
    return "[" + ", ".join(lean_sector(sector) for sector in box) + "]"


def lean_tree(tree: Tree, names: tuple[str, ...], indent: int = 2) -> list[str]:
    pad = " " * indent
    if isinstance(tree, Bounded):
        return [f"{pad}.bounded"]
    if isinstance(tree, Obstruction):
        return [f"{pad}(.obstruction {names[tree.index]})"]
    location = LOCATION_NAMES[tree.location]
    lines = [
        f"{pad}(.split ⟨.{location}, {tree.sector}, {tree.bound}, true⟩"
    ]
    lines.extend(lean_tree(tree.left, names, indent + 2))
    lines.extend(lean_tree(tree.right, names, indent + 2))
    lines[-1] += ")"
    return lines


def module_source(
    source_hash: str,
    rules: tuple[Box, ...],
    obstructions: tuple[Box, ...],
    trees: dict[int, Tree],
) -> str:
    names = tuple(f"obstruction{index:02d}" for index in range(len(obstructions)))
    lines = [
        "import Mettapedia.GraphTheory.FourColor.ClassicalCertificateRuleBound",
        "",
        "/-! Generated sharp-bound certificate for the classical discharge rules. -/",
        "",
        "set_option autoImplicit false",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 200000000",
        "",
        "namespace Mettapedia.GraphTheory.FourColor",
        "",
        "namespace ClassicalCertificateDischargeRuleBoundData",
        "",
        "open ClassicalCertificateDischargePotential",
        "open ClassicalCertificateDischargeRuleData",
        "open ClassicalCertificatePresentationPattern",
        "open ClassicalCertificateRuleBound",
        "",
        f'def sourceSha256 : String := "{source_hash}"',
        "",
    ]
    for name, obstruction in zip(names, obstructions, strict=True):
        lines.extend((f"def {name} : Pattern :=", f"  {lean_box(obstruction)}", ""))
    lines.append("def obstructions : List Pattern :=")
    lines.append("  [" + ", ".join(names) + "]")
    lines.append("")
    for arity, tree in trees.items():
        split_count, bounded_count, obstruction_count, depth = tree_statistics(tree)
        lines.extend(
            (
                f"def code{arity} : BoundCode :=",
                *lean_tree(tree, names),
                "",
                f"def splitCount{arity} : Nat := {split_count}",
                f"def boundedLeafCount{arity} : Nat := {bounded_count}",
                f"def obstructionLeafCount{arity} : Nat := {obstruction_count}",
                f"def maximumDepth{arity} : Nat := {depth}",
                "",
                f"theorem check{arity}_eq_true :",
                f"    code{arity}.check rules obstructions 5 (Pattern.free {arity}) = true := by",
                "  rfl",
                "",
            )
        )
    lines.extend(
        (
            f"theorem obstructions_length : obstructions.length = {len(obstructions)} := by",
            "  rfl",
            "",
            "end ClassicalCertificateDischargeRuleBoundData",
            "",
            "end Mettapedia.GraphTheory.FourColor",
            "",
        )
    )
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("--lean-output", required=True, type=Path)
    args = parser.parse_args()

    source_hash, _, extracted_rules = extract(args.source)
    rule_boxes = tuple(full_box(rule) for rule in extracted_rules)
    all_obstructions: list[Box] = []
    for arity in range(5, 9):
        arity_rules = tuple(rule for rule in rule_boxes if len(rule) == arity)
        all_obstructions.extend(six_clique_intersections(arity_rules))
    obstructions = tuple(sorted(set(all_obstructions), key=lambda item: (len(item), repr(item))))
    trees = {
        arity: build_tree(rule_boxes, obstructions, free_box(arity), 5)
        for arity in range(5, 9)
    }
    args.lean_output.write_text(
        module_source(source_hash, rule_boxes, obstructions, trees),
        encoding="utf-8",
    )

    print(f"rules={len(rule_boxes)} obstructions={len(obstructions)}")
    for arity, tree in trees.items():
        print(f"arity={arity} statistics={tree_statistics(tree)}")


if __name__ == "__main__":
    main()
