#!/usr/bin/env python3
"""Independently test the uniform matching codec and cyclic arc witnesses.

This bounded replay checks exact answer sets, not just one accepted word.
The Lean induction supplies the arbitrary-width theorem. Neither this probe
nor that codec alone establishes a strict graph reduction or coverage.
"""
from __future__ import annotations

import argparse
from functools import lru_cache
import hashlib
from itertools import combinations, product
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]

if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are audit checks.")


@lru_cache(None)
def matchings(lo, hi):
    if lo == hi:
        return ((),)
    result = [(lo,) + rest for rest in matchings(lo + 1, hi)]
    for other in range(lo + 1, hi):
        for inner in matchings(lo + 1, other):
            for tail in matchings(other + 1, hi):
                result.append((other,) + inner + (lo,) + tail)
    return tuple(result)


def accepts(word, gram):
    stack = []
    for color, symbol in zip(word, gram, strict=True):
        if symbol == "skip":
            if color != 1:
                return False
        elif symbol == "push":
            if color not in (2, 3):
                return False
            stack.append(color)
        else:
            if not stack or color not in (2, 3):
                return False
            same = color == stack.pop()
            if same != (symbol == "pop0"):
                return False
    return not stack


def matching_replay(width):
    grams_count = answers_count = 0
    for mate in matchings(0, width):
        assert all(mate[mate[i]] == i for i in range(width))
        stack = lambda i: [j for j in reversed(range(i)) if i <= mate[j]]
        assert stack(0) == stack(width) == []
        for i in range(width):
            if mate[i] == i:
                assert stack(i + 1) == stack(i)
            elif i < mate[i]:
                assert stack(i + 1) == [i] + stack(i)
            else:
                assert stack(i) == [mate[i]] + stack(i + 1)
        words = tuple(product(*( (1,) if mate[i] == i else (2, 3)
                                for i in range(width))))
        representatives = {}
        for word in words:
            gram = tuple("skip" if mate[i] == i else "push" if i < mate[i]
                         else "pop0" if word[i] == word[mate[i]] else "pop1"
                         for i in range(width))
            assert accepts(word, gram)
            representatives.setdefault(gram, word)
        pairs = [i for i in range(width) if i < mate[i]]
        for gram, original in representatives.items():
            expected = set()
            for flags in product((False, True), repeat=len(pairs)):
                selected = {j for i, flag in zip(pairs, flags, strict=True) if flag
                            for j in (i, mate[i])}
                expected.add(tuple(5 - c if i in selected else c
                                   for i, c in enumerate(original)))
            actual = {word for word in words if accepts(word, gram)}
            assert actual == expected
            for answer in actual:
                difference = [a != b for a, b in zip(original, answer, strict=True)]
                assert all(difference[i] == difference[mate[i]] for i in range(width))
            grams_count += 1
            answers_count += len(words)
    return {"width": width, "matchings": len(matchings(0, width)),
            "chromograms": grams_count, "answer_tests": answers_count}


def arc_replay(max_width):
    count = 0
    for n in range(4, max_width + 1):
        for cut, left, separator, right in combinations(range(n), 4):
            left_steps, right_steps = left - cut - 1, n - right + cut
            assert (cut + 1 + left_steps) % n == left
            assert (right + right_steps) % n == cut
            assert all((cut + 1 + j) % n not in (cut, separator) for j in range(left_steps))
            assert all((right + j) % n not in (cut, separator) for j in range(right_steps))
            count += 1
    return {"max_width": max_width, "ordered_quadruples": count}


def intrinsic_replay():
    source = ROOT / "lean/fourcolor-classical/MettapediaFourColor/MixedDiamondTangle.lean"
    text = source.read_text()
    def table(name):
        return [ord(c) - 65 for c in json.loads(re.search("def " + name + r" : String := (.*)", text)[1])]
    vertices, rotation = table("vertexCodes"), table("rotationCodes")
    alpha = table("alphaCodes") + list(range(32, 39))
    adjacency = [set() for _ in range(13)]
    for d in range(32):
        adjacency[vertices[d]].add(vertices[alpha[d]])
    order = [0]
    for vertex in order:
        for neighbor in sorted(adjacency[vertex]):
            if neighbor not in order:
                order.append(neighbor)
    assert len(order) == 13
    phi = [rotation[alpha[d]] for d in range(39)]
    arcs = []
    for i in range(7):
        arc, dart = [32 + i], phi[32 + i]
        while dart < 32:
            assert dart not in arc
            arc.append(dart)
            dart = phi[dart]
        arc.append(dart)
        assert dart == 32 + (i + 1) % 7
        arcs.append(arc)
    unseen, faces = set(range(39)), []
    while unseen:
        first = dart = min(unseen)
        face = []
        while dart in unseen:
            unseen.remove(dart)
            face.append(dart)
            dart = phi[dart]
        assert dart == first
        faces.append(face)
    assert len(faces) == 5 and 2 * 13 - 32 + 2 * len(faces) == 4
    code = lambda xs: "".join(chr(65 + x) for x in xs)
    geometry = ROOT / "lean/fourcolor-classical/MettapediaFourColor/MixedDiamondIntrinsic.lean"
    gtext = geometry.read_text()
    for expected in (code(order), code([order.index(i) for i in range(13)]),
                     code([len(arc) - 1 for arc in arcs])):
        assert json.dumps(expected) in gtext
    return {"vertices": 13, "ports": 7, "vertex_order": order,
            "first_return_arcs": arcs, "open_face_count": len(faces), "euler_mass": 4}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-width", type=int, default=8)
    parser.add_argument("--arc-max-width", type=int, default=16)
    parser.add_argument("--output", type=Path, default=HERE / "uniform-matching-probe.json")
    args = parser.parse_args()
    if args.max_width < 0 or args.arc_max_width < 0:
        parser.error("widths must be nonnegative")
    paths = [Path(__file__),
             ROOT / "lean/fourcolor-classical/MettapediaFourColor/MixedDiamondTangle.lean",
             ROOT / "lean/fourcolor-classical/MettapediaFourColor/MixedDiamondIntrinsic.lean"]
    report = {"scope": "Independent finite replay; the general results are proved separately in Lean.",
              "matching_codec": [matching_replay(n) for n in range(args.max_width + 1)],
              "cyclic_arcs": arc_replay(args.arc_max_width),
              "mixed_diamond_geometry": intrinsic_replay(),
              "source_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                                for p in paths}}
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"matching_codec": report["matching_codec"],
                      "cyclic_arcs": report["cyclic_arcs"]}, indent=2))


if __name__ == "__main__":
    main()
