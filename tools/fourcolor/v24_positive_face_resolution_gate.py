#!/usr/bin/env python3
"""Test positive count resolution at the pentagon frontier.

Endpoint pieces consist of cubic vertex slots and labelled boundary terminals,
paired into physical edges. All pairings are included: loops, parallel edges,
disconnected components, and nonplanar boundary orders. Vertex-free circles
are omitted; they only multiply the count by three. Boundary labels are fixed.

Controls are the triangle-to-vertex bijection and the two square resolutions.
The pentagon test asks whether any nonempty smaller piece has support contained
in the pentagon's support. Such containment is necessary for a positive summand
of an exact count identity. If candidates survive, this test is inconclusive
about their possible linear combinations. It is not a reducibility catalogue.
"""

from collections import Counter
from itertools import permutations, product
import json
from math import prod

from v24_square_physical_observable_gate import pairings


COLORS = range(3)
PERMS = tuple(permutations(COLORS))


def face_profile(n):
    """Independent cycle-edge enumeration; the third colour fixes each port."""
    result = Counter()
    for edges in product(COLORS, repeat=n):
        if all(edges[i - 1] != edges[i] for i in range(n)):
            result[tuple(3 - edges[i - 1] - edges[i] for i in range(n))] += 1
    return result


def endpoint_profile(vertices, boundary, pairs):
    size = 3 * vertices + boundary
    assert sorted(x for pair in pairs for x in pair) == list(range(size))
    mate = [None] * size
    for a, b in pairs:
        mate[a], mate[b] = b, a
        if a < 3 * vertices and b < 3 * vertices and a // 3 == b // 3:
            return Counter()
    slots = [-1] * size
    result = Counter()
    wires = [(a, b) for a, b in pairs if min(a, b) >= 3 * vertices]

    def visit(v):
        if v == vertices:
            for wire_colors in product(COLORS, repeat=len(wires)):
                for (a, b), c in zip(wires, wire_colors):
                    slots[a] = slots[b] = c
                word = tuple(slots[3 * vertices:])
                assert all(c in COLORS for c in word)
                if vertices:
                    for p in PERMS:
                        result[tuple(p[c] for c in word)] += 1
                else:
                    result[word] += 1
            return
        positions = range(3 * v, 3 * v + 3)
        # At the first cubic vertex all six colour permutations are equivalent.
        for colors in (PERMS[:1] if v == 0 else PERMS):
            if any(slots[a] not in (-1, c) or slots[mate[a]] not in (-1, c)
                   for a, c in zip(positions, colors)):
                continue
            changed = []
            for a, c in zip(positions, colors):
                for b in (a, mate[a]):
                    if slots[b] == -1:
                        changed.append(b)
                        slots[b] = c
            visit(v + 1)
            for b in changed:
                slots[b] = -1

    visit(0)
    return result


def basis_profiles():
    star_wire = endpoint_profile(1, 5, ((0, 3), (1, 4), (2, 5), (6, 7)))
    tree = endpoint_profile(3, 5, ((0, 9), (1, 10), (2, 3), (4, 11),
                                 (5, 6), (7, 12), (8, 13)))
    basis = {}
    for kind, profile in (("star_wire", star_wire), ("tree", tree)):
        assert set(profile.values()) == {1}
        for p in permutations(range(5)):
            key = tuple(sorted(tuple(w[i] for i in p) for w in profile))
            basis[key] = kind
    assert Counter(basis.values()) == dict(star_wire=10, tree=15)
    return basis


def run():
    star = endpoint_profile(1, 3, ((0, 3), (1, 4), (2, 5)))
    assert face_profile(3) == star
    horizontal = endpoint_profile(0, 4, ((0, 1), (2, 3)))
    vertical = endpoint_profile(0, 4, ((0, 3), (1, 2)))
    assert face_profile(4) == horizontal + vertical
    target = face_profile(5)
    assert len(target) == 30 and sum(target.values()) == 30
    basis = basis_profiles()
    classes = []
    for vertices in (1, 3):
        examined = nonempty = contained = 0
        supports = Counter()
        multipliers = Counter()
        first_candidate = None
        for pairs in pairings(list(range(3 * vertices + 5))):
            examined += 1
            profile = endpoint_profile(vertices, 5, pairs)
            if not profile:
                continue
            nonempty += 1
            key = tuple(sorted(profile))
            supports[key] += 1
            assert key in basis and len(set(profile.values())) == 1
            multipliers[next(iter(profile.values()))] += 1
            if set(profile) <= set(target):
                contained += 1
                if first_candidate is None:
                    first_candidate = pairs
        assert examined == prod(range(1, 3 * vertices + 5, 2))
        row = dict(vertices=vertices, endpoint_pairings=examined, nonempty=nonempty,
                   distinct_supports=len(supports), contained=contained,
                   scalar_multipliers=dict(sorted(multipliers.items())),
                   first_candidate=first_candidate)
        classes.append(row)
    return dict(schema="fourcolor-positive-face-resolution-v1",
                controls=dict(triangle_words=len(star), square_words=len(face_profile(4)),
                              pentagon_words=len(target)),
                classes=classes,
                positive_resolution_ruled_out=all(c["contained"] == 0 for c in classes),
                scope="Complete smaller endpoint-piece gate; no target-class reduction claim.")


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
