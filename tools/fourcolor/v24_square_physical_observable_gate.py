#!/usr/bin/env python3
"""Constructor-law gate: smaller physical realizations of a marked square.

Compare full marked-colour support with the particular equality observation
against boundary port 2. Enumerate all edge pairings of the cubic vertex slots
and four labelled terminal slots for zero or two internal vertices. This
includes loops, parallel edges, disconnected pieces and nonplanar pairings;
it is not a catalogue of reducible configurations. Components consisting of
vertex-free circles are not represented by this endpoint model.

Pre-registered outcomes: a smaller full-profile summand must have no output
outside the square support; failure forbids a nonnegative exact decomposition.
An equality-only realization is checked for exact multiplicities, not just
support. Boundary labels are fixed throughout.
"""

import argparse
from collections import Counter
from itertools import product
import json
from pathlib import Path

from v24_marked_square_gate import COLORS, extensions


def pairings(items):
    if not items:
        yield ()
        return
    a, *rest = items
    for j, b in enumerate(rest):
        for tail in pairings(rest[:j] + rest[j + 1:]):
            yield ((a, b),) + tail


def profiles(vertices, pairs):
    assert sorted(a for p in pairs for a in p) == list(range(3 * vertices + 4))
    result = [Counter() for _ in pairs]
    for colors in product(COLORS, repeat=len(pairs)):
        slots = [0] * (3 * vertices + 4)
        for (a, b), color in zip(pairs, colors):
            slots[a] = slots[b] = color
        if not all(len(set(slots[3 * i:3 * i + 3])) == 3 for i in range(vertices)):
            continue
        word = tuple(slots[-4:])
        for mark, color in enumerate(colors):
            result[mark][word, color] += 1
    return result


def equality_profile(profile):
    return Counter({w: n for (w, color), n in profile.items() if color == w[2]})


def rotation_faces(edges, rotations):
    """Explicit dart-permutation check; supports parallel edges."""
    ends = {(e, b): edge[b] for e, edge in enumerate(edges) for b in (0, 1)}
    assert sorted(d for ds in rotations for d in ds) == sorted(ends)
    rho = {}
    for v, ds in enumerate(rotations):
        assert all(ends[d] == v for d in ds)
        rho.update({d: ds[(i + 1) % len(ds)] for i, d in enumerate(ds)})
    phi = {d: rho[(d[0], 1 - d[1])] for d in ends}
    todo, cycles = set(ends), []
    while todo:
        first = min(todo)
        cycle, d = [], first
        while d not in cycle:
            assert d in todo
            cycle.append(d)
            todo.remove(d)
            d = phi[d]
        assert d == first
        cycles.append(cycle)
    return cycles


def run():
    square = Counter((w, x[0]) for w in product(COLORS, repeat=4) for x in extensions(w))
    target = equality_profile(square)
    census = []
    for v in (0, 2):
        n_pairings = n_marked = contained = all_red_blue = eq_exact = 0
        for ps in pairings(list(range(3 * v + 4))):
            n_pairings += 1
            for profile in profiles(v, ps):
                n_marked += 1
                if profile and set(profile) <= set(square):
                    contained += 1
                if profile[((1, 1, 1, 1), 2)]:
                    all_red_blue += 1
                    assert not set(profile) <= set(square)
                if equality_profile(profile) == target:
                    eq_exact += 1
        assert contained == 0
        census.append(dict(vertices=v, pairings=n_pairings, marked_pieces=n_marked,
                           nonempty_full_support_contained=contained,
                           all_red_blue_pieces=all_red_blue, equality_exact=eq_exact))

    # Two parallel edges, two terminal edges, and one terminal-to-terminal wire.
    ps = ((0, 6), (1, 4), (2, 5), (3, 7), (8, 9))
    marked = profiles(2, ps)[1]
    assert equality_profile(marked) == target
    assert set(marked) != set(square)
    # Suppressing the digon turns the equality observation into INEQUALITY
    # of the two surviving wire colours. It is not ordinary mark renaming.
    for w in product(COLORS, repeat=4):
        assert target[w] == int(w[0] == w[1] and w[2] == w[3] and w[0] != w[2])

    # Cap the four ordered terminals by their boundary cycle to certify that
    # this drawing has the requested disk order, not a crossed pairing.
    edges = [(0, 1), (0, 1), (0, 2), (1, 3), (4, 5),
             (2, 3), (3, 4), (4, 5), (5, 2)]
    rotations = [[(0, 0), (2, 0), (1, 0)], [(0, 1), (1, 1), (3, 0)],
                 [(2, 1), (5, 0), (8, 1)], [(3, 1), (6, 0), (5, 1)],
                 [(4, 0), (7, 0), (6, 1)], [(4, 1), (8, 0), (7, 1)]]
    faces = rotation_faces(edges, rotations)
    assert len(edges) == 9 and len(rotations) == 6 and len(faces) == 5
    assert all(len(ds) == 3 for ds in rotations)
    reached = {0}
    while True:
        extended = reached | {b for a, b in edges if a in reached} | {a for a, b in edges if b in reached}
        if extended == reached:
            break
        reached = extended
    assert reached == set(range(6))
    assert any({e for e, _ in face} == {5, 6, 7, 8} for face in faces)
    return dict(schema='fourcolor-square-physical-observable-v1', census=census,
                square_full_states=len(square), equality_states=len(target),
                full_profile_nonnegative_decomposition=False,
                boundary_equality_exact_replacement=True,
                replacement=dict(vertices=2, pairs=ps, marked_edge=1,
                                 marked_capped_edge=0, reference_capped_edge=4,
                                 capped_edges=edges, capped_rotation=rotations, capped_faces=faces),
                suppressed_observation='w0=w1 and w2=w3 and w0!=w2',
                scope='complete endpoint-model constructor gate; full profile obstruction; equality-only repair; no ambient minimality-class theorem')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--check', type=Path)
    args = parser.parse_args()
    result = json.loads(json.dumps(run()))
    if args.check:
        assert result == json.loads(args.check.read_text())
    if args.output:
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
