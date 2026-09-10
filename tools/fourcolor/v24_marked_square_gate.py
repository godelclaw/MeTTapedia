#!/usr/bin/env python3
"""Test erased-edge observables in the generic square constructor.

Gate: the unmarked square count must equal the two smoothing counts; test
whether choosing either surviving seam edge as the image of an internal
mark preserves its equality target. Independently check reconstruction of
every extension from one internal colour, including arbitrary colour tags.
This is a constructor-law test, not a configuration/reducibility catalogue.
Colour codes are the nonzero elements 1, 2, 3 of the Klein four group.
"""

import argparse
from itertools import product
import json
from pathlib import Path


COLORS = (1, 2, 3)


def extensions(word):
    return [x for x in product(COLORS, repeat=4)
            if all(len({word[i], x[i - 1], x[i]}) == 3 for i in range(4))]


def reconstruct(word, seed):
    return seed, word[1] ^ seed, word[2] ^ word[1] ^ seed, word[3] ^ word[2] ^ word[1] ^ seed


def valid_seed(word, seed):
    return (word[0] ^ word[1] ^ word[2] ^ word[3]) == 0 and all(reconstruct(word, seed))


def reduced(word, side):
    pairs = ((0, 1), (2, 3)) if side == 0 else ((1, 2), (3, 0))
    return [tuple(word[a] for a, _ in pairs)] if all(word[a] == word[b] for a, b in pairs) else []


def run():
    words, extensions_checked, tagged = 0, 0, 0
    for word in product(COLORS, repeat=4):
        xs = extensions(word)
        assert len(xs) == len(reduced(word, 0)) + len(reduced(word, 1))
        rebuilt = [reconstruct(word, t) for t in COLORS if valid_seed(word, t)]
        assert sorted(xs) == sorted(rebuilt)
        for edge, target in product(range(4), COLORS):
            assert sum(x[edge] == target for x in xs) == sum(x[edge] == target for x in rebuilt)
            tagged += 1
        words += 1
        extensions_checked += len(xs)
    word = (1, 1, 1, 1)
    xs = extensions(word)
    assert xs == [(2, 3, 2, 3), (3, 2, 3, 2)]
    # Both reductions have only colour 1 on BOTH surviving seam edges.
    assert all(reduced(word, s) == [(1, 1)] for s in (0, 1))
    assert all(x[i] != word[2] for x in xs for i in range(4))
    # The transposition fixing red exchanges the two extensions and fixes
    # each labelled reduction state. No equivariant selector can choose one.
    swap = {1: 1, 2: 3, 3: 2}
    assert all(tuple(swap[c] for c in x) != x for x in xs)
    return dict(schema='fourcolor-marked-square-gate-v1',
        words=words, extensions=extensions_checked, tagged_checks=tagged,
        unmarked_identity=True, seeded_reconstruction=True,
        witness=dict(boundary=word, internal_mark=0, external_reference_port=2,
                     reference_color=1, extensions=xs,
                     upstairs_equal_count=0, literal_image_reduction_counts=[1, 1],
                     swap_fixes_both_labelled_reduction_states=True),
        scope='generic square law; literal erased-edge tracking fails; virtual seed is not a physical replacement')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--check', type=Path)
    args = parser.parse_args()
    result = json.loads(json.dumps(run()))
    if args.check:
        assert json.loads(args.check.read_text()) == result
    if args.output:
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
