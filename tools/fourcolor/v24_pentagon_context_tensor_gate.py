#!/usr/bin/env python3
"""An exact five-port test of signed linear identities plus positivity.

The tensors are delta times epsilon, corrected by the cyclic boundary gauge.
The experiment does not assert that every nonnegative tensor is realizable by
a plane tangle. It tests that relaxation, including abstract noncrossing Kempe
closure, before attempting a physical-exterior theorem. No patch certificates
or catalogue are generated.
"""

from itertools import combinations, permutations, product
import json

from v24_positive_face_resolution_gate import endpoint_profile, face_profile
from v24_square_physical_observable_gate import pairings


PAIRS = tuple(combinations(range(5), 2))
WORDS = tuple(tuple(1 if k == i else 2 if k == j else 0 for k in range(5))
              for i, j in PAIRS)
BAD = (0, 1, 1, 0, 0, 1, 1, 0, 1, 0)
COEFFICIENTS = (0, -1, 0, 0, 1, -1, 0, 0, 0, 0)
RELATIONS = ((-1, 1, -1, 1, 0, 0, 0, 0, 0, 0),
             (-1, 0, 0, 0, 1, -1, 1, 0, 0, 0),
             (0, -1, 0, 0, 1, 0, 0, -1, 1, 0),
             (0, 0, -1, 0, 0, 1, 0, -1, 0, 1))


def epsilon(colors):
    if len(set(colors)) != 3:
        return 0
    inversions = sum(colors[i] > colors[j] for i in range(3) for j in range(i + 1, 3))
    return (-1) ** inversions


def delta_epsilon(word, pair):
    return int(word[pair[0]] == word[pair[1]]) * epsilon(
        tuple(word[i] for i in range(5) if i not in pair))


def legal(word):
    return all(word.count(c) % 2 == 1 for c in range(3))


def gauge(word):
    if not legal(word):
        return 1
    signs = [delta_epsilon(word, tuple(sorted((i, (i + 1) % 5))))
             for i in range(5) if word[i] == word[(i + 1) % 5]]
    assert signs and len(set(signs)) == 1 and signs[0] != 0
    return signs[0]


def basis_row(word):
    return tuple(gauge(word) * delta_epsilon(word, p) for p in PAIRS)


def adversary(word):
    return sum(a * b for a, b in zip(COEFFICIENTS, basis_row(word)))


def noncrossing(matching):
    chords = [sorted(pair) for pair in matching]
    return not any(a < c < b < d or c < a < d < b
                   for a, b in chords for c, d in chords)


def closed_matching(word, colors, support, matching):
    if not noncrossing(matching):
        return False
    for chosen in product((False, True), repeat=len(matching)):
        ports = {p for edge, take in zip(matching, chosen) if take for p in edge}
        switched = tuple(sum(colors) - c if i in ports else c for i, c in enumerate(word))
        if switched not in support:
            return False
    return True


def run():
    from sympy import Matrix

    matrix = Matrix([basis_row(w) for w in WORDS])
    relations = Matrix(RELATIONS)
    assert matrix.rank() == 6 and relations.rank() == 4
    assert relations * matrix == Matrix.zeros(4, 10)
    assert matrix * Matrix(COEFFICIENTS) == Matrix(BAD)
    good = [i for i, v in enumerate(BAD) if not v]
    kernels = matrix[good, :].nullspace()
    image = Matrix.hstack(*(matrix * v for v in kernels))
    assert image.rank() == 1
    pentagon = face_profile(5)
    support = {w for w in product(range(3), repeat=5) if adversary(w)}
    assert support == {w for w in product(range(3), repeat=5) if legal(w) and not pentagon[w]}
    assert all(adversary(w) in (0, 1) for w in product(range(3), repeat=5))
    tree = endpoint_profile(3, 5, ((0, 9), (1, 10), (2, 3), (4, 11),
                                  (5, 6), (7, 12), (8, 13)))
    star = endpoint_profile(1, 5, ((0, 3), (1, 4), (2, 5), (6, 7)))
    physical_basis = Matrix([[star[tuple(w[(i + r) % 5] for i in range(5))]
                              for r in range(5)] + [pentagon[w]] for w in WORDS])
    assert physical_basis.rank() == 6
    connected_basis = Matrix([[tree[tuple(w[(i + r) % 5] for i in range(5))]
                               for r in range(5)] + [pentagon[w]] for w in WORDS])
    assert connected_basis.rank() == 6
    for w in product(range(3), repeat=5):
        stars = sum(star[tuple(w[(i + r) % 5] for i in range(5))] for r in range(5))
        assert adversary(w) == stars - 2 * pentagon[w]
        trees = sum(tree[tuple(w[(i + r) % 5] for i in range(5))] for r in range(5))
        assert 3 * adversary(w) == trees - pentagon[w]
    for profile in (pentagon, tree, star):
        for shift in range(5):
            row = Matrix([profile[tuple(w[(i + shift) % 5] for i in range(5))] for w in WORDS])
            assert relations * row == Matrix.zeros(4, 1)
    for p in permutations(range(3)):
        assert {tuple(p[c] for c in w) for w in support} == support
    cases = 0
    for word in support:
        for colors in combinations(range(3), 2):
            active = [i for i, c in enumerate(word) if c in colors]
            assert any(closed_matching(word, colors, support, m) for m in pairings(active))
            cases += 1
    return dict(schema="fourcolor-pentagon-context-tensor-v1", rank=6,
                relation_rank=4, bad_only_dimension=1, bad_vector=list(BAD),
                coefficients=list(COEFFICIENTS), planar_controls=15,
                physical_span_rank=6,
                physical_identity="adversary = sum(five cyclic Y-wire counts) - 2 pentagonCount",
                connected_span_rank=6,
                connected_identity="3 adversary = sum(five cyclic tree counts) - pentagonCount",
                admissible_words=60, adversary_words=len(support),
                noncrossing_closure_cases=cases,
                verdict="Linear identities, positivity and abstract Kempe closure are insufficient.",
                scope="No realization as an actual plane exterior is claimed.")


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
