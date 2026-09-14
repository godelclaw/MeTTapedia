#!/usr/bin/env python3
"""Refute the adjacent two-vertex positive resolution of a facial cycle.

For an ``n``-face, delete two adjacent cubic vertices.  The remaining path has
four loose ends: the two deleted boundary ports and the two ends of the path.
There are exactly three ways to pair those ends.  This gate compares the exact
boundary-colouring count of each resulting physical tangle with that of the
original facial cycle.

The conclusion is deliberately narrow.  It rules out a nonnegative exact
linear combination of these three local smoothings; it says nothing about
arbitrary smaller tangles or context-dependent reductions.
"""

from itertools import product
import json

from v24_positive_face_resolution_gate import endpoint_profile, face_profile


FOUR_END_PAIRINGS = (
    ((0, 1), (2, 3)),
    ((0, 2), (1, 3)),
    ((0, 3), (1, 2)),
)


def adjacent_two_vertex_profiles(n):
    """The three profiles after deleting adjacent cycle vertices 0 and 1."""
    assert n >= 4
    vertices = n - 2
    fixed_pairs = []

    # Retained old vertices 2,...,n-1.  Their slots are left, right, boundary.
    for vertex in range(vertices):
        fixed_pairs.append((3 * vertex + 2, 3 * vertices + vertex + 2))
    for vertex in range(vertices - 1):
        fixed_pairs.append((3 * vertex + 1, 3 * (vertex + 1)))

    loose = (3 * vertices, 3 * vertices + 1, 0, 3 * (vertices - 1) + 1)
    profiles = []
    for pairing in FOUR_END_PAIRINGS:
        closing_pairs = [(loose[left], loose[right]) for left, right in pairing]
        profiles.append(endpoint_profile(vertices, n, tuple(fixed_pairs + closing_pairs)))
    return profiles


def first_support_violation(target, candidate):
    return next(
        (word for word in product(range(3), repeat=len(next(iter(candidate))))
         if candidate[word] > 0 and target[word] == 0),
        None,
    )


def run(first=5, last=10):
    rows = []
    for n in range(first, last + 1):
        target = face_profile(n)
        resolutions = adjacent_two_vertex_profiles(n)
        witnesses = [first_support_violation(target, profile) for profile in resolutions]
        assert all(witness is not None for witness in witnesses)
        rows.append({
            "face_length": n,
            "target_support": len(target),
            "target_total": sum(target.values()),
            "resolutions": [
                {
                    "support": len(profile),
                    "total": sum(profile.values()),
                    "bad_word": list(witness),
                    "bad_word_multiplicity": profile[witness],
                    "target_multiplicity": target[witness],
                }
                for profile, witness in zip(resolutions, witnesses)
            ],
        })
    return {
        "schema": "fourcolor-long-face-local-resolution-v1",
        "tested_face_lengths": [first, last],
        "rows": rows,
        "positive_resolution_ruled_out": True,
        "scope": (
            "Only the three adjacent two-vertex smoothings are refuted; arbitrary "
            "smaller tangles and context-dependent reductions are not tested."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
