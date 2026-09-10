#!/usr/bin/env python3
"""Adversarial controls for bounded-interface pumping, not a graph census.

Pre-registered outcomes:
* Equal complete prefix supports must preserve every terminal acceptance test
  after deletion. One failure rejects the implementation of this algebraic rule.
* Repeated interface type or support cardinality alone should fail that test.
* A finite state carrier need not bound natural-number Count values.
* The seam's orientation-reversal condition is independent of support data.

These controls do not supply geometric cuts, represent least counterexamples,
or give a lower bound for the supports realizable by planar tangles.
"""

import itertools
import json


def image(relation, support, width=2):
    """Bit-matrix relation acting on a bitset of source states."""
    out = 0
    for source in range(width):
        if support & (1 << source):
            out |= (relation >> (source * width)) & ((1 << width) - 1)
    return out


def run(word, initial):
    for letter in word:
        initial = image(letter, initial)
    return initial


def set_image(relation, support):
    """Independent set-comprehension specification of the two-state step."""
    return {y for y in range(2) if any(
        x in support and relation & (1 << (2 * x + y)) for x in range(2))}


def orientation_reversing(left, right, matching):
    return all(right[matching[i]] == matching[left.index(i)] for i in range(len(left)))


def checked_controls():
    step_checks = 0
    for relation, support in itertools.product(range(16), range(4)):
        expected = set_image(relation, {i for i in range(2) if support & (1 << i)})
        actual = {i for i in range(2) if image(relation, support) & (1 << i)}
        assert actual == expected
        step_checks += 1

    # Four transitions give five positions but only four possible supports.
    runs = terminal_checks = nonempty_final = 0
    for word in itertools.product(range(16), repeat=4):
        for initial in range(4):
            prefix = [initial]
            for letter in word:
                prefix.append(image(letter, prefix[-1]))
            left, right = next((i, j) for j in range(1, 5) for i in range(j)
                               if prefix[i] == prefix[j])
            assert left < right
            shortened = word[:left] + word[right:]
            after = run(shortened, initial)
            assert after == prefix[-1]
            for accepting in range(4):
                assert bool(after & accepting) == bool(prefix[-1] & accepting)
                terminal_checks += 1
            runs += 1
            nonempty_final += bool(after)

    # Same interface type and cardinality, different support, changed answer.
    before, after = 1, run((6,), 1)  # swap the two states
    assert before.bit_count() == after.bit_count() == 1
    assert bool(before & 1) and not bool(after & 1)

    # Universal terminal tests separate every two distinct abstract supports.
    context_checks = 0
    for left, right in itertools.product(range(4), repeat=2):
        indistinguishable = all(bool(left & a) == bool(right & a) for a in range(4))
        assert indistinguishable == (left == right)
        context_checks += 1

    counts = [2 ** n for n in range(16)]
    assert len(set(counts)) == 16 and all(count > 0 for count in counts)

    # With identity matching, a three-port seam needs opposite rotations.
    rotation, inverse = (1, 2, 0), (2, 0, 1)
    assert all(inverse[rotation[i]] == i for i in range(3))
    assert orientation_reversing(rotation, inverse, (0, 1, 2))
    assert not orientation_reversing(rotation, rotation, (0, 1, 2))

    return {
        "scope": "abstract two-state transfer algebra and three-port seam condition",
        "reference_step_checks": step_checks,
        "complete_support_runs": runs,
        "terminal_context_checks": terminal_checks,
        "runs_with_nonempty_final_support": nonempty_final,
        "support_separation_checks": context_checks,
        "same_cardinality_deletion_counterexample": {
            "letter": 6, "initial_support": before, "final_support": after,
            "accepting_support": 1, "before_deletion_accepts": False,
            "after_deletion_accepts": True,
        },
        "one_state_count_control": counts,
        "three_port_seam": {"left": list(rotation), "reversing_right": list(inverse),
                            "nonreversing_right": list(rotation)},
        "failures_of_complete_support_deletion": 0,
        "geometric_supply_established": False,
    }


if __name__ == "__main__":
    print(json.dumps(checked_controls(), indent=2))
