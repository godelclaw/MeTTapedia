#!/usr/bin/env python3
"""Dart-level controls for cyclic vertex encoding and physical decoding.

Expected result: every prefix reconstructs its induced source side, for
arbitrary vertex orders and boundary coordinates, including handled sources.
Negative control: reversing only the encoded cyclic order must be detected
even when the edge involution and vertex incidence still round-trip.
No colour witness, planar assumption, or frontier-width bound is used.
"""

import json
import random


def source(vertices, rng):
    while True:
        darts = list(range(3 * vertices))
        rng.shuffle(darts)
        pairs = list(zip(darts[::2], darts[1::2]))
        if all(a // 3 != b // 3 for a, b in pairs):
            return {d: e for a, b in pairs for d, e in ((a, b), (b, a))}


def encode(alpha, seen, vertex, start, before, after, reverse=False):
    incoming, outgoing = {d: i for i, d in enumerate(before)}, {d: i for i, d in enumerate(after)}
    step = -1 if reverse else 1
    slots = [3 * vertex + (start + step * i) % 3 for i in range(3)]
    ports = [("in", incoming[alpha[d]]) if alpha[d] // 3 in seen
             else ("out", outgoing[d]) for d in slots]
    wires = [incoming[d] if d // 3 in seen else None for d in after]
    return ports, wires, slots


def decode(ports, wires, before, vertex, alpha):
    after = [None] * len(wires)
    consumed = set()
    for i, (side, coordinate) in enumerate(ports):
        dart = 3 * vertex + i
        if side == "in":
            old = before[coordinate]
            assert coordinate not in consumed and old not in alpha
            consumed.add(coordinate)
            alpha[dart], alpha[old] = old, dart
        else:
            assert after[coordinate] is None and wires[coordinate] is None
            after[coordinate] = dart
    for j, old in enumerate(wires):
        if old is not None:
            assert old not in consumed and after[j] is None
            after[j] = before[old]
    assert all(d is not None for d in after)
    assert len(set(after)) == len(after)
    assert consumed | {i for i in wires if i is not None} == set(range(len(before)))
    return after


def check(alpha, order, rng, reverse=False):
    seen, before, decoded_boundary = set(), [], []
    decoded_alpha, labels = {}, {}
    rotation_failures = disconnected_prefixes = 0
    for step, vertex in enumerate(order):
        enlarged = seen | {vertex}
        after = [d for d in alpha if d // 3 in enlarged and alpha[d] // 3 not in enlarged]
        rng.shuffle(after)
        ports, wires, slots = encode(alpha, seen, vertex, rng.randrange(3), before, after, reverse)
        decoded_boundary = decode(ports, wires, decoded_boundary, step, decoded_alpha)
        labels.update((3 * step + i, d) for i, d in enumerate(slots))
        assert len(set(labels.values())) == 3 * len(enlarged)
        assert set(labels.values()) == {d for d in alpha if d // 3 in enlarged}
        assert [labels[d] for d in decoded_boundary] == after
        for d, original in labels.items():
            assert original // 3 == order[d // 3]
            mate = alpha[original] if alpha[original] // 3 in enlarged else original
            assert labels[decoded_alpha.get(d, d)] == mate
            rotation_failures += labels[3 * (d // 3) + (d + 1) % 3] != 3 * (original // 3) + (original + 1) % 3
        visited, pending = set(), [next(iter(enlarged))]
        while pending:
            v = pending.pop()
            if v not in visited:
                visited.add(v)
                pending.extend(alpha[3 * v + i] // 3 for i in range(3)
                               if alpha[3 * v + i] // 3 in enlarged)
        disconnected_prefixes += visited != enlarged
        seen, before = enlarged, after
    assert not decoded_boundary
    return rotation_failures, disconnected_prefixes


def run(trials=2000):
    rng = random.Random(20260913)
    prefixes = disconnected = 0
    for _ in range(trials):
        n = 2 * rng.randrange(1, 9)
        alpha = source(n, rng)
        order = list(range(n))
        rng.shuffle(order)
        failures, splits = check(alpha, order, rng)
        assert failures == 0
        disconnected += splits
        prefixes += n
    theta = {0: 3, 3: 0, 1: 5, 5: 1, 2: 4, 4: 2}
    assert check(theta, [0, 1], rng, reverse=True)[0] > 0
    return {"runs": trials, "prefixes": prefixes, "disconnected_prefixes": disconnected,
            "roundtrip_failures": 0, "reversed_rotation_detected": True}


if __name__ == "__main__":
    print(json.dumps(run(), sort_keys=True))
