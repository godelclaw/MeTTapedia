#!/usr/bin/env python3
"""Finite exploration of five/six-rim wheels; this is not a Lean certificate.

The centre has degree n, one rim vertex has degree five and the others six.
The ring has length 2*n-1. At n=7 the literal pinned D3009 source is used.
Every terminal witness is checked against all actual graph edges. Closure
quantifies over every noncrossing pairing and every union of whole chords,
modulo global interchange of the two active colours.
The optional two-five test uses all three separations around a seven-rim
wheel and constructs the full twelve-port graph directly.
"""

import argparse
import hashlib
import itertools
import json
import time
from pathlib import Path

from generate_exceptional_repair import boundary, canonical, pairings, traces


SOURCE_SHA256 = "5453856a156bd63835ddac419ebbe276ac6ae81b0a11b909cf928bf0b1686a3f"
SOURCE_REVISION = "c2ce7a96e35256201526e2abb51a39d04a588b53"


def wheel(n):
    """Return outer incidences, centre label, rim labels, and all graph edges."""
    if n < 3:
        raise ValueError("a wheel requires at least three rim vertices")
    r = 2 * n - 1
    outer = [[r - 1, 0]] + [[2*i - 2, 2*i - 1, 2*i] for i in range(1, n)]
    center, rim = r, list(range(r + 1, r + n + 1))
    if n == 7:
        raw = Path(__file__).with_name("D3009.conf").read_bytes()
        assert hashlib.sha256(raw).hexdigest() == SOURCE_SHA256
        rows = [list(map(int, line.split())) for line in raw.decode().splitlines() if line.strip()]
        assert rows[0] == [21, 13]
        stars = {row[0] - 1: [v - 1 for v in row[2:]] for row in rows[1:]}
        rim = stars[center]
        source_outer = [[v for v in stars[i] if v < r] for i in rim]
        assert all(set(b) == {(v + 5) % r for v in a}
                   for a, b in zip(outer, source_outer))
        outer = source_outer
        edges = {tuple(sorted((i, j))) for i, row in stars.items() for j in row}
    else:
        edges = {(center, i) for i in rim}
        edges.update(tuple(sorted((rim[i], rim[(i + 1) % n]))) for i in range(n))
        edges.update(tuple(sorted((rim[i], b))) for i, row in enumerate(outer) for b in row)
    edges.update(tuple(sorted((i, (i + 1) % r))) for i in range(r))
    assert len(edges) == 7 * n - 2
    return outer, center, rim, sorted(edges)


def witness(word, outer):
    """Compose allowed rim colours with one retained centre and closing seam."""
    ports = boundary(word)
    for center in range(4):
        allowed = [tuple(c for c in range(4)
                         if c != center and all(c != ports[j] for j in row))
                   for row in outer]
        if any(not choices for choices in allowed):
            continue
        for first in allowed[0]:
            paths = {first: (first,)}
            for choices in allowed[1:]:
                following = {}
                for old, path in paths.items():
                    for c in choices:
                        if c != old:
                            following.setdefault(c, path + (c,))
                paths = following
                if not paths:
                    break
            for last, path in paths.items():
                if last != first:
                    return center, path
    return None


def answers(word, fixed, chords, slots):
    # Complementary subsets differ by a global colour permutation. Selected
    # larger answers do not establish that fewer chords could not suffice.
    for count in range(1, max(1, len(chords) // 2) + 1):
        for chosen in itertools.combinations(chords, count):
            changed = list(word)
            for pair in chosen:
                for k in pair:
                    changed[slots[k]] ^= fixed
            yield canonical(changed)


def profile_wheel(n, fives):
    """A wheel with specified five-rim positions and all other rim degrees six.

    Each wedge has one shared outer corner. A six-rim position has one
    further outer vertex between its two corners. The construction retains
    all boundary and interior edges; it makes no ambient embedding claim.
    """
    fives = set(fives)
    if n < 3 or not fives <= set(range(n)):
        raise ValueError("invalid wheel profile")
    fans, corners, size = [], [], 0
    for i in range(n):
        if i in fives:
            fans.append(None)
        else:
            fans.append(size)
            size += 1
        corners.append(size)
        size += 1
    outer = [[corners[i-1]] + ([] if fans[i] is None else [fans[i]]) + [corners[i]]
             for i in range(n)]
    center, rim = size, list(range(size + 1, size + n + 1))
    edges = {(center, i) for i in rim}
    edges.update(tuple(sorted((rim[i], rim[(i + 1) % n]))) for i in range(n))
    edges.update(tuple(sorted((rim[i], b))) for i, row in enumerate(outer) for b in row)
    edges.update(tuple(sorted((i, (i + 1) % size))) for i in range(size))
    assert len(edges) == 3*n + 2*size
    for i, v in enumerate(rim):
        assert sum(v in edge for edge in edges) == (5 if i in fives else 6)
    return outer, center, rim, sorted(edges)


def run(n, deadline=None, *, fives=None):
    started = time.monotonic()
    outer, center, rim, edges = wheel(n) if fives is None else profile_wheel(n, fives)
    r = center
    words = traces(r)
    known = set()
    for word in words:
        extension = witness(word, outer)
        if extension is not None:
            z, colors = extension
            actual = dict(enumerate(boundary(word))) | {center: z} | dict(zip(rim, colors))
            assert all(actual[a] != actual[b] for a, b in edges)
            known.add(word)
    stages = [len(known)]
    first_nonextending = next((w for w in words if w not in known), None)
    while len(known) < len(words):
        added = []
        for word in words:
            if word in known:
                continue
            if deadline is not None and time.monotonic() > deadline:
                return dict(width=n, ring=r, states=len(words), stages=stages,
                            complete=False, seconds=round(time.monotonic()-started, 2))
            for fixed in (1, 2, 3):
                slots = [j for j, c in enumerate(word) if c != fixed]
                if all(any(a in known for a in answers(word, fixed, chords, slots))
                       for chords in pairings(len(slots))):
                    added.append(word)
                    break
        if not added:
            break
        known.update(added)
        stages.append(len(known))
    return dict(width=n, ring=r, states=len(words), stages=stages, complete=True,
                survivors=len(words)-len(known), first_nonextending=first_nonextending,
                first_survivor=next((w for w in words if w not in known), None),
                edges_checked_per_terminal=len(edges),
                seconds=round(time.monotonic()-started, 2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--widths", nargs="+", type=int, default=[5, 6, 7])
    parser.add_argument("--two-fives", action="store_true",
                        help="test the three two-five positions on a seven-rim wheel")
    parser.add_argument("--seconds", type=float, help="optional total exploration deadline")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    deadline = None if args.seconds is None else time.monotonic() + args.seconds
    report = {
        "status": "independent program experiment, not a Lean repair certificate",
        "source_revision": SOURCE_REVISION,
        "D3009_sha256": SOURCE_SHA256,
        "D3009_input_used": not args.two_fives and 7 in args.widths,
        "canonicalization": "nonzero xor-zero traces modulo global edge-colour permutations",
        "closure": "all noncrossing pairings, whole-chord subsets modulo complement",
        "scope": "no uniform D-repair, actual exterior reconstruction, or coverage claim",
        "domain": "two-five seven-rim wheels" if args.two_fives else "single-five wheels",
        "results": [dict(run(7, deadline, fives={0, gap}), separation=gap)
                    for gap in (1, 2, 3)] if args.two_fives else
                   [run(n, deadline) for n in args.widths],
    }
    text = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
