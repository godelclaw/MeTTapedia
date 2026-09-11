#!/usr/bin/env python3
"""A constructor-law gate for exact physical-context compression.

Three four-port cubic pieces, not a configuration catalogue. Two encode
one bit by different noncrossing digon pairings; the third tests the bit.
Pre-registered outcome: an exact colourability observer must distinguish
all bit strings if the tester accepts exactly the selected bit. Disc-order,
closed incidence, and bridge checks delimit the admissible-context scope.
"""

import argparse
from itertools import product
import json

from v24_square_physical_observable_gate import rotation_faces


def piece(kind):
    if kind in ("A", "B"):
        return [(0, 1), (0, 1), (2, 3), (2, 3)], (
            [0, 1, 2, 3] if kind == "A" else [0, 2, 3, 1])
    assert kind == "T"
    return [(0, 1), (1, 2), (2, 0), (2, 3)], [0, 1, 3, 3]


def count_colorings(vertices, edges):
    """Direct edge search with distinct incident colours; no support tables."""
    incidence = [[i for i, e in enumerate(edges) if v in e] for v in range(vertices)]
    assert all(u != v for u, v in edges)
    colors = [0] * len(edges)

    def visit(left):
        if not left:
            return 1
        options = []
        for e in left:
            forbidden = {colors[f] for v in edges[e] for f in incidence[v]}
            allowed = [c for c in (1, 2, 3) if c not in forbidden]
            if not allowed:
                return 0
            options.append((len(allowed), e, allowed))
        _, e, allowed = min(options)
        total = 0
        for c in allowed:
            colors[e] = c
            total += visit(left - {e})
        colors[e] = 0
        return total

    return visit(set(range(len(edges))))


def extension_count(kind, word):
    edges, ports = piece(kind)
    total = 0
    for internal in product((1, 2, 3), repeat=4):
        triples = [[internal[e] for e, ends in enumerate(edges) if v in ends]
                   + [word[p] for p, u in enumerate(ports) if u == v]
                   for v in range(4)]
        total += all(len(t) == len(set(t)) == 3 for t in triples)
    return total


def components(vertices, edges):
    remaining, result = set(range(vertices)), []
    while remaining:
        seen, queue = set(), [min(remaining)]
        while queue:
            v = queue.pop()
            if v in seen:
                continue
            seen.add(v)
            queue.extend(w for e in edges if v in e for w in e if w not in seen)
        remaining -= seen
        result.append(sorted(seen))
    return result


def disc_rotation(kind):
    """Close ordered terminals with a cycle and verify a spherical disc."""
    inside, ports = piece(kind)
    return find_disc_rotation(inside, ports)


def find_disc_rotation(inside, ports):
    edges = inside + [(v, 4 + p) for p, v in enumerate(ports)]
    edges += [(4 + p, 4 + (p + 1) % 4) for p in range(4)]
    at = [[(e, b) for e, ends in enumerate(edges) for b in (0, 1) if ends[b] == v]
          for v in range(8)]
    rim = [[(8 + (p - 1) % 4, 1), (8 + p, 0), (4 + p, 1)] for p in range(4)]
    for flips in product((False, True), repeat=4):
        rot = [ds[::-1] if flip else ds for ds, flip in zip(at[:4], flips)] + rim
        faces = rotation_faces(edges, rot)
        if len(faces) == 6 and any({e for e, _ in f} == set(range(8, 12)) for f in faces):
            return rot[:4]
    raise AssertionError("no ordered disc certificate")


def closed(inside_kind, outside_kind):
    a, pa = piece(inside_kind)
    b, pb = piece(outside_kind)
    edges = a + [(u + 4, v + 4) for u, v in b] + [(pa[p], pb[p] + 4) for p in range(4)]
    ra, rb = disc_rotation(inside_kind), disc_rotation(outside_kind)
    # Interior edge indices are shifted; port edges are the common seam.
    ca = [[(e if e < 4 else e + 4, end) for e, end in row] for row in ra]
    cb = [[(e + 4, end) if e < 4 else (e + 4, 1) for e, end in row[::-1]] for row in rb]
    faces = rotation_faces(edges, ca + cb)
    comps = components(8, edges)
    assert len(faces) == len(edges) - 8 + 2 * len(comps)
    assert all(sum(v in e for e in edges) == 3 for v in range(8))
    bridges = [i for i in range(len(edges))
               if len(components(8, edges[:i] + edges[i + 1:])) > len(comps)]
    return dict(inner=inside_kind, outer=outside_kind, edges=edges,
                rotations=ca + cb, faces=len(faces), components=comps,
                bridges=bridges, colorings=count_colorings(8, edges))


def run():
    results = [closed(a, b) for a in ("A", "B") for b in ("A", "T")]
    expected = {("A", "A"): 144, ("B", "A"): 48,
                ("A", "T"): 0, ("B", "T"): 24}
    for result in results:
        a, b = result["inner"], result["outer"]
        glued = sum(extension_count(a, w) * extension_count(b, w)
                    for w in product((1, 2, 3), repeat=4))
        assert result["colorings"] == glued == expected[a, b]
        assert bool(result["bridges"]) == (a == "A" and b == "T")
    checks = 0
    for n in range(1, 7):
        languages = set()
        for bits in product((False, True), repeat=n):
            observations = []
            for probe in range(n):
                count = 1
                for j, bit in enumerate(bits):
                    count *= expected["B" if bit else "A", "T" if j == probe else "A"]
                observations.append(count > 0)
                assert (count > 0) == bits[probe]
                checks += 1
            languages.add(tuple(observations))
        assert len(languages) == 2**n
    return dict(scope="loopless cubic ordered-disc pieces; bridge-producing contexts allowed",
                local_blocks=results, bit_experiments=checks,
                bits_checked=6, boundary_ports_per_bit=4,
                warning="The rejecting closure has a bridge; not a bridgeless target-class lower bound.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output")
    args = parser.parse_args()
    receipt = json.dumps(run(), indent=2) + "\n"
    if args.output:
        with open(args.output, "w") as stream:
            stream.write(receipt)
    else:
        print(receipt, end="")
