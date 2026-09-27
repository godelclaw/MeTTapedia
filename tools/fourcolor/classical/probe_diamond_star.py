"""Test a cubic-star boundary relation on configurations 1, 2 and 4.

The original embedded graphs share the diamond as their internal graph.
Their boundary supports are independently recomputed by vertex colouring.
The test distinguishes inclusion of the entire star image from existence of
at least one compatible branch for each source word. It does not establish
graph or Kempe transport, nor reducibility.
"""

import argparse
from hashlib import sha256
from functools import reduce
from itertools import permutations, product
import json
from pathlib import Path
from operator import xor
import time

from probe_common_support import close_colors, parity, read_input
from configuration_map_isomorphism import EXPECTED_HASHES, records

if not __debug__:
    raise SystemExit('Run without Python optimization: assertions are audit checks.')

INPUT_HASHES = {
    1: 'cbb90220c26e162c752847c87057b9f59291b2ae21a844b7f3df81ab95354faa',
    2: '5964d1abb43cf7fa124df7ee5a459e4c4421294b80eb9eee6626c37b7249d02b',
    4: '9ca06cbedcbf91033f18dc118a13e6fd98dbeba31f1931eba21c5a913a5aa19c',
}


def full_support(path):
    ring, good, _, digest = read_input(path)
    words = {tuple(map(int, parity(word) + word)) for word in close_colors(good)}
    for word in words:
        assert len(word) == ring and set(word) <= {1, 2, 3}
        value = 0
        for color in word:
            value ^= color
        assert value == 0
        for perm in permutations((1, 2, 3)):
            assert tuple(perm[c - 1] for c in word) in words
    return ring, words, digest


def geometric_support(source):
    """Colour the original free completion, fixing boundary vertex 1 to zero.

    Four vertex colours are the Klein four group. Nonzero XOR differences
    around the ring give the three edge colours. Every boundary assignment
    with its first vertex fixed is enumerated; internal vertices are coloured
    by a separate backtracking search on the original adjacency lists.
    """
    ring = source['ring']
    assert 6 <= ring <= 8 and source['vertices'] - ring == 4
    adjacency = {v: [w for u, w in source['darts'] if u == v]
                 for v in range(1, source['vertices'] + 1)}
    internal = set(range(ring + 1, source['vertices'] + 1))

    def extends(colors, todo):
        if not todo:
            return True
        domains = {v: set(range(4)) - {colors[w] for w in adjacency[v] if w in colors}
                   for v in todo}
        v = min(todo, key=lambda u: (len(domains[u]), u))
        return any(extends(colors | {v: c}, todo - {v}) for c in sorted(domains[v]))

    accepted = set()
    for prefix in product((1, 2, 3), repeat=ring - 1):
        final = reduce(xor, prefix, 0)
        if final == 0:
            continue
        colors = {1: 0}
        for v, c in enumerate(prefix, 2):
            colors[v] = colors[v - 1] ^ c
        if any(colors[v] == colors[w] for v, w in source['darts']
               if v <= ring and w <= ring):
            continue
        if extends(colors, internal):
            accepted.add(prefix + (final,))
    return accepted


def attach(words, port):
    output = set()
    for word in words:
        c = word[port]
        for a in (1, 2, 3):
            for b in (1, 2, 3):
                if a != b and a ^ b == c:
                    output.add(word[:port] + (a, b) + word[port + 1:])
    assert len(output) == 2 * len(words)
    recovered = {word[:port] + (word[port] ^ word[port + 1],) + word[port + 2:]
                 for word in output}
    assert recovered == words
    return output


def orient(words, rotation, reflection):
    return {(word[::-1] if reflection else word)[rotation:] +
            (word[::-1] if reflection else word)[:rotation] for word in words}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--configurations', type=Path, required=True)
    parser.add_argument('--inputs', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    input_paths = {args.configurations.resolve()} | {
        (args.inputs / f'{i-1}.in').resolve() for i in INPUT_HASHES}
    assert args.output.resolve() not in input_paths, 'Output must differ from inputs'
    start = time.monotonic()
    raw = args.configurations.read_bytes()
    assert sha256(raw).hexdigest() == EXPECTED_HASHES['configurations']
    sources = records(raw.decode())
    supports = {i: full_support(args.inputs / f'{i-1}.in') for i in INPUT_HASHES}
    geometry = []
    for i, (ring, words, digest) in supports.items():
        assert digest == INPUT_HASHES[i]
        source = sources[i - 1]
        assert ring == source['ring']
        calculated = geometric_support(source)
        alignments = [dict(rotation=rotation, reflection=reflection)
                      for rotation in range(ring) for reflection in (False, True)
                      if calculated == orient(words, rotation, reflection)]
        assert alignments, ('Stored and geometric supports differ', i)
        geometry.append(dict(ordinal=i, ring=ring, support=len(calculated),
                             matching_alignments=alignments))
    trials = []
    for first, second in [(1, 2), (2, 4)]:
        ring, left, _ = supports[first]
        target_ring, right, _ = supports[second]
        assert target_ring == ring + 1
        for port in range(ring):
            image = attach(left, port)
            branches = {word: attach({word}, port) for word in left}
            for reflection in (False, True):
                for rotation in range(target_ring):
                    target = orient(right, rotation, reflection)
                    assert len(target) == len(right)
                    missing = image - target
                    blocked = sorted(word for word, choices in branches.items()
                                     if choices.isdisjoint(target))
                    trials.append(dict(source=first, target=second, port=port,
                        reflection=reflection, rotation=rotation,
                        source_support=len(left), star_image=len(image),
                        target_support=len(target), missing=len(missing),
                        blocked_source_words=len(blocked),
                        blocked_source_witness=list(blocked[0]) if blocked else None,
                        outside_witness=list(min(missing)) if missing else None))
    result = dict(evidence='Finite program probe; no geometric or Kempe-transport proof.',
                  configurations_sha256=sha256(raw).hexdigest(),
                  probe_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                  source_sha256={str(i): values[2] for i, values in supports.items()},
                  geometric_support_checks=geometry,
                  trials=trials, comparisons=len(trials),
                  containments=[t for t in trials if t['missing'] == 0],
                  existential_attachments=[t for t in trials if t['blocked_source_words'] == 0],
                  existential_scope='For one fixed port and target orientation, every source word has at least one target-supported star branch.',
                  closest_per_pair=[min((t for t in trials if (t['source'], t['target']) == pair),
                                        key=lambda t:t['missing']) for pair in [(1, 2), (2, 4)]],
                  elapsed_seconds=round(time.monotonic()-start, 3))
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'trials'}, indent=2))


if __name__ == '__main__':
    main()
