"""Compare literal boundary-triangle subdivisions with diamond variants."""

import argparse
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import time
import networkx as nx
from configuration_map_isomorphism import records, EXPECTED_HASHES

if not __debug__:
    raise SystemExit('Run without Python optimization: assertions are audit checks.')


def rows(source):
    return {v: [w for u, w in source['darts'] if u == v]
            for v in range(1, source['vertices'] + 1)}


def subdivide(source, a, b, c):
    before = rows(source)
    assert b in before[a] and a in before[b]
    if before[c][(before[c].index(b) + 1) % len(before[c])] == a:
        x, y = b, a
    elif before[c][(before[c].index(a) + 1) % len(before[c])] == b:
        x, y = a, b
    else:
        return None
    assert before[x][(before[x].index(y) + 1) % len(before[x])] == c
    assert before[y][(before[y].index(c) + 1) % len(before[y])] == x
    fresh = source['vertices'] + 1
    after = {v: list(ns) for v, ns in before.items()}
    after[a][after[a].index(b)] = fresh
    after[b][after[b].index(a)] = fresh
    after[c].insert(after[c].index(x) + 1, fresh)
    after[fresh] = [y, c, x]
    original_edges = {tuple(sorted((v, w))) for v, ns in before.items() for w in ns}
    new_edges = {tuple(sorted((v, w))) for v, ns in after.items() for w in ns}
    expected_edges = (original_edges - {tuple(sorted((a, b)))}) | {
        tuple(sorted((fresh, v))) for v in (a, b, c)}
    assert new_edges == expected_edges
    boundary = list(range(1, source['ring'] + 1))
    boundary.insert(boundary.index(a) + 1, fresh)
    return after, boundary, fresh


def cyclic(a, b):
    return len(a) == len(b) and any(a == b[i:] + b[:i] for i in range(len(b)))

def verify(adjacency, boundary, target, witness):
    other = rows(target)
    mapping = dict(witness['mapping'])
    assert set(mapping) == set(adjacency)
    assert sorted(mapping.values()) == sorted(other)
    orientation = witness['orientation']
    assert orientation in (1, -1)
    assert all(cyclic([mapping[w] for w in ns], other[mapping[v]][::orientation])
               for v, ns in adjacency.items())
    image = [mapping[v] for v in boundary]
    assert witness['boundary_image'] == image
    assert cyclic(image, list(range(1, target['ring'] + 1))[::orientation])


def negative_controls(adjacency, boundary, target, witness):
    bad_image = deepcopy(witness)
    bad_image['mapping'][0][1] = bad_image['mapping'][1][1]
    bad_orientation = deepcopy(witness)
    bad_orientation['orientation'] *= -1
    bad_boundary = deepcopy(witness)
    bad_boundary['boundary_image'][0], bad_boundary['boundary_image'][1] = (
        bad_boundary['boundary_image'][1], bad_boundary['boundary_image'][0])
    for bad in (bad_image, bad_orientation, bad_boundary):
        try:
            verify(adjacency, boundary, target, bad)
        except AssertionError:
            continue
        raise AssertionError('Corrupted map witness was accepted')


def compare(adjacency, boundary, target):
    other = rows(target)
    def graph(rs, bd):
        g = nx.Graph()
        g.add_nodes_from((v, {'boundary': v in bd}) for v in rs)
        g.add_edges_from((v, w) for v, ns in rs.items() for w in ns)
        return g
    matcher = nx.algorithms.isomorphism.GraphMatcher(
        graph(adjacency, boundary), graph(other, range(1, target['ring'] + 1)),
        node_match=lambda a,b: a['boundary'] == b['boundary'])
    for mapping in matcher.isomorphisms_iter():
        for orientation in (1, -1):
            if all(cyclic([mapping[w] for w in ns], other[mapping[v]][::orientation])
                   for v, ns in adjacency.items()):
                image = [mapping[v] for v in boundary]
                target_boundary = list(range(1, target['ring'] + 1))
                assert cyclic(image, target_boundary) or cyclic(image, target_boundary[::-1])
                return dict(mapping=[list(pair) for pair in sorted(mapping.items())], orientation=orientation,
                            boundary_image=image)
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--configurations', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert args.configurations.resolve() != args.output.resolve()
    start = time.monotonic()
    raw = args.configurations.read_bytes()
    assert sha256(raw).hexdigest() == EXPECTED_HASHES['configurations']
    sources = records(raw.decode())
    successes, attempts = [], 0
    for first, second in ((1,2), (2,4)):
        source, target = sources[first-1], sources[second-1]
        adjacency = rows(source)
        for a in range(1, source['ring'] + 1):
            b = a % source['ring'] + 1
            for c in range(source['ring'] + 1, source['vertices'] + 1):
                if c not in adjacency[a] or c not in adjacency[b]:
                    continue
                result = subdivide(source, a, b, c)
                if result is None:
                    continue
                attempts += 1
                after, boundary, fresh = result
                witness = compare(after, boundary, target)
                if witness is not None:
                    verify(after, boundary, target, witness)
                    negative_controls(after, boundary, target, witness)
                    successes.append(dict(source=first,target=second,triangle=[a,b,c],
                                          fresh=fresh,**witness))
    result = dict(evidence='Finite cyclic-map isomorphisms; not a Lean theorem.',
                  attempts=attempts,successes=successes,source_sha256=sha256(raw).hexdigest(),
                  verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                  negative_controls_rejected=3 * len(successes),
                  elapsed_seconds=round(time.monotonic()-start,3))
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    saved = json.loads(args.output.read_text())
    for witness in saved['successes']:
        source, target = sources[witness['source']-1], sources[witness['target']-1]
        adjacency, boundary, fresh = subdivide(source, *witness['triangle'])
        assert fresh == witness['fresh']
        verify(adjacency, boundary, target, witness)
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
