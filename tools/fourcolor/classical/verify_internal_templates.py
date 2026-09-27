"""Independently check template classes using vertex graph isomorphisms.

The classifier uses rooted dart traversals. This check enumerates vertex
isomorphisms instead, and then checks all cyclic neighbour orders with one
global orientation. It does not inspect the classifier's dart witnesses.
"""

import argparse
from hashlib import sha256
import json
from pathlib import Path
import time

import networkx as nx

from configuration_map_isomorphism import EXPECTED_HASHES, records

if not __debug__:
    raise SystemExit('Run without Python optimization: assertions are audit checks.')


def prepare(source):
    vertices = set(range(source['ring'] + 1, source['vertices'] + 1))
    rows = {v: [w for a, w in source['darts'] if a == v and w in vertices]
            for v in vertices}
    graph = nx.Graph()
    graph.add_nodes_from(vertices)
    graph.add_edges_from((v, w) for v, row in rows.items() for w in row)
    signature = (len(vertices), graph.number_of_edges(),
                 tuple(sorted(dict(graph.degree()).values())))
    return graph, rows, signature


def cyclic(left, right):
    return len(left) == len(right) and any(left == right[i:] + right[:i]
                                         for i in range(len(right)))


def equivalent(left, right):
    g, rows, signature = left
    h, target, other_signature = right
    if signature != other_signature:
        return False
    matcher = nx.algorithms.isomorphism.GraphMatcher(g, h)
    for mapping in matcher.isomorphisms_iter():
        for orientation in (1, -1):
            if all(cyclic([mapping[w] for w in row], target[mapping[v]][::orientation])
                   for v, row in rows.items()):
                return True
    return False


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--configurations', type=Path, required=True)
    parser.add_argument('--classification', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert args.output.resolve() not in {args.configurations.resolve(), args.classification.resolve()}
    start = time.monotonic()
    raw = args.configurations.read_bytes()
    assert sha256(raw).hexdigest() == EXPECTED_HASHES['configurations']
    sources = records(raw.decode())
    graphs = [prepare(s) for s in sources]
    report = json.loads(args.classification.read_text())
    assert report['source_sha256'] == sha256(raw).hexdigest()
    assert len(sources) == len(report['members']) == 633
    membership = {m['ordinal']: m['template'] for m in report['members']}
    assert sorted(membership) == list(range(1, 634))
    actual = {}
    for ordinal, key in membership.items():
        actual.setdefault(key, []).append(ordinal)
    assert report['configurations'] == len(sources)
    assert report['templates'] == len(actual)
    assert report['repeated_templates'] == sum(len(group) > 1 for group in actual.values())
    assert len(report['groups']) == len(actual)
    assert {g['template']: sorted(g['ordinals']) for g in report['groups']} == {
        key: sorted(group) for key, group in actual.items()}
    assert all(g['count'] == len(g['ordinals']) for g in report['groups'])
    positives = 0
    representatives = []
    for key, group in actual.items():
        first = group[0] - 1
        representatives.append(first)
        for ordinal in group:
            assert equivalent(graphs[first], graphs[ordinal - 1]), (key, ordinal)
            positives += 1
    negatives = 0
    for i, first in enumerate(representatives):
        for second in representatives[i + 1:]:
            assert not equivalent(graphs[first], graphs[second]), (first + 1, second + 1)
            negatives += 1
    out = dict(status='passed', evidence='Independent finite program check; not a Lean theorem.',
               method='Vertex graph isomorphisms with all cyclic orders and a single global orientation.',
               configurations=len(sources), templates=len(actual),
               within_template_comparisons=positives, between_template_comparisons=negatives,
               networkx_version=nx.__version__,
               source_sha256=sha256(raw).hexdigest(),
               classification_sha256=sha256(args.classification.read_bytes()).hexdigest(),
               verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
               elapsed_seconds=round(time.monotonic() - start, 3))
    args.output.write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps(out))


if __name__ == '__main__':
    main()
