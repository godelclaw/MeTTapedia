#!/usr/bin/env python3
"""Find repeated embedded internal graphs in the pinned RSST catalogue.

This is geometric program evidence, not a reducibility proof. Cyclic order is
retained. Boundary contacts and original contracts remain attached to each
member; equality of internal templates does not identify the whole pieces.
"""

import argparse
from collections import Counter, defaultdict, deque
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import time

from configuration_map_isomorphism import EXPECTED_HASHES, records

if not __debug__:
    raise SystemExit('Run without Python optimization: assertions are audit checks.')


def core(source, orientation=1):
    vertices = set(range(source['ring'] + 1, source['vertices'] + 1))
    adjacency = {v: [w for u, w in source['darts'] if u == v]
                 for v in range(1, source['vertices'] + 1)}
    darts = [(v, w) for v, w in source['darts'] if v in vertices and w in vertices]
    ids = {d: i for i, d in enumerate(darts)}
    if not darts or {v for v, _ in darts} != vertices:
        raise ValueError('The internal graph has an isolated vertex')
    edge = [ids[w, v] for v, w in darts]
    rotation, contacts = [], []
    for v, w in darts:
        row = adjacency[v]
        position = row.index(w)
        gap = []
        for offset in range(1, len(row) + 1):
            neighbour = row[(position + orientation * offset) % len(row)]
            if neighbour in vertices:
                rotation.append(ids[v, neighbour])
                contacts.append(gap)
                break
            gap.append(neighbour)
        else:
            raise AssertionError('The next internal dart is missing')
    assert sorted(edge) == sorted(rotation) == list(range(len(darts)))
    contract = {tuple(sorted(pair)) for pair in source['contract']}
    flags = [tuple(sorted(pair)) in contract for pair in darts]
    external_contract = [list(pair) for pair in source['contract']
                         if not set(pair) <= vertices]
    return dict(darts=darts, edge=edge, rotation=rotation, contacts=contacts,
                contract=flags, external_contract=external_contract,
                vertex_count=len(vertices))


def rooted(data, start):
    order, numbering = [], {}
    pending = deque([start])
    while pending:
        dart = pending.popleft()
        if dart in numbering:
            continue
        numbering[dart] = len(order)
        order.append(dart)
        pending.extend((data['edge'][dart], data['rotation'][dart]))
    if len(order) != len(data['darts']):
        raise ValueError('The internal graph is disconnected')
    topology = tuple((numbering[data['edge'][dart]], numbering[data['rotation'][dart]])
                     for dart in order)
    gaps = tuple(len(data['contacts'][dart]) for dart in order)
    contracts = tuple(data['contract'][dart] for dart in order)
    return ((topology, gaps, contracts),
            [numbering[d] for d in range(len(order))], order)


def canonical(source):
    selected = None
    for orientation in (1, -1):
        data = core(source, orientation)
        for start in range(len(data['darts'])):
            key, numbering, order = rooted(data, start)
            candidate = (key, orientation, start, numbering, order)
            if selected is None or candidate[:3] < selected[:3]:
                selected = candidate
    key, orientation, start, numbering, order = selected
    data = core(source, orientation)
    topology, gaps, contracts = key
    vertex_map = {}
    for dart in order:
        vertex = data['darts'][dart][0]
        if vertex not in vertex_map:
            vertex_map[vertex] = len(vertex_map)
    edges = sorted({tuple(sorted((vertex_map[v], vertex_map[w])))
                    for v, w in data['darts']})
    contacts = [data['contacts'][d] for d in order]
    source_degrees = Counter(v for v, _ in source['darts'])
    degrees = [source_degrees[v] for v in sorted(vertex_map, key=vertex_map.get)]
    return dict(topology=topology, gaps=gaps, contract_flags=contracts,
                orientation=orientation, source_to_canonical_dart=numbering,
                source_vertex_to_canonical=sorted(vertex_map.items()),
                internal_vertices=len(vertex_map), internal_edges=edges,
                full_vertex_degrees=degrees, boundary_contacts=contacts,
                external_contract=data['external_contract'])


def verify(source, witness):
    """Check a saved witness directly against the full cyclic adjacency rows."""
    n = len(witness['source_to_canonical_dart'])
    number = witness['source_to_canonical_dart']
    assert witness['orientation'] in (-1, 1)
    assert sorted(number) == list(range(n))
    vertices = dict(witness['source_vertex_to_canonical'])
    assert witness['internal_vertices'] == len(vertices)
    assert sorted(vertices) == list(range(source['ring'] + 1, source['vertices'] + 1))
    assert sorted(vertices.values()) == list(range(len(vertices)))
    darts = [(v, w) for v, w in source['darts'] if v in vertices and w in vertices]
    assert len(darts) == n
    ids = {dart: i for i, dart in enumerate(darts)}
    selected_contract = {frozenset(pair) for pair in source['contract']}
    for i, (v, w) in enumerate(darts):
        j = number[i]
        assert witness['topology'][j][0] == number[ids[w, v]]
        row = [b for a, b in source['darts'] if a == v]
        position = row.index(w)
        boundary = []
        for offset in range(1, len(row) + 1):
            u = row[(position + witness['orientation'] * offset) % len(row)]
            if u in vertices:
                assert witness['topology'][j][1] == number[ids[v, u]]
                break
            boundary.append(u)
        assert witness['boundary_contacts'][j] == boundary
        assert witness['gaps'][j] == len(boundary)
        assert witness['contract_flags'][j] == (frozenset((v, w)) in selected_contract)
        assert witness['full_vertex_degrees'][vertices[v]] == len(row)
    assert {tuple(edge) for edge in witness['internal_edges']} == {
        tuple(sorted((vertices[v], vertices[w]))) for v, w in darts}
    assert witness['external_contract'] == [list(pair) for pair in source['contract']
                                            if not set(pair) <= vertices.keys()]


def reject(source, witness):
    try:
        verify(source, witness)
    except AssertionError:
        return True
    return False


def negative_controls(source, witness):
    corruptions = {}
    bad = deepcopy(witness)
    bad['source_to_canonical_dart'][0] = bad['source_to_canonical_dart'][1]
    corruptions['duplicate_dart_image'] = bad
    bad = deepcopy(witness)
    bad['topology'] = [list(row) for row in bad['topology']]
    bad['topology'][0][0] = 0
    corruptions['wrong_edge'] = bad
    bad = deepcopy(witness)
    bad['gaps'] = list(bad['gaps'])
    bad['gaps'][0] += 1
    corruptions['wrong_gap'] = bad
    bad = deepcopy(witness)
    bad['contract_flags'] = list(bad['contract_flags'])
    bad['contract_flags'][0] = not bad['contract_flags'][0]
    corruptions['wrong_contract'] = bad
    bad = deepcopy(witness)
    bad['external_contract'].append([1, 1])
    corruptions['spurious_external_contract'] = bad
    for kind, bad in corruptions.items():
        assert reject(source, bad), kind
    return list(corruptions)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--configurations', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert args.configurations.resolve() != args.output.resolve(), 'Output must differ from input'
    start = time.monotonic()
    raw = args.configurations.read_bytes()
    assert sha256(raw).hexdigest() == EXPECTED_HASHES['configurations']
    sources = records(raw.decode())
    assert len(sources) == 633
    groups = defaultdict(list)
    checked = []
    rejected = Counter()
    for i, source in enumerate(sources):
        witness = canonical(source)
        verify(source, witness)
        rejected.update(negative_controls(source, witness))
        topology = witness['topology']
        key = sha256(json.dumps(topology).encode()).hexdigest()
        row = dict(ordinal=i + 1, name=source['name'], ring=source['ring'],
                   source_residual=source['residual'], template=key, witness=witness)
        checked.append(row)
        groups[key].append(row)
    result = []
    for key, members in groups.items():
        first = members[0]['witness']
        assert all(m['witness']['topology'] == first['topology'] for m in members)
        result.append(dict(template=key, count=len(members),
            internal_vertices=first['internal_vertices'],
            internal_edges=first['internal_edges'],
            ordinals=[m['ordinal'] for m in members],
            rings=dict(sorted(Counter(m['ring'] for m in members).items())),
            zero_residual_count=sum(m['source_residual'] == 0 for m in members),
            original_internal_contract_counts=dict(sorted(Counter(
                sum(m['witness']['contract_flags'])//2 for m in members).items())),
            has_external_contract=any(m['witness']['external_contract'] for m in members)))
    result.sort(key=lambda r: (-r['count'], r['internal_vertices'], r['template']))
    report = dict(evidence='Program classification with saved dart-isomorphism witnesses; no reducibility claim.',
        source_sha256=sha256(raw).hexdigest(), configurations=len(sources),
        classifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        templates=len(groups), repeated_templates=sum(len(g)>1 for g in groups.values()),
        grouping='Induced internal graph with cyclic order, up to global reflection. Boundary contacts and contracts remain member-specific.',
        configuration_removal_credit=0, groups=result, members=checked,
        negative_controls_rejected=dict(rejected),
        elapsed_seconds=round(time.monotonic()-start, 3))
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    saved = json.loads(args.output.read_text())
    for source, row in zip(sources, saved['members']):
        verify(source, row['witness'])
    print(json.dumps({k:v for k,v in report.items() if k not in ('groups','members')}))


if __name__ == '__main__':
    main()
