#!/usr/bin/env python3
"""Compare RSST free completions with decoded Lean construction programs.

This finite-array mirror follows FourColor.CfMap and FourColor.CfContract from
Chris Emery's MIT-licensed port (copyright 2026 Chris Emery). The full MIT
notice and Gonthier/Werner attribution are retained in
lean/fourcolor-classical/LICENSE. The original mathematics is due to Robertson,
Sanders, Seymour and Thomas; Gonthier and Werner supplied the formal reference.

The graph comparison retains cyclic order, the outer ring and, where supplied
in the original data, contracted edges. It permits a global orientation reversal.
This is program evidence: equivalence of the mirror and Lean's noncomputable
map decoder is not proved here. No reducibility or colourability is inferred.
"""

import argparse
from collections import Counter, deque
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import time

if not __debug__:
    raise SystemExit('Run without Python optimization: assertions are audit checks.')

INVENTORY_SOURCE = Path(__file__).resolve().parent.parent/'classical_source_inventory.py'
spec = importlib.util.spec_from_file_location('inventory', INVENTORY_SOURCE)
inventory = importlib.util.module_from_spec(spec)
spec.loader.exec_module(inventory)

EXPECTED_HASHES = {
    'configurations': '1c92fc280a9b384f736b94077fc59aac75e3d830d441ffd2d18683ee4b524e84',
    'lean_programs': '7a05039e76944dd51616721039edb872ccb2f1a6d90fa8b93ef4834095760966',
    'lean_geometry': 'a4cc5372a705b583a6ed4d96349cbe3fbf41b5c5e0dee73917b52f472c648301',
    'lean_contract': '5de89d9a2d83b41f6320c812e5a805d2ec5557af7228397c3adcae39cb5acca7',
}


def inverse(p):
    assert sorted(p) == list(range(len(p)))
    q = [None] * len(p)
    for x, y in enumerate(p):
        q[y] = x
    return q


def cycle(p, x):
    result, y = [], x
    while y not in result:
        result.append(y)
        y = p[y]
    assert y == x
    return result


def classes(p):
    ids, orbits = [None] * len(p), []
    for x in range(len(p)):
        if ids[x] is None:
            orbit = cycle(p, x)
            for y in orbit:
                assert ids[y] is None
                ids[y] = len(orbits)
            orbits.append(orbit)
    return ids, orbits


def extension(edge, node, face, point, kind):
    size = len(edge)
    x, xe = size, size + 1
    e = edge + [xe, x]
    nx = node[point]
    if kind == 'U':
        n = [x if y == nx else node[y] for y in range(size)] + [xe, node[nx]]
        f = [xe if face[y] == nx else face[y] for y in range(size)] + [x, nx]
    else:
        assert kind == 'N'
        ni = inverse(node)
        px = ni[point]
        n = [xe if y == point else x if node[node[y]] == point else node[y]
             for y in range(size)] + [x if px == nx else nx, px]
        f = [xe if y == edge[px] else x if y == edge[nx] else face[y]
             for y in range(size)] + [point, x if px == nx else ni[px]]
    for p in e, n, f:
        inverse(p)
    assert all(n[f[e[y]]] == y for y in range(size + 2))
    return e, n, f, x


def decode(program):
    edge, node, face, point = [1, 0], [1, 0], [0, 1], 1
    contracts = []
    for index, step in enumerate(reversed(program)):
        if step[0] == 'R':
            ni = inverse(node)
            # All source rotations are within the ring; no overflow convention.
            assert step[1] < len(cycle(node, point))
            for _ in range(step[1]):
                point = ni[point]
        else:
            assert step[0] in ('Y', 'H')
            feet = [node[point], point]
            for kind in ('UN' if step[0] == 'Y' else 'UNN'):
                edge, node, face, point = extension(edge, node, face, point, kind)
            if step[0] == 'H':
                contracts = [face[point], *feet, *contracts]
            elif index != 0:
                contracts = [feet[0], *contracts]
    ring = cycle(inverse(node), node[point])
    face_ids, faces = classes(face)
    nodes = classes(node)[1]
    assert all(len(c) == 3 or set(c) == set(ring) for c in nodes)
    assert len(faces) + len(nodes) - len(edge)//2 == 2
    boundary = [face_ids[d] for d in ring]
    assert len(set(boundary)) == len(boundary)
    return {'edge': edge, 'rotation': face, 'point': point,
            'boundary_faces': boundary, 'face_ids': face_ids,
            'contract_darts': contracts}


def records(text):
    validated = inventory.read_configurations(text)
    tokens = iter(text.split())
    result = []
    for name in tokens:
        count, ring, c, residual = [int(next(tokens)) for _ in range(4)]
        contract = [(int(next(tokens)), int(next(tokens))) for _ in range(int(next(tokens)))]
        adjacency = {}
        for _ in range(count):
            v, degree = int(next(tokens)), int(next(tokens))
            adjacency[v] = [int(next(tokens)) for _ in range(degree)]
        for _ in range(count):
            next(tokens)
        darts = [(v, w) for v, ns in adjacency.items() for w in ns]
        ids = {d: i for i, d in enumerate(darts)}
        edge = [ids[w, v] for v, w in darts]
        rotation = [ids[v, adjacency[v][(adjacency[v].index(w)+1) % len(adjacency[v])]]
                    for v, w in darts]
        result.append({'name': name, 'ring': ring, 'vertices': count, 'darts': darts,
                       'edge': edge, 'rotation': rotation, 'contract': contract,
                       'residual': residual, 'seed': ids[1, 2]})
    assert len(result) == len(validated)
    return result


def verify(source, target, orientation, mapping):
    assert orientation in (1, -1)
    size = len(source['edge'])
    assert len(target['edge']) == size
    assert sorted(mapping) == list(range(size))
    rotation = target['rotation'] if orientation == 1 else inverse(target['rotation'])
    for d in range(size):
        assert mapping[source['edge'][d]] == target['edge'][mapping[d]]
        assert mapping[source['rotation'][d]] == rotation[mapping[d]]
    vertex_map = {}
    for d, (v, w) in enumerate(source['darts']):
        face = target['face_ids'][mapping[d]]
        assert v not in vertex_map or vertex_map[v] == face
        vertex_map[v] = face
        assert face != target['face_ids'][target['edge'][mapping[d]]]
    assert len(set(vertex_map.values())) == source['vertices']
    source_ring = [vertex_map[v] for v in range(1, source['ring']+1)]
    target_ring = target['boundary_faces']
    assert len(target_ring) == source['ring']
    matches = [(sign, shift) for sign in (1, -1) for shift in range(source['ring'])
               if all(source_ring[k] == target_ring[(shift+sign*k) % source['ring']]
                      for k in range(source['ring']))]
    assert len(matches) == 1
    return {'vertex_to_decoded_face': [vertex_map[v] for v in range(1,source['vertices']+1)],
            'ring_direction': matches[0][0], 'ring_offset': matches[0][1]}


def isomorphism(source, target, selected_contract=None):
    size = len(source['edge'])
    if len(target['edge']) != size:
        return None
    source_ids, source_orbits = classes(source['rotation'])
    target_ids, target_orbits = classes(target['rotation'])
    source_degrees = [len(source_orbits[source_ids[d]]) for d in range(size)]
    target_degrees = [len(target_orbits[target_ids[d]]) for d in range(size)]
    if Counter(source_degrees) != Counter(target_degrees):
        return None
    seed = source['seed']
    sc = {d for d, pair in enumerate(source['darts'])
          if pair in source['contract'] or pair[::-1] in source['contract']}
    tc = set() if selected_contract is None else set(selected_contract)
    tc |= {target['edge'][d] for d in tc}
    if selected_contract is not None and len(sc) != len(tc):
        return None
    for orientation in (1, -1):
        tr = target['rotation'] if orientation == 1 else inverse(target['rotation'])
        for image in range(size):
            if source_degrees[seed] != target_degrees[image]:
                continue
            mapping, reverse = [None]*size, [None]*size
            pending = deque([(seed, image)])
            valid = True
            while pending:
                d, e = pending.popleft()
                if mapping[d] is not None:
                    if mapping[d] != e:
                        valid = False
                        break
                    continue
                if reverse[e] is not None or source_degrees[d] != target_degrees[e]:
                    valid = False
                    break
                if selected_contract is not None and (d in sc) != (e in tc):
                    valid = False
                    break
                mapping[d], reverse[e] = e, d
                pending.append((source['edge'][d], target['edge'][e]))
                pending.append((source['rotation'][d], tr[e]))
            if valid:
                assert None not in mapping
                checked = verify(source, target, orientation, mapping)
                return {'orientation': orientation, 'dart_mapping': mapping, **checked}
    return None


def cyclic_equal(left, right):
    return len(left) == len(right) and any(
        left == right[k:] + right[:k] for k in range(len(right)))


def verify_rows(source, target, witness, selected_contract=None):
    """Check quotient cyclic adjacency independently of the dart propagation."""
    vertex_map = witness['vertex_to_decoded_face']
    assert len(vertex_map) == source['vertices']
    assert len(set(vertex_map)) == len(vertex_map)
    face_ids, face_cycles = classes(target['rotation'])
    assert len(face_cycles) == len(vertex_map)
    assert sorted(vertex_map) == list(range(len(face_cycles)))
    assert witness['orientation'] in (1, -1)
    assert witness['ring_direction'] in (1, -1)
    assert 0 <= witness['ring_offset'] < source['ring']
    for v in range(1, source['vertices'] + 1):
        neighbours = [w for u, w in source['darts'] if u == v]
        expected = [vertex_map[w-1] for w in neighbours]
        actual = [face_ids[target['edge'][d]] for d in face_cycles[vertex_map[v-1]]]
        if witness['orientation'] == -1:
            actual.reverse()
        assert cyclic_equal(expected, actual)
    boundary = target['boundary_faces']
    observed = [boundary[(witness['ring_offset'] + witness['ring_direction']*k)
                         % len(boundary)] for k in range(source['ring'])]
    assert vertex_map[:source['ring']] == observed
    if selected_contract is not None:
        expected = {tuple(sorted((vertex_map[v-1], vertex_map[w-1])))
                    for v, w in source['contract']}
        actual = {tuple(sorted((face_ids[d], face_ids[target['edge'][d]])))
                  for d in selected_contract}
        assert len(actual) == len(selected_contract)
        assert expected == actual


def rejects(action):
    try:
        action()
    except AssertionError:
        return True
    return False


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for field in EXPECTED_HASHES:
        parser.add_argument('--'+field.replace('_', '-'), type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--witnesses', type=Path, required=True)
    args = parser.parse_args()
    inputs = {getattr(args, field).resolve() for field in EXPECTED_HASHES}
    outputs = {args.output.resolve(), args.witnesses.resolve()}
    assert len(outputs) == 2 and not inputs & outputs, 'Outputs must be separate from inputs'
    start = time.monotonic()
    hashes = {}
    for field, expected in EXPECTED_HASHES.items():
        digest = sha256(getattr(args, field).read_bytes()).hexdigest()
        assert digest == expected, f'{field}: differs from the pinned source'
        hashes[field] = digest
    hashes['audit_program'] = sha256(Path(__file__).read_bytes()).hexdigest()
    hashes['inventory_program'] = sha256(INVENTORY_SOURCE.read_bytes()).hexdigest()
    sources = records(args.configurations.read_text())
    programs = inventory.read_lean_programs(args.lean_programs.read_text())
    assert len(sources) == len(programs) == 633
    output = []
    contract_count = 0
    controls = Counter()
    for i, (source, (_, indices, program)) in enumerate(zip(sources, programs), 1):
        target = decode(program)
        witness = isomorphism(source, target)
        assert witness is not None, f'Configuration {i}: map mismatch'
        verify_rows(source, target, witness)
        selected = None
        if source['residual']:
            assert all(0 <= j < len(target['contract_darts']) for j in indices)
            selected = [target['contract_darts'][j] for j in indices]
            witness = isomorphism(source, target, selected)
            assert witness is not None, f'Configuration {i}: contract mismatch'
            verify_rows(source, target, witness, selected)
            contract_count += 1
            assert rejects(lambda: verify_rows(source, target, witness, selected[:-1]))
            controls['missing_contract_edge_rejected'] += 1
        else:
            assert not source['contract']
        broken = witness['dart_mapping'].copy()
        broken[0], broken[1] = broken[1], broken[0]
        assert rejects(lambda: verify(source, target, witness['orientation'], broken))
        controls['swapped_dart_images_rejected'] += 1
        assert rejects(lambda: verify(source, target, -witness['orientation'],
                                      witness['dart_mapping']))
        controls['wrong_orientation_rejected'] += 1
        broken_row = dict(witness)
        broken_row['vertex_to_decoded_face'] = witness['vertex_to_decoded_face'].copy()
        broken_row['vertex_to_decoded_face'][0] = broken_row['vertex_to_decoded_face'][1]
        assert rejects(lambda: verify_rows(source, target, broken_row, selected))
        controls['duplicate_vertex_image_rejected'] += 1
        output.append({'configuration': i, 'source_name': source['name'],
                       'ring_size': source['ring'], 'darts': len(source['edge']),
                       'contract_compared': selected is not None, **witness})
    assert contract_count == 384
    saved = {'source_sha256': hashes, 'records': output}
    args.witnesses.write_text(json.dumps(saved, indent=2)+'\n')
    # Re-read the actual saved evidence and check both conditions again.
    reloaded = json.loads(args.witnesses.read_text())
    assert reloaded['source_sha256'] == hashes
    assert len(reloaded['records']) == 633
    for i, (source, (_, indices, program), record) in enumerate(zip(
            sources, programs, reloaded['records']), 1):
        target = decode(program)
        assert record['configuration'] == i and record['source_name'] == source['name']
        checked = verify(source, target, record['orientation'], record['dart_mapping'])
        assert all(record[k] == v for k, v in checked.items())
        selected = [target['contract_darts'][j] for j in indices] if source['residual'] else None
        verify_rows(source, target, record, selected)
    result = {
        'verification': 'Program-checked embedded map and contraction correspondence',
        'reference_revision': '3db71e0a786a1f19be04c5266fe3d06fed216885',
        'configurations': len(output),
        'all_isomorphic': True,
        'matched_darts': sum(r['darts'] for r in output),
        'contract_sets_compared': contract_count,
        'zero_residual_cases_without_original_contract': 633-contract_count,
        'orientation_histogram': dict(sorted(Counter(r['orientation'] for r in output).items())),
        'negative_controls': dict(controls),
        'source_sha256': hashes,
        'witnesses_sha256': sha256(args.witnesses.read_bytes()).hexdigest(),
        'saved_witnesses_rechecked': True,
        'seconds': round(time.monotonic()-start, 3),
        'scope': ['Complete dart bijections commute with edge reversal and vertex rotation.',
                  'A global reversal of orientation is permitted.',
                  'The specified outer ring is preserved up to cyclic shift and reversal.',
                  'Cyclic adjacency rows are checked separately on the face quotient.',
                  'All 384 nonzero-residual contraction edge sets are preserved.'],
        'limitations': ['The finite-array mirror is not proved equivalent to the Lean decoder.',
                        'The 249 zero-residual cases have no original contraction to compare.',
                        'No header colour counts, reducibility or discharging claims are checked.',
                        'No kernel theorem or compression credit results from this program audit.'],
    }
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
