#!/usr/bin/env python3
"""Replay the actual pentagon/lobe patch and its joint six-port repair.

This program checks geometry, primal/dual colouring correspondence and the
finite boundary calculation independently of Lean. PentagonalLobePatch.lean
proves repair for the literal dual graph and every Kempe-closed predicate.
PentagonalLobeTangle.lean reconstructs actual open-tangle colourings and glues
them into compatible exteriors. Recognition of extracted embedded lobes and
deriving exterior closure from geometry remain separate obligations.
"""

import argparse
from collections import deque
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import re
import sys

import networkx as nx

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from alternating_lobe_probe import data, inspect
from diamond_coloring_alternatives import colorings as vertex_colourings, support
from probe_diamond_disk_replacements import verify_disk
from probe_diamond_kempe import PERMS, apply_perm, closure, system
from v24_deletion_orbit_gate import colorings as edge_colourings

if not __debug__:
    raise SystemExit('Run without Python optimization: assertions are audit checks.')


def extract(raw):
    graph, alpha, _, faces = data(raw['rotation'])
    lobe = inspect(raw)['shortest_lobe']['vertices']
    if len(lobe) != 11:
        return None
    components = list(nx.connected_components(graph.subgraph(set(graph) - set(lobe))))
    candidates = [c for c in components if len(c) == 5 and
                  all(graph.subgraph(c).degree(v) == 2 for v in c)]
    assert len(candidates) == 1
    inner = candidates[0]
    patch = set(lobe) | inner
    ports = [(v, w) for v in lobe for w in graph[v] if w not in patch]
    assert len(ports) == 6 and len({w for _, w in ports}) == 6
    face_of = {d: i for i, face in enumerate(faces) for d in face}
    sides = [{face_of[d], face_of[alpha[d]]} for d in ports]
    assert all(len(sides[i - 1] & sides[i]) == 1 for i in range(6))
    boundary = [next(iter(sides[i - 1] & sides[i])) for i in range(6)]
    inside = [i for i, face in enumerate(faces) if all(d[0] in patch for d in face)]
    assert len(set(boundary)) == 6 and len(inside) == 6 and not set(boundary) & set(inside)
    assert all(sides[i] == {boundary[i], boundary[(i + 1) % 6]} for i in range(6))
    labels = boundary + inside
    index = {v: i for i, v in enumerate(labels)}
    primal = sorted(tuple(sorted(e)) for e in graph.edges() if set(e) & patch)
    dual_of = {e: tuple(sorted((index[face_of[e]], index[face_of[e[::-1]]]))) for e in primal}
    dual = sorted(dual_of.values())
    assert len(primal) == len(set(dual)) == 27
    triangles = sorted(tuple(sorted(index[face_of[v, w]] for w in graph[v])) for v in patch)
    adjacency = verify_disk(6, 6, triangles)
    assert sorted((u, v) for u in adjacency for v in adjacency[u] if u < v) == dual
    return dict(id=raw['id'], lobe=lobe, pentagon=sorted(inner),
                patch_vertices=sorted(patch), ports=ports, dual_face_indices=labels,
                primal_edges=primal, dual_edges=dual, triangles=triangles), adjacency, dual_of


@lru_cache(None)
def trees(leaves):
    if len(leaves) == 1:
        return (leaves[0],)
    return tuple((a, b) for i in range(1, len(leaves))
                 for a in trees(leaves[:i]) for b in trees(leaves[i:]))


def tree_support(tree):
    edges, count = [], [6]
    def walk(t):
        if isinstance(t, int):
            return t
        v = count[0]
        count[0] += 1
        for child in t:
            edges.append((v, walk(child)))
        return v
    root = walk(tree)
    edges.append((0, root))
    edges = sorted(tuple(sorted(e)) for e in edges)
    ports = [next(i for i, e in enumerate(edges) if j in e) for j in range(6)]
    return {tuple(c[i] + 1 for i in ports) for c in edge_colourings(count[0], edges)}


def correspondence(source, target):
    left, right = nx.Graph(source['dual_edges']), nx.Graph(target['dual_edges'])
    for graph in (left, right):
        nx.set_node_attributes(graph, {v: v < 6 for v in graph}, 'boundary')
    matcher = nx.algorithms.isomorphism.GraphMatcher(
        left, right, node_match=lambda a, b: a['boundary'] == b['boundary'])
    for mapping in matcher.isomorphisms_iter():
        for sign in (1, -1):
            if all(mapping[i] == (mapping[0] + sign * i) % 6 for i in range(6)):
                assert sorted(tuple(sorted((mapping[u], mapping[v]))) for u, v in source['dual_edges']) == target['dual_edges']
                assert sorted(tuple(sorted(mapping[v] for v in t)) for t in source['triangles']) == target['triangles']
                return dict(mapping=[mapping[i] for i in range(12)], orientation=sign)
    raise AssertionError('Extracted patch differs from the literal disk, including its ordered ring.')


def read_string(text, name):
    match = re.search(r'def ' + name + r' : String :=\s*("(?:[^"\\]|\\.)*")', text)
    assert match, name
    return json.loads(match[1])


def check_tangle(raw, patch, source):
    """Compare every literal half-edge and rotation with the extracted piece."""
    _, _, rho, faces = data(raw['rotation'])
    vertices = patch['patch_vertices']
    inside = set(vertices)
    internal = [tuple(e) for e in patch['primal_edges'] if set(e) <= inside]
    darts = [d for e in internal for d in (e, e[::-1])] + list(map(tuple, patch['ports']))
    assert len(internal) == 21 and len(darts) == 48
    face_of = {d: i for i, face in enumerate(faces) for d in face}
    face_index = {f: i for i, f in enumerate(patch['dual_face_indices'])}
    tables = dict(
        vertexCodes=[vertices.index(u) for u, _ in darts],
        rotationCodes=[darts.index(rho[d]) for d in darts],
        leftCodes=[face_index[face_of[d]] for d in darts],
        rightCodes=[face_index[face_of[d[::-1]]] for d in darts],
        alphaCodes=[i ^ 1 for i in range(42)])
    tables['inverseCodes'] = [tables['rotationCodes'].index(i) for i in range(48)]
    text = source.read_text()
    for name, values in tables.items():
        assert read_string(text, name) == ''.join(chr(65 + v) for v in values), name
    assert tables['leftCodes'][42:] == list(range(6))
    assert tables['rightCodes'][42:] == [1, 2, 3, 4, 5, 0]
    return dict(vertices=16, internal_edges=21, boundary_half_edges=6,
                darts=48, all_tables_match_extracted_rotation=True)


def run(fixtures, lean_source, tangle_source):
    maps = json.loads(fixtures.read_text())['maps']
    extracted = [result for raw in maps if (result := extract(raw)) is not None]
    patch, adjacency, dual_of = next(r for r in extracted if r[0]['id'] == 'C30-plantri-1')
    keys, colours = vertex_colourings(adjacency)
    good = support(keys, colours, list(range(6)))
    original = patch['primal_edges']
    vertices = sorted({v for e in original for v in e})
    index = {v: i for i, v in enumerate(vertices)}
    states = edge_colourings(len(vertices), [(index[u], index[v]) for u, v in original])
    potentials = set()
    for c in states:
        edge_values = {dual_of[e]: value + 1 for e, value in zip(original, c)}
        value, queue = {0: 0}, deque([0])
        while queue:
            u = queue.popleft()
            for v in sorted(adjacency[u]):
                candidate = value[u] ^ edge_values[tuple(sorted((u, v)))]
                if v in value:
                    assert value[v] == candidate
                else:
                    value[v] = candidate
                    queue.append(v)
        assert len(value) == 12
        potentials.add(tuple(value[i] for i in keys))
    assert potentials == colours and len(states) == len(colours)
    port_indices = [original.index(tuple(sorted(e))) for e in patch['ports']]
    assert {tuple(c[i] + 1 for i in port_indices) for c in states} == good
    universe, grams = system(6)
    bad, stages, _ = closure(universe, grams, good)
    assert not bad
    canon = lambda w: min(apply_perm(w, p) for p in PERMS)
    terminals = sorted({canon(w) for w in good})
    reps = sorted({canon(w) for w in universe})
    text = lean_source.read_text()
    read = lambda name: read_string(text, name)
    assert read('adjacency') == ''.join('1' if j in adjacency[i] else '0' for i in range(12) for j in range(12))
    code = lambda w: ''.join(map(str, w))
    assert read('terminalCodes').split() == list(map(code, terminals))
    assert read('allCodes').split() == list(map(code, reps))
    witnesses = [tuple(map(int, s)) for s in read('colouringCodes').split()]
    assert len(witnesses) == len(terminals)
    for w, c in zip(terminals, witnesses):
        assert c in colours and tuple(c[i] ^ c[(i + 1) % 6] for i in range(6)) == w
    tree_results = [dict(tree=tree, unsupported_words=len(tree_support(tree) - good))
                    for tree in trees(tuple(range(1, 6)))]
    assert len(tree_results) == 14 and all(r['unsupported_words'] > 0 for r in tree_results)
    literal = check_tangle(next(r for r in maps if r['id'] == patch['id']), patch, tangle_source)
    return dict(
        evidence='Independent program checks. The literal boundary repair has a separate Lean proof.',
        fixtures_sha256=hashlib.sha256(fixtures.read_bytes()).hexdigest(),
        lean_source_sha256=hashlib.sha256(lean_source.read_bytes()).hexdigest(),
        tangle_source_sha256=hashlib.sha256(tangle_source.read_bytes()).hexdigest(),
        literal_tangle=literal,
        patch=patch, primal_colourings=len(states), normalized_dual_colourings=len(colours),
        supported_words=len(good), admissible_words=len(universe),
        terminal_colour_permutation_classes=len(terminals), input_classes=len(reps),
        obstruction_rounds=stages,
        disk_replacements=tree_results,
        recognized_instances=[dict(id=r['id'], lobe=r['lobe'], pentagon=r['pentagon'],
                                   **correspondence(r, patch)) for r, _, _ in extracted],
        limits=['Ambient recognition remains program evidence; literal graph-to-tangle reconstruction has a separate Lean theorem.',
                'Deriving the exterior Kempe-closure hypothesis from embedding geometry remains open for this consumer.',
                'No strict closed-map replacement, universal coverage or catalogue savings are established.',
                'The boundary proof retains finite terminal witnesses and nine finite answer-cover checks.'])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fixtures', type=Path,
                        default=Path(__file__).with_name('alternating-lobe-fixtures.json'))
    parser.add_argument('--lean-source', type=Path,
                        default=Path(__file__).resolve().parents[3] /
                        'lean/fourcolor-classical/MettapediaFourColor/PentagonalLobePatch.lean')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--tangle-source', type=Path,
                        default=Path(__file__).resolve().parents[3] /
                        'lean/fourcolor-classical/MettapediaFourColor/PentagonalLobeTangle.lean')
    args = parser.parse_args()
    if args.output.resolve() in {args.fixtures.resolve(), args.lean_source.resolve(),
                                args.tangle_source.resolve(), Path(__file__).resolve()}:
        parser.error('The output must not overwrite an input.')
    result = run(args.fixtures, args.lean_source, args.tangle_source)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('supported_words', 'admissible_words', 'obstruction_rounds')}))
