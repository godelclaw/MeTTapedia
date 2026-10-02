#!/usr/bin/env python3
"""Search small spherical triangulations for actual adjacent flat 8-8 pairs.

This is exploratory evidence, not a Lean certificate. Each graph is built
from a subdivided icosahedron by legal oriented edge flips. Rule readings
retain all degree bounds, cyclic steps and shared ambient vertex identities.
"""

import argparse
from collections import Counter, deque
from hashlib import sha256
import json
from pathlib import Path
import random

from generate_rule_traces import compile_traces


def initial_faces():
    import networkx as nx

    graph = nx.icosahedral_graph()
    planar, embedding = nx.check_planarity(graph)
    if not planar:
        raise ValueError('Initial graph is not planar')
    seen, faces = set(), []
    for a, b in embedding.edges():
        if (a, b) not in seen:
            f = embedding.traverse_face(a, b)
            assert len(f) == 3
            seen.update(zip(f, f[1:] + f[:1]))
            faces.append(tuple(f))
    mid = {tuple(sorted(e)): i + 12 for i, e in enumerate(sorted(graph.edges()))}
    result = []
    for a, b, c in faces:
        ab, bc, ca = (mid[tuple(sorted(e))] for e in [(a, b), (b, c), (c, a)])
        result += [(a, ab, ca), (b, bc, ab), (c, ca, bc), (ab, bc, ca)]
    return result


def geometry(faces):
    darts, neighbors, nexts, prevs = {}, {}, {}, {}
    for i, (a, b, c) in enumerate(faces):
        for u, v, w in [(a, b, c), (b, c, a), (c, a, b)]:
            assert (u, v) not in darts
            darts[u, v] = (i, w)
            neighbors.setdefault(u, set()).add(v)
            nexts[u, v] = w
            prevs[u, w] = v
    for u, vs in neighbors.items():
        start = min(vs)
        cycle, v = [], start
        while v not in cycle:
            cycle.append(v)
            v = nexts[u, v]
        assert v == start and set(cycle) == vs
    assert len(neighbors) - len(darts) // 2 + len(faces) == 2
    return darts, neighbors, nexts, prevs


def read_rules(here):
    manifest = json.loads((here / 'discharging-sources.json').read_text())
    rules = []
    for item in manifest['files']:
        raw = (here / 'discharging-rules' / item['file']).read_bytes()
        assert sha256(raw).hexdigest() == item['sha256']
        data = [[int(x) for x in row.split()] for row in raw.decode().splitlines() if row.strip()]
        rules.append((item['file'], data, compile_traces(data)))
    return rules, manifest['revision']


def reading(rule, u, v, neighbors, nexts, prevs):
    _, data, traces = rule
    degree = lambda x: len(neighbors[x])
    sender, receiver = data[0][1:3]
    for row, image in [(data[sender], u), (data[receiver], v)]:
        if not (row[1] <= degree(image) and (row[2] == 0 or degree(image) <= row[2])):
            return None
    images = []
    for trace in traces:
        a, b = u, v
        for op, _, _ in trace:
            if op == 0:
                a, b = b, a
            elif op == 1:
                b = nexts[a, b]
            else:
                b = prevs[a, b]
        images.append(a)
    if [images[sender - 1], images[receiver - 1]] != [u, v]:
        return None
    for i, lower, upper, *row in data[1:]:
        a = images[i - 1]
        if not (lower <= degree(a) and (upper == 0 or degree(a) <= upper)):
            return None
        for j in row:
            if j != -1 and images[j - 1] not in neighbors[a]:
                return None
        for j, k in zip(row, row[1:] + row[:1]):
            if j != -1 and k != -1 and nexts[a, images[j - 1]] != images[k - 1]:
                return None
    return images


def breadth_first_reading(data, u, v, neighbors, nexts, prevs):
    """Independent rooted propagation, without using compiled vertex traces."""
    n, sender, receiver, _ = data[0]
    rows = {i: (lower, upper, row) for i, lower, upper, *row in data[1:]}
    queue = deque([((sender, receiver), (u, v))])
    images, darts = {}, {}
    while queue:
        (a, b), (x, y) = queue.popleft()
        if (a, b) in darts:
            if darts[a, b] != (x, y):
                return None
            continue
        if y not in neighbors[x] or (a in images and images[a] != x):
            return None
        lower, upper, row = rows[a]
        if len(neighbors[x]) < lower or (upper and len(neighbors[x]) > upper):
            return None
        images[a], darts[a, b] = x, (x, y)
        queue.append(((b, a), (y, x)))
        index = row.index(b)
        for offset, operation in [(1, nexts), (-1, prevs)]:
            c = row[(index + offset) % len(row)]
            if c != -1:
                queue.append(((a, c), (x, operation[x, y])))
    assert set(images) == set(range(1, n + 1))
    # Some edges separated from their neighbours by gaps need not be visited.
    for a, (_, _, row) in rows.items():
        for b in row:
            if b != -1 and images[b] not in neighbors[images[a]]:
                return None
        for b, c in zip(row, row[1:] + row[:1]):
            if b != -1 and c != -1 and nexts[images[a], images[b]] != images[c]:
                return None
    return [images[i] for i in range(1, n + 1)]


def configuration_rule(here, name):
    """Read complete core stars and ring edges; boundary turns stay unspecified."""
    manifest = json.loads((here / 'sources.json').read_text())
    raw = (here / name).read_bytes()
    assert sha256(raw).hexdigest() == manifest['files'][name]['sha256']
    rows = [[int(x) for x in row.split()] for row in raw.decode().splitlines() if row.strip()]
    n, ring = rows[0]
    core = {row[0]: row[1:] for row in rows[1:]}
    adj = {i: set() for i in range(1, n + 1)}
    for a, (_, *vs) in core.items():
        for b in vs:
            adj[a].add(b)
            adj[b].add(a)
    for a in range(1, ring + 1):
        b = a % ring + 1
        adj[a].add(b)
        adj[b].add(a)
    sender = min(core)
    receiver = min(adj[sender] & core.keys())
    data = [[n, sender, receiver, 0]]
    for a in range(1, n + 1):
        if a in core:
            degree, *vs = core[a]
            data.append([a, degree, degree, *vs])
        else:
            data.append([a, 0, 0, *[x for b in sorted(adj[a]) for x in [b, -1]]])
    return (name, data, compile_traces(data)), ring


def analyze_found(result, rules, here):
    darts, neighbors, nexts, prevs = geometry(result['faces'])
    assert len(neighbors) == result['vertices']
    assert {str(d): n for d, n in Counter(map(len, neighbors.values())).items()} == {
        str(d): n for d, n in result['degree_counts'].items()}
    matches = 0
    sent = dict.fromkeys(darts, 0)
    applications = {f'{u},{v}': [] for u, v in darts}
    for rule in rules:
        for u, v in darts:
            compiled = reading(rule, u, v, neighbors, nexts, prevs)
            propagated = breadth_first_reading(rule[1], u, v, neighbors, nexts, prevs)
            assert compiled == propagated
            matches += compiled is not None
            if propagated is not None:
                name, data, _ = rule
                sent[u, v] += data[0][3]
                applications[f'{u},{v}'].append([name, data[0][3], propagated])
    result['independent_matcher_comparison'] = {
        'rooted_tests': len(rules) * len(darts), 'matching_occurrences': matches,
        'disagreements': 0, 'method': 'Compiled traces versus independent dart propagation.'}
    for edge, hits in result['rule_applications'].items():
        assert json.loads(json.dumps(hits)) == applications[edge]
    pair = result['pair']
    assert pair[1] in neighbors[pair[0]] and all(len(neighbors[c]) == 8 for c in pair)
    charges = {str(c): 10 * (6 - len(neighbors[c])) +
               sum(sent[w, c] - sent[c, w] for w in neighbors[c]) for c in pair}
    assert charges == {str(c): amount for c, amount in result['charges'].items()}
    boundary = sum(sent[w, c] - sent[c, w] for c in pair for w in neighbors[c] if w not in pair)
    assert boundary == result['net_external_supply'] == 40 and set(charges.values()) == {0}

    def ball(centre):
        return {centre} | neighbors[centre] | set().union(*(neighbors[x] for x in neighbors[centre]))

    balls = list(map(ball, result['pair']))
    together = set.union(*balls)
    found = {}
    for name in ['D0000.conf', 'D0001.conf']:
        rule, ring = configuration_rule(here, name)
        occurrences = {}
        for a, b in darts:
            images = reading(rule, a, b, neighbors, nexts, prevs)
            if images is not None:
                assert images == breadth_first_reading(rule[1], a, b, neighbors, nexts, prevs)
                occurrences.setdefault(tuple(sorted(images[ring:])), images)
        joint = [images for core, images in occurrences.items()
                 if set(core) <= together and not any(set(core) <= bs for bs in balls)]
        found[name] = {'distinct_core_images': len(occurrences),
                       'cores_in_union_but_neither_ball': len(joint),
                       'joint_vertex_images_in_source_order': joint}
    result['joint_core_probe'] = {
        'ball_sizes': list(map(len, balls)), 'union_size': len(together), 'readings': found,
        'scope': 'Complete core stars and ring edges, allowing boundary identifications. '
                 'Not an induced embedded occurrence or a Lean reconstruction certificate. '
                 'Other reducible pieces exist in the individual neighbourhoods.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seed', type=int, default=1774)
    parser.add_argument('--steps', type=int, default=2000)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--replay', type=Path, help='Replay a saved graph and its edge flips')
    args = parser.parse_args()
    rng = random.Random(args.seed)
    here = Path(__file__).resolve().parent
    rules, revision = read_rules(here)
    if args.replay:
        result = json.loads(args.replay.read_text())
        assert result['rule_revision'] == revision
        faces = [tuple(face) for face in result['initial_faces']]
        for a, b, c, d in result['edge_flip_history']:
            darts, neighbors, _, _ = geometry(faces)
            i, actual_c = darts[a, b]
            j, actual_d = darts[b, a]
            assert [actual_c, actual_d] == [c, d] and d not in neighbors[c]
            faces[i], faces[j] = (c, d, b), (d, c, a)
        assert faces == [tuple(face) for face in result['faces']]
        analyze_found(result, rules, here)
        args.output.write_text(json.dumps(result, indent=2) + '\n')
        print(json.dumps({k: result[k] for k in ['independent_matcher_comparison', 'joint_core_probe']}))
        return
    faces = initial_faces()
    first_faces = list(faces)
    history, tested = [], 0
    best = None
    for step in range(args.steps + 1):
        darts, neighbors, nexts, prevs = geometry(faces)
        candidates = [(u, v) for u, v in darts if u < v and
                      len(neighbors[u]) == len(neighbors[v]) == 8]
        for u, v in candidates:
            tested += 1
            sent = {}
            applications = {}
            for centre in [u, v]:
                for w in neighbors[centre]:
                    for a, b in [(centre, w), (w, centre)]:
                        if (a, b) in sent:
                            continue
                        hits = [(name, data[0][3], images)
                                for rule in rules for name, data, _ in [rule]
                                if (images := reading(rule, a, b, neighbors, nexts, prevs)) is not None]
                        sent[a, b] = sum(amount for _, amount, _ in hits)
                        applications[f'{a},{b}'] = hits
            charge = {c: 10 * (6 - len(neighbors[c])) +
                      sum(sent[w, c] - sent[c, w] for w in neighbors[c]) for c in [u, v]}
            score = abs(charge[u]) + abs(charge[v])
            if best is None or score < best['score']:
                best = {'score': score, 'charges': charge, 'pair': [u, v], 'step': step}
            if score == 0:
                boundary = sum(sent.get((w, c), 0) - sent.get((c, w), 0)
                               for c in [u, v] for w in neighbors[c] if w not in [u, v])
                assert boundary == 40
                result = {'evidence': 'Exploratory exact integer calculation, not Lean-certified.',
                          'seed': args.seed, 'step': step, 'pairs_tested': tested,
                          'rule_revision': revision, 'vertices': len(neighbors),
                          'degree_counts': dict(Counter(map(len, neighbors.values()))),
                          'initial_faces': first_faces, 'faces': faces, 'edge_flip_history': history,
                          'pair': [u, v], 'charges': charge, 'net_external_supply': boundary,
                          'rule_applications': applications}
                analyze_found(result, rules, here)
                args.output.write_text(json.dumps(result, indent=2) + '\n')
                print(json.dumps({k: result[k] for k in ['step', 'pairs_tested', 'vertices',
                                 'degree_counts', 'pair', 'charges', 'net_external_supply']}))
                return
        legal = []
        for a, b in darts:
            if a >= b:
                continue
            i, c = darts[a, b]
            j, d = darts[b, a]
            if d not in neighbors[c] and min(len(neighbors[a]), len(neighbors[b])) >= 6 and \
                    max(len(neighbors[c]), len(neighbors[d])) <= 7:
                legal.append((a, b, c, d, i, j))
        if not legal:
            break
        a, b, c, d, i, j = rng.choice(legal)
        faces[i], faces[j] = (c, d, b), (d, c, a)
        history.append([a, b, c, d])
    result = {'evidence': 'Bounded exploratory search; no flat pair found.',
              'seed': args.seed, 'pairs_tested': tested, 'best': best}
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
