#!/usr/bin/env python3
"""Replay exact port messages and compatible physical repairs across an edge.

The generic composition and lifting laws are Lean theorems. The spherical
source geometry, messages and executions here are independent program checks.
No joint table of colourings of the two pieces is constructed.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path

from audit_boundary_observation import proper
from audit_cycle_anchors import whole_case
from audit_cycle_blocks import source_faces, sphere
from audit_diamond_sources import require
from audit_forest_repair import forest_guard, forest_order, realize


def after(pair, label):
    a, b = pair
    c, bit = label
    return (b if c == a else a if c == b else c) if bit else c


def compatible(pair, s, t):
    return s[0] != t[0] and after(pair, s) != after(pair, t)


def port_message(adj, hidden, piece, root, before, target, pair):
    """Eliminate a tree towards its port, retaining at most eight labels.

    Snapshots reconstruct the supporting assignment for each surviving label.
    The joining edge is reserved for the subsequent compatibility test.
    """
    require(root in piece <= hidden, 'Invalid port or piece')
    parents, order = {root: None}, [root]
    for v in order:
        for w in sorted(adj[v] & piece):
            if w == parents[v]:
                continue
            require(w not in parents, 'Piece is not a tree')
            parents[w] = v
            order.append(w)
    require(set(order) == piece, 'Piece is disconnected')
    labels = [(c, bit) for c in range(4) for bit in (False, True)]
    domains = {x: [s for s in labels if all(
        s[0] != before[y] and after(pair, s) != target[y]
        for y in adj[x] - hidden)] for x in piece}
    snapshots, comparisons = {}, 0
    for v in reversed(order):
        snapshots[v] = list(domains[v])
        p = parents[v]
        if p is None:
            continue
        kept = []
        for t in domains[p]:
            for s in domains[v]:
                comparisons += 1
                if compatible(pair, s, t):
                    kept.append(t)
                    break
        domains[p] = kept
    messages = {}
    for root_label in domains[root]:
        chosen = {root: root_label}
        for v in order[1:]:
            chosen[v] = next(s for s in snapshots[v]
                             if compatible(pair, s, chosen[parents[v]]))
        messages[root_label] = ({x: s[0] for x, s in chosen.items()},
                                {x: after(pair, s) for x, s in chosen.items()})
    # Cross-check each possible port label against the existing leaf evaluator.
    # Retaining the port as a fixed before/after observation gives exactly its message.
    for s in labels:
        test, _ = forest_guard(adj, piece - {root},
            {**before, root: s[0]}, {**target, root: after(pair, s)}, pair)
        # Edges to the other piece must not enter this local test.
        unary = all(s[0] != before[y] and after(pair, s) != target[y]
                    for y in adj[root] - hidden)
        require((s in messages) == (unary and test is not None), 'Port message differs')
    return messages, {'leaf_messages': len(piece) - 1,
                      'forward_edge_comparisons': comparisons,
                      'possible_port_labels': len(messages)}


def check_local(adj, hidden, piece, before, target, pair, witness):
    old, new = witness
    require(set(old) == set(new) == piece, 'Local witness carrier differs')
    for x in piece:
        require(new[x] in (old[x], after(pair, (old[x], True))), 'Wrong transposition')
        for y in adj[x] & piece:
            require(old[x] != old[y] and new[x] != new[y], 'Local edge lost')
        for y in adj[x] - hidden:
            require(old[x] != before[y] and new[x] != target[y], 'Exterior edge lost')


def verify(here):
    fixture_path = here / 'bridge-guard-example.json'
    fixture = json.loads(fixture_path.read_text())
    for pin in fixture['sources']:
        require(sha256((here / pin['file']).read_bytes()).hexdigest() == pin['sha256'],
                'Source pin differs: ' + pin['file'])
    sources = json.loads((here / 'independent-repair-example.json').read_text())['cases']
    results = []
    for case in fixture['cases']:
        source = sources[case['source_case']]
        adj, current = whole_case(here, source)
        faces = source_faces(here, source)
        require(adj == sphere(faces), 'Colouring graph and spherical geometry differ')
        proper(adj, current)
        cycles = [set(c) for c in case['cycles']]
        require(not cycles[0] & cycles[1], 'Cycles intersect')
        for centre, cycle in zip(case['centres'], cycles):
            require(adj[centre] == cycle, 'Cycle is not the stated star boundary')
            require(all(len(adj[x] & cycle) == 2 for x in cycle), 'Cycle has extra edges')
        anchors, bridge, pair = case['anchors'], case['bridge'], case['pair']
        require(all(a in cy for a, cy in zip(anchors, cycles)), 'Foreign anchor')
        cross = sorted((x, y) for x in cycles[0] for y in adj[x] & cycles[1])
        require(cross == [tuple(bridge)], 'The joining edge is not unique')
        pieces = [cy - {a} for cy, a in zip(cycles, anchors)]
        hidden = pieces[0] | pieces[1]
        require(set(bridge) <= hidden, 'Joining port was removed')
        forest_order(adj, hidden)
        before = {x: c for x, c in current.items() if x not in hidden}
        target = dict(before)
        changed = set(case['changed_anchors'])
        require(changed <= set(anchors), 'A non-anchor retained vertex moves')
        for x in changed:
            target[x] = after(pair, (before[x], True))
        proper({x: ns - hidden for x, ns in adj.items() if x not in hidden}, target)
        local = [tuple({int(x): c for x, c in w.items()} for w in ws)
                 for ws in case['local_witnesses']]
        for piece, witness in zip(pieces, local):
            check_local(adj, hidden, piece, before, target, pair, witness)
        x, y = bridge
        conflicts = [phase for phase in (0, 1) if local[0][phase][x] == local[1][phase][y]]
        require(conflicts, 'Expected incompatible independent choices')
        cut_adj = {v: ns - ({y} if v == x else {x} if v == y else set())
                   for v, ns in adj.items()}
        messages, costs = [], []
        for piece, root in zip(pieces, bridge):
            m, cost = port_message(cut_adj, hidden, piece, root, before, target, pair)
            messages.append(m)
            costs.append(cost)
        pairs = [(s, t) for s in messages[0] for t in messages[1]]
        accepted = [(s, t) for s, t in pairs if compatible(pair, s, t)]
        require(accepted and len(accepted) < len(pairs), 'Joining relation is not decisive')
        s, t = accepted[0]
        selected = [messages[0][s], messages[1][t]]
        for piece, witness in zip(pieces, selected):
            check_local(adj, hidden, piece, before, target, pair, witness)
        joint = tuple(selected[0][phase] | selected[1][phase] for phase in (0, 1))
        proper(adj, before | joint[0])
        final = target | joint[1]
        proper(adj, final)
        global_guard, global_cost = forest_guard(adj, hidden, before, target, pair)
        require(global_guard is not None, 'Composed guard disagrees with whole forest')
        execution = realize(adj, hidden, current, final, pair, joint)
        require(all(final[v] == current[v] for v in adj if v not in cycles[0] | cycles[1]),
                'Original exterior changed')
        results.append({'source_case': case['source_case'], 'vertices': len(adj),
            'faces': len(faces), 'degree_range': [min(map(len, adj.values())), max(map(len, adj.values()))],
            'cycle_lengths': list(map(len, cycles)), 'hidden_vertices': len(hidden),
            'bridge': bridge, 'pair': pair, 'changed_anchors': sorted(changed),
            'independent_port_colours': [[w[p][v] for p in (0, 1)] for w, v in zip(local, bridge)],
            'independent_conflict_phases': conflicts, 'messages': costs,
            'port_label_pairs_tested': len(pairs), 'compatible_port_label_pairs': len(accepted),
            'selected_port_labels': [s, t],
            'composed_port_colours': [[joint[p][v] for p in (0, 1)] for v in bridge],
            'whole_forest_crosscheck': global_cost, 'execution': execution,
            'whole_joint_colourings_enumerated': False})
    return {'evidence': 'Independent program replay; generic bridge and physical lifting are Lean proved.',
            'fixture_sha256': sha256(fixture_path.read_bytes()).hexdigest(), 'cases': results,
            'scope': 'Two concrete repairs; no universal coverage, strict map reduction or catalogue saving.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parent)
    output = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(output)
    print(output, end='')


if __name__ == '__main__':
    main()
