#!/usr/bin/env python3
"""Replay factored cyclic interfaces in joined spherical triangulations.

Only local cycle states and one alternative per frozen block are checked.
The Boolean product of alternatives is supplied by the generic Lean theorem,
not by enumerating joint colourings. Spherical geometry remains program evidence.
"""
import argparse
from hashlib import sha256
import json
from math import prod
from pathlib import Path

from audit_boundary_observation import proper
from audit_chain_boundary import subdivide
from audit_cycle_anchors import analyse, connected_components, whole_case
from audit_diamond_sources import require
from audit_forest_repair import forest_guard, forest_order, realize
from audit_frozen_observer import OBSERVER_EDGES, OBSERVER_INITIAL
from audit_independent_repair import verify_case
from probe_flat_pairs import geometry, initial_faces


def source_faces(here, case):
    fixture = json.loads((here / case['source_fixture']).read_text())
    origin = json.loads((here / fixture['source_fixture']).read_text())
    faces = subdivide(initial_faces())
    for a, b, c, d in origin['edge_flip_history'][:fixture['edge_flip_prefix']]:
        darts, _, _, _ = geometry(faces)
        i, ac = darts[a, b]
        j, ad = darts[b, a]
        require((ac, ad) == (c, d), 'Source flip differs')
        faces[i], faces[j] = (c, d, b), (d, c, a)
    return faces


def sphere(faces):
    require(all(len(set(face)) == 3 for face in faces), 'Degenerate face')
    require(len({frozenset(face) for face in faces}) == len(faces), 'Repeated face')
    darts, adj, _, _ = geometry(faces)  # Also checks every cyclic vertex star and Euler characteristic.
    require(all((v, u) in darts for u, v in darts), 'Missing reverse dart')
    require(len(connected_components(adj)) == 1, 'Disconnected surface')
    return adj


def append_copy(faces, colour, base_faces, base_colour, incoming, outgoing, next_face):
    """Delete one face on each sphere and identify their oppositely oriented rims."""
    images = dict(zip(incoming, [outgoing[0], outgoing[2], outgoing[1]]))
    fresh = max(colour) + 1
    for x in sorted(base_colour):
        if x not in images:
            images[x] = fresh
            fresh += 1
    palette = dict(zip([base_colour[x] for x in incoming], [colour[images[x]] for x in incoming]))
    require(len(palette) == len(set(palette.values())) == 3, 'Seam colours are not distinct')
    palette[next(iter(set(range(4)) - palette.keys()))] = next(iter(set(range(4)) - set(palette.values())))
    joined = [face for face in faces if face != outgoing]
    require(len(joined) == len(faces) - 1, 'Outgoing face is not present exactly once')
    joined.extend(tuple(images[x] for x in face) for face in base_faces if face != incoming)
    whole = dict(colour)
    for x, c in base_colour.items():
        if images[x] in whole:
            require(whole[images[x]] == palette[c], 'Seam colours disagree')
        whole[images[x]] = palette[c]
    return joined, whole, tuple(images[x] for x in next_face), images, palette


def endpoints(adj, initial, cycle, anchor):
    """Feasible anchor colours, with one full witness each, from leaf messages."""
    hidden = set(cycle) - {anchor}
    retained = set(adj) - hidden
    result = {}
    for c in range(4):
        word = initial | {anchor: c}
        if any(word[x] == word[y] for x in retained for y in adj[x] & retained):
            continue
        choices, _ = forest_guard(adj, hidden, word, word, (0, 0))
        if choices is not None:
            result[c] = word | choices[0]
            proper(adj, result[c])
    return result


def factored_guard(adj, blocks, hidden, before, after, pair):
    local = [forest_guard(adj, block & hidden, before, after, pair)[0] is not None
             for block in blocks]
    whole, _ = forest_guard(adj, hidden, before, after, pair)
    require(all(local) == (whole is not None), 'Joint guard does not factor')
    return local


def check_joined(adj, initial, copies, frozen, working):
    cycles = [[images[x] for x in cycle] for images, _ in copies
              for cycle in [frozen['hidden'], working['cycle']]]
    blocks = list(map(set, cycles))
    region = set().union(*blocks)
    require(sum(map(len, blocks)) == len(region), 'Cycle blocks intersect')
    require(all(not adj[x] & (region - block) for block in blocks for x in block),
            'An edge crosses hidden blocks')
    anchors = {cycle[0] for cycle in cycles}
    hidden = region - anchors
    forest_order(adj, hidden)
    local = []
    for cycle in cycles:
        selected = set(cycle)
        require(all(adj[x] & selected == {cycle[(i-1) % len(cycle)], cycle[(i+1) % len(cycle)]}
                    for i, x in enumerate(cycle)), 'Cycle acquired a chord')
        local.append(analyse(adj, initial, cycle, cycle[0], check=True))
    # These clauses are the concrete premises of FrozenCycleFamily.Witnesses.
    rejected = []
    for index, (images, palette) in enumerate(copies):
        observer = [images[x] for x in frozen['observer_images']]
        renamed = [palette[c] for c in frozen['palette']]
        require(all(observer[v] in adj[observer[u]] for u, v in OBSERVER_EDGES), 'Observer edge lost')
        require([initial[x] for x in observer] == [renamed[c] for c in OBSERVER_INITIAL],
                'Frozen observation changed')
        require(set(observer[3:]).isdisjoint(region), 'Observer context is not protected')
        require(set(observer[:3]) == blocks[2 * index], 'Observer core is not owned by its block')
        alternative = initial | {images[x]: palette[c] for x, c in
                                 zip(frozen['hidden'], frozen['target_hidden'])}
        proper(adj, alternative)
        require(alternative[observer[2]] != renamed[1], 'Observed core did not change')
        anchor = cycles[2 * index][0]
        accepted = factored_guard(adj, blocks, hidden, initial, alternative,
                                  (initial[anchor], alternative[anchor]))
        require(not accepted[2 * index], 'A frozen choice crossed classes')
        rejected.append(index)
    # Compose the working-cycle histories, retaining all other local witnesses.
    current = dict(initial)
    commands = []
    for index in range(len(copies)):
        cycle = cycles[2 * index + 1]
        candidates = endpoints(adj, initial, cycle, cycle[0])
        require(len(candidates) == 2, 'Expected two working anchor colours')
        a, b = sorted(candidates)
        current.update((x, candidates[a][x]) for x in cycle)
        commands.append((set(cycle), cycle[0], (a, b), {x: candidates[b][x] for x in cycle}))
    proper(adj, current)
    composed = []
    for selected, anchor, pair, values in commands:
        target = current | values
        proper(adj, target)
        require(all(factored_guard(adj, blocks, hidden, current, target, pair)),
                'A compatible local command failed the joint guard')
        choices, cost = forest_guard(adj, selected - {anchor}, current, target, pair)
        require(choices is not None, 'Working cycle did not supply witnesses')
        old, new = ({x: current[x] for x in hidden}, {x: target[x] for x in hidden})
        old.update(choices[0])
        new.update(choices[1])
        physical = realize(adj, hidden, current, target, pair, (old, new))
        require(all(current[x] == target[x] == initial[x] for x in set(adj) - region),
                'Composed endpoint changed the fixed exterior')
        composed.append({'pair': list(pair), **cost, **physical})
        current = target
    return {'copies': len(copies), 'vertices': len(adj), 'cycle_blocks': len(blocks),
            'degree_range': [min(map(len, adj.values())), max(map(len, adj.values()))],
            'hidden_vertices': len(hidden), 'retained_anchors': len(anchors),
            'cross_interface_edges': sum(len(adj[x] - hidden) for x in hidden),
            'frozen_observers': len(copies), 'physical_classes_lower_bound': 2 ** len(copies),
            'feasible_joint_anchor_words_factored': prod(len(record['feasible']) for record in local),
            'local_anchor_states_stored': sum(len(record['feasible']) for record in local),
            'local_transitions_stored': sum(len(record['transitions']) for record in local),
            'rejected_frozen_commands': rejected, 'composed_repair': composed,
            'joint_colourings_enumerated': 0, 'local_cycle_crosschecks': len(local),
            'concrete_instance_kernel_certified': False}


def verify(here):
    path = here / 'cycle-blocks-example.json'
    fixture = json.loads(path.read_text())
    sources = {}
    for key, pin in fixture['sources'].items():
        source = here / pin['file']
        require(sha256(source.read_bytes()).hexdigest() == pin['sha256'], 'Source pin differs')
        sources[key] = json.loads(source.read_text())
    case = sources['repair']['cases'][fixture['source_case']]
    verify_case(here, case)
    base, colour = whole_case(here, case)
    base_faces = source_faces(here, case)
    require(sphere(base_faces) == base, 'Source geometry differs')
    frozen = sources['frozen']['cases'][1]
    working = sources['anchors']['cases'][1]
    incoming, outgoing = tuple(fixture['incoming_face']), tuple(fixture['outgoing_face'])
    require(incoming in base_faces and outgoing in base_faces, 'Seam is not an actual face')
    require(set(incoming).isdisjoint(outgoing), 'The two seam faces intersect')
    protected = set(frozen['observer_images']) | set(working['cycle'])
    require((set(incoming) | set(outgoing)).isdisjoint(protected), 'A seam meets a retained witness')
    faces = list(base_faces)
    whole = dict(colour)
    next_face = outgoing
    copies = [(dict(zip(base, base)), dict(zip(range(4), range(4))))]
    records = []
    for n in range(1, fixture['copies'] + 1):
        if n > 1:
            faces, whole, next_face, images, palette = append_copy(
                faces, whole, base_faces, colour, incoming, next_face, outgoing)
            copies.append((images, palette))
        adj = sphere(faces)
        proper(adj, whole)
        record = check_joined(adj, whole, copies, frozen, working)
        require(record['vertices'] == 159 * n + 3, 'Unexpected vertex count')
        record['faces'] = len(faces)
        record['connected_oriented_sphere_checked'] = True
        records.append(record)
    return {'evidence': 'Independent program checks of separated cyclic witnesses and composed repairs.',
            'cases': records,
            'kernel_theorems': ['SimpleGraph.KempeBlockChoices.combine',
                               'SimpleGraph.KempeBlockChoices.anchored_history_iff',
                               'Mettapedia.GraphTheory.FourColor.FrozenCycleFamily.Witnesses.no_path',
                               'Mettapedia.GraphTheory.FourColor.FrozenCycleFamily.Witnesses.summary_card_lower_bound'],
            'scope': 'The generic conditional family theorem constructs all Boolean choices and '
                     'separates their physical classes. Concrete joined-sphere geometry and local '
                     'executions are program checks. Exponential class counts do not require an '
                     'exponential symbolic interface in these separated cases. No bound for '
                     'interacting hidden blocks or universal geometric supply is asserted.',
            'fixture_sha256': sha256(path.read_bytes()).hexdigest(),
            'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
            'credited_compression': False}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parent)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
