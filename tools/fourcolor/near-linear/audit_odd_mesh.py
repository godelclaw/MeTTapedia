#!/usr/bin/env python3
"""Replay preparation and repair beyond the short-separator cases.

The general bichromatic route projection and one width-five triangular
mesh are Lean checked. This program independently checks larger oriented
spheres, every simple cycle of length three through five, initial phase
choices, and specified boundary-silent preparations followed by repair.
It performs no search for recolouring commands.
"""
import argparse
from collections import Counter
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path

from audit_boundary_observation import components, proper, switch
from audit_clique_fill import connected, make_profile, phases, source_faces
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_two_port_core import eliminate
from probe_flat_pairs import geometry


def refine(outer, colours, first_new, width):
    """Odd triangular subdivision, with a fan along each old boundary edge.

    Colours are the Klein four group, represented by bitwise xor. At each
    barycentric lattice point, xor the old colours with odd coefficients.
    Every old edge becomes an alternating path of odd length. A boundary
    strip retains the literal old ring edge and triangulates the intervening
    (width+1)-gon with one vertex of a third colour.
    """
    require(width >= 3 and width % 2 == 1, 'Width must be odd and at least three')
    colours = dict(colours)
    labels, faces, paths, oriented = {}, [], {}, set()
    next_vertex = first_new

    def vertex(face, i, j):
        nonlocal next_vertex
        key = tuple(sorted((v, w) for v, w in zip(face, (width-i-j, i, j)) if w))
        if len(key) == 1:
            return key[0][0]
        if key not in labels:
            colour = 0
            for v, w in key:
                if w % 2:
                    colour ^= colours[v]
            labels[key] = next_vertex
            colours[next_vertex] = colour
            next_vertex += 1
        return labels[key]

    for face in outer:
        require(len(set(face)) == 3, 'Repeated triangle vertex')
        a, b, c = face
        oriented.update(((a, b), (b, c), (c, a)))
        for i in range(width + 1):
            for j in range(width + 1 - i):
                if i+j < width:
                    faces.append((vertex(face, i, j), vertex(face, i+1, j), vertex(face, i, j+1)))
                if i+j < width-1:
                    faces.append((vertex(face, i+1, j), vertex(face, i+1, j+1), vertex(face, i, j+1)))
        for u, v in ((a, b), (b, c), (c, a)):
            paths[u, v] = [u] + [labels[tuple(sorted(((u, width-k), (v, k))))]
                                  for k in range(1, width)] + [v]
    mesh_faces = list(faces)
    for u, v in sorted(oriented):
        if (v, u) in oriented:
            continue
        rim = [u] + list(reversed(paths[u, v][1:]))
        centre = next_vertex
        next_vertex += 1
        colours[centre] = min(set(range(4)) - {colours[u], colours[v]})
        faces.extend((centre, a, b) for a, b in zip(rim, rim[1:] + rim[:1]))
    return faces, colours, paths, mesh_faces


def short_cycles(adj):
    """Each undirected simple cycle of length 3..5, once.

    Start at its smallest vertex, visit all distinct-vertex paths through
    five vertices, and retain one of the two orientations. Chorded cycles
    are included. No geometric pruning or source-specific pattern is used.
    """
    for first in sorted(adj):
        def visit(path):
            last = path[-1]
            if len(path) >= 3 and first in adj[last] and path[1] < last:
                yield tuple(path)
            if len(path) < 5:
                for following in sorted(adj[last]):
                    if following > first and following not in path:
                        yield from visit(path + [following])
        yield from visit([first])


def flood(adj, root, blocked=frozenset()):
    seen, todo = set(), [root]
    while todo:
        v = todo.pop()
        if v not in seen:
            seen.add(v)
            todo.extend(u for u in adj[v] - seen if frozenset((v, u)) not in blocked)
    return seen


def cycle_census(faces):
    """Count vertices on the two actual facial shores of every short cycle.

    Connectedness, simple triangular faces, opposite darts, single vertex
    rotations and Euler characteristic two give a closed oriented sphere.
    Deleting its cycle-crossing dual edges must give exactly two connected
    facial shores. Their off-cycle vertex sets are counted separately.
    """
    require(all(len(set(f)) == 3 for f in faces), 'A face repeats a vertex')
    require(len({tuple(sorted(f)) for f in faces}) == len(faces), 'A face is duplicated')
    darts, adj, _, _ = geometry(faces)
    require(all((v, u) in darts for u, v in darts), 'Missing opposite dart')
    require(connected(adj), 'Disconnected sphere')
    edge_faces = {tuple(sorted((u, v))): (darts[u, v][0], darts[v, u][0])
                  for u, v in darts if u < v}
    dual = {i: set() for i in range(len(faces))}
    for i, j in edge_faces.values():
        dual[i].add(j)
        dual[j].add(i)
    counts, sizes, obstructions = Counter(), Counter(), []
    for cycle in short_cycles(adj):
        length, boundary = len(cycle), set(cycle)
        cuts = {tuple(sorted((cycle[i], cycle[(i+1) % length]))) for i in range(length)}
        blocked = {frozenset(edge_faces[e]) for e in cuts}
        left = flood(dual, edge_faces[min(cuts)][0], blocked)
        right = set(dual) - left
        require(right and flood(dual, min(right), blocked) == right,
                'The cycle does not have exactly two connected facial shores')
        shores = [{v for f in side for v in faces[f]} - boundary for side in (left, right)]
        require(not shores[0] & shores[1] and shores[0] | shores[1] == set(adj) - boundary,
                'The cycle shores do not partition off-cycle vertices')
        numbers = tuple(sorted(map(len, shores)))
        counts[length] += 1
        sizes[length, numbers] += 1
        if (length < 5 and numbers[0] > 0) or (length == 5 and numbers[0] > 1):
            obstructions.append({'cycle': list(cycle), 'side_vertices': list(numbers)})
    return {'vertices': len(adj), 'faces': len(faces),
        'minimum_degree': min(map(len, adj.values())),
        'cycles_by_length': dict(sorted(counts.items())),
        'shore_counts': [{'length': n, 'side_vertices': list(sz), 'cycles': count}
                        for (n, sz), count in sorted(sizes.items())],
        'obstructing_cycles': len(obstructions),
        'first_obstruction': obstructions[0] if obstructions else None}


def partition(adj, colours, pair, ring):
    return sorted(sorted(s & set(range(ring))) for s in components(adj, colours, pair)
                  if s & set(range(ring)))


def check_lean_mesh(here):
    _, colours, paths, faces = refine([[0, 1, 2]], {0: 0, 1: 1, 2: 2}, 3, 5)
    edges = sorted({tuple(sorted((f[i], f[(i+1) % 3]))) for f in faces for i in range(3)})
    path = here.parents[2] / 'lean/mettapedia/Mettapedia/GraphTheory/FourColor/OddMeshAudit.lean'
    text = path.read_text()
    literal = '[' + ','.join(f'({a},{b})' for a, b in edges) + ']'
    require('def edges : List (Fin 21 × Fin 21) := ' + literal in text, 'Lean mesh edges differ')
    literal = '[' + ','.join(str(colours[v]) for v in range(21)) + ']'
    require('(' + literal + ' : List (Fin 4)).get' in text, 'Lean mesh colours differ')
    for route in paths.values():
        require('[' + ','.join(map(str, route)) + ']' in text, 'Lean edge route differs')
    return sha256(path.read_bytes()).hexdigest()


def verify(here):
    fixture_path = here / 'odd-mesh-example.json'
    fixture = json.loads(fixture_path.read_text())
    source_path = here / fixture['source_fixture']
    require(sha256(source_path.read_bytes()).hexdigest() == fixture['source_fixture_sha256'],
            'Base fixture pin differs')
    source = json.loads(source_path.read_text())
    for pin in source['sources']:
        require(sha256((here / pin['file']).read_bytes()).hexdigest() == pin['sha256'],
                'Configuration source pin differs')
    mesh_sha = check_lean_mesh(here)
    results = []
    for base, commands in zip(source['cases'], fixture['cases'], strict=True):
        require(base['configuration'] == commands['configuration'], 'Source order differs')
        raw = (here / base['configuration']).read_bytes()
        ring, patch = graph(raw)
        inside = set(range(ring, len(patch)))
        inner_faces = source_faces(raw)
        _, small, _, _ = geometry(inner_faces + [tuple(f) for f in base['outer_faces']])
        original = {v: ns-inside for v, ns in small.items() if v not in inside}
        before = dict(enumerate(base['boundary']))
        proper(original, before)
        profile = make_profile(patch, ring)
        initial_profile = profile(base['boundary'])
        baseline_phases = phases(original, before, ring, profile)
        rows = []
        for width in fixture['widths']:
            refined, colours, paths, _ = refine(base['outer_faces'], before, len(patch), width)
            faces = inner_faces + refined
            _, ambient, _, _ = geometry(faces)
            require(all(ambient[v] == set(patch[v]) for v in inside), 'Source core adjacency changed')
            # Source facial triangles, hence its full cyclic core stars, are literal inputs.
            exterior = {v: ns-inside for v, ns in ambient.items() if v not in inside}
            proper(exterior, colours)
            for (u, v), route in paths.items():
                require(all(b in exterior[a] for a, b in zip(route, route[1:])), 'Broken route edge')
                require(all(colours[x] == (colours[u] if k % 2 == 0 else colours[v])
                            for k, x in enumerate(route)), 'Route is not alternating')
            for pair in combinations(range(4), 2):
                require(partition(original, before, pair, ring) == partition(exterior, colours, pair, ring),
                        'Initial boundary components differ from the base')
            phase_report = phases(exterior, colours, ring, profile)
            require(phase_report == baseline_phases, 'Initial phase choices changed')
            census = cycle_census(faces)
            if width == 3:
                require(census['minimum_degree'] == 4 and census['obstructing_cycles'] > 0,
                        'The negative control failed to detect short separators')
            else:
                require(census['minimum_degree'] >= 5 and census['obstructing_cycles'] == 0,
                        'A claimed internally six-connected example has an obstructing cycle')
            row = {'width': width, 'geometry': census, 'initial_phase_choices': phase_report,
                   'source_core_stars_preserved': True, 'alternating_edge_routes_checked': len(paths)}
            repaired = dict(colours)
            for command in base['repair_commands']:
                repaired, _ = switch(exterior, repaired, command['pair'], command['root'])
            repaired_core, _ = eliminate(patch, ring, [repaired[v] for v in range(ring)])
            require(repaired_core is not None, 'The retained base repair no longer extends')
            proper(ambient, repaired | repaired_core)
            row['base_two_switch_repair_reconstructs'] = True
            if width == 5:
                first, support = switch(exterior, colours, commands['prepare']['pair'], commands['prepare']['root'])
                require(len(support) == commands['prepare']['size'] and not support & set(range(ring)),
                        'Preparation is not the specified boundary-silent component')
                support_degrees = Counter(len(exterior[v] & support) for v in support)
                require(support_degrees == Counter({1: 2, 2: len(support)-2}),
                        'The connected preparation component is not a simple path')
                require(profile([first[v] for v in range(ring)]) == initial_profile,
                        'Silent preparation changed the potential')
                pair = commands['finish']['pair']
                old_parts = partition(exterior, colours, pair, ring)
                new_parts = partition(exterior, first, pair, ring)
                require(old_parts != new_parts, 'Preparation did not change the next pair observation')
                final, support2 = switch(exterior, first, pair, commands['finish']['root'])
                require(len(support2) == commands['finish']['size'], 'Finish support differs')
                word = [final[v] for v in range(ring)]
                core, _ = eliminate(patch, ring, word)
                require(core is not None and profile(word)[0] > 0, 'Final boundary does not extend')
                proper(ambient, final | core)
                row['preparation_and_repair'] = {
                    'prepare': commands['prepare'], 'finish': commands['finish'],
                    'preparation_is_a_boundary_silent_path': True,
                    'initial_profile': initial_profile, 'prepared_profile': initial_profile,
                    'final_profile': profile(word), 'final_boundary': word,
                    'core_colours': [core[v] for v in sorted(inside)],
                    'next_pair_components_before': old_parts, 'next_pair_components_after': new_parts,
                    'whole_colouring_reconstructed': True}
            rows.append(row)
        results.append({'configuration': base['configuration'], 'examples': rows})
    return {'evidence': 'Exact program replay; general fixed-pair route projection and the small mesh are separately Lean checked.',
        'fixture_sha256': sha256(fixture_path.read_bytes()).hexdigest(),
        'lean_mesh_sha256': mesh_sha, 'cases': results,
        'scope': 'Strict increase after every fixed-pair phase fails in internally six-connected spheres. '
                 'In both width-five examples a boundary-silent preparation then a different-pair switch succeeds '
                 'without decreasing the count vector. This does not refute weakly monotone repair allowing '
                 'preparation, nor prove uniform availability or a bound on that preparation. No catalogue reduction.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parent)
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')
