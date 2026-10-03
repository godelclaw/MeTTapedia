#!/usr/bin/env python3
"""Replay clique fillings, physical repairs and a failed monotone potential.

The general clique history theorem and the twelve-vertex filling incidence
are Lean checked. This script checks concrete oriented spheres and counts
near-extensions; those claims are separate program evidence. No repair
search or catalogue-wide boundary enumeration is needed on replay.
"""
import argparse
from collections import Counter
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path

from audit_boundary_observation import components, proper, switch
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_pair_phase import canonical
from audit_two_port_core import eliminate
from probe_flat_pairs import geometry


def core_colours(patch, ring):
    """The 384 proper seven-vertex core colourings, independently enumerated."""
    result = []
    def visit(part):
        v = ring + len(part)
        if v == len(patch):
            result.append(part)
            return
        for c in range(4):
            if all(part[u-ring] != c for u in patch[v] if ring <= u < v):
                visit(part + (c,))
    visit(())
    return result


def make_profile(patch, ring):
    """Coefficient k counts proper core colourings with k bad attachment edges.

    Lexicographic order starts with genuine extensions (coefficient zero),
    then one-conflict colourings, two-conflict colourings, and so on.
    """
    colours = core_colours(patch, ring)
    require(len(colours) == 384, 'Core-colouring count differs')
    costs = [[[sum(cs[v-ring] == c for v in patch[j] if v >= ring)
               for c in range(4)] for j in range(ring)] for cs in colours]
    size = sum(sum(v >= ring for v in patch[j]) for j in range(ring)) + 1
    cache = {}
    def profile(word):
        key = canonical(word)
        if key not in cache:
            counts = Counter(sum(cost[j][c] for j, c in enumerate(key)) for cost in costs)
            cache[key] = tuple(counts[i] for i in range(size))
        return cache[key]
    return profile


def phases(adj, colours, ring, profile):
    initial = [colours[j] for j in range(ring)]
    value = profile(initial)
    require(value[0] == 0, 'Initial word already extends')
    results = []
    for pair in combinations(range(4), 2):
        blocks = [s for s in components(adj, colours, pair) if s.intersection(range(ring))]
        counts = Counter()
        for mask in range(2 ** len(blocks)):
            after = dict(colours)
            for i, support in enumerate(blocks):
                if mask >> i & 1:
                    after, actual = switch(adj, after, pair, min(support))
                    require(actual == support, 'Fixed-pair component changed')
            word = [after[j] for j in range(ring)]
            score = profile(word)
            require(score <= value, 'A fixed-pair phase increases the potential')
            if score == value:
                require(canonical(word) == canonical(initial),
                        'An equal-potential phase changes the boundary beyond palette renaming')
                counts['palette_only'] += 1
            else:
                counts['strictly_worse'] += 1
        results.append({'pair': list(pair), 'boundary_components': len(blocks), **counts})
    return results


def source_faces(raw):
    rows = [list(map(int, line.split())) for line in raw.decode().splitlines() if line.strip()]
    faces = set()
    for v, degree, *ns in rows[1:]:
        require(len(ns) == degree, 'Wrong source star')
        ns = [x-1 for x in ns]
        for a, b in zip(ns, ns[1:] + ns[:1]):
            f = (v-1, a, b)
            faces.add(min(f, f[1:] + f[:1], f[2:] + f[:2]))
    return sorted(faces)


def insert_filling(face, next_vertex, colours, filling):
    """Replace an oriented face; its boundary colours remain literally fixed."""
    a, b, c = face
    all_faces = filling['faces']
    removed = filling['removed_face']
    template = all_faces[removed]
    old = filling['colouring']
    mapping = dict(zip(template, (a, c, b)))
    palette = {old[u]: colours[v] for u, v in mapping.items()}
    require(len(palette) == 3 and len(set(palette.values())) == 3, 'Improper triangular seam')
    palette.update(zip(sorted(set(range(4))-palette.keys()),
                       sorted(set(range(4))-set(palette.values()))))
    hidden = []
    for v in range(12):
        if v not in mapping:
            mapping[v] = next_vertex
            hidden.append(next_vertex)
            next_vertex += 1
        colours[mapping[v]] = palette[old[v]]
    faces = [tuple(mapping[v] for v in f) for i, f in enumerate(all_faces) if i != removed]
    return faces, next_vertex, {'seam': list(face), 'hidden': hidden}


def check_filling_source(here, filling):
    """Match the finite Lean consumer to the exact filling used by the replay."""
    face = filling['faces'][filling['removed_face']]
    order = face + [v for v in range(12) if v not in face]
    label = {v: i for i, v in enumerate(order)}
    edges = sorted({tuple(sorted((label[f[i]], label[f[(i+1) % 3]])))
                    for f in filling['faces'] for i in range(3)})
    colours = [filling['colouring'][v] for v in order]
    source = here.parents[2] / 'lean/mettapedia/Mettapedia/GraphTheory/FourColor/CliqueFillAudit.lean'
    text = source.read_text()
    edge_literal = '[' + ','.join(f'({a},{b})' for a, b in edges) + ']'
    colour_literal = '[' + ','.join(map(str, colours)) + ']'
    require('def edges : List (Fin 12 × Fin 12) := ' + edge_literal in text,
            'Lean filling edges differ from the replay')
    require('(' + colour_literal + ' : List (Fin 4)).get' in text,
            'Lean filling colouring differs from the replay')
    return sha256(source.read_bytes()).hexdigest()


def connected(adj):
    seen, todo = set(), [next(iter(adj))]
    while todo:
        v = todo.pop()
        if v not in seen:
            seen.add(v)
            todo.extend(adj[v] - seen)
    return seen == set(adj)


def verify(here):
    path = here / 'clique-fill-example.json'
    fixture = json.loads(path.read_text())
    lean_sha = check_filling_source(here, fixture['filling'])
    for pin in fixture['sources']:
        require(sha256((here / pin['file']).read_bytes()).hexdigest() == pin['sha256'],
                'Source pin differs')
    _, cap, _, _ = geometry(fixture['filling']['faces'])
    require(connected(cap) and len(cap) == 12 and all(len(ns) == 5 for ns in cap.values()), 'Filling is not degree five')
    proper(cap, dict(enumerate(fixture['filling']['colouring'])))
    results = []
    for case in fixture['cases']:
        raw = (here / case['configuration']).read_bytes()
        ring, patch = graph(raw)
        inside = set(range(ring, len(patch)))
        inner_faces = source_faces(raw)
        outer_faces = [tuple(f) for f in case['outer_faces']]
        _, small, _, _ = geometry(inner_faces + outer_faces)
        require(connected(small), 'Small sphere is disconnected')
        require(all(small[v] == set(patch[v]) for v in inside), 'A source core star changed')
        base = {v: ns-inside for v, ns in small.items() if v not in inside}
        before = dict(enumerate(case['boundary']))
        proper(base, before)
        profile = make_profile(patch, ring)
        require(eliminate(patch, ring, case['boundary'])[0] is None, 'Initial boundary extends')
        base_phases = phases(base, before, ring, profile)
        # Every exterior triangle receives a filling. Then test one nested filling too.
        faces, colours, blocks, next_vertex = list(inner_faces), dict(before), [], len(patch)
        for face in outer_faces:
            added, next_vertex, block = insert_filling(face, next_vertex, colours, fixture['filling'])
            faces.extend(added)
            blocks.append(block)
        filled_results = []
        for nested in range(2):
            _, ambient, _, _ = geometry(faces)
            require(connected(ambient), 'Filled sphere is disconnected')
            require(min(map(len, ambient.values())) >= 5, 'A full-map degree is below five')
            require(all(ambient[v] == set(patch[v]) for v in inside), 'A prescribed source degree changed')
            exterior = {v: ns-inside for v, ns in ambient.items() if v not in inside}
            proper(exterior, colours)
            # The first simultaneous attachments have disjoint hidden sets.
            if nested == 0:
                for block in blocks:
                    hidden, seam = set(block['hidden']), set(block['seam'])
                    require(all(exterior[v]-hidden <= seam for v in hidden), 'Attachment leaves its seam')
                    require(all(b in exterior[a] for a, b in combinations(seam, 2)), 'Seam is not a clique')
            phase_report = phases(exterior, colours, ring, profile)
            require(phase_report == base_phases, 'Filling changed fixed-pair boundary choices')
            current, retained, steps = dict(colours), dict(before), []
            for command in case['repair_commands']:
                current, support = switch(exterior, current, command['pair'], command['root'])
                retained, small_support = switch(base, retained, command['pair'], command['root'])
                require(len(small_support) == command['size'], 'Small repair support differs')
                if nested == 0:
                    require(len(support) == command['filled_size'], 'Filled repair support differs')
                require(all(current[v] == retained[v] for v in range(ring)), 'Repair failed to project')
                steps.append({'pair': command['pair'], 'root': command['root'],
                              'component_size': len(support),
                              'near_extension_profile': profile([current[j] for j in range(ring)])})
            word = [current[j] for j in range(ring)]
            core, _ = eliminate(patch, ring, word)
            require(core is not None, 'Repair does not extend to the core')
            proper(ambient, current | core)
            filled_results.append({'vertices': len(ambient), 'faces': len(faces),
                'minimum_degree': min(map(len, ambient.values())),
                'exact_source_stars_preserved': True, 'phase_choices_preserved': True,
                'repair_steps': steps, 'whole_colouring_reconstructed': True})
            if nested == 0:
                face = faces.pop()
                require(not inside.intersection(face), 'Nested filling touches the source core')
                added, next_vertex, _ = insert_filling(face, next_vertex, colours, fixture['filling'])
                faces.extend(added)
        results.append({'configuration': case['configuration'], 'boundary': case['boundary'],
            'small_vertices': len(small), 'initial_near_extension_profile': profile(case['boundary']),
            'proper_core_colourings': 384, 'fixed_pair_phases': base_phases, 'filled_examples': filled_results,
            'scope': 'These spheres have separating triangles. Minimum degree five does not establish the stronger connectivity hypotheses of a minimal counterexample.'})
    return {'evidence': 'Exact program replay of spherical fillings, failed monotone count potential and successful physical repairs. General clique history lifting is separately Lean checked.',
        'fixture_sha256': sha256(path.read_bytes()).hexdigest(),
        'lean_filling_source_sha256': lean_sha, 'cases': results,
        'scope': 'Refutes monotone improvement of this specified near-extension count vector on these inputs. Does not refute other potentials, nonmonotone repair, or a compositional Four Colour proof. No coverage or certificate-dependency reduction.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parent)
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')
