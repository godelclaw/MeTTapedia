#!/usr/bin/env python3
"""Check a palette-rigid source, its spherical rotation, and failed seam.

Six connected pair supports certify the invariant without enumerating histories.
The Lean consumer independently proves closure for arbitrary physical histories.
The spherical embedding receipt is a separate exact program check.
"""
import argparse
from hashlib import sha256
from itertools import combinations, permutations
import json
from pathlib import Path
import re

from audit_diamond_sources import require, read_rows
from audit_five_triangle_collapse import graph, extends


def cyclic_equal(a, b):
    return len(a) == len(b) and any(a == b[i:] + b[:i] for i in range(len(b)))


def verify(here):
    fixture_file = here / 'five-triangle-kempe-trap-example.json'
    f = json.loads(fixture_file.read_text())
    raw = {}
    for role in ('source', 'target'):
        raw[role] = (here / f[role]).read_bytes()
        require(sha256(raw[role]).hexdigest() == f[role + '_sha256'], 'Source pin differs')
    ring, source = graph(raw['source'])
    target_ring, target = graph(raw['target'])
    require((len(source), ring, len(target), target_ring) == (18, 11, 17, 10), 'Wrong sizes')
    for a, b in f['exterior']:
        require(a != b and a < ring and b < ring, 'Invalid exterior edge')
        source[a].add(b)
        source[b].add(a)

    # Exact orientable rotation certificate: one star per vertex, every dart
    # in one face, connected sphere by Euler characteristic two.
    rotation = f['rotation']
    require(len(rotation) == len(source), 'Missing rotation star')
    for v, star in enumerate(rotation):
        require(len(star) == len(set(star)) and set(star) == source[v], 'Wrong cyclic star')
    seen, todo = {0}, [0]
    while todo:
        v = todo.pop()
        for w in source[v] - seen:
            seen.add(w)
            todo.append(w)
    require(len(seen) == len(source), 'Graph disconnected')
    remaining = {(v, w) for v, ns in enumerate(source) for w in ns}
    darts, faces = len(remaining), []
    while remaining:
        start = min(remaining)
        d, face = start, []
        while True:
            require(d in remaining, 'Face repeats before closing')
            remaining.remove(d)
            u, v = d
            face.append(u)
            star = rotation[v]
            d = (v, star[(star.index(u) - 1) % len(star)])
            if d == start:
                break
        faces.append(face)
    require(len(source) - darts // 2 + len(faces) == 2, 'Rotation is not spherical')
    require(all(len(face) == len(set(face)) == 3 for face in faces), 'Not a triangulation')
    rows = read_rows(raw['source'].decode())[1:]
    require(any(all(cyclic_equal(rotation[a - 1], [v - 1 for v in (vs[::-1] if rev else vs)])
                    for a, _, *vs in rows) for rev in (False, True)), 'Core orientation differs')

    assignment = f['assignment']
    def proper(g, c):
        return len(c) == len(g) and all(x in range(4) for x in c) and all(
            c[v] != c[w] for v, ns in enumerate(g) for w in ns)
    require(proper(source, assignment), 'Initial colouring improper')
    require(len(f['chains']) == 6, 'Expected six pair chains')
    for (a, b), chain in zip(combinations(range(4), 2), f['chains']):
        active = {v for v, c in enumerate(assignment) if c in (a, b)}
        require(set(chain) == active and bool(chain), 'Chain does not cover the active support')
        require(all(v in source[u] for u, v in zip(chain, chain[1:])), 'Disconnected pair chain')

    triangle = (11, 12, 14)
    require(all(v in target[u] for u, v in combinations(triangle, 2)), 'Missing target triangle')
    require(len(f['ports']) == 2, 'Expected both boundary orientations')
    for ports in f['ports']:
        require(len(ports) == len(set(ports)) == target_ring, 'Port map is not injective')
        for i, j in combinations(range(target_ring), 2):
            fan = j == i + 1 or (i == 0 and j == target_ring - 1) or i == 0
            require((ports[j] in source[ports[i]]) == fan, 'Interface is not exactly the fan')
        boundary = [assignment[v] for v in ports]
        for v in triangle:
            forbidden = {boundary[w] for w in target[v] if w < target_ring}
            require(forbidden == {1, 3}, 'Target triangle not restricted to two colours')
        require(not extends(target, boundary), 'Independent search found a target extension')
        for palette in permutations(range(4)):
            require(not extends(target, [palette[c] for c in boundary]), 'A renamed state extends')

    target_with_fan = [set(ns) for ns in target]
    for v in range(1, target_ring):
        target_with_fan[0].add(v)
        target_with_fan[v].add(0)
    require(proper(source, f['compatible_source']), 'Alternative source is improper')
    require(proper(target_with_fan, f['compatible_target']), 'Alternative target is improper')
    require(all(f['compatible_source'][v] == f['compatible_target'][i]
                for i, v in enumerate(f['ports'][0])), 'Alternative witnesses disagree')

    lean_file = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor/FiveTriangleKempeTrap.lean'
    text = lean_file.read_text()
    for name, key in [('assignment', 'assignment'), ('goodSource', 'compatible_source'),
                      ('goodTarget', 'compatible_target')]:
        match = re.search(r'def ' + name + r'.*?!\[(.*?)\]', text, re.S)
        require(match is not None and [int(x) for x in re.findall(r'c([0-3])', match[1])] == f[key],
                'Lean assignment differs')
    for name, data in [('chains', f['chains']), ('ports', f['ports'])]:
        block = text.split('def ' + name + ' ', 1)[1].split('\ndef ', 1)[0].split('\ntheorem ', 1)[0]
        lists = re.findall(r'\[([0-9, ]+)\]', block)
        require([[int(x) for x in re.findall(r'\d+', xs)] for xs in lists] == data,
                'Lean chains or ports differ')
    block = text.split('def exterior ', 1)[1].split('\ndef ', 1)[0]
    require([[int(a), int(b)] for a, b in re.findall(r'\((\d+), (\d+)\)', block)] == f['exterior'],
            'Lean exterior differs')
    return {
        'evidence': 'Exact program checks; Kempe invariant and reconstruction obstruction separately certified in Lean.',
        'vertices': len(source), 'edges': darts // 2, 'triangular_faces': len(faces),
        'spherical_rotation_checked': True, 'core_rotation_preserved': True,
        'embedding_kernel_certified': False,
        'minimum_degree': min(map(len, source)),
        'pair_supports_connected': 6, 'palette_orbit_size': 24,
        'both_seam_orientations_excluded': True,
        'target_triangle': list(triangle), 'target_allowed_colours': [0, 2],
        'alternative_compatible_colourings_checked': True,
        'scope': 'A prescribed source colouring cannot reach a compatible target at the fixed seam by any finite whole-component Kempe history. Another starting colouring works. Alternative seams, other operations and stronger minimal-counterexample hypotheses remain open.',
        'credited_compression': False,
        'fixture_sha256': sha256(fixture_file.read_bytes()).hexdigest(),
        'lean_source_sha256': sha256(lean_file.read_bytes()).hexdigest(),
        'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parent)
    rendered = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end='')
