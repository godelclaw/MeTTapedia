#!/usr/bin/env python3
"""Check spatial and switch-count obstructions on actual D0092 exteriors.

The radius-two obstruction and radius-three endpoint are also checked in
Lean on the literal graph. Spherical geometry and the separate three-switch
lower bound are independent program evidence. Discovery used a SAT solver;
this replay needs no solver and checks every supplied colouring directly.
"""
import argparse
import ast
from collections import Counter
from functools import lru_cache
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path
import re

from audit_boundary_observation import components, proper, switch
from audit_chain_boundary import short_cycles, subdivide
from audit_cycle_blocks import sphere
from audit_diamond_sources import require
from audit_flat_seven_return import verify as verify_sphere
from audit_forest_repair import load_case
from audit_independent_repair import complete_patch
from audit_two_port_core import eliminate
from probe_flat_pairs import geometry, initial_faces, read_rules, reading
from probe_hidden_exterior import canonical


def source_faces(here, fixture):
    original = json.loads((here / fixture['source_fixture']).read_text())
    faces = subdivide(initial_faces())
    for a, b, c, d in original['edge_flip_history'][:fixture['edge_flip_prefix']]:
        darts, adj, _, _ = geometry(faces)
        i, ac = darts[a, b]
        j, ad = darts[b, a]
        require((ac, ad) == (c, d) and d not in adj[c], 'Invalid source flip')
        faces[i], faces[j] = (c, d, b), (d, c, a)
    return faces


def triangle_refutation(adj, lists):
    """Branch only when triangle support propagation stops. Each branch
    retains all allowed colours; an empty list is a contradiction."""
    vertices = sorted(adj)
    triangles = [(u, v, w) for u in vertices for v in sorted(adj[u]) if v > u
                 for w in sorted(adj[u] & adj[v]) if w > v]
    counts = Counter()
    def refute(dom):
        counts['nodes'] += 1
        require(counts['nodes'] <= 100, 'Bounded small proof became a large search')
        while all(dom.values()):
            change = False
            for tri in triangles:
                for target in tri:
                    u, w = [v for v in tri if v != target]
                    new = {a for a, b, c in product(dom[target], dom[u], dom[w])
                           if len({a, b, c}) == 3}
                    if new != dom[target]:
                        dom[target] = new
                        counts['triangle_steps'] += 1
                        change = True
                        if not new:
                            counts['leaves'] += 1
                            return True
            if not change:
                break
        todo = [v for v in vertices if len(dom[v]) > 1]
        if not todo:
            return False
        v = min(todo, key=lambda v: (len(dom[v]), -len(adj[v])))
        counts['branches'] += 1
        return all(refute({u: {c} if u == v else set(cs) for u, cs in dom.items()})
                   for c in sorted(dom[v]))
    require(refute({v: set(cs) for v, cs in lists.items()}), 'The local region extends')
    return dict(counts)


def verify(here):
    path = here / 'local-repair-radius-example.json'
    fixture = json.loads(path.read_text())
    source_path = here / fixture['source_fixture']
    require(sha256(source_path.read_bytes()).hexdigest() == fixture['source_fixture_sha256'],
            'Source geometry pin differs')
    geo = verify_sphere(here, source_path.name)
    source = json.loads(source_path.read_text())
    seed = json.loads((here / 'independent-repair-example.json').read_text())['cases'][0]
    ambient, exterior, occurrence, ring, patch, ports, _ = load_case(here, seed)
    core = set(occurrence['images'][ring:])
    initial = {v: c for v, c in enumerate(fixture['initial']) if c is not None}
    proper(exterior, initial)
    require({v for v, c in enumerate(fixture['initial']) if c is None} == core,
            'Wrong deleted core')
    words = json.loads((here / 'core-profile-switch-example.json').read_text())['initial']
    require([initial[v] for v in ports] == words[0], 'Wrong first source word')
    balls = [core]
    for _ in range(3):
        balls.append(balls[-1] | set().union(*(ambient[v] for v in balls[-1])))
    local = {v: ambient[v] & balls[2] for v in balls[2]}
    lists = {v: set(range(4)) - {initial[w] for w in ambient[v] - balls[2]} for v in local}
    proof = triangle_refutation(local, lists)
    final = dict(enumerate(fixture['extension_fixing_outside_radius_three']))
    proper(ambient, final)
    require(all(final[v] == initial[v] for v in exterior if v not in balls[3]),
            'Positive endpoint changes the outside of radius three')
    require(any(final[v] != initial[v] for v in exterior if v not in balls[2]),
            'Positive endpoint contradicts the radius-two obstruction')
    lean = here.parents[2] / 'lean/mettapedia/Mettapedia/GraphTheory/FourColor/LocalRepairRadius.lean'
    text = lean.read_text()
    def literal(name):
        return ast.literal_eval(re.search(r'^def ' + name + r' : .* := (\[.*\])$', text, re.M)[1])
    require(literal('edges') == [(u, v) for u in sorted(ambient) for v in sorted(ambient[u]) if u < v],
            'Lean graph differs from the sphere')
    for name, ball in zip(['core', 'ballOne', 'ballTwo', 'ballThree'], balls):
        require(literal(name) == sorted(ball), 'Lean neighbourhood differs: ' + name)
    require(literal('initialData') == [initial.get(v, 0) for v in range(len(ambient))],
            'Lean starting colours differ')
    require(literal('finalData') == list(final.values()), 'Lean positive endpoint differs')

    other_path = here / 'three-switch-strong-example.json'
    other = json.loads(other_path.read_text())
    require(other['source_fixture_sha256'] == fixture['source_fixture_sha256'], 'Source pin differs')
    flat = list(map(int, other['face_data'].split()))
    require(len(flat) == 3 * geo['faces'], 'Wrong spherical face count')
    faces = [tuple(flat[i:i + 3]) for i in range(0, len(flat), 3)]
    graph = sphere(faces)
    darts, graph2, nxt, prev = geometry(faces)
    require(graph == graph2, 'Independent adjacency decoders disagree')
    _, original, old_nxt, _ = geometry(source_faces(here, source))
    require(all(graph[v] == original[v] and
                all(nxt[v, u] == old_nxt[v, u] for u in graph[v]) for v in core),
            'Source stars or cyclic orders changed')
    require(all(5 <= len(ns) <= 7 for ns in graph.values()), 'Ambient degree bounds differ')
    cycle_count = short_cycles(faces, darts, graph)
    adj = {v: ns - core for v, ns in graph.items() if v not in core}
    start = {v: c for v, c in enumerate(other['initial']) if c is not None}
    proper(adj, start)
    require([start[v] for v in ports] == words[1], 'Wrong second source word')

    @lru_cache(None)
    def extends(word):
        answer = eliminate(patch, ring, word)[0] is not None
        require(answer == (complete_patch(patch, word) is not None), 'Core solvers disagree')
        return answer
    vertices = sorted(adj)
    index = [vertices.index(v) for v in ports]
    state = tuple(start[v] for v in vertices)
    require(not extends(tuple(state[i] for i in index)), 'Starting boundary already extends')
    seen, front = {canonical(state)}, [state]
    levels = []
    for _ in range(2):
        following = []
        for state in front:
            colouring = dict(zip(vertices, state))
            for a, b in combinations(range(4), 2):
                for support in components(adj, colouring, (a, b)):
                    target = tuple((b if c == a else a) if v in support else c
                                   for v, c in zip(vertices, state))
                    signature = canonical(target)
                    if signature in seen:
                        continue
                    seen.add(signature)
                    require(not extends(tuple(target[i] for i in index)), 'Two switches suffice')
                    following.append(target)
        levels.append(len(following))
        front = following
    current = dict(start)
    require(len(other['history']) == 3, 'Expected three physical switches')
    for a, b, root, size in other['history']:
        current, support = switch(adj, current, (a, b), root)
        require(len(support) == size, 'Component size differs')
    witness, _ = eliminate(patch, ring, tuple(current[v] for v in ports))
    require(witness is not None, 'Three-switch endpoint does not extend')
    proper(graph, current | {occurrence['images'][v]: c for v, c in witness.items()})
    rules, _ = read_rules(here)
    charges = []
    for v in source['centres']:
        charge = 10 * (6 - len(graph[v]))
        for u in graph[v]:
            for a, b, sign in [(u, v, 1), (v, u, -1)]:
                charge += sum(sign * rule[1][0][3] for rule in rules
                              if reading(rule, a, b, graph, nxt, prev) is not None)
        charges.append(charge)
    return {'classification': 'CHECKED_LOCALITY_OBSTRUCTION_AND_PROGRAM_SWITCH_BOUND',
            'source_geometry': source['configuration_source'],
            'radius_obstruction': {'vertices': len(ambient), 'exterior_vertices': len(exterior),
                'ball_sizes': list(map(len, balls)), 'triangle_refutation': proof,
                'centre_charges': geo['charges'], 'short_cycles_checked': geo['short_cycles_checked'],
                'lean_graph_and_colours_match': True, 'endpoint_fixing_radius_three': True,
                'physical_history_confined_to_radius_three_claimed': False},
            'three_switch_obstruction': {'vertices': len(graph), 'exterior_vertices': len(adj),
                'ambient_degrees': dict(sorted(Counter(map(len, graph.values())).items())),
                'short_cycles_checked': cycle_count, 'obstructing_short_cycles': 0,
                'source_core_stars_and_rotations_preserved': True,
                'original_centre_charges': charges, 'minimum_physical_steps': 3,
                'new_palette_classes_by_depth': levels, 'history': other['history'],
                'kernel_checked': False},
            'pins': {p.name: sha256(p.read_bytes()).hexdigest() for p in [path, other_path, lean]},
            'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
            'limits': ['No unbounded repair-radius or switch-count lower bound.',
                'The obstructions concern the supplied starting colourings; other starting colourings or selected pieces remain possible.',
                'The modified three-switch sphere need not retain the original flat centres.',
                'No failure of adaptive larger-region repair, alternative reduction, or compact compositional proofs.',
                'No whole-ball flatness, minimal-counterexample status, occurrence supply, or catalogue reduction.',
                'Spherical geometry and the three-switch lower bound remain independent program checks.']}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parent)
    encoded = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(encoded)
    print(encoded, end='')
