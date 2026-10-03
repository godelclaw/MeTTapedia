#!/usr/bin/env python3
"""Test fixed single-collapse transport using three explicit source colourings.

Fixed-alignment failures use explicit colourings and short local contradictions,
independently checked by searching the seven target interior vertices. A separate
enumeration tests adaptive choices. The Lean theorem certifies one fixed alignment.
"""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import re

from audit_diamond_sources import require, read_rows, validate


def graph(raw):
    rows = read_rows(raw.decode())
    validate(rows)
    n, ring = rows[0]
    adj = [set() for _ in range(n)]
    for a, _, *vs in rows[1:]:
        for b in vs:
            adj[a - 1].add(b - 1)
            adj[b - 1].add(a - 1)
    for a in range(ring):
        adj[a].add((a + 1) % ring)
        adj[(a + 1) % ring].add(a)
    return ring, adj


def trace(colours, ring):
    return tuple(colours[i] ^ colours[(i + 1) % ring] for i in range(ring))


def integrate(word):
    colours = [0]
    for c in word[:-1]:
        colours.append(colours[-1] ^ c)
    require(trace(colours, len(word)) == tuple(word), 'Trace does not close')
    return colours


def local_obstruction(adj, boundary):
    ring = len(boundary)
    allowed = {a: set(range(4)) - {boundary[b] for b in adj[a] if b < ring}
               for a in range(ring, len(adj))}
    steps = 0
    while True:
        if any(not cs for cs in allowed.values()):
            return 'forced_colour', steps
        removal = next(((b, next(iter(cs))) for a, cs in allowed.items() if len(cs) == 1
                        for b in sorted(adj[a]) if b in allowed and
                        next(iter(cs)) in allowed[b]), None)
        if removal is None:
            break
        b, colour = removal
        allowed[b].remove(colour)
        steps += 1
    for a in allowed:
        for b in sorted(adj[a] & allowed.keys()):
            for c in sorted(adj[a] & adj[b] & allowed.keys()):
                if len(allowed[a] | allowed[b] | allowed[c]) < 3:
                    return 'two_colour_triangle', steps
    return None


def extends(adj, boundary):
    """Independent exhaustive vertex assignment; no propagation certificate."""
    colours = list(boundary) + [-1] * (len(adj) - len(boundary))
    def visit(a):
        if a == len(adj):
            return True
        forbidden = {colours[b] for b in adj[a] if colours[b] >= 0}
        for c in range(4):
            if c not in forbidden:
                colours[a] = c
                if visit(a + 1):
                    return True
                colours[a] = -1
        return False
    return visit(len(boundary))


def boundary_support(adj, ring):
    """Enumerate all colourings with vertex zero coloured zero.

    Every colouring has exactly one translate of this form. Translation by
    bitwise xor preserves properness and all edge colours.
    """
    colours = [-1] * len(adj)
    colours[0] = 0
    support, count = set(), 0
    def visit(todo):
        nonlocal count
        if not todo:
            count += 1
            support.add(trace(colours, ring))
            return
        a = max(todo, key=lambda v: (len({colours[b] for b in adj[v] if colours[b] >= 0}),
                                    len(adj[v]), v))
        forbidden = {colours[b] for b in adj[a] if colours[b] >= 0}
        for c in range(4):
            if c not in forbidden:
                colours[a] = c
                visit(todo - {a})
                colours[a] = -1
    visit(set(range(1, len(adj))))
    return support, count


def collapse(word, seam, reverse, shift):
    rotated = word[seam:] + word[:seam]
    if rotated[0] == rotated[1]:
        return None
    target = (rotated[0] ^ rotated[1], *rotated[2:])
    if reverse:
        target = target[::-1]
    return target[shift:] + target[:shift]


def verify(here):
    fixture_path = here / 'five-triangle-collapse-example.json'
    fixture = json.loads(fixture_path.read_text())
    sources = [(here / fixture[role]).read_bytes() for role in ('source', 'target')]
    for role, raw in zip(('source', 'target'), sources):
        require(sha256(raw).hexdigest() == fixture[role + '_sha256'], 'Source hash differs')
    source_ring, source_adj = graph(sources[0])
    target_ring, target_adj = graph(sources[1])
    require((source_ring, target_ring) == (11, 10), 'Boundary sizes differ')
    colours = fixture['source_colourings']
    require(len(colours) == 3, 'Expected three covering witnesses')
    fixed = fixture['fixed_alignment_source_colouring']
    joint_colouring = fixture['joint_choice_source_colouring']
    for assignment in [*colours, fixed, joint_colouring]:
        require(len(assignment) == len(source_adj) and all(c in range(4) for c in assignment),
                'Invalid source colour assignment')
        require(all(assignment[a] != assignment[b] for a, ns in enumerate(source_adj) for b in ns),
                'Source colouring is improper')
    words = [trace(c, source_ring) for c in colours]
    used, reasons, max_steps, checked = Counter(), Counter(), 0, 0
    for seam in range(source_ring):
        for reverse in (False, True):
            for shift in range(target_ring):
                for index, word in enumerate(words):
                    target = collapse(word, seam, reverse, shift)
                    if target is None:
                        continue
                    boundary = integrate(target)
                    obstruction = local_obstruction(target_adj, boundary)
                    if obstruction is None:
                        continue
                    require(not extends(target_adj, boundary), 'Independent search found an extension')
                    reason, steps = obstruction
                    used[index] += 1
                    reasons[reason] += 1
                    max_steps = max(max_steps, steps)
                    checked += 1
                    break
                else:
                    raise AssertionError(f'Witnesses do not exclude alignment {(seam, reverse, shift)}')
    word = trace(fixed, source_ring)
    target = (word[0] ^ word[1], *word[2:])
    boundary = integrate(target)
    require(word[0] != word[1] and not extends(target_adj, boundary), 'Fixed alignment is not obstructed')
    require(all({boundary[b] for b in target_adj[a] if b < target_ring} == {1, 3}
                for a in (11, 14, 15)), 'The fixed triangle has different forbidden colours')
    require(all(b in target_adj[a] for a, b in ((11, 14), (14, 15), (15, 11))),
            'The target obstruction is not a triangle')

    lean = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor/FiveTriangleCollapseObstruction.lean'
    text = lean.read_text()
    encoded = re.findall(r'source := "(.*?)"', text, re.S)
    require(len(encoded) == 2, 'Lean source declarations differ')
    for value, raw in zip(encoded, sources):
        value = re.sub(r'\\\n\s*', '', value).replace(r'\n', '\n')
        require(read_rows(value) == read_rows(raw.decode()), 'Lean graph source differs')
    assignment = re.search(r'def assignment.*?\!\[(.*?)\]', text, re.S)
    require(assignment is not None, 'Lean assignment missing')
    require([int(x) for x in re.findall(r'c([0-3])', assignment[1])] == fixed,
            'Lean colouring differs')
    source_support, source_count = boundary_support(source_adj, source_ring)
    target_support, target_count = boundary_support(target_adj, target_ring)
    for adaptive_word in source_support:
        require(any(collapse(adaptive_word, seam, reverse, shift) in target_support
                    for seam in range(source_ring) for reverse in (False, True)
                    for shift in range(target_ring)), 'An interior trace has no adaptive choice')
    exterior = fixture['joint_choice_exterior']
    require(exterior['vertices'] == target_ring and
            exterior['boundary_order'] == list(range(target_ring)) and
            exterior['interior_edges'] == [[0, i] for i in range(2, target_ring - 1)],
            'Exterior is not the stated planar decagon fan')
    fan_edges = [*exterior['interior_edges'],
                 *[[i, (i + 1) % target_ring] for i in range(target_ring)]]
    def outside_accepts(et):
        cs = integrate(et)
        return all(cs[a] != cs[b] for a, b in fan_edges)
    joint_word = trace(joint_colouring, source_ring)
    choices = {collapse(joint_word, seam, reverse, shift)
               for seam in range(source_ring) for reverse in (False, True)
               for shift in range(target_ring)} - {None}
    inside = choices & target_support
    outside = {et for et in choices if outside_accepts(et)}
    require(inside and outside and not inside & outside, 'Joint-choice obstruction fails')
    for et in choices:
        require(extends(target_adj, integrate(et)) == (et in inside),
                'Independent joint-choice search disagrees')
    unrestricted = {et for et in target_support if outside_accepts(et)}
    require(unrestricted, 'The glued target and exterior lack a colouring')
    repair = fixture['coordinated_repair']
    seam, reverse, shift = repair['choice']
    ports = list(range(source_ring))
    ports = ports[seam:] + ports[:seam]
    ports.pop(1)
    if reverse:
        ports = [ports[0], *ports[:0:-1]]
    ports = ports[shift:] + ports[:shift]
    require(ports == repair['target_boundary_in_source_vertices'], 'Repair port map differs')
    glued = [set(vs) for vs in source_adj]
    for a, b in fan_edges:
        glued[ports[a]].add(ports[b])
        glued[ports[b]].add(ports[a])
    state = joint_colouring.copy()
    require(all(state[a] != state[b] for a, vs in enumerate(glued) for b in vs),
            'Initial colouring does not colour the source with its actual exterior')
    for move in repair['path']:
        active = set(move['colours'])
        require(len(active) == 2, 'A Kempe step needs two distinct colours')
        component = set(move['component'])
        require(component and all(state[v] in active for v in component), 'Inactive switched vertex')
        reached = {min(component)}
        todo = list(reached)
        while todo:
            for v in glued[todo.pop()]:
                if v not in reached and state[v] in active:
                    reached.add(v)
                    todo.append(v)
        require(reached == component, 'The switched set is not a whole component in the glued graph')
        a, b = move['colours']
        state = [b if c == a and v in component else a if c == b and v in component else c
                 for v, c in enumerate(state)]
        require(all(state[a] != state[b] for a, vs in enumerate(glued) for b in vs),
                'The switch broke a source or exterior edge')
    require(state == repair['final_source_colouring'], 'Final source colours differ')
    final_target = repair['final_target_colouring']
    require(len(final_target) == len(target_adj) and all(c in range(4) for c in final_target),
            'Invalid target assignment')
    require(all(final_target[a] != final_target[b]
                for a, vs in enumerate(target_adj) for b in vs), 'Improper target colouring')
    require(all(final_target[a] != final_target[b] for a, b in fan_edges), 'Target breaks the exterior')
    require(all(final_target[i] == state[ports[i]] for i in range(target_ring)),
            'The actual boundary vertex colours do not agree')
    require(trace(final_target, target_ring) == tuple(repair['final_target_trace']),
            'Final target trace differs')

    joint_lean = lean.with_name('FiveTriangleJointChoice.lean')
    joint_text = joint_lean.read_text()
    for name, expected in [('before', joint_colouring), ('target', final_target)]:
        array = re.search(r'def ' + name + r'\s*:.*?\!\[(.*?)\]', joint_text, re.S)
        require(array is not None and [int(x) for x in re.findall(r'c([0-3])', array[1])] == expected,
                f'Lean joint assignment differs: {name}')
    port_array = re.search(r'def ports.*?\!\[(.*?)\]', joint_text, re.S)
    require(port_array is not None and [int(x) for x in re.findall(r'\d+', port_array[1])] == ports,
            'Lean port map differs')
    return {'evidence': 'Exact independent program checks; one fixed-alignment obstruction is separately proved in Lean.',
            'source': fixture['source'], 'target': fixture['target'],
            'covering_source_colourings': len(colours), 'fixed_alignments_excluded': checked,
            'alignments_per_witness': dict(sorted(used.items())),
            'local_obstructions': dict(reasons), 'max_forced_colour_steps': max_steps,
            'independent_target_searches': checked + 1,
            'independent_joint_target_searches': len(choices),
            'adaptive_interior_choice': {
                'source_colourings_fixing_vertex_zero': source_count,
                'target_colourings_fixing_vertex_zero': target_count,
                'source_boundary_traces': len(source_support),
                'target_boundary_traces': len(target_support),
                'all_source_traces_have_some_successful_alignment': True,
                'compatible_exterior_choice_established': False,
                'graph_operation_or_Kempe_transport_established': False},
            'joint_choice_obstruction': {
                'source_word': joint_word,
                'distinct_proper_collapses': len(choices),
                'interior_compatible': len(inside), 'exterior_compatible': len(outside),
                'jointly_compatible': len(inside & outside),
                'interior_example': min(inside), 'exterior_example': min(outside),
                'exterior': 'Planar decagon triangulated by a fan at boundary vertex zero',
                'unrestricted_joint_traces': len(unrestricted),
                'unrestricted_joint_example': min(unrestricted),
                'scope': 'The source colouring is held fixed. Recolouring the source or using '
                         'another boundary operation is not excluded.'},
            'coordinated_repair': {'kempe_steps': len(repair['path']),
                'switched_vertices': [m['component'] for m in repair['path']],
                'whole_components_in_glued_graph': True,
                'source_and_target_include_same_fan': True,
                'actual_boundary_vertex_colours_agree': True,
                'uniform_repair_or_strict_reduction_claimed': False},
            'fixed_alignment': {'source_word': word, 'collapsed_word': target,
                                'target_boundary_colours': boundary,
                                'triangle_source_labels': [12, 15, 16],
                                'allowed_colours': [0, 2]},
            'scope': 'No fixed seam/dihedral alignment satisfies unconditional successful-trace reconstruction. '
                     'Pointwise adaptive interior choices exist. An explicit planar exterior defeats '
                     'joint selection from one fixed source colouring; coordinated recolouring is not excluded.',
            'fixture_sha256': sha256(fixture_path.read_bytes()).hexdigest(),
            'lean_source_sha256': sha256(lean.read_bytes()).hexdigest(),
            'joint_lean_source_sha256': sha256(joint_lean.read_bytes()).hexdigest(),
            'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parent)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
