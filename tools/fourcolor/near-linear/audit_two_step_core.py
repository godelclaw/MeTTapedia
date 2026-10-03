#!/usr/bin/env python3
"""Check shortest two-switch repairs and short one-step nonextension traces.

All physical components of the two specified initial exteriors are checked.
The generated Lean module proves source-core nonextension for every resulting
boundary using at most six forced-colour deductions. Concrete spherical
geometry, component enumeration and physical execution remain program evidence.
"""
import argparse
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path

from audit_boundary_observation import components, observe, proper, switch
from audit_cycle_blocks import source_faces, sphere
from audit_diamond_sources import read_rows, require, validate
from audit_forest_repair import load_case
from audit_independent_repair import complete_patch
from audit_two_port_core import eliminate, repair_exterior
from probe_flat_pairs import geometry


def forced_trace(patch, ring, word):
    """Find a short list-propagation contradiction, not a colouring search."""
    lists = {v: set(range(4)) - {word[x] for x in patch[v] if x < ring}
             for v in range(ring, len(patch))}
    trace = []
    while all(lists.values()):
        found = False
        for v in sorted(lists):
            if len(lists[v]) != 1:
                continue
            c = next(iter(lists[v]))
            for u in sorted(patch[v]):
                if u in lists and c in lists[u]:
                    lists[u].remove(c)
                    trace.append([v - ring, u - ring])
                    found = True
                    break
            if found:
                break
        require(found, 'Propagation stalled; do not infer nonextension')
    return {'edges': trace, 'empty_vertex': min(v for v in lists if not lists[v]) - ring}


def one_switches(adj, colouring, ports, patch, ring):
    rows, silent = [], []
    for pair in combinations(range(4), 2):
        blocks = components(adj, colouring, pair)
        # Independently check disjointness and exact coverage of active vertices.
        active = {x for x in adj if colouring[x] in pair}
        require(sum(map(len, blocks)) == len(active) and set().union(*blocks) == active,
                'Component census does not partition the active vertices')
        for block in blocks:
            root = min(block)
            target, support = switch(adj, colouring, pair, root)
            require(support == block, 'Component execution differs')
            record = {'pair': list(pair), 'root': root, 'size': len(block)}
            if not block & set(ports):
                require(all(target[x] == colouring[x] for x in ports), 'Silent word changed')
                silent.append(record)
                continue
            word = [target[x] for x in ports]
            extension, _ = eliminate(patch, ring, word)
            # Independent backtracking is a cross-check of this tiny core only.
            require((extension is not None) == (complete_patch(patch, word) is not None),
                    'Independent extension test disagrees')
            rows.append(record | {'ports': [i for i, x in enumerate(ports) if x in block],
                                  'word': word, 'extends': extension is not None})
    return rows, silent


def verify(here):
    path = here / 'two-step-core-example.json'
    fixture = json.loads(path.read_text())
    require([c['source_case'] for c in fixture['cases']] == [0, 1], 'Expected both source cases in order')
    for pin in fixture['sources']:
        require(sha256((here / pin['file']).read_bytes()).hexdigest() == pin['sha256'],
                'Source pin differs')
    sources = json.loads((here / 'independent-repair-example.json').read_text())['cases']
    results = []
    for selected in fixture['cases']:
        case = sources[selected['source_case']]
        ambient, adj, occurrence, ring, patch, ports, initial = load_case(here, case)
        faces = source_faces(here, case)
        require(ambient == sphere(faces), 'Spherical graph differs')
        _, _, nexts, prevs = geometry(faces)
        images = occurrence['images']
        require(len(images) == len(set(images)) == len(patch), 'Occurrence is not injective')
        require(occurrence['orientation'] in ('source', 'reverse'), 'Unknown source orientation')
        turn = nexts if occurrence['orientation'] == 'source' else prevs
        rows = read_rows((here / occurrence['configuration']).read_text())
        validate(rows)
        for v, degree, *neighbours in rows[1:]:
            x = images[v - 1]
            ys = [images[y - 1] for y in neighbours]
            require(len(ambient[x]) == degree and ambient[x] == set(ys), 'Full core star differs')
            require(all(turn[x, y] == ys[(k + 1) % len(ys)] for k, y in enumerate(ys)),
                    'Core cyclic order differs')
        require(all(images[y] in ambient[images[x]] for x, ns in enumerate(patch) for y in ns),
                'Source adjacency or ordered boundary differs')
        word = [initial[x] for x in ports]
        require(eliminate(patch, ring, word)[0] is None, 'Initial boundary extends')
        visible, silent = one_switches(adj, initial, ports, patch, ring)
        require(all(not r['extends'] for r in visible), 'A one-switch repair exists')
        words = [word] + [r['word'] for r in visible]
        traces = [forced_trace(patch, ring, w) for w in words]
        require(max(len(t['edges']) for t in traces) <= 6, 'Unexpected propagation cost')
        require(len(selected['repair']) == 2, 'Expected a two-switch repair')
        repaired, moves = repair_exterior(adj, initial, selected['repair'])
        final_word = [repaired[x] for x in ports]
        core, _ = eliminate(patch, ring, final_word)
        require(core is not None, 'Two-switch target does not extend')
        whole = repaired | {occurrence['images'][x]: c for x, c in core.items()}
        proper(ambient, whole)
        intermediate, _ = switch(adj, initial, moves[0]['pair'], moves[0]['root'])
        supports = []
        current = initial
        for move in moves:
            current, support = switch(adj, current, move['pair'], move['root'])
            supports.append(support)
        result = {'configuration': occurrence['configuration'], 'ambient_vertices': len(ambient),
            'exterior_vertices': len(adj), 'boundary_ports': ring,
            'initial_boundary': word, 'visible_moves': visible, 'silent_moves': silent,
            'forced_traces': traces, 'repair': moves,
            'intermediate_boundary': [intermediate[x] for x in ports],
            'final_boundary': final_word, 'core_assignment': [core[x] for x in range(ring, len(patch))],
            'vertices_touched': len(set().union(*supports)),
            'vertex_switches': sum(map(len, supports)), 'shortest_switch_count': 2,
            'complete_source_stars_and_cyclic_order_checked': True,
            'whole_sphere_reconstructed': True}
        if 'silent_preparation' in selected:
            prepared, prep_moves = repair_exterior(adj, initial, [selected['silent_preparation']])
            require([prepared[x] for x in ports] == word, 'Preparation is not boundary silent')
            next_moves, _ = one_switches(adj, prepared, ports, patch, ring)
            successes = [r for r in next_moves if r['extends']]
            require(successes, 'Preparation opens no successful next move')
            result['silent_preparation'] = {'moves': prep_moves, 'successful_next_moves': successes,
                'same_boundary': True, 'same_six_partitions': observe(adj, initial, ports) ==
                    observe(adj, prepared, ports), 'initial_repair_distance': 2,
                'prepared_repair_distance': 1}
        results.append(result)
    return {'evidence': 'Exact program census and replay; source-core rejection and acceptance are Lean checked.',
            'fixture_sha256': sha256(path.read_bytes()).hexdigest(), 'cases': results,
            'scope': 'Two specified exteriors. No one-switch repair exists; a two-switch repair does. '
                     'Silent preparation is one option, not necessary on every successful path. '
                     'No universal two-switch theorem or coverage claim.'}


def lean_module(result):
    """Small source words and forced-edge traces consumed by one soundness law."""
    out = ['import MettapediaFourColor.TwoPortCoreElimination',
           'import Mettapedia.GraphTheory.Kempe.ListPropagation', '', '/-!',
           '# One-switch boundaries of two source exteriors do not extend', '',
           'Generated by `audit_two_step_core.py`. Each rejection uses a short',
           'edge propagation trace on the decoded core, never a table of complete',
           'core colourings. Concrete spherical realizations and exhaustiveness',
           'of their physical component census are separately checked program evidence.',
           '-/', '', 'namespace FourColor.TwoStepCoreProgress', '',
           'open Color FiveTriangleCollapseObstruction TwoPortCoreElimination',
           'open SimpleGraph.ColoringListPropagation', '']
    for name, which, row in zip(['upper', 'lower'], ['false', 'true'], result['cases']):
        ring = row['boundary_ports']
        words = [row['initial_boundary']] + [r['word'] for r in row['visible_moves']]
        n = len(words)
        colours = lambda w: '![' + ','.join('c' + str(c) for c in w) + ']'
        vector = lambda lines: '![' + ',\n    '.join(lines) + ']'
        out += [f'def {name}Word : Fin {n} → Fin {ring} → Color :=',
                '  ' + vector([colours(w) for w in words]), '',
                f'def {name}Trace : Fin {n} → List (Fin 7 × Fin 7) :=',
                '  ' + vector(['[' + ','.join(f'({u},{v})' for u, v in t['edges']) + ']'
                               for t in row['forced_traces']]), '',
                f'def {name}Empty : Fin {n} → Fin 7 :=',
                '  ![' + ','.join(str(t['empty_vertex']) for t in row['forced_traces']) + ']', '',
                f'def {name}Lists (word : Fin {ring} → Color) (v : Fin 7) : Finset Color :=',
                f'  Finset.univ.filter fun c => ∀ i : Fin {ring},',
                f'    {name}.graph.Adj ({name}Vertex v) (i.castAdd 7) → c ≠ word i', '',
                f'theorem {name}_traces_valid : ∀ i : Fin {n},',
                f'    (∀ e ∈ {name}Trace i, (core {which}).Adj e.1 e.2) ∧',
                f'    run ({name}Lists ({name}Word i)) ({name}Trace i) ({name}Empty i) = ∅ := by',
                '  decide +kernel', '',
                f'theorem {name}_no_extension (i : Fin {n}) (C : {name}.graph.Coloring Color)',
                f'    (boundary : ∀ j : Fin {ring}, C (j.castAdd 7) = {name}Word i j) : False := by',
                f'  let D : (core {which}).Coloring Color :=',
                f'    .mk (fun v => C ({name}Vertex v)) (fun h => C.valid h)',
                f'  have fits (v : Fin 7) : D v ∈ {name}Lists ({name}Word i) v := by',
                f'    simp only [{name}Lists, Finset.mem_filter, Finset.mem_univ, true_and]',
                '    intro j hj',
                f'    change C ({name}Vertex v) ≠ {name}Word i j',
                '    simpa only [boundary j] using C.valid hj',
                f'  exact empty_refutes ({name}Lists ({name}Word i)) ({name}Trace i)',
                f'    ({name}_traces_valid i).1 ({name}Empty i) ({name}_traces_valid i).2 ⟨D, fits⟩', '',
                f'def {name}Repaired : Fin {ring + 7} → Color :=',
                '  ' + colours(row['final_boundary'] + row['core_assignment']), '',
                f'theorem {name}_repaired_proper : ∀ x y, {name}.graph.Adj x y →',
                f'    {name}Repaired x ≠ {name}Repaired y := by decide +kernel', '']
    return '\n'.join(out + ['end FourColor.TwoStepCoreProgress', ''])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--lean-output', type=Path)
    parser.add_argument('--check-lean', type=Path)
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parent)
    generated = lean_module(result)
    if args.lean_output:
        args.lean_output.write_text(generated)
    if args.check_lean:
        require(args.check_lean.read_text() == generated, 'Lean source differs from replay')
    output = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(output)
    print(output, end='')
