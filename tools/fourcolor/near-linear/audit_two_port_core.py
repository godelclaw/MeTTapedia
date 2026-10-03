#!/usr/bin/env python3
"""Eliminate the two five-triangle cores using exact binary port relations.

The source ear stages and the two nonextension claims are Lean checked.
This program independently replays their spherical exteriors, witnesses,
matrix calculations and physical repairs. No table over all boundary words
or all core colourings is constructed.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path

from audit_boundary_observation import proper, switch
from audit_cycle_blocks import source_faces, sphere
from audit_diamond_sources import require
from audit_forest_repair import load_case
from audit_independent_repair import complete_patch


def eliminate(patch, ring, word, relax_ear=None):
    """Exact ear elimination, with an optional deliberately unsound marginal.

    The altered version omits reconstruction of that ear and returns a
    witness for the remaining graph, exposing the missing joint choice.
    """
    active = {v: set(patch[v]) - set(range(ring)) for v in range(ring, len(patch))}
    lists = {v: set(range(4)) - {word[x] for x in patch[v] if x < ring} for v in active}
    relations = {(u, v): {(a, b) for a in range(4) for b in range(4) if a != b}
                 for u in active for v in active[u]}
    records, snapshots = [], []
    tests = 0
    while len(active) > 2:
        ears = [v for v in sorted(active) if len(active[v]) == 2 and
                all(y in active[x] for x in active[v] for y in active[v] if x != y)]
        require(ears, 'The remaining core has no triangular ear')
        v = ears[0]
        u, w = sorted(active[v])
        message = set()
        for a in sorted(lists[u]):
            for b in sorted(lists[w]):
                for c in sorted(lists[v]):
                    tests += 1
                    if (a, c) in relations[u, v] and (c, b) in relations[v, w]:
                        message.add((a, b))
                        break
        marginal = {(a, b) for a, _ in message for _, b in message}
        snapshots.append((v, u, w, set(relations[u, v]), set(relations[v, w])))
        previous = set(relations[u, w])
        relations[u, w] &= marginal if v == relax_ear else message
        relations[w, u] = {(b, a) for a, b in relations[u, w]}
        records.append({'ear': v, 'ports': [u, w],
            'exact_message': sorted(message), 'kept_relation': sorted(relations[u, w]),
            'phantom_pairs': sorted((marginal - message) & previous)})
        for x in active[v]:
            active[x].remove(v)
            del relations[x, v], relations[v, x]
        del active[v]
    require(len(active) == 2, 'Wrong terminal size')
    u, w = sorted(active)
    require(w in active[u], 'The terminal ports are not adjacent')
    terminal = sorted((a, b) for a, b in relations[u, w] if a in lists[u] and b in lists[w])
    assignment = None
    if terminal:
        a, b = terminal[0]
        assignment = {u: a, w: b}
        for v, u, w, left, right in reversed(snapshots):
            if v == relax_ear:
                continue
            choices = [c for c in sorted(lists[v]) if
                       (assignment[u], c) in left and (c, assignment[w]) in right]
            require(choices, 'An exact message lost its reconstruction witness')
            assignment[v] = choices[0]
        # Check all source edges, including every boundary attachment.
        colouring = dict(enumerate(word)) | assignment
        omitted = {relax_ear} if relax_ear is not None else set()
        proper({x: set(ns) - omitted for x, ns in enumerate(patch) if x not in omitted}, colouring)
    return assignment, {'stages': records, 'terminal_ports': [u, w], 'terminal_pairs': terminal,
                        'colour_triples_tested': tests, 'max_relation_capacity': 16}


def repair_exterior(adj, initial, commands):
    """Replay specified actual components, without searching for a repair."""
    current, moves = dict(initial), []
    for command in commands:
        pair, root = command['pair'], command['root']
        require(len(pair) == 2 and pair[0] != pair[1] and all(c in range(4) for c in pair),
                'Invalid repair pair')
        require(root in current and current[root] in pair, 'Inactive repair root')
        current, support = switch(adj, current, pair, root)
        proper(adj, current)
        require(len(support) == command['size'], 'Physical component size differs')
        moves.append({'pair': pair, 'root': root, 'size': len(support)})
    return current, moves


def verify(here):
    path = here / 'two-port-core-example.json'
    fixture = json.loads(path.read_text())
    for pin in fixture['sources']:
        require(sha256((here / pin['file']).read_bytes()).hexdigest() == pin['sha256'],
                'Source pin differs: ' + pin['file'])
    sources = json.loads((here / 'independent-repair-example.json').read_text())['cases']
    results = []
    for selected in fixture['cases']:
        case = sources[selected['source_case']]
        ambient, adj, occurrence, ring, patch, ports, _ = load_case(here, case)
        require(ambient == sphere(source_faces(here, case)), 'Spherical graph differs')
        raw = selected['exterior_colours']
        require(len(raw) == len(ambient) and set(raw) <= set('0123-'), 'Invalid colour encoding')
        exterior = {x: int(c) for x, c in enumerate(raw) if c != '-'}
        require(set(exterior) == set(adj), 'Punctured carrier differs')
        proper(adj, exterior)
        word = [exterior[x] for x in ports]
        require(word == selected['boundary_word'], 'Boundary word differs')
        exact, rejected = eliminate(patch, ring, word)
        require(exact is None and complete_patch(patch, word) is None, 'Bad boundary extends')
        fake, relaxed = eliminate(patch, ring, word, selected['relaxed_ear'])
        require(fake is not None, 'Marginal relaxation did not yield a false positive')
        row = next(r for r in rejected['stages'] if r['ear'] == selected['relaxed_ear'])
        u, w = row['ports']
        phantom = [fake[u], fake[w]]
        require(tuple(phantom) in row['phantom_pairs'], 'Missing joint-port obstruction')
        candidates = set(range(4)) - {word[x] for x in patch[row['ear']] if x < ring}
        require(any(c != fake[u] for c in candidates) and any(c != fake[w] for c in candidates),
                'Individual ports are not both feasible')
        require(not any(c != fake[u] and c != fake[w] for c in candidates),
                'The supposedly conflicting ports have a common colour')
        repaired, moves = repair_exterior(adj, exterior, selected['repair_commands'])
        repaired_word = [repaired[x] for x in ports]
        require(repaired_word == selected['repaired_boundary'], 'Repaired boundary differs')
        core, accepted = eliminate(patch, ring, repaired_word)
        require(core is not None, 'Repaired source lost its core extension')
        # Independent finite search is a cross-check, not the construction above.
        require(complete_patch(patch, repaired_word) is not None, 'Independent extension check differs')
        whole = repaired | {occurrence['images'][x]: c for x, c in core.items()}
        proper(ambient, whole)
        results.append({'configuration': occurrence['configuration'], 'ambient_vertices': len(ambient),
            'boundary_ports': ring, 'core_vertices': len(patch) - ring,
            'bad_boundary': word, 'exact_bad_result': rejected,
            'relaxed_ear': selected['relaxed_ear'], 'spurious_port_pair': phantom,
            'eliminated_vertex_colours': sorted(candidates),
            'proper_assignment_except_ear': {str(x): c for x, c in sorted(fake.items())},
            'relaxed_terminal_pairs': relaxed['terminal_pairs'],
            'source_physical_switches': moves, 'repaired_boundary': repaired_word,
            'exact_good_result': accepted, 'reconstructed_core': {str(x): c for x, c in sorted(core.items())},
            'whole_sphere_reconstructed': True, 'joint_boundary_table_enumerated': False})
    return {'evidence': 'Exact program replay; general ear law, source stages and bad-boundary nonextension are Lean proved.',
            'fixture_sha256': sha256(path.read_bytes()).hexdigest(), 'cases': results,
            'scope': 'Two specified spherical exteriors and repairs, not arbitrary-exterior reducibility or coverage.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parent)
    output = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(output)
    print(output, end='')
