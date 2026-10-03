#!/usr/bin/env python3
"""Replay failure of a fixed preparation strategy and a different repair.

The general obstruction to every following zero/two phase is Lean proved.
This program independently checks the concrete sphere, source occurrence,
component observations and alternative whole colouring. It uses the existing
source fixture and seven-core-vertex elimination, without a colouring table.
"""
import argparse
import ast
from hashlib import sha256
import json
from pathlib import Path

from audit_boundary_observation import components, proper, switch
from audit_component_detach import chain, data, PAIRS
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_two_port_core import eliminate


def verify(here):
    path = here / 'port-preparation-obstruction-example.json'
    fixture = json.loads(path.read_text())
    require(fixture['source_fixture'] == 'component-detach-example.json', 'Wrong source')
    source = here / fixture['source_fixture']
    require(sha256(source.read_bytes()).hexdigest() == fixture['source_fixture_sha256'],
            'Source fixture pin differs')
    base, ambient, exterior, ports, _, *_ = data(here)
    carrier = sorted(exterior)
    raw = fixture['exterior_colouring']
    require(len(raw) == len(carrier) and set(raw) <= set('0123'), 'Wrong colour carrier')
    initial = dict(zip(carrier, map(int, raw)))
    proper(exterior, initial)
    ring, patch = graph((here / base['configuration']).read_bytes())
    word = [initial[v] for v in ports]
    require(word == [1,3,2,3,1,0,3,0,2,0,2], 'Wrong initial boundary')
    residual = next(b for b in components(exterior, initial, (1,3)) if ports[6] in b)
    require(ports[3] in residual and ports[1] not in residual, 'Not the residual case')
    one_step = 0
    initial_components = 0
    for pair in PAIRS:
        for block in components(exterior, initial, pair):
            initial_components += 1
            changed = [initial[v] ^ pair[0] ^ pair[1] if v in block else initial[v]
                       for v in ports]
            one_step += eliminate(patch, ring, changed)[0] is not None
    require(one_step == 0, 'An immediate repair exists')

    require(fixture['preparing_pair'] == [1,2] and fixture['preparing_port'] == 2,
            'Preparation command differs from the claim')
    prepared, support = switch(exterior, initial, (1,2), ports[2])
    changed_ports = [i for i,v in enumerate(ports) if v in support]
    require(changed_ports == [2,4] == fixture['preparing_boundary'], 'Wrong first component')
    require([prepared[v] for v in ports] == [1,3,1,3,2,0,3,0,2,0,2],
            'Wrong prepared boundary')
    route = [carrier[i] for i in fixture['post_preparation_path']]
    require(route[0] == ports[1] and route[-1] == ports[6], 'Wrong route endpoints')
    require(all(v in exterior[u] for u,v in zip(route,route[1:])), 'Missing route edge')
    require(all(prepared[v] in (1,3) for v in route), 'Route has wrong colours')
    blocked = []
    for b in (False,True):
        for c in (False,True):
            candidate = [1,3,1,3,0 if b else 2,2 if b else 0,3,
                         2 if c else 0,0 if c else 2,2 if c else 0,0 if c else 2]
            require(eliminate(patch,ring,candidate)[0] is None, 'A phase word extends')
            blocked.append(candidate)

    current = initial
    moves = []
    states = [initial, prepared]
    traces = [chain(exterior, support, ports[2])]
    for command in fixture['alternative_commands']:
        pair = command['pair']
        require(len(pair) == 2 and pair[0] != pair[1] and set(pair) <= set(range(4)),
                'Invalid alternative colour pair')
        require(command['port'] in range(ring), 'Invalid root port')
        root = ports[command['port']]
        require(current[root] in pair, 'Inactive alternative root')
        current, block = switch(exterior, current, pair, root)
        proper(exterior, current)
        states.append(current)
        traces.append(chain(exterior, block, root))
        moves.append({'pair':pair, 'port':command['port'], 'size':len(block),
                      'changed_ports':[i for i,v in enumerate(ports) if v in block]})
    require([m['size'] for m in moves] == fixture['alternative_component_sizes'] == [2,1],
            'Alternative component sizes differ')
    assignment = fixture['alternative_source_assignment']
    require(len(assignment) == len(patch), 'Wrong source assignment size')
    proper(dict(enumerate(patch)), dict(enumerate(assignment)))
    require([current[v] for v in ports] == assignment[:ring], 'Boundary mismatch')
    whole = current | {base['images'][i]: assignment[i] for i in range(ring,len(patch))}
    proper(ambient,whole)

    # Match both the reused graph and new finite colour/chain literals to
    # exactly the data consumed by the Lean theorems.
    repo = here.parents[2]
    graph_source = (repo / 'lean/mettapedia/Mettapedia/GraphTheory/FourColor/ComponentDetachExample.lean').read_text()
    example_path = repo / 'lean/fourcolor-classical/MettapediaFourColor/PortPreparationObstructionExample.lean'
    example_source = example_path.read_text()
    def literal(source, name):
        rows = [line for line in source.splitlines() if line.startswith(f'def {name} :')]
        require(len(rows) == 1, 'Missing unique Lean literal: '+name)
        return ast.literal_eval(rows[0].split(':=',1)[1].strip())
    index = {v:i for i,v in enumerate(carrier)}
    expected = {
        'carrier':carrier, 'ports':[index[v] for v in ports],
        'edges':sorted((index[u],index[v]) for u in exterior for v in exterior[u] if u<v),
        'ambientEdges':sorted((u,v) for u in ambient for v in ambient[u] if u<v),
    }
    for name,value in expected.items():
        require(literal(graph_source,name) == value, 'Reused Lean geometry differs: '+name)
    require(literal(example_source,'colourData') ==
            [sum(col[v] << (2*i) for i,v in enumerate(carrier)) for col in states],
            'Lean states differ')
    require(literal(example_source,'completeData') == sum(whole[v] << (2*v) for v in ambient),
            'Lean whole colouring differs')
    for i,trace in enumerate(traces):
        require(literal(example_source,f'trace{i}') == [index[v] for v in trace],
                'Lean physical component trace differs')
    return {
        'evidence':'Exact program replay alongside parameterized and finite Lean theorems.',
        'fixture_sha256':sha256(path.read_bytes()).hexdigest(),
        'source_fixture_sha256':fixture['source_fixture_sha256'],
        'lean_example_sha256':sha256(example_path.read_bytes()).hexdigest(),
        'lean_graph_and_colour_literals_match':True,
        'ambient_vertices':len(ambient), 'exterior_vertices':len(exterior),
        'source_core_vertices':len(patch)-ring,
        'source_geometry':'Pinned oriented sphere, exact source stars and cyclic order; '
                          'the base data replay includes every simple cycle of lengths 3 through 5.',
        'initial_residual':True, 'initial_components':initial_components,
        'one_switch_repairs':one_step,
        'failed_preparing_component_size':len(support), 'failed_preparing_ports':changed_ports,
        'post_preparation_complementary_path_edges':len(route)-1,
        'all_four_phase_words_reject':blocked,
        'alternative_moves':moves, 'whole_colouring_reconstructed':True,
        'scope':'The fixed one/two preparation followed by arbitrary zero/two phases fails. '
                'Two different physical component switches repair the same input. '
                'No obstruction to arbitrary mixed-pair repair or compositional coverage is claimed.',
        'catalogue_entries_removed':0, 'original_certificates_removed':0,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parent)
    text = json.dumps(result,indent=2)+'\n'
    if args.output:
        args.output.write_text(text)
    print(text,end='')
