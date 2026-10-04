#!/usr/bin/env python3
"""Replay the source obstruction to forgetting boundary-update responses.

Lean proves exact core elimination for arbitrary boundary colours, the two
source outcomes, and preservation of each input's matching chromogram.
This independent replay compares ear elimination with source colouring search.
It does not assert realization of the matching by a particular exterior.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import re

from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_independent_repair import complete_patch
from audit_two_port_core import eliminate
from audit_two_round_repair import matching, witness


def edge_trace(b):
    return tuple(c ^ b[(i+1) % len(b)] for i, c in enumerate(b))


def verify(here):
    source = (here / 'D0099.conf').read_bytes()
    require(sha256(source).hexdigest() ==
            '932265e50ca2493734dc03f20b4259d6506e968b6cbd8bc16b48f9f53083ae82',
            'Source pin differs')
    ring, g = graph(source)
    require(ring == 11 and len(g) == 19, 'Source carrier differs')
    lean_dir = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor'
    lean = (lean_dir / 'StripResponseSummary.lean').read_text()
    encoded = re.search(r'def boundary : Bool → Boundary(.*?)\n/--', lean, re.S)[1]
    inputs = [list(map(int, re.findall(r'c([0-3])', row)))
              for row in re.findall(r'!\[([^\]]+)\]', encoded)]
    require(inputs == [[0,1,0,1,3,2,0,3,1,0,1], [0,1,3,1,3,2,0,3,1,0,1]],
            'Boundary fixtures differ')
    require([i for i in range(ring) if inputs[0][i] != inputs[1][i]] == [2],
            'Distinguishing port differs')
    attachments = json.loads(re.search(r'def attachments.*?=\s*!([^\n]+)', lean, re.S)[1])
    require(attachments == [sorted(x for x in g[v] if x < ring) for v in range(ring, len(g))],
            'Source attachments differ')
    edge_text = re.search(r'def edges.*?:=\s*\[(.*?)\]', lean, re.S)[1]
    edges = [tuple(map(int, p)) for p in re.findall(r'\((\d+),(\d+)\)', edge_text)]
    require(edges == [(u-ring, v-ring) for u in range(ring, len(g)) for v in sorted(g[u]) if u < v],
            'Source core edges differ')
    mate = json.loads('[' + re.search(r'def mate.*?:= !\[([^\]]+)\]', lean)[1] + ']')
    require(mate[1] == 9, 'Selected chord differs')
    data = re.search(r'def data : String := "([0-3]+)"',
                     (lean_dir / 'StripTwoRoundRepair.lean').read_text())[1]
    reused = list(map(int, data[:19]))
    rows = []
    for b in inputs:
        w = edge_trace(b)
        pairs = matching(w, 3, mate)
        before, state = eliminate(g, ring, b)
        require(before is None and complete_patch(g, b) is None, 'An original input extends')
        updated = [c ^ 3 if 2 <= i <= 9 else c for i, c in enumerate(b)]
        changed = edge_trace(updated)
        require(changed == tuple(c ^ 3 if i in (1,9) else c for i, c in enumerate(w)),
                'Interval update is not the selected whole-chord switch')
        matching(changed, 3, mate)
        require(all((w[i] == w[j]) == (changed[i] == changed[j]) for i, j in pairs),
                'Component parity changed')
        after, next_state = eliminate(g, ring, updated)
        require((after is not None) == (complete_patch(g, updated) is not None),
                'Independent extension checks disagree')
        rows.append({'boundary': b, 'edge_trace': list(w),
                     'relations': [r['kept_relation'] for r in state['stages']],
                     'raw_messages': [r['exact_message'] for r in state['stages']],
                     'updated_boundary': updated, 'updated_edge_trace': list(changed),
                     'updated_terminal': next_state['terminal_pairs'],
                     'updated_extends': after is not None})
    require(rows[0]['relations'] == rows[1]['relations'], 'Evaluated retained relations differ')
    require(len(rows[0]['relations']) == 6, 'Elimination order differs')
    require(rows[0]['updated_extends'] and not rows[1]['updated_extends'],
            'The update no longer distinguishes the source inputs')
    require(rows[0]['raw_messages'] != rows[1]['raw_messages'],
            'The recorded distinction between raw messages and retained relations changed')
    witness(g, rows[0]['updated_edge_trace'], reused)
    return {'evidence': 'Kernel-checked source theorem with independent program replay.',
            'source_sha256': sha256(source).hexdigest(), 'core_edges': edges,
            'boundary_attachments': attachments, 'matching': mate, 'switched_chord': [1,9],
            'distinguishing_boundary_vertex_zero_based': 2, 'cases': rows,
            'exact_retained_relations_equal': True, 'raw_messages_equal': False,
            'new_colour_witness_bytes': 0, 'reused_colour_witness': reused,
            'limits': ['Equality of evaluated retained relations is refuted as an update congruence.',
                       'No impossibility of symbolic relations or other compositional summaries is proved.',
                       'Each input retains its own chromogram; no common physical exterior is constructed.',
                       'No catalogue dependency, geometric supply or strict reduction is replaced.'],
            'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    payload = json.dumps(verify(Path(__file__).resolve().parent), indent=2) + '\n'
    if args.output:
        args.output.write_text(payload)
    print(payload, end='')
