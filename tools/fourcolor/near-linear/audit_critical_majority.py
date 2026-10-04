#!/usr/bin/env python3
"""Replay the five majority consumers and measure their anchor continuation.

Lean certifies the five source repairs via the arbitrary-width exterior
decoder. The full anchor closure is independent program evidence only.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import re

from audit_adaptive_chords import flip
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_majority_repair import policies, close
from audit_strip_parent_fan import direct_words
from audit_two_port_core import eliminate
from generate_exceptional_repair import boundary, pairings, traces


def verify(here):
    source = (here / 'D0099.conf').read_bytes()
    require(sha256(source).hexdigest() ==
            '932265e50ca2493734dc03f20b4259d6506e968b6cbd8bc16b48f9f53083ae82',
            'Pinned source differs')
    n, g = graph(source)
    lean = (here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor/StripCriticalRepair.lean').read_text()
    block = lean.split('def source', 1)[1].split('def palette', 1)[0]
    inputs = [tuple(map(int, re.findall(r'c([0-3])', s))) for s in re.findall(r'!\[([^\[\]]+)\]', block)]
    text = lean.split('def positions', 1)[1].split('def embed', 1)[0]
    orders = [list(map(int, re.findall(r'\d+', s))) for s in re.findall(r'\[([^\[\]]+)\]', text)]
    expected = ['12322212313', '12322223131', '12323211232', '12323321221', '12332132221']
    require([''.join(map(str, w)) for w in inputs] == expected, 'Critical input domain differs')
    require(len(orders) == 5, 'Five active coordinate orders required')
    rows = []
    for w, fixed, order in zip(inputs, [2,1,3,1,1], orders):
        ports = [i for i,c in enumerate(w) if c != fixed]
        require(len(order) == len(ports) and set(order) == set(ports), 'Active carrier differs')
        require(order in [ports[k:] + ports[:k] for k in range(len(ports))], 'Cyclic order differs')
        majority = order[:len(ports)//2+1]
        good = {tuple(sorted(pair)) for pair in zip(majority, majority[1:])}
        require(eliminate(g, n, boundary(w))[0] is None, 'Input already extends')
        answers = []
        for a,b in sorted(good):
            changed = flip(w, fixed, [(a,b)])
            f, _ = eliminate(g, n, boundary(changed))
            require(f is not None, 'Majority answer has no reconstructed source colouring')
            colours = boundary(changed) + [f[i] for i in range(n,len(g))]
            require(all(colours[u] != colours[v] for u in range(len(g)) for v in g[u]),
                    'Reconstructed source colouring is improper')
            answers.append(''.join(map(str, changed)))
        layouts = pairings(len(ports))
        require(all(any(tuple(sorted((ports[a],ports[b]))) in good for a,b in m)
                    for m in layouts), 'Independent matching cross-check failed')
        rows.append({'input': ''.join(map(str,w)), 'fixed_colour': fixed,
                     'active_order': order, 'majority_block': majority,
                     'successful_pairs': sorted(good), 'direct_answers': answers,
                     'program_matching_crosscheck_count': len(layouts)})

    words = traces(n)
    index, cache = policies(words)
    direct = {index[w] for w in direct_words(g, words)}
    seeds = {index[w] for w in inputs}
    require(not direct & seeds, 'A seed is already directly extending')
    covered, stages = close(direct | seeds, cache, 'anchor')
    require(len(covered) == len(words) == 7381, 'The five seeds no longer generate the full closure')
    return {'evidence': 'Five source repairs and uniform exterior recovery are Lean certified; full continuation closure is program evidence.',
            'source_sha256': sha256(source).hexdigest(),
            'catalogue_revision': 'c2ce7a96e35256201526e2abb51a39d04a588b53',
            'attribution': 'Yuta Inoue catalogue, MIT; Gonthier/Emery chord scan and flip semantics.',
            'source_repairs': rows,
            'new_stored_source_colouring_bytes': 0,
            'kernel_matching_layout_checks': 0,
            'program_anchor_continuation': {'canonical_inputs': len(words), 'direct_inputs': len(direct),
                'new_seed_inputs': len(seeds), 'stages': stages, 'full_source_lean_proof': False},
            'limits': ['Source-coordinate and terminal-relation checks remain finite.',
                       'No structural rank proving the complete anchor continuation is supplied.',
                       'No strict ambient reduction, geometric supply or catalogue deletion follows.'],
            'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    payload = json.dumps(verify(Path(__file__).resolve().parent), indent=2) + '\n'
    if args.output:
        args.output.write_text(payload)
    print(payload, end='')
