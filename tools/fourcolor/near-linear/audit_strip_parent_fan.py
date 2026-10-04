#!/usr/bin/env python3
"""Replay exact fan parents, two small repairs, and a bounded closure experiment.

Lean checks fan transport and the two specified input repairs. Complete parent
closures and their combined coverage below are program evidence only. A
surviving abstract trace does not exhibit an unrepairable physical exterior.
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
from generate_exceptional_repair import boundary, canonical, pairings, traces
from probe_wheel_repair import answers


def trace(colours):
    return tuple(colours[i] ^ colours[(i + 1) % len(colours)] for i in range(len(colours)))


def parents(adj):
    result = []
    for ear, omitted, ports, shift in [
            (11, 7, list(range(7)) + [11] + list(range(8, 11)), 6),
            (18, 0, [18] + list(range(1, 11)), 10)]:
        order = ports + [v for v in range(11, 19) if v != ear]
        inverse = {v: i for i, v in enumerate(order)}
        require(set(order) == set(range(19)) - {omitted}, 'Parent carrier differs')
        g = [{inverse[v] for v in adj[u] if v in inverse} for u in order]
        require(all((i + 1) % 11 in g[i] for i in range(11)), 'Parent ring is incomplete')
        require(all(g[i] == {inverse[v] for v in adj[u]}
                    for i, u in enumerate(order) if i >= 11), 'A parent core star changed')
        seam = (inverse[(omitted - 1) % 11], inverse[ear], inverse[(omitted + 1) % 11])
        require(seam[1] in g[seam[0]] and seam[2] in g[seam[1]], 'Missing old path edge')
        grown = [set(ns) for ns in g] + [set(seam)]
        for v in seam:
            grown[v].add(18)
        image = order + [omitted]
        require(all({image[j] for j in grown[i]} == adj[image[i]] for i in range(19)),
                'Fan growth is not the entire source graph')
        result.append({'order': order, 'omitted': omitted, 'shift': shift, 'graph': g})
    return result


def direct_words(g, ws):
    known = set()
    for w in ws:
        ports = boundary(w)
        dfs = complete_patch(g, ports)
        ear, _ = eliminate(g, len(w), ports)
        require((dfs is None) == (ear is None), 'Independent extension checks disagree')
        if dfs is not None:
            known.add(w)
    return known


def closure(ws, known):
    known = set(known)
    stages = [len(known)]
    while len(known) < len(ws):
        new = []
        for w in ws:
            if w in known:
                continue
            for fixed in (1, 2, 3):
                slots = [i for i, c in enumerate(w) if c != fixed]
                if all(any(a in known for a in answers(w, fixed, ps, slots))
                       for ps in pairings(len(slots))):
                    new.append(w)
                    break
        if not new:
            break
        known.update(new)
        stages.append(len(known))
    return known, stages


def lean_cases(lean, ps, child):
    text = lean.read_text()
    def block(name):
        return re.search(rf'^def {name}\b(.*?)(?=^\S)', text, re.M | re.S)[1]
    cases = []
    for side, tag in enumerate(('false', 'true')):
        def word(name):
            row = re.search(rf'\| {tag} => \[([^\]]+)\]', block(name))[1]
            return tuple(map(int, re.findall(r'c([0-3])', row)))
        pword, cword = word('parentWord'), word('childWord')
        raw = re.search(rf'\| {tag} => "([0-3]+)"', block('data'))[1]
        require(len(raw) == 36, 'Expected two full parent colourings')
        witnesses = [list(map(int, raw[i:i + 18])) for i in (0, 18)]
        p = ps[side]
        shift = p['shift']
        g = p['graph']
        accepted = []
        for colours in witnesses:
            require(all(colours[u] != colours[v] for u, ns in enumerate(g) for v in ns),
                    'Source witness is improper')
            w = trace(colours[:11])
            accepted.append(w[shift:] + w[:shift])
        slots = [i for i, c in enumerate(pword) if c != 1]
        anchor = (4, 0)[side]
        require(anchor in slots and len(slots) == 4, 'Unexpected chord interface')
        for pskeleton in pairings(len(slots)):
            chord = next(e for e in pskeleton if slots.index(anchor) in e)
            changed = tuple(c ^ 1 if i in {slots[j] for j in chord} else c
                            for i, c in enumerate(pword))
            require(changed in accepted, 'Uniform first-chord answer lacks a witness')
        require(pword[2:] == cword[2:] and pword[0] != cword[0] and
                pword[0] ^ pword[1] == cword[0] ^ cword[1], 'Fan relation differs')
        unrotate = lambda w: w[-shift:] + w[:-shift]
        require(complete_patch(g, boundary(unrotate(pword))) is None, 'Parent input already extends')
        require(complete_patch(child, boundary(unrotate(cword))) is None, 'Child input already extends')
        cases.append({'side': tag, 'parent_word': ''.join(map(str, pword)),
                      'source_word': ''.join(map(str, cword)), 'active_ports': len(slots),
                      'parent_colour_witnesses': len(witnesses), 'flat_colour_bytes': len(raw),
                      'parent_input_nonextending': True, 'source_input_nonextending': True,
                      'all_chord_answers_reconstruct': True})
    return cases


def verify(here):
    raw = (here / 'D0099.conf').read_bytes()
    ring, child = graph(raw)
    require(ring == 11 and len(child) == 19, 'Source dimensions changed')
    ps = parents(child)
    ws = traces(ring)
    results, winning = [], []
    for p in ps:
        direct = direct_words(p['graph'], ws)
        known, stages = closure(ws, direct)
        winning.append(known)
        results.append({'source_labels_in_parent_order': [v + 1 for v in p['order']],
                        'core_degrees': [len(ns) for ns in p['graph'][ring:]],
                        'stages': stages, 'abstract_survivors': len(ws) - len(known)})
    direct = direct_words(child, ws)
    transported = [set(), set()]
    for w in ws:
        colours = boundary(w)
        for side, p in enumerate(ps):
            slot = p['omitted']
            for c in set(range(4)) - {colours[slot - 1], colours[slot], colours[(slot + 1) % ring]}:
                before = colours.copy()
                before[slot] = c
                if canonical(trace(before)) in winning[side]:
                    transported[side].add(w)
                    break
    combined = direct | transported[0] | transported[1]
    final, stages = closure(ws, combined)
    require([r['abstract_survivors'] for r in results] == [1053, 3824], 'Parent census differs')
    require(stages == [6777, 7305, 7381] and len(final) == len(ws), 'Combined repair census differs')
    lean_dir = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor'
    example = lean_dir / 'StripParentFanExample.lean'
    source = (lean_dir / 'StripParentFan.lean').read_text()
    image_block = source.split('def image', 1)[1].split('def omitted', 1)[0]
    for tag, p in zip(('false', 'true'), ps):
        order = list(map(int, re.search(rf'\| {tag} => !\[([^\]]+)\]', image_block)[1].split(',')))
        require(order == p['order'], 'Lean parent map differs from independent construction')
    return {'evidence': 'Lean fan law and two small repair consumers; full closure census is independent program evidence.',
            'source': 'D0099.conf', 'source_sha256': sha256(raw).hexdigest(),
            'catalogue_revision': 'c2ce7a96e35256201526e2abb51a39d04a588b53',
            'attribution': 'Yuta Inoue, 2026, MIT licence; Gonthier/Emery chromogram semantics.',
            'parents': results, 'canonical_traces': len(ws), 'direct_source_traces': len(direct),
            'transported_parent_traces': list(map(len, transported)), 'combined_stages': stages,
            'checked_examples': lean_cases(example, ps, child),
            'limits': ['Abstract parent survivors do not exhibit unrepairable physical exteriors.',
                       'Complete parent closures and the 7381-trace source cover are not Lean certified.',
                       'No net certificate or runtime compression follows from the census.',
                       'No new occurrence supply, strict ambient reduction, or coverage theorem.'],
            'catalogue_entries_removed': 0, 'certificate_dependencies_removed': 0,
            'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    payload = json.dumps(verify(Path(__file__).resolve().parent), indent=2) + '\n'
    if args.output:
        args.output.write_text(payload)
    print(payload, end='')
