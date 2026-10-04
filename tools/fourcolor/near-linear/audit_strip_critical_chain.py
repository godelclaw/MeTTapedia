#!/usr/bin/env python3
"""Check the two critical boundaries and test conflict-preserving repairs.

Lean certifies the shared forced-chain obstruction and every proper source
restriction. The finite repair game below is program evidence only; its
strategy table is neither exported nor used as a proof certificate.
"""
import argparse
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import re

from audit_adaptive_chords import flip
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_majority_repair import policies
from audit_strip_partial import partial
from generate_exceptional_repair import boundary, canonical, pairings, traces


def verify(here):
    raw = (here / 'D0099.conf').read_bytes()
    require(sha256(raw).hexdigest() ==
            '932265e50ca2493734dc03f20b4259d6506e968b6cbd8bc16b48f9f53083ae82',
            'Source pin differs')
    ring, g = graph(raw)
    require((ring, len(g)) == (11, 19), 'Source dimensions differ')
    lean = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor/StripCriticalChain.lean'
    block = lean.read_text().split('def boundary', 1)[1].split('def step', 1)[0]
    decoded = [list(map(int, re.findall(r'c([0-3])', line)))
               for line in block.splitlines() if '=> ![' in line]
    consumers = []
    for s, word in enumerate(('12211121113', '12333313331')):
        b = boundary(tuple(map(int, word)))
        require(decoded[s] == b, 'Lean boundary differs')
        require(all(b[i] != b[j] for i in range(ring) for j in g[i] if j < ring),
                'Improper boundary')
        require(partial(g, ring, b, []) is None, 'Full source unexpectedly extends')
        for h in range(8):
            f = partial(g, ring, b, [h])
            require(f is not None, 'Single deletion does not extend')
            k = dict(enumerate(b)) | f
            require(all(k[u] != k[v] for u in k for v in g[u] if v in k),
                    'Reconstructed deletion witness violates a source edge')
        consumers.append({'word': word, 'single_deletions_extend': 8,
                          'full_extension': False})

    words = traces(ring)
    index, cache = policies(words)
    core_edges = [(u,v) for u in range(8) for v in range(u+1,8) if ring+v in g[ring+u]]
    full, one, clean, forced_pair = set(), set(), set(), set()
    for i,w in enumerate(words):
        b = boundary(w)
        lists = [set(range(4)) - {b[j] for j in g[ring+v] if j < ring} for v in range(8)]
        if partial(g, ring, b, []) is not None:
            full.add(i)
        if any(partial(g, ring, b, [h]) is not None for h in range(8)):
            one.add(i)
            if not any(len(lists[u]) == 1 and lists[u] == lists[v] for u,v in core_edges):
                clean.add(i)
            if len(lists[5]) == 1 and lists[5] == lists[7]:
                forced_pair.add(i)
    require((len(full), len(one), len(clean), len(forced_pair)) == (1587,5876,4912,502),
            'Boundary domains differ')

    responses = {}
    for i in one:
        phases = []
        for fixed,(slots,singles,_,_) in enumerate(cache[i],1):
            rows = []
            for m in pairings(len(slots)):
                chords = [(slots[a],slots[b]) for a,b in m]
                ordinary = {i} | {singles[p] for p in chords if singles[p] in one}
                preserved = {i} | {singles[p] for p in chords if singles[p] in clean}
                for ps in combinations(chords,2):
                    j = index[canonical(flip(words[i],fixed,ps))]
                    if j in one and any(singles[p] in one for p in ps):
                        ordinary.add(j)
                    if j in clean and any(singles[p] in clean for p in ps):
                        preserved.add(j)
                rows.append((ordinary,preserved))
            phases.append(rows)
        responses[i] = phases

    release = {i for i in one-clean if any(all(r[0] & clean for r in phase)
                                             for phase in responses[i])}
    require(forced_pair <= release, 'Forced-pair release failed')
    require(len(release) == 962, 'Whole-source release count differs')
    known = set(full)
    layers = [len(known)]
    while True:
        new = {i for i in clean-known if any(all(r[1] & known for r in phase)
                                             for phase in responses[i])}
        if not new:
            break
        known |= new
        layers.append(len(known))
    require(known == clean, 'Conflict-preserving completion failed')
    require(layers == [1587,2348,3002,3644,4260,4716,4877,4911,4912],
            'Closure layers differ')
    return {
        'source_sha256': sha256(raw).hexdigest(),
        'catalogue_revision': 'c2ce7a96e35256201526e2abb51a39d04a588b53',
        'attribution': 'Yuta Inoue D0099 catalogue, MIT; source semantics from Gonthier/Emery.',
        'kernel_consumers': consumers,
        'new_stored_colour_witness_bytes': 0,
        'program_only_repair_test': {
            'canonical_inputs': len(words), 'one_hole_or_complete': len(one),
            'no_adjacent_singleton_conflict': len(clean),
            'forced_pair_5_7': len(forced_pair), 'forced_pair_5_7_release': len(forced_pair & release),
            'all_forced_conflict_inputs': len(one-clean), 'one_query_release': len(release),
            'one_query_release_failures': [''.join(map(str,words[i])) for i in sorted(one-clean-release)],
            'conflict_preserving_closure_layers': layers,
            'model': 'A fresh adversarial noncrossing matching per query; choose at most two of its chords. Every single-switch prefix admits a source colouring with at most one hole. After release, every prefix also has no adjacent equal-singleton lists.'},
        'limits': [
            'The critical-boundary theorem concerns fixed boundary colours, not failure of Kempe repair.',
            'Compatible witnesses remain sufficient for gluing; independent local existence is what fails.',
            'Repair closure and its finite round bound are program evidence, not Lean theorems.',
            'Successive partial witnesses need not be recolourings of one chosen interior witness.',
            'The abstract game is not a prescribed physical exterior or a physical history bound.',
            'No geometric supply, strict reduction, catalogue deletion or full-source repair certification is added.'],
        'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    payload = json.dumps(verify(Path(__file__).resolve().parent), indent=2) + '\n'
    if args.output:
        args.output.write_text(payload)
    print(payload, end='')
