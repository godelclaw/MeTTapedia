#!/usr/bin/env python3
"""Independently verify the eleven finite critical-chain repair contracts.

Decode the actual Lean stage data, inspect every noncrossing matching, and
reconstruct terminal colourings of the pinned source graph. This verifier
uses no all-boundaries closure table. Lean supplies the soundness of the
matching selection, composition and same-exterior reconstruction.
"""
import argparse
import ast
from hashlib import sha256
import json
from pathlib import Path
import re

from audit_adaptive_chords import flip
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_strip_partial import partial
from generate_exceptional_repair import boundary, canonical, pairings


def verify(here):
    raw = (here / 'D0099.conf').read_bytes()
    require(sha256(raw).hexdigest() ==
            '932265e50ca2493734dc03f20b4259d6506e968b6cbd8bc16b48f9f53083ae82',
            'Source pin differs')
    ring, g = graph(raw)
    require((ring, len(g)) == (11, 19), 'Source dimensions differ')
    source = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor/StripChainRepair.lean'
    text = source.read_text()

    def rows(name, end, decode):
        block = text.split('def ' + name + ' :', 1)[1].split(end, 1)[0]
        result = []
        for i, value in re.findall(r'\| (\d+) => ([^\n]+)', block):
            require(int(i) == len(result), 'Stage order differs')
            result.append(decode(value))
        require(len(result) == 11, 'Stage count differs')
        return result

    words = rows('word', 'def anchors', lambda x: tuple(map(int, re.findall(r'c([1-3])', x))))
    anchors = rows('anchors', 'def palette', lambda x: ast.literal_eval(x[1:]))
    singles = rows('singles', 'def doubles', ast.literal_eval)
    doubles = rows('doubles', 'def single ', ast.literal_eval)
    perms = re.findall(r'\.e([123]{3})', text.split('def palette', 1)[1].split('def colour', 1)[0])
    require(len(perms) == 11, 'Palette count differs')
    fixed = [p.index('1') + 1 for p in perms]
    stages = []
    direct_checks = 0
    for s, w in enumerate(words):
        require(len(w) == ring and canonical(w) == w, 'Word not canonical')
        require(len(anchors[s]) == 3, 'Anchor arity differs')
        require(all(0 <= a < ring and w[a] != fixed[s] for a in anchors[s]), 'Inactive anchor')
        successors = set()

        def ready(chords):
            nonlocal direct_checks
            out = canonical(flip(w, fixed[s], chords))
            if out in words[:s]:
                successors.add(words.index(out))
                return
            b = boundary(out)
            require(all(b[i] != b[j] for i in range(ring) for j in g[i] if j < ring),
                    'Terminal boundary improper')
            f = partial(g, ring, b, [])
            require(f is not None, f'Stage {s} contract does not extend or enter an earlier stage')
            k = dict(enumerate(b)) | f
            require(len(k) == len(g) and all(k[u] != k[v] for u in k for v in g[u]),
                    'Terminal reconstruction violates a source edge')
            direct_checks += 1

        for p in singles[s]:
            require(len(p) == 2 and all(0 <= x < ring for x in p), 'Invalid single')
            ready([p])
        for r,t,p,q in doubles[s]:
            require(0 <= r < 3 and 0 <= t < 3 and 0 <= p < ring and 0 <= q < ring,
                    'Invalid double')
            ready([(anchors[s][r],p),(anchors[s][t],q)])

        slots = [i for i,c in enumerate(w) if c != fixed[s]]
        require(len(slots) % 2 == 0, 'Odd active set')
        matching_count = 0
        for m in pairings(len(slots)):
            matching_count += 1
            chords = {tuple(sorted((slots[a],slots[b]))) for a,b in m}
            one = any(tuple(sorted(p)) in chords for p in singles[s])
            two = any(tuple(sorted((anchors[s][r],p))) in chords and
                      tuple(sorted((anchors[s][t],q))) in chords
                      for r,t,p,q in doubles[s])
            require(one or two, f'Stage {s} misses a noncrossing matching')
        stages.append({'index': s, 'word': ''.join(map(str,w)), 'fixed_colour': fixed[s],
                       'anchors': anchors[s], 'single_contracts': len(singles[s]),
                       'paired_contracts': len(doubles[s]), 'matchings_checked': matching_count,
                       'earlier_stages_used': sorted(successors)})

    require(words[8] == tuple(map(int,'12211121113')) and
            words[10] == tuple(map(int,'12333313331')), 'Consumers differ')
    for s in (8,10):
        require(partial(g,ring,boundary(words[s]),[]) is None,
                'Initial boundary unexpectedly extends')
    return {
        'source_sha256': sha256(raw).hexdigest(),
        'catalogue_revision': 'c2ce7a96e35256201526e2abb51a39d04a588b53',
        'attribution': 'Yuta Inoue D0099 catalogue, MIT; source semantics from Gonthier/Emery.',
        'lean_source_sha256': sha256(source.read_bytes()).hexdigest(),
        'stages': stages,
        'totals': {'stages': len(stages), 'single_contracts': sum(map(len,singles)),
                   'paired_contracts': sum(map(len,doubles)),
                   'noncrossing_matchings_checked': sum(s['matchings_checked'] for s in stages),
                   'terminal_reconstructions_checked': direct_checks,
                   'stored_interior_colourings': 0},
        'limits': ['Two specified initial boundaries; no uniform repair for all forced chains.',
                   'Same-exterior reconstruction assumes the exterior trace predicate is Kempe closed.',
                   'No physical recolouring-history or runtime bound is claimed.',
                   'No geometric supply, strict graph reduction or catalogue removal is added.'],
        'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest()}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    payload = json.dumps(verify(Path(__file__).resolve().parent), indent=2) + '\n'
    if args.output:
        args.output.write_text(payload)
    print(payload, end='')
