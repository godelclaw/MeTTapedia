#!/usr/bin/env python3
"""Discover a small extension of the already checked three-run seed repair.

Discovery is untrusted and stops after three additional abstract rounds.
Lean checks all source witnesses, references to earlier states, matching
answers and rank inequalities. This is not full D0092 reducibility.
"""
import argparse
from collections import Counter
from functools import lru_cache
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import re

import generate_residual_seed_repair as seed
from generate_exceptional_repair import traces


def inputs():
    here = Path(__file__).resolve().parent
    raw = (here / 'D0092.conf').read_bytes()
    assert sha256(raw).hexdigest() == seed.SOURCE_SHA256
    ring, graph = seed.graph(raw)
    receipt = json.loads((here / 'residual-seed-repair-measurements.json').read_text())
    pin = next(m for m in receipt['modules']
               if m['module'] == 'MettapediaFourColor.ResidualSeedRepairData')
    path = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor/ResidualSeedRepairData.lean'
    data = path.read_bytes()
    assert sha256(data).hexdigest() == pin['source_sha256']
    section = data.decode().split('private def recordsPart0', 1)[1].split('\ndef records (', 1)[0]
    packed = ''.join(re.findall(r'"([0-9A-Z]+)"', section))
    assert len(packed) == 22 * 41
    old = [tuple(map(int, packed[i:i + 11])) for i in range(0, len(packed), 22)]
    probe = json.loads((here / 'three-block-seed-transfer-probe.json').read_text())
    roots = [tuple(map(int, r['word'])) for r in probe['uncovered_canonical_classes']]
    return graph, ring, old, roots, pin['source_sha256']


def discover(graph, ring, old, roots):
    old_index = {seed.canonical(w): i for i, w in enumerate(old)}
    proof = {}

    @lru_cache(None)
    def terminal(word):
        if word in old_index:
            return dict(level=0, word=word, old=old_index[word])
        witness = seed.eliminate(graph, ring, seed.boundary(word))[0]
        if witness is not None:
            return dict(level=0, word=word, witness=witness)
        return None

    @lru_cache(None)
    def win(word, depth):
        leaf = terminal(word)
        if leaf is not None:
            proof.setdefault(word, leaf)
            return True
        if depth == 0:
            return False
        for fixed in sorted((1, 2, 3), key=lambda c: sum(x != c for x in word)):
            slots = [i for i, c in enumerate(word) if c != fixed]
            children = []
            for pairs in seed.pairings(len(slots)):
                candidates = sorted(set(seed.answers(word, fixed, pairs, slots)),
                                    key=lambda w: (terminal(w) is None, w))
                target = next((w for w in candidates if win(w, depth - 1)), None)
                if target is None:
                    break
                children.append(dict(matching=pairs, target=target))
            else:
                if word not in proof or depth < proof[word]['level']:
                    proof[word] = dict(level=depth, word=word, fixed=fixed, children=children)
                return True
        return False

    for depth in range(1, 4):
        results = [win(w, depth) for w in roots]
        if all(results):
            break
    else:
        raise ValueError('No shared transfer within three additional rounds')
    compressed = {}
    for root in roots:
        compressed.update(seed.compress(root, proof))
    keep = set().union(*(seed.reachable(root, compressed) for root in roots))
    return {w: compressed[w] for w in keep}, win.cache_info().misses


def encode(nodes, old):
    ordered = sorted(nodes)
    index = {w: i for i, w in enumerate(ordered)}
    oriented = {w: seed.permute(w, next(p for p in seed.PERMS if p[n['fixed'] - 1] == 1))
                if n['level'] else w for w, n in nodes.items()}
    records, chords = [], []
    for word in ordered:
        row = nodes[word]
        if row['level']:
            kind, payload = 2, '0000000'
        elif 'old' in row:
            kind = 1
            p = next(p for p in seed.PERMS if seed.permute(word, p) == old[row['old']])
            payload = seed.code(row['old'], 2) + seed.code(seed.PERMS.index(p)) + '0000'
        else:
            kind, payload = 0, ''.join(str(row['witness'][j]) for j in range(11, 18))
        record = (''.join(map(str, oriented[word])) + seed.code(row['level']) +
                  seed.code(kind) + payload + seed.code(len(chords), 3))
        assert len(record) == 23
        records.append(record)
        if not row['level']:
            continue
        slots = [j for j, c in enumerate(oriented[word]) if c != 1]
        children = sorted(row['children'], key=lambda r:
                          tuple(any(a == k for a, _ in r['matching']) for k in range(len(slots))))
        assert len(children) == len(seed.pairings(len(slots)))
        for child in children:
            pairs, target = child['matching'], child['target']
            assert nodes[target]['level'] < row['level']
            chosen = None
            for size in range(1, max(1, len(pairs) // 2) + 1):
                for selection in combinations(pairs, size):
                    mask = sum(1 << i for pair in selection for i in pair)
                    changed = tuple(c ^ 1 if j in slots and mask >> slots.index(j) & 1 else c
                                    for j, c in enumerate(oriented[word]))
                    if seed.canonical(changed) == target:
                        p = next(p for p in seed.PERMS if seed.permute(changed, p) == oriented[target])
                        chosen = seed.code(mask, 2) + seed.code(index[target], 2) + seed.code(seed.PERMS.index(p))
                        break
                if chosen is not None:
                    break
            assert chosen is not None
            chords.append(chosen)
    return records, chords, index


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    graph, ring, old, roots, old_hash = inputs()
    nodes, search_states = discover(graph, ring, old, roots)
    records, chords, index = encode(nodes, old)
    text = '''/-! # Three shared decisions extending the checked D0092 seed repair

Flat untrusted data checked by `ThreeBlockRepairTransfer`. Leaves either
supply a source colouring or invoke an existing checked seed state.
No earlier strategy is copied. Source attribution is retained in
`FiveTriangleCollapseObstruction`.
-/
namespace FourColor.ThreeBlockRepairTransferData

'''
    text += f'def count : Nat := {len(records)}\n\n'
    text += 'def records : String := "' + ''.join(records) + '"\n\n'
    text += 'def chords : String := "' + ''.join(chords) + '"\n\n'
    text += 'end FourColor.ThreeBlockRepairTransferData\n'
    args.output.write_text(text)
    boundary_words = traces(ring)
    direct_count = sum(seed.eliminate(graph, ring, seed.boundary(w))[0] is not None
                       for w in boundary_words)
    report = {
        'status': 'UNTRUSTED_DISCOVERY_SEPARATE_LEAN_CHECK_REQUIRED',
        'source_revision': seed.SOURCE_REVISION, 'source_sha256': seed.SOURCE_SHA256,
        'previous_seed_data_sha256': old_hash,
        'roots': [{'trace': ''.join(map(str, w)), 'state': index[w]} for w in roots],
        'states': len(records), 'search_states': search_states,
        'kinds': dict(Counter('old_repair' if 'old' in n else 'direct' if n['level'] == 0
                              else 'decision' for n in nodes.values())),
        'matching_cases': len(chords), 'max_additional_rank': max(n['level'] for n in nodes.values()),
        'encoded_bytes': sum(map(len, records + chords)),
        'data_sha256': sha256(text.encode()).hexdigest(),
        'boundary_inventory': {
            'canonical_proper_traces': len(boundary_words),
            'directly_extendible': direct_count,
            'not_directly_extendible': len(boundary_words) - direct_count,
            'scope': 'Program enumeration modulo colour permutations, preserving every boundary position.'
        },
        'decisions': [{'trace': ''.join(map(str, w)), 'rank': n['level'], 'fixed_colour': n['fixed'],
                       'matching_cases': len(n['children']),
                       'distinct_targets': len({c['target'] for c in n['children']})}
                      for w, n in sorted(nodes.items()) if n['level']],
        'limits': ['Only the symbolic three-run family, not every D0092 boundary word.',
                   'Rank counts additional abstract rounds before invoking a leaf repair.',
                   'No physical switch count, occurrence supply or catalogue saving.']
    }
    args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in ('states', 'kinds', 'matching_cases', 'encoded_bytes')}))


if __name__ == '__main__':
    main()
