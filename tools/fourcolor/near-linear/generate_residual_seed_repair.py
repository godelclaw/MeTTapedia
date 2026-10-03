#!/usr/bin/env python3
"""Discover and compress a repair strategy for the retained D0092 seed trace.

The search is untrusted. Lean checks every source-colouring witness, every
whole-chord answer and strict rank descent. Only this seed and its dependency
closure are certified; no catalogue-wide reducibility claim is made.
"""
import argparse
from collections import Counter
from functools import lru_cache
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import time

from audit_five_triangle_collapse import graph
from audit_two_port_core import eliminate
from generate_exceptional_repair import PERMS, boundary, canonical, code, lean_blocks, pairings, permute
from probe_wheel_repair import answers

SOURCE_REVISION = 'c2ce7a96e35256201526e2abb51a39d04a588b53'
SOURCE_SHA256 = 'cc8286c01ce19b57b793a4eb1b28633d66cd210ea2a313dd0ba3e7d07231ea14'
SEED = (1, 3, 2, 3, 1, 0, 3, 0, 2, 0, 2)


def discover(g, ring):
    root = canonical(tuple(a ^ b for a, b in zip(SEED, SEED[1:] + SEED[:1])))
    proof = {}

    @lru_cache(None)
    def witness(word):
        return eliminate(g, ring, boundary(word))[0]

    @lru_cache(None)
    def win(word, depth):
        k = witness(word)
        if k is not None:
            proof.setdefault(word, dict(level=0, word=word, witness=k))
            return True
        if depth == 0:
            return False
        for fixed in sorted((1, 2, 3), key=lambda c: sum(x != c for x in word)):
            slots = [j for j, c in enumerate(word) if c != fixed]
            children = []
            for chords in pairings(len(slots)):
                target = next((a for a in sorted(set(answers(word, fixed, chords, slots)))
                               if win(a, depth - 1)), None)
                if target is None:
                    break
                assert proof[target]['level'] < depth
                children.append(dict(matching=chords, target=target))
            else:
                # A later successful call must never overwrite a lower rank.
                if word not in proof or depth < proof[word]['level']:
                    proof[word] = dict(level=depth, word=word, fixed=fixed, children=children)
                return True
        return False

    for depth in range(1, 6):
        if win(root, depth):
            return root, proof
    raise ValueError('no strategy found within the five-round discovery bound')


def reachable(root, nodes):
    found, pending = set(), [root]
    while pending:
        w = pending.pop()
        if w in found:
            continue
        found.add(w)
        for child in nodes[w].get('children', []):
            assert nodes[child['target']]['level'] < nodes[w]['level']
            pending.append(child['target'])
    return found


def compress(root, proof):
    opt = {w: dict(n) for w, n in proof.items() if n['level'] == 0}
    cone = {w: frozenset([w]) for w in opt}
    for level in range(1, proof[root]['level'] + 1):
        for word, row in sorted(proof.items()):
            if row['level'] != level:
                continue
            best = None
            for fixed in (1, 2, 3):
                slots = [j for j, c in enumerate(word) if c != fixed]
                matchings, choices = pairings(len(slots)), []
                for chords in matchings:
                    candidates = {w for w in answers(word, fixed, chords, slots)
                                  if w in opt and opt[w]['level'] < level}
                    if not candidates:
                        break
                    choices.append(candidates)
                else:
                    pending, selected, used = set(range(len(choices))), set(), {word}
                    while pending:
                        coverage = {}
                        for i in pending:
                            for a in choices[i]:
                                coverage.setdefault(a, set()).add(i)
                        a = min(coverage, key=lambda a: (len(cone[a] - used) / len(coverage[a]),
                                len(cone[a] - used), opt[a]['level'], a))
                        selected.add(a)
                        used.update(cone[a])
                        pending -= coverage[a]
                    targets = [min(c & selected, key=lambda a: (opt[a]['level'], a)) for c in choices]
                    used = {word}.union(*(cone[a] for a in targets))
                    candidate = dict(level=level, word=word, fixed=fixed,
                                     children=[dict(matching=c, target=a) for c, a in zip(matchings, targets)])
                    score = (len(used), sum(opt[a]['level'] > 0 for a in set(targets)),
                             len(set(targets)), fixed)
                    if best is None or score < best[0]:
                        best = score, candidate, frozenset(used)
            assert best is not None
            _, opt[word], cone[word] = best
    return {w: opt[w] for w in reachable(root, opt)}


def encode(root, nodes, g, ring):
    ordered = sorted(nodes)
    index = {w: i for i, w in enumerate(ordered)}
    oriented = {w: permute(w, next(p for p in PERMS if p[n['fixed'] - 1] == 1))
                if n['level'] else w for w, n in nodes.items()}
    records, chords = [], []
    for w in ordered:
        row = nodes[w]
        core = ()
        if row['level'] == 0:
            k = dict(enumerate(boundary(w))) | row['witness']
            assert all(k[a] != k[b] for a in range(len(g)) for b in g[a])
            core = tuple(k[j] for j in range(ring, len(g)))
        records.append(''.join(map(str, oriented[w])) + code(row['level']) +
                       ''.join(map(str, core)).ljust(7, '0') + code(len(chords), 3))
        assert len(records[-1]) == 22
        if row['level'] == 0:
            continue
        slots = [j for j, c in enumerate(oriented[w]) if c != 1]
        # The shared Lean enumeration uses lexicographic Boolean skeletons.
        children = sorted(row['children'], key=lambda r:
                          tuple(any(a == k for a, _ in r['matching']) for k in range(len(slots))))
        assert len(children) == len(pairings(len(slots)))
        for child in children:
            pairs, target = child['matching'], child['target']
            assert nodes[target]['level'] < row['level']
            chosen = None
            for size in range(1, max(1, len(pairs) // 2) + 1):
                for selection in combinations(pairs, size):
                    mask = sum(1 << i for a in selection for i in a)
                    changed = tuple(c ^ 1 if j in slots and mask >> slots.index(j) & 1 else c
                                    for j, c in enumerate(oriented[w]))
                    if canonical(changed) == target:
                        p = next(p for p in PERMS if permute(changed, p) == oriented[target])
                        chosen = code(mask, 2) + code(index[target], 2) + code(PERMS.index(p))
                        break
                if chosen is not None:
                    break
            assert chosen is not None
            chords.append(chosen)
    return index[root], records, chords


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    started = time.monotonic()
    here = Path(__file__).resolve().parent
    fixture = json.loads((here / 'component-detach-example.json').read_text())
    raw = (here / fixture['configuration']).read_bytes()
    assert sha256(raw).hexdigest() == SOURCE_SHA256
    ring, g = graph(raw)
    root, proof = discover(g, ring)
    before = reachable(root, proof)
    nodes = compress(root, proof)
    seed, records, chords = encode(root, nodes, g, ring)
    block = 4
    text = '''/-!
# A compact repair strategy for one D0092 boundary class

Generated by tools/fourcolor/near-linear/generate_residual_seed_repair.py.
Untrusted flat data: the separate Lean checker verifies all source colourings,
whole-chord answers and descending ranks. This is one seed closure, not a
complete eleven-port reducibility certificate. Source and licence are retained
under tools/fourcolor/near-linear.
-/
namespace FourColor.ResidualSeedRepairData

'''
    text += f'def count : Nat := {len(nodes)}\ndef seed : Nat := {seed}\ndef block : Nat := {block}\n\n'
    text += lean_blocks('records', records, block) + lean_blocks('chords', chords, block)
    text += 'end FourColor.ResidualSeedRepairData\n'
    args.output.write_text(text)
    report = dict(status='untrusted discovery; separate Lean kernel check required',
                  source_revision=SOURCE_REVISION, source_sha256=SOURCE_SHA256,
                  vertex_seed=SEED, canonical_edge_seed=root, seed_local_index=seed,
                  states_before=len(before), matching_cases_before=sum(len(proof[w].get('children', [])) for w in before),
                  states_after=len(nodes), rank_counts=dict(Counter(n['level'] for n in nodes.values())),
                  matching_cases_after=len(chords), encoded_bytes=sum(map(len, records + chords)),
                  lean_data_bytes=len(text.encode()), data_sha256=sha256(text.encode()).hexdigest(),
                  edges=[(a, b) for a in range(len(g)) for b in sorted(g[a]) if a < b],
                  seconds=round(time.monotonic() - started, 3))
    args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'edges'}))


if __name__ == '__main__':
    main()
