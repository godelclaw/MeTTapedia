#!/usr/bin/env python3
"""Generate a ranked D3009 repair certificate for a chosen trace.

Discovery is untrusted. Lean checks every retained terminal, unsigned exterior
skeleton and decreasing answer. The seed is the proper boundary whose odd rim
has no extension. All subsets of complete chords are considered, including
three-chord exchanges on twelve active ports. Catalogue provenance is pinned
by probe_wheel_repair.wheel.
"""
import argparse
from collections import Counter
from itertools import combinations
import json
from pathlib import Path
import time

from generate_exceptional_repair import PERMS, boundary, canonical, code, lean_blocks, pairings, permute, traces
from probe_wheel_repair import SOURCE_REVISION, SOURCE_SHA256, answers, wheel, witness


def rank_states(cache):
    words = traces(13)
    if cache and cache.exists():
        data = json.loads(cache.read_text())
        assert data['source_sha256'] == SOURCE_SHA256
        assert len(data['ranks']) == len(words)
        return words, data['ranks'], data['stages']
    outer, _, _, _ = wheel(7)
    ranks = [0 if witness(w, outer) else None for w in words]
    known = {w for w, r in zip(words, ranks) if r == 0}
    stages = [len(known)]
    while len(known) < len(words):
        added = []
        for i, w in enumerate(words):
            if ranks[i] is not None:
                continue
            for fixed in (1, 2, 3):
                slots = [j for j, c in enumerate(w) if c != fixed]
                if all(any(a in known for a in answers(w, fixed, ps, slots))
                       for ps in pairings(len(slots))):
                    added.append(i)
                    break
        if not added:
            raise ValueError('repair closure has a survivor')
        for i in added:
            ranks[i] = len(stages)
            known.add(words[i])
        stages.append(len(known))
        print('rank stage', len(stages)-1, len(known), flush=True)
    if cache:
        cache.write_text(json.dumps(dict(source_sha256=SOURCE_SHA256, ranks=ranks, stages=stages)))
    return words, ranks, stages


def masks_for(pairs):
    for size in range(1, max(1, len(pairs)//2)+1):
        for selected in combinations(pairs, size):
            yield sum(1 << k for p in selected for k in p)


def choice(w, fixed, ranks, index, retained):
    p = next(p for p in PERMS if p[fixed-1] == 1)
    oriented = permute(w, p)
    slots = [k for k, c in enumerate(oriented) if c != 1]
    pairs = sorted(pairings(len(slots)), key=lambda ps: tuple(any(a == k for a, _ in ps) for k in range(len(slots))))
    rows = []
    for ps in pairs:
        row = {}
        for mask in masks_for(ps):
            changed = tuple(c ^ 1 if j in slots and mask >> slots.index(j) & 1 else c
                            for j, c in enumerate(oriented))
            target = index[canonical(changed)]
            if ranks[target] < ranks[index[w]]:
                row.setdefault(target, (mask, changed))
        if not row:
            return None
        rows.append(row)
    # Share lower-rank targets across skeletons before taking their closure.
    pending = set(range(len(rows)))
    chosen = {}
    while pending:
        counts = Counter(j for k in pending for j in rows[k])
        target = min(counts, key=lambda j: (0 if j in retained else 1,
                     ranks[j], -counts[j], j))
        for k in list(pending):
            if target in rows[k]:
                chosen[k] = (target, *rows[k][target])
                pending.remove(k)
    result = [chosen[k] for k in range(len(rows))]
    cost = (sum(1+ranks[j] for j in {a[0] for a in result} if j not in retained), len(rows))
    return cost, oriented, result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cache', type=Path)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--report', type=Path, required=True)
    p.add_argument('--block', type=int, default=4)
    args = p.parse_args()
    started = time.monotonic()
    outer, center, rim, edges = wheel(7)
    words, ranks, stages = rank_states(args.cache)
    index = {w:i for i,w in enumerate(words)}
    seed = (1,)*11 + (2,3)
    seed_id = index[seed]
    retained, pending, records = {seed_id}, [seed_id], {}
    while pending:
        i = pending.pop(0)
        w = words[i]
        if ranks[i] == 0:
            z, colors = witness(w, outer)
            full = dict(enumerate(boundary(w))) | {center:z} | dict(zip(rim, colors))
            assert all(full[a] != full[b] for a,b in edges)
            records[i] = (w, tuple(full[j] for j in range(13,21)), [])
        else:
            candidates = [a for f in (1,2,3) if (a := choice(w,f,ranks,index,retained))]
            _, oriented, rows = min(candidates)
            records[i] = (oriented, (), rows)
            for j, _, _ in rows:
                if j not in retained:
                    retained.add(j)
                    pending.append(j)
        if len(records) % 100 == 0:
            print('records',len(records),'retained',len(retained),flush=True)
    ordered = sorted(retained)
    local = {i:j for j,i in enumerate(ordered)}
    encoded, chord_records = [], []
    for i in ordered:
        w, colors, rows = records[i]
        row = ''.join(map(str,w)) + code(ranks[i]) + ''.join(map(str,colors)).ljust(8,'0') + code(len(chord_records),5)
        assert len(row) == 27
        encoded.append(row)
        for j, mask, changed in rows:
            pp = next(pp for pp in PERMS if permute(changed,pp) == records[j][0])
            assert ranks[j] < ranks[i]
            chord_records.append(code(mask,3)+code(local[j],4)+code(PERMS.index(pp)))
    text = '''/-!
# A D3009 seed repair certificate

Generated by tools/fourcolor/near-linear/generate_wheel_seed_repair.py.
Flat data is untrusted until the separate kernel checks pass. This certificate
covers the dependency closure of one trace, not all thirteen-port traces.
Pinned catalogue and licence: tools/fourcolor/near-linear.
-/
namespace FourColor.WheelSeedRepairData

'''
    text += f'def count : Nat := {len(ordered)}\ndef seed : Nat := {local[seed_id]}\ndef block : Nat := {args.block}\n\n'
    for name, data in [('records',encoded),('chords',chord_records)]:
        text += lean_blocks(name,data,args.block)
    text += 'end FourColor.WheelSeedRepairData\n'
    args.output.write_text(text)
    report = dict(status='untrusted certificate; requires Lean kernel replay', source_revision=SOURCE_REVISION,
                  source_sha256=SOURCE_SHA256, seed=list(seed), seed_local_index=local[seed_id],
                  complete_discovery_states=len(words), stages=stages, retained_states=len(ordered),
                  terminals=sum(ranks[i]==0 for i in ordered), max_rank=max(ranks[i] for i in ordered),
                  active_counts=dict(Counter(sum(c!=1 for c in records[i][0]) for i in ordered if ranks[i])),
                  chord_records=len(chord_records), three_chord_records=sum(int(a[:3],36).bit_count()==6 for a in chord_records),
                  bytes=args.output.stat().st_size, block=args.block,
                  edges=edges, selected_indices=ordered, seconds=round(time.monotonic()-started,3))
    args.report.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('edges','selected_indices')}),flush=True)

if __name__ == '__main__':
    main()
