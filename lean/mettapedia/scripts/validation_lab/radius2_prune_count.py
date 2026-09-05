#!/usr/bin/env python3
"""How many radius-2 balls survive pruning by radius-1 reducibility?

A radius-2 ball is (central face c; ring-1 sizes l_1..l_c; ring-2 sizes), all
in [5,7].  The ring-2 faces are the c corner faces C_{i,i+1} (one per
consecutive ring-1 pair) and the l_i - 5 private faces of each ring-1 face, in
cyclic order.  A ball containing a reducible radius-1 flower is already
covered, so the list only needs balls whose c+1 sub-flowers (the centre's and
each ring-1 face's) are all irreducible.  The sub-flower of ring-1 face i has
neighbours [centre, f_{i+1}, C_{i,i+1}, private faces of i, C_{i-1,i}, f_{i-1}].

Flower verdicts come from the sweep log; types not in the log are counted
both ways (upper estimate: unknown = irreducible; lower: unknown = reducible).
Exact enumeration when 3^n <= EXACT_MAX, otherwise Monte Carlo.

Usage: radius2_prune_count.py <sweep log> [samples]
"""
import sys, json, itertools, random, math
from patch_reducibility_lab import canon_outs

random.seed(4)
EXACT_MAX = 3 ** 8


def load(logp):
    table = {}
    for line in open(logp):
        if line.startswith('{'):
            r = json.loads(line)
            table[(r['s'], tuple(canon_outs(r['s'], list(r['outs']))))] = r['reducible']
    return table


def key(s, outs):
    return (s, tuple(canon_outs(s, list(outs))))


def ring2_layout(c, l):
    """positions of ring-2 faces: list of ('corner', i) or ('priv', i, j) in cyclic order"""
    lay = []
    for i in range(c):
        lay.append(('corner', i))            # C_{i,i+1}
        for j in range(l[(i + 1) % c] - 5):  # private faces of f_{i+1}
            lay.append(('priv', (i + 1) % c, j))
    return lay


def subflowers(c, l, r2, lay):
    """yield (size, neighbour sizes) for the centre and every ring-1 face"""
    yield (c, list(l))
    corner = {}
    priv = {i: [] for i in range(c)}
    for pos, size in zip(lay, r2):
        if pos[0] == 'corner': corner[pos[1]] = size
        else: priv[pos[1]].append(size)
    for i in range(c):
        nb = [c, l[(i + 1) % c], corner[i]] + priv[i] + [corner[(i - 1) % c], l[(i - 1) % c]]
        assert len(nb) == l[i]
        yield (l[i], nb)


RING_CAP = 13

def verdict(table, s, nb):
    k = key(s, nb)
    if k in table: return 'red' if table[k] else 'irr'
    # unknown: the closure tool never reaches second rings above RING_CAP
    return 'unk_big' if sum(x - 4 for x in nb) > RING_CAP else 'unk'


def main():
    logp = sys.argv[1] if len(sys.argv) > 1 else 'patch_sweep_B7_r13.log'
    samples = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
    table = load(logp)
    print(f"flower table: {len(table)} types ({sum(table.values())} reducible)")
    tot_raw = tot_hi = tot_lo = tot_real = 0.0
    types = 0
    per_center = {5: [0, 0, 0, 0], 6: [0, 0, 0, 0], 7: [0, 0, 0, 0]}
    for c in (5, 6, 7):
        seen = set()
        for outs in itertools.product((5, 6, 7), repeat=c):
            l = tuple(canon_outs(c, list(outs)))
            if l in seen: continue
            seen.add(l); types += 1
            # centre flower prunes everything at once
            vc = verdict(table, c, list(l))
            lay = ring2_layout(c, l); n = len(lay)
            raw = 3 ** n
            if vc == 'red':
                tot_raw += raw; per_center[c][0] += raw; continue
            if raw <= EXACT_MAX:
                hi = lo = real = 0
                for r2 in itertools.product((5, 6, 7), repeat=n):
                    vs = [verdict(table, s, nb) for s, nb in subflowers(c, l, r2, lay)]
                    if 'red' in vs: continue
                    hi += 1
                    if 'unk' not in vs and 'unk_big' not in vs: lo += 1
                    if 'unk' not in vs: real += 1
            else:
                h = lo_ = real_ = 0
                for _ in range(samples):
                    r2 = [random.choice((5, 6, 7)) for _ in range(n)]
                    vs = [verdict(table, s, nb) for s, nb in subflowers(c, l, r2, lay)]
                    if 'red' in vs: continue
                    h += 1
                    if 'unk' not in vs and 'unk_big' not in vs: lo_ += 1
                    if 'unk' not in vs: real_ += 1
                hi = raw * h / samples; lo = raw * lo_ / samples; real = raw * real_ / samples
            tot_raw += raw; tot_hi += hi; tot_lo += lo; tot_real += real
            per_center[c][0] += raw; per_center[c][1] += hi; per_center[c][2] += lo; per_center[c][3] += real
    print(f"radius-1 types: {types}")
    for c in (5, 6, 7):
        raw, hi, lo, real = per_center[c]
        print(f"  centre {c}: raw {raw:.3g}  surviving upper {hi:.3g}  lower {lo:.3g}  realistic {real:.3g}")
    print(f"TOTAL raw {tot_raw:.3g} (no symmetry reduction); surviving: upper {tot_hi:.3g}, lower {tot_lo:.3g}, realistic (unknown small types reducible, unknown big types irreducible) {tot_real:.3g}")


if __name__ == '__main__':
    main()
