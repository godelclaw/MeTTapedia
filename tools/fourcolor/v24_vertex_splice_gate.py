#!/usr/bin/env python3
"""Test actual vertex-code deletion, including its structural side conditions.

Gate: start from spherical bridgeless cubic controls, find equal nonempty
prefix supports at equal arity, delete the intervening vertex letters,
and reconstruct the literal smaller rotation system. Test its topology,
not only Count. Compare the boundary face-return and connectivity data.
No claim about minimal counterexamples is tested by a colourable control.
"""

from collections import Counter
from itertools import combinations, permutations
import json
from random import Random

from v24_vertex_transfer_gate import extract, step, valid
from v24_plantri_seed_audit import graph_record, parse_ascii_graph


def encode_rotation(rot, order):
    graph = graph_record(rot, 0)
    edges = [tuple(e) for e in graph['primal_edges']]
    letters = extract(len(rot), edges, order)
    for t, v in enumerate(order):
        l, r, _, wires = letters[t]
        seen = set(order[:t])
        old = [e for e, (a, b) in enumerate(edges) if (a in seen) != (b in seen)]
        seen.add(v)
        new = [e for e, (a, b) in enumerate(edges) if (a in seen) != (b in seen)]
        incident = [edges.index(tuple(sorted((v, w)))) for w in rot[v]]
        star = tuple(old.index(e) if e in old else l + new.index(e) for e in incident)
        letters[t] = l, r, star, wires
    return letters


def decode(letters, close=False):
    """Retain cyclic star positions and identify wires without ghost vertices."""
    frontier, pairs = [], []
    for v, letter in enumerate(letters):
        l, r, star, wires = letter
        assert valid(letter) and len(frontier) == l
        new = [None if i is None else frontier[i] for i in wires]
        for slot, p in enumerate(star):
            d = 3 * v + slot
            if p < l:
                pairs.append((frontier[p], d))
            else:
                new[p - l] = d
        assert all(d is not None for d in new)
        frontier = new
    if close:
        assert not frontier
    return len(letters), pairs, frontier


def parts(n, pairs, omit=None):
    adj = [set() for _ in range(n)]
    for e, (d, f) in enumerate(pairs):
        if e != omit:
            adj[d // 3].add(f // 3)
            adj[f // 3].add(d // 3)
    result, seen = [], set()
    for v in range(n):
        if v in seen:
            continue
        comp, todo = set(), [v]
        while todo:
            w = todo.pop()
            if w in comp:
                continue
            comp.add(w)
            todo.extend(adj[w] - comp)
        seen |= comp
        result.append(comp)
    return result


def profile(n, pairs, frontier):
    """Boundary return, components, and all single-internal-edge failures."""
    alpha = dict(pairs)
    alpha.update((f, d) for d, f in pairs)
    leaves = list(range(3 * n, 3 * n + len(frontier)))
    for d, f in zip(frontier, leaves):
        alpha[d], alpha[f] = f, d
    assert set(alpha) == set(range(3 * n + len(frontier)))
    rho = lambda d: 3 * (d // 3) + (d + 1) % 3 if d < 3 * n else d
    phi = {d: rho(alpha[d]) for d in alpha}
    unseen, cycles = set(phi), []
    while unseen:
        start = min(unseen)
        cycle, d = [], start
        while d not in cycle:
            assert d in unseen
            unseen.remove(d)
            cycle.append(d)
            d = phi[d]
        assert d == start
        cycles.append(cycle)
    ret = []
    for d in leaves:
        f = phi[d]
        while f not in leaves:
            f = phi[f]
        ret.append(f - 3 * n)

    def boundary_partition(comps):
        blocks = [tuple(i for i, d in enumerate(frontier) if d // 3 in comp) for comp in comps]
        return tuple(sorted(blocks))

    comps = parts(n, pairs)
    partition = boundary_partition(comps)
    failures = tuple(sorted({boundary_partition(parts(n, pairs, e)) for e in range(len(pairs))}))
    return dict(face_return=tuple(ret), partition=partition, failures=failures,
                faces=len(cycles), euler=n - len(pairs) + len(cycles), components=len(comps),
                internal_faces=sum(not (set(cycle) & set(leaves)) for cycle in cycles))


def closed_structure(letters):
    n, pairs, frontier = decode(letters, close=True)
    p = profile(n, pairs, frontier)
    bridges = [e for e in range(len(pairs)) if len(parts(n, pairs, e)) > p['components']]
    ends = [tuple(sorted((d // 3, f // 3))) for d, f in pairs]
    return dict(vertices=n, components=p['components'], euler=p['euler'], faces=p['faces'],
                bridges=bridges, loopless=all(v != w for v, w in ends),
                simple=len(ends) == len(set(ends)),
                admissible=p['components'] == 1 and p['euler'] == 2 and not bridges
                and all(v != w for v, w in ends))


def supports(letters):
    states = [frozenset({()})]
    for letter in letters:
        states.append(frozenset(y for x in states[-1] for y in step(letter, x)))
    return states


def splice(letters, i, j, match=None):
    """match maps the later input position to the earlier output position."""
    assert 0 < i < j < len(letters)
    assert letters[i - 1][1] == letters[j][0]
    suffix = list(letters[j:])
    if match is not None:
        l, r, star, wires = suffix[0]
        assert sorted(match) == list(range(l))
        suffix[0] = (l, r, tuple(match[p] if p < l else p for p in star),
                     tuple(None if p is None else match[p] for p in wires))
    return letters[:i] + suffix


def transport_profile(p, match):
    assert sorted(match) == list(range(len(p['face_return'])))
    inverse = {old: new for new, old in enumerate(match)}
    relabel = lambda part: tuple(sorted(tuple(sorted(inverse[i] for i in b)) for b in part))
    return dict(face_return=tuple(inverse[p['face_return'][old]] for old in match),
                partition=relabel(p['partition']),
                failures=tuple(sorted(relabel(part) for part in p['failures'])))


def repair(letters, i, j, si, sj, pi, pj):
    width = letters[i - 1][1]
    assert width <= 6, 'the diagnostic permutation search is bounded'
    for match in permutations(range(width)):
        if frozenset(tuple(x[p] for p in match) for x in si) != sj:
            continue
        moved = transport_profile(pi, match)
        if moved['face_return'] != pj['face_return'] or moved['partition'] != pj['partition']:
            continue
        result = closed_structure(splice(letters, i, j, match))
        if result['admissible']:
            return dict(match=match, smaller=result)
    return None


def prism(m):
    return [[(i - 1) % m, (i + 1) % m, m + i] for i in range(m)] + [
        [m + (i + 1) % m, m + (i - 1) % m, i] for i in range(m)]


def run():
    rng = Random(731)
    controls = [('tetrahedron', [[1, 2, 3], [0, 3, 2], [0, 1, 3], [0, 2, 1]]),
                ('prism4', prism(4)), ('prism6', prism(6)), ('prism8', prism(8)),
                ('prism16', prism(16)), ('prism24', prism(24)),
                ('sphere30', parse_ascii_graph(
                    '30 bcd,aef,agh,aij,bjk,blg,cfm,cni,dho,dpe,eqr,frs,gst,htu,iuv,jvq,kpw,kxl,lym,mzn,n{o,o|p,q}x,rwy,sx~,t~{,uz|,v{},w|~,y}z'))]
    tally, specimens = Counter(), {}
    for name, rot in controls:
        orders = [list(range(len(rot)))]
        if name.startswith('prism'):
            m = len(rot) // 2
            orders += [[v for i in range(m) for v in (i, i + m)],
                       [v for i in reversed(range(m)) for v in (i, i + m)]]
        for _ in range(60):
            order = list(range(len(rot)))
            rng.shuffle(order)
            orders.append(order)
        for order in orders:
            letters = encode_rotation(rot, order)
            if max(letter[1] for letter in letters) > 10:
                continue
            assert closed_structure(letters)['admissible']
            tally['orders'] += 1
            states = supports(letters)
            profiles = [profile(*decode(letters[:i])) for i in range(len(letters) + 1)]
            for i, j in combinations(range(1, len(letters)), 2):
                if len(letters) - j + i < 2 or not states[i] or states[i] != states[j]:
                    continue
                smaller = splice(letters, i, j)
                result = closed_structure(smaller)
                assert bool(supports(smaller)[-1]) == bool(states[-1])
                tally['support_repeats'] += 1
                keys = ['face_return', 'partition', 'failures']
                matches = [profiles[i][k] == profiles[j][k] for k in keys]
                witness = dict(control=name, rotations=rot, order=order,
                    cuts=[i, j], width=letters[i - 1][1], support_size=len(states[i]),
                    before=profiles[i], after=profiles[j], smaller=result, letters=letters)
                if not result['admissible']:
                    if witness['width'] <= 6:
                        witness['repair'] = repair(letters, i, j, states[i], states[j], profiles[i], profiles[j])
                        tally['repair_attempts'] += 1
                        tally['repaired'] += witness['repair'] is not None
                    if result['simple']:
                        specimens.setdefault('simple', witness)
                for k in range(4):
                    if all(matches[:k]):
                        tally[f'level{k}_cases'] += 1
                        if not result['admissible']:
                            tally[f'level{k}_failures'] += 1
                            specimens.setdefault(str(k), witness)
    return dict(schema='fourcolor-vertex-splice-v1', tally=dict(tally), specimens=specimens,
                scope='Generic physical controls, not counterexamples; no universal topology claim.')


if __name__ == '__main__':
    print(json.dumps(run(), sort_keys=True, indent=2))
