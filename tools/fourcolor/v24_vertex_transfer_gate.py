#!/usr/bin/env python3
"""Construct literal one-vertex-plus-wire Count letters.

Preregistered gate: each extracted letter must agree with independent
edge-colouring of its actual star-and-wire graph, and whole sweeps must
agree with direct closed-graph colouring counts. Include a nonplanar snark
as a zero-count control: algebraic compilation must not assert planarity
or manufacture positivity. No uniform frontier bound is asserted.
"""

from collections import Counter, deque
from itertools import combinations, permutations, product
import json

from v24_deletion_orbit_gate import colorings, incidence
from v24_goldberg import make_goldberg_graph


def valid(letter):
    l, r, star, wires = letter
    if l < 0 or r < 0:
        return False
    if len(star) != 3 or len(set(star)) != 3 or len(wires) != r:
        return False
    if any(not (0 <= p < l + r) for p in star):
        return False
    if any(i is not None and not (0 <= i < l) for i in wires):
        return False
    if any((wires[j] is None) != (l + j in star) for j in range(r)):
        return False
    return sorted(i for i in wires if i is not None) == [i for i in range(l) if i not in star]


def step(letter, x):
    l, r, star, wires = letter
    assert valid(letter) and len(x) == l and all(c in range(3) for c in x)
    out = []
    for colors in permutations(range(3)):
        if any(p < l and x[p] != c for p, c in zip(star, colors)):
            continue
        y = [None if i is None else x[i] for i in wires]
        for p, c in zip(star, colors):
            if p >= l:
                y[p - l] = c
        assert all(c is not None for c in y)
        out.append(tuple(y))
    assert len(out) == len(set(out)), 'a single-vertex fibre must have multiplicity at most one'
    return out


def literal_graph(letter):
    l, r, star, wires = letter
    assert valid(letter)
    edges = [(0, 1 + p) for p in star]
    edges += [(1 + i, 1 + l + j) for j, i in enumerate(wires) if i is not None]
    boundary = [next(e for e, ends in enumerate(edges) if 1 + p in ends) for p in range(l + r)]
    return 1 + l + r, edges, boundary


def check_literal(letter):
    n, edges, boundary = literal_graph(letter)
    l, r, _, _ = letter
    actual = Counter()
    for c in colorings(n, edges):
        b = tuple(c[e] for e in boundary)
        actual[b[:l], b[l:]] += 1
    computed = Counter((tuple(x), y) for x in product(range(3), repeat=l) for y in step(letter, x))
    assert actual == computed
    return len(actual)


def extract(n, edges, order):
    assert sorted(order) == list(range(n))
    assert all(u != v for u, v in edges)
    inc = incidence(n, edges)
    assert all(len(row) == 3 for row in inc)
    seen, previous, letters = set(), [], []
    for v in order:
        seen.add(v)
        after = [i for i, (a, b) in enumerate(edges) if (a in seen) != (b in seen)]
        l, r = len(previous), len(after)
        star = tuple(previous.index(e) if e in previous else l + after.index(e) for e in inc[v])
        wires = tuple(previous.index(e) if e in previous else None for e in after)
        letter = l, r, star, wires
        assert valid(letter)
        letters.append(letter)
        previous = after
    assert not previous
    return letters


def evaluate(letters):
    counts, widths, supports = {(): 1}, [0], [1]
    for letter in letters:
        # Validate syntax even after the colouring support becomes empty.
        assert valid(letter) and letter[0] == widths[-1]
        result = Counter()
        for x, count in counts.items():
            for y in step(letter, x):
                result[y] += count
        counts = dict(result)
        widths.append(letter[1])
        supports.append(len(counts))
    assert widths[-1] == 0, 'a closed sweep must finish at the empty boundary'
    return counts.get((), 0), max(widths), max(supports)


def bfs_order(n, edges):
    inc = incidence(n, edges)
    seen, result = set(), []
    for root in range(n):
        if root in seen:
            continue
        seen.add(root)
        queue = deque([root])
        while queue:
            v = queue.popleft()
            result.append(v)
            for w in sorted({w for e in inc[v] for w in edges[e]} - seen):
                seen.add(w)
                queue.append(w)
    return result


def alphabet(bound):
    """Every well-formed ordered star-and-through-wire letter at this bound.

    No disk embedding in the specified boundary order is asserted for the
    whole alphabet; source-planar admissibility is a separate restriction.
    """
    for l in range(bound + 1):
        for consumed in range(4):
            r = l + 3 - 2 * consumed
            if not 0 <= r <= bound or consumed > l or 3 - consumed > r:
                continue
            for inside in combinations(range(l), consumed):
                for outside in combinations(range(r), 3 - consumed):
                    unused_in = tuple(i for i in range(l) if i not in inside)
                    unused_out = tuple(j for j in range(r) if j not in outside)
                    for wire_order in permutations(unused_in):
                        wires = [None] * r
                        for j, i in zip(unused_out, wire_order):
                            wires[j] = i
                        for star in permutations(inside + tuple(l + j for j in outside)):
                            letter = l, r, star, tuple(wires)
                            assert valid(letter)
                            yield letter


def closure(letters):
    initial = frozenset({()})
    transitions, queue = {initial: ()}, deque([initial])
    while queue:
        current = queue.popleft()
        images = []
        for letter in letters:
            image = frozenset(y for x in current if len(x) == letter[0] for y in step(letter, x))
            images.append(image)
            if image not in transitions:
                transitions[image] = ()
                queue.append(image)
        transitions[current] = tuple(images)
    block = {s: int(() in s) for s in transitions}
    while True:
        ids, refined = {}, {}
        for s, targets in transitions.items():
            signature = (block[s], tuple(block[t] for t in targets))
            refined[s] = ids.setdefault(signature, len(ids))
        if len(set(refined.values())) == len(set(block.values())):
            break
        block = refined
    return dict(raw_reachable=len(set.union(set(), *(set(s) for s in transitions))),
                subset_reachable=len(transitions), nerode_classes=len(ids),
                subset_sizes=sorted(map(len, transitions)))


def run():
    dodeca = make_goldberg_graph(1)
    petersen = [(i, (i + 1) % 5) for i in range(5)] + [(i, i + 5) for i in range(5)]
    petersen += [(i + 5, (i + 2) % 5 + 5) for i in range(5)]
    controls = [('tetrahedron', 4, list(combinations(range(4), 2))),
                ('dodecahedron', 20, [tuple(e) for e in dodeca['primal_edges']]),
                ('Petersen_nonplanar_zero_control', 10, petersen)]
    rows, checked = [], set()
    for name, n, edges in controls:
        direct = len(colorings(n, edges))
        for kind, order in [('numeric', list(range(n))), ('bfs', bfs_order(n, edges))]:
            letters = extract(n, edges, order)
            total, width, support = evaluate(letters)
            assert total == direct
            for letter in letters:
                if letter not in checked:
                    check_literal(letter)
                    checked.add(letter)
            rows.append(dict(control=name, order=kind, count=total, width=width, max_support=support))
    small = tuple(alphabet(3))
    assert len(small) == len(set(small))
    for letter in small:
        check_literal(letter)
    return dict(schema='fourcolor-vertex-transfer-v1', controls=rows,
                checked_extracted_letters=len(checked), width3_alphabet=len(small),
                width3_closure=closure(small),
                scope='Exact cubic vertex-sweep Count, not a uniform width or source-planarity theorem.')


if __name__ == '__main__':
    print(json.dumps(run(), sort_keys=True, indent=2))
