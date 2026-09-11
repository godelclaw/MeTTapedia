#!/usr/bin/env python3
"""Preregistered joint physical vertex-step gate.

An oriented cubic star plus through-wires updates Count, boundary face
return and the realized small-cut profile. Compare every prefix with its
literal decoded graph. The face-cycle delta and touched component count
must compute the exact Euler/genus change, not assume it is zero.
Include reversed rotations and nonplanar zero-colouring controls. No
uniform interface bound or counterexample reduction is asserted.
"""

from collections import Counter, deque
from itertools import permutations, product
import json

from v24_deletion_orbit_gate import colorings
from v24_structural_bridge_gate import cut_profile
from v24_vertex_splice_gate import decode, profile, prism
from v24_vertex_transfer_gate import alphabet, extract, step, valid


def encode_rotation(rot, order):
    """Encode any simple cubic rotation, without preassuming sphere topology."""
    assert all(len(row) == 3 and len(set(row)) == 3 for row in rot)
    assert all(0 <= w < len(rot) and v != w and v in rot[w]
               for v, row in enumerate(rot) for w in row)
    edges = sorted({tuple(sorted((v, w))) for v, row in enumerate(rot) for w in row})
    letters = extract(len(rot), edges, order)
    seen = set()
    for t, v in enumerate(order):
        l, r, _, wires = letters[t]
        old = [e for e, (a, b) in enumerate(edges) if (a in seen) != (b in seen)]
        seen.add(v)
        new = [e for e, (a, b) in enumerate(edges) if (a in seen) != (b in seen)]
        incident = [edges.index(tuple(sorted((v, w)))) for w in rot[v]]
        star = tuple(old.index(e) if e in old else l + new.index(e) for e in incident)
        letters[t] = l, r, star, wires
    return letters


def cycles(perm):
    assert sorted(perm) == list(range(len(perm)))
    todo, result = set(range(len(perm))), []
    while todo:
        point, cycle = min(todo), []
        while point in todo:
            todo.remove(point)
            cycle.append(point)
            point = perm[point]
        assert point == cycle[0]
        result.append(tuple(cycle))
    return result


def cut_step(letter, states):
    l, r, star, wires = letter
    assert valid(letter)
    result = set()
    for bits, selected, omitted, cost in states:
        assert len(bits) == l
        for new in (False, True):
            out = tuple(new if i is None else bits[i] for i in wires)
            mismatch = sum(bits[p] != new for p in star if p < l)
            result.add((out, selected or new, omitted or not new, min(2, cost + mismatch)))
    return result


def boundary_partition(states, width):
    """Zero-cut records distinguish exactly the interior components at ports."""
    zero = [bits for bits, _, _, cost in states if cost == 0]
    assert zero
    groups = {}
    for p in range(width):
        groups.setdefault(tuple(bits[p] for bits in zero), []).append(p)
    return tuple(tuple(group) for group in groups.values())


def face_step(letter, previous):
    l, r, star, wires = letter
    assert valid(letter) and len(previous) == l
    cycles(previous)
    base = tuple(previous) + tuple(l + (i + 1) % 3 for i in range(3))
    seam = list(range(l + 3))
    for i, p in enumerate(star):
        if p < l:
            seam[p], seam[l + i] = l + i, p
    composite = tuple(base[seam[p]] for p in range(l + 3))
    exposed = tuple(i if i is not None else l + star.index(l + j)
                    for j, i in enumerate(wires))
    assert len(exposed) == len(set(exposed))
    coord = {p: j for j, p in enumerate(exposed)}
    out = []
    for p in exposed:
        q = composite[p]
        while q not in coord:
            q = composite[q]
        out.append(coord[q])
    return tuple(out), len(cycles(composite)) - len(cycles(previous))


def joint_step(state, letter):
    """Boundary-only support/cuts/return transfer; reject newly created genus.

    The state space is finite at a fixed arity. Exact colouring counts and
    total component/face counts are intentionally not stored in this quotient.
    """
    returns, cuts, support = state
    l, _, star, _ = letter
    assert valid(letter) and len(returns) == l
    partition = boundary_partition(cuts, l)
    touched = {next(i for i, block in enumerate(partition) if p in block)
               for p in star if p < l}
    out, delta = face_step(letter, returns)
    twice_genus = 1 + sum(p < l for p in star) - 2 * len(touched) - delta
    assert twice_genus >= 0 and twice_genus % 2 == 0
    if twice_genus:
        return None
    return (out, frozenset(cut_step(letter, cuts)),
            frozenset(y for x in support for y in step(letter, x)))


def structurally_accepting(state):
    returns, cuts, _ = state
    # Nonempty, closed, connected, bridgeless; genus-zero already enforced.
    return (not returns and any(selected for _, selected, _, _ in cuts)
            and not any(selected and omitted and cost <= 1
                        for _, selected, omitted, cost in cuts))


def rejects_extension(state):
    """A hidden component forbids further vertices, not final acceptance."""
    return any(selected and cost == 0 and not any(bits)
               for bits, selected, _, cost in state[1])


def bounded_closure(width, prune_hidden=False):
    """Exhaust all valid letters at the bound, not a list of graph patches."""
    letters = tuple(alphabet(width))
    initial = ((), frozenset({((), False, False, 0)}), frozenset({()}))
    paths, queue = {initial: ()}, deque([initial])
    transitions, genus_rejections, extension_rejections = 0, 0, 0
    while queue:
        state = queue.popleft()
        if prune_hidden and rejects_extension(state):
            extension_rejections += 1
            continue
        for letter in letters:
            if letter[0] != len(state[0]):
                continue
            transitions += 1
            image = joint_step(state, letter)
            if image is None:
                genus_rejections += 1
                continue
            if image not in paths:
                paths[image] = paths[state] + (letter,)
                queue.append(image)
    # Every reached summary has a literal witness, independently reconstructed.
    for state, path in paths.items():
        check_sweep(path)
        if structurally_accepting(state):
            assert () in state[2], ('colourless accepting state', path)
    result = dict(width=width, alphabet=len(letters), states=len(paths),
                  transitions=transitions, genus_rejections=genus_rejections,
                  accepting_states=sum(map(structurally_accepting, paths)),
                  longest_witness=max(map(len, paths.values())),
                  scope='Python fixed-point check, not a kernel closure certificate or global width bound.')
    if prune_hidden:
        result['hidden_extension_rejections'] = extension_rejections
    return result


def check_sweep(letters, direct_colours=True):
    counts, cuts, returns = {(): 1}, {((), False, False, 0)}, ()
    components, euler, genus, deltas = 0, 0, 0, []
    for index, letter in enumerate(letters):
        l, _, star, _ = letter
        assert valid(letter) and len(returns) == l
        partition = boundary_partition(cuts, l)
        touched = {next(i for i, block in enumerate(partition) if p in block)
                   for p in star if p < l}
        consumed = sum(p < l for p in star)
        returns, face_delta = face_step(letter, returns)
        genus_twice_delta = 1 + consumed - 2 * len(touched) - face_delta
        assert genus_twice_delta >= 0 and genus_twice_delta % 2 == 0
        deltas.append(genus_twice_delta // 2)
        genus += genus_twice_delta // 2
        components += 1 - len(touched)
        euler += 1 - consumed + face_delta
        cuts = cut_step(letter, cuts)
        nxt = Counter()
        for x, count in counts.items():
            for y in step(letter, x):
                nxt[y] += count
        counts = dict(nxt)

        # Independent reconstruction retains vertices and individual edge pairs.
        n, pairs, frontier = decode(letters[:index + 1])
        actual = profile(n, pairs, frontier)
        edges = [(a // 3, b // 3) for a, b in pairs]
        assert cuts == cut_profile(n, edges, tuple(d // 3 for d in frontier))
        assert returns == actual['face_return']
        assert components == actual['components'] and euler == actual['euler']
        assert 2 * genus == 2 * components - euler
        assert sorted(boundary_partition(cuts, len(frontier))) == sorted(
            block for block in actual['partition'] if block)
        if direct_colours:
            opened = edges + [(d // 3, n + i) for i, d in enumerate(frontier)]
            direct = Counter(tuple(c[len(edges):]) for c in colorings(n + len(frontier), opened))
            assert counts == direct
    return dict(vertices=len(letters), count=counts.get((), 0),
                components=components, euler=euler, genus=genus,
                genus_steps=deltas, final_width=len(returns))


def run():
    tetra = [[1, 2, 3], [0, 3, 2], [0, 1, 3], [0, 2, 1]]
    rows = []
    for turns in product((False, True), repeat=4):
        rot = [list(reversed(row)) if turn else row for row, turn in zip(tetra, turns)]
        for order in permutations(range(4)):
            result = check_sweep(encode_rotation(rot, order))
            assert result['count'] == 6
            rows.append(result)
    # The same graph and Count can have spherical or positive-genus rotation data.
    assert {row['genus'] for row in rows} == {0, 1}
    other = []
    for m in (3, 4, 5):
        for order in (list(range(2 * m)), [v for i in range(m) for v in (i, i + m)]):
            result = check_sweep(encode_rotation(prism(m), order))
            assert result['genus'] == 0
            other.append(dict(control=f'prism{m}', **result))
    petersen = [[(i - 1) % 5, (i + 1) % 5, i + 5] for i in range(5)]
    petersen += [[(i - 2) % 5 + 5, (i + 2) % 5 + 5, i] for i in range(5)]
    result = check_sweep(encode_rotation(petersen, list(range(10))))
    assert result['genus'] > 0 and result['count'] == 0
    other.append(dict(control='Petersen_nonplanar_zero', **result))
    return dict(schema='fourcolor-joint-vertex-step-v1', tetra_sweeps=len(rows),
                tetra_genus_histogram=dict(Counter(row['genus'] for row in rows)),
                checked_prefixes=sum(row['vertices'] for row in rows + other),
                controls=other,
                width3_joint_closure=bounded_closure(3),
                scope='Joint physical prefix semantics; no global width, reduction or base claim.')


if __name__ == '__main__':
    print(json.dumps(run(), sort_keys=True, indent=2))
