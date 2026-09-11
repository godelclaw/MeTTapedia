#!/usr/bin/env python3
"""Generic colour-copy constructor gate, without boundary-state enumeration.

Pre-registered test: a proper cubic tangle that accepts a monochromatic
boundary cannot force three designated ports equal in every colouring.
Switch the bichromatic component through one designated port. It has only
two boundary endpoints, so at least one of the other two ports is unchanged.
The two-port digon is a positive control: equality there does survive.
This tests a physical compiler for sharing colours between candidate
replacements, not a configuration catalogue or a reduction certificate.
"""

import argparse
import json


def validate(vertices, edges, ports, internal, boundary):
    assert len(edges) == len(internal) and len(ports) == len(boundary)
    assert all(0 <= u < vertices and 0 <= v < vertices and u != v for u, v in edges)
    assert all(0 <= v < vertices for v in ports)
    for v in range(vertices):
        colors = [internal[i] for i, e in enumerate(edges) if v in e]
        colors += [boundary[p] for p, u in enumerate(ports) if u == v]
        assert sorted(colors) == [1, 2, 3], 'not a proper cubic presentation'


def switch_component(vertices, edges, ports, internal, boundary, root, pair):
    validate(vertices, edges, ports, internal, boundary)
    assert len(set(pair)) == 2 and set(pair) <= {1, 2, 3}
    assert boundary[root] in pair
    # Use edge and port incidences as nodes. Parallel edges stay distinct.
    slots = [('e', i) for i, c in enumerate(internal) if c in pair]
    slots += [('p', i) for i, c in enumerate(boundary) if c in pair]
    adjacency = {s: set() for s in slots}
    for v in range(vertices):
        active = [('e', i) for i, e in enumerate(edges) if v in e and internal[i] in pair]
        active += [('p', p) for p, u in enumerate(ports) if u == v and boundary[p] in pair]
        assert len(active) == 2
        a, b = active
        adjacency[a].add(b)
        adjacency[b].add(a)
    seen, pending = set(), [('p', root)]
    while pending:
        s = pending.pop()
        if s not in seen:
            seen.add(s)
            pending.extend(adjacency[s] - seen)
    endpoints = sorted(i for kind, i in seen if kind == 'p')
    assert len(endpoints) == 2
    swap = dict(zip(pair, pair[::-1]))
    new_internal = [swap[c] if ('e', i) in seen else c for i, c in enumerate(internal)]
    new_boundary = [swap[c] if ('p', i) in seen else c for i, c in enumerate(boundary)]
    validate(vertices, edges, ports, new_internal, new_boundary)
    return dict(endpoints=endpoints, internal=new_internal, boundary=new_boundary)


def cycle(n):
    assert n >= 2 and n % 2 == 0
    # At n=2 the two different edges share endpoints: the digon control.
    return (n, [(i, (i + 1) % n) for i in range(n)], list(range(n)),
            [2 if i % 2 == 0 else 3 for i in range(n)], [1] * n)


def run():
    rows = []
    for n in (2, 4, 6, 8, 20):
        v, edges, ports, internal, boundary = cycle(n)
        changed = switch_component(v, edges, ports, internal, boundary, 0, (1, 2))
        assert changed['endpoints'] == [0, 1]
        assert (len(set(changed['boundary'])) == 1) == (n == 2)
        rows.append(dict(ports=n, vertices=v, endpoints=changed['endpoints'],
                         before=boundary, after=changed['boundary']))
    # A disconnected tangle is not an escape: two disjoint digons.
    disconnected = switch_component(4, [(0, 1), (0, 1), (2, 3), (2, 3)],
                                    [0, 1, 2, 3], [2, 3, 2, 3], [1] * 4, 0, (1, 2))
    assert disconnected['boundary'] == [2, 2, 1, 1]
    # Both actual digon pairings accept the all-red word. Their conjunction
    # requires all four ports equal; the switched word escapes one factor.
    validate(4, [(0, 1), (0, 1), (2, 3), (2, 3)],
             [0, 2, 3, 1], [2, 3, 2, 3], [1] * 4)
    assert disconnected['boundary'][1] != disconnected['boundary'][2]
    return dict(schema='fourcolor-colour-copy-constructor-v1', cycles=rows,
                disconnected=disconnected,
                intersection_control=dict(pairings=[[0, 1, 2, 3], [0, 3, 1, 2]],
                                          common_word=[1, 1, 1, 1],
                                          escape_word=disconnected['boundary']),
                conclusion='the two-ended Kempe switch breaks a three-port equality fork',
                scope='unrestricted proper colourings; no frozen auxiliary ports')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output')
    args = parser.parse_args()
    encoded = json.dumps(run(), indent=2) + '\n'
    if args.output:
        with open(args.output, 'w') as stream:
            stream.write(encoded)
    else:
        print(encoded, end='')
