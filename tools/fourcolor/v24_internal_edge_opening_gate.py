"""Preregistered attempted use of free-port rigidity after literal surgery.

Test the claim: exposing two internal edges that are equal in every closed
colouring preserves that equality in every colouring of the open piece.
Calibrate on K4 (six labelled colourings) and odd prisms (6 and 30).
Use the existing two independent whole-graph colouring enumerators.  Check
the actual endpoint model, rotation, connectivity and exact reclosure map.
This is a constructor diagnostic, not a configuration or ring-word census.
"""

from itertools import combinations
import argparse
import json

from v24_deletion_orbit_gate import colorings, vertex_colorings, incidence, components
from v24_square_physical_observable_gate import rotation_faces


def connected(n, edges):
    seen = {0}
    while True:
        new = seen | {v for u, v in edges if u in seen} | {u for u, v in edges if v in seen}
        if new == seen:
            return len(seen) == n
        seen = new


def prism(m):
    edges = [(i, (i + 1) % m) for i in range(m)]
    edges += [(m + i, m + (i + 1) % m) for i in range(m)]
    edges += [(i, m + i) for i in range(m)]
    rot = [[((i - 1) % m, 1), (i, 0), (2*m+i, 0)] for i in range(m)]
    rot += [[(m+i, 0), (m+(i-1) % m, 1), (2*m+i, 1)] for i in range(m)]
    return edges, rot


def open_edges(n, edges, selected):
    retained = [i for i in range(len(edges)) if i not in selected]
    opened = [edges[i] for i in retained]
    for j, i in enumerate(selected):
        u, v = edges[i]
        opened += [(u, n+2*j), (v, n+2*j+1)]
    return opened, retained


def opening_record(m, expected):
    """Keep the closed graph, the free opening and reclosure distinguishable."""
    n = 2*m
    edges, rot = prism(m)
    faces = rotation_faces(edges, rot)
    assert n - len(edges) + len(faces) == 2
    assert connected(n, edges)
    assert all(connected(n, edges[:i] + edges[i+1:]) for i in range(len(edges)))
    closed = colorings(n, edges)
    assert closed == vertex_colorings(n, edges)
    assert len(closed) == expected
    forced = [(i, j) for i, j in combinations(range(len(edges)), 2)
              if all(c[i] == c[j] for c in closed)]
    cofacial = [(i, j) for i, j in forced
                if any({i, j} <= {e for e, _ in face} for face in faces)]
    selected = cofacial[0]
    opened, retained = open_edges(n, edges, selected)
    assert connected(n, [edges[i] for i in retained])
    assert all(len(es) == 3 for es in incidence(n+4, opened)[:n])
    free = colorings(n+4, opened)
    assert free == vertex_colorings(n+4, opened)
    off = len(retained)
    reclosed = [c for c in free if c[off] == c[off+1] and c[off+2] == c[off+3]]
    def glue(c):
        result = [0] * len(edges)
        for i, old in enumerate(retained):
            result[old] = c[i]
        result[selected[0]], result[selected[1]] = c[off], c[off+2]
        return tuple(result)
    assert sorted(map(glue, reclosed)) == sorted(map(tuple, closed))
    assert all(len(set(c[off:])) == 1 for c in reclosed)
    escape = next(c for c in free if c[off] != c[off+2])
    assert escape not in reclosed

    # Positive control: opening ONE edge creates just two ports. All free
    # colourings already satisfy the matching needed to glue it back.
    single, _ = open_edges(n, edges, selected[:1])
    single_states = colorings(n+2, single)
    assert single_states == vertex_colorings(n+2, single)
    assert len(single_states) == len(closed)
    assert all(c[-2] == c[-1] for c in single_states)

    # A free Kempe path escapes, but the whole closed component need not.
    c = reclosed[0]
    pair = (c[off], (c[off]+1) % 3)
    paths = components(incidence(n+4, opened), c, pair)
    path = next(p for p in paths if off in p)
    changed = bytes(pair[0]+pair[1]-a if i in path else a for i, a in enumerate(c))
    assert changed in free and changed not in reclosed
    full = glue(c)
    closed_path = next(p for p in components(incidence(n, edges), full, pair)
                       if selected[0] in p)
    switched = tuple(pair[0]+pair[1]-a if i in closed_path else a for i, a in enumerate(full))
    assert bytes(switched) in closed
    assert switched[selected[0]] == switched[selected[1]]
    return dict(vertices=n, edges=edges, rotations=rot, faces=faces,
                closed_colorings=len(closed), single_open_colorings=len(single_states),
                selected_edges=selected, cofacial=True,
                free_open_colorings=len(free), reclosed_colorings=len(reclosed),
                open_edges=opened, retained_old_edge_indices=retained,
                free_escape=list(escape), escape_word=list(escape[off:]),
                free_switch_word=list(changed[off:]),
                closed_switch_preserves_forced_equality=True)


def run():
    k4 = list(combinations(range(4), 2))
    assert len(colorings(4, k4)) == 6
    records = [opening_record(m, expected) for m, expected in [(3, 6), (5, 30)]]
    return dict(claim='internal forced equality survives free opening',
                verdict='false', records=records)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', help='compare with an existing receipt')
    args = parser.parse_args()
    result = json.loads(json.dumps(run()))
    if args.check:
        with open(args.check, encoding='utf-8') as stream:
            assert result == json.load(stream)
    print(json.dumps(result, indent=2))
