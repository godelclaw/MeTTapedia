#!/usr/bin/env python3
"""Full-path avoidance gate for ordered split-grid meshes.

A forbidden vertex may lie between branch positions, so branch-only
avoidance is deliberately tested and rejected. Clean rows and columns
retain every vertex of their full original paths. The positive gate uses
the actual ambient closed neighbourhood, not distance in index space.
No zero-Count reduction or empty-disk conclusion is inferred. The negative
control has an explicit proper colouring, distinguishing it from a
counterexample to the colouring theorem.
"""
import argparse
import json
from pathlib import Path


def split_grid(a, b):
    def A(i, j):
        return 2 * (i * b + j)
    def B(i, j):
        return A(i, j) + 1
    rows = [[v for j in range(b) for v in (A(i, j), B(i, j))] for i in range(a)]
    cols = [[v for i in range(a) for v in (A(i, j), B(i, j))] for j in range(b)]
    adjacency = {v: set() for v in range(2 * a * b)}
    for path in rows + cols:
        for u, v in zip(path, path[1:]):
            adjacency[u].add(v)
            adjacency[v].add(u)
    return rows, cols, adjacency


def closed(adjacency, marks, radius):
    result = set(marks)
    for _ in range(radius):
        result |= {v for u in result for v in adjacency[u]}
    return result


def check_family(paths, adjacency):
    seen = set()
    for path in paths:
        assert len(path) >= 2 and len(set(path)) == len(path)
        edges = {tuple(sorted((u, v))) for u, v in zip(path, path[1:])}
        assert not edges & seen
        seen |= edges
        assert all(v in adjacency[u] for u, v in zip(path, path[1:]))


def extract(rows, cols, forbidden, p, q):
    clean_rows = [i for i, path in enumerate(rows) if not set(path) & forbidden]
    clean_cols = [j for j, path in enumerate(cols) if not set(path) & forbidden]
    assert len(rows) - len(clean_rows) <= 3 * len(forbidden)
    assert len(cols) - len(clean_cols) <= 3 * len(forbidden)
    assert len(clean_rows) >= p and len(clean_cols) >= q
    return clean_rows[:p], clean_cols[:q]


def enclosed_mark_control():
    """A cubic bridgeless planar carrier avoids a mark INSIDE its cell.

    Subdivide two opposite edges of a split-grid cell and join the two
    subdivisions through a diamond, then cap the exterior deficits by an
    eight-cycle. Integer coordinates verify the drawing directly; no
    planarity-library certificate is assumed. A proper colouring witness
    explicitly separates this specimen from the counterexample class.
    """
    rows, cols, adjacency = split_grid(2, 2)
    points = {2 * (2 * i + j) + bit: (4 * j + 2 * bit - 1, 4 * i + 2 * bit - 1)
              for i in range(2) for j in range(2) for bit in range(2)}
    points.update({8: (2, 0), 9: (2, 4), 10: (2, 1), 11: (2, 3),
                   12: (1, 2), 13: (3, 2)})
    for u, v, new in ((1, 2, 8), (5, 6, 9)):
        adjacency[u].remove(v)
        adjacency[v].remove(u)
        adjacency[new] = {u, v}
        adjacency[u].add(new)
        adjacency[v].add(new)
        for path in rows + cols:
            for pos in range(len(path) - 1):
                if {path[pos], path[pos + 1]} == {u, v}:
                    path.insert(pos + 1, new)
                    break
    def add(u, v):
        adjacency.setdefault(u, set()).add(v)
        adjacency.setdefault(v, set()).add(u)

    for u, v in ((8, 10), (9, 11), (10, 12), (10, 13), (11, 12), (11, 13), (12, 13)):
        add(u, v)
    outer = [(-3, -2), (0, -3), (4, -3), (7, 0), (7, 6), (4, 7), (0, 7), (-3, 4)]
    for i, anchor in enumerate((0, 0, 2, 3, 7, 7, 5, 4)):
        points[14 + i] = outer[i]
        add(14 + i, anchor)
        add(14 + i, 14 + (i + 1) % 8)

    def cross(a, b, c):
        return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])

    def on(a, b, p):
        return cross(a, b, p) == 0 and all(min(a[i], b[i]) <= p[i] <= max(a[i], b[i])
                                         for i in range(2))

    edges = sorted((u, v) for u in adjacency for v in adjacency[u] if u < v)
    for n, (u, v) in enumerate(edges):
        a, b = points[u], points[v]
        assert all(not on(a, b, p) for w, p in points.items() if w not in (u, v))
        for w, x in edges[n + 1:]:
            if {u, v} & {w, x}:
                continue
            c, d = points[w], points[x]
            assert not (on(a, b, c) or on(a, b, d) or on(c, d, a) or on(c, d, b))
            assert not (cross(a, b, c) * cross(a, b, d) < 0
                        and cross(c, d, a) * cross(c, d, b) < 0)
    cycle = [1, 8, 2, 3, 6, 9, 5, 4]
    assert all(v in adjacency[u] for u, v in zip(cycle, cycle[1:] + cycle[:1]))
    assert all(cross(points[u], points[v], points[10]) > 0
               for u, v in zip(cycle, cycle[1:] + cycle[:1]))
    check_family(rows, adjacency)
    check_family(cols, adjacency)
    assert all(len(neighbours) == 3 for neighbours in adjacency.values())
    # Independently check connectedness after deletion of every edge.
    for removed in edges:
        reached, frontier = {0}, [0]
        while frontier:
            u = frontier.pop()
            for v in adjacency[u]:
                if tuple(sorted((u, v))) != removed and v not in reached:
                    reached.add(v)
                    frontier.append(v)
        assert len(reached) == len(adjacency)
    # Find one colouring, then check it directly. No support enumeration.
    incident = {u: [i for i, edge in enumerate(edges) if u in edge] for u in adjacency}
    colouring = {}

    def colour_one():
        if len(colouring) == len(edges):
            return True
        def available(i):
            return {1, 2, 3} - {colouring[j] for u in edges[i] for j in incident[u]
                               if j in colouring}
        i = min((j for j in range(len(edges)) if j not in colouring),
                key=lambda j: (len(available(j)), j))
        for c in sorted(available(i)):
            colouring[i] = c
            if colour_one():
                return True
            del colouring[i]
        return False

    assert colour_one()
    assert all({colouring[i] for i in incident[u]} == {1, 2, 3} for u in adjacency)
    assert all(10 not in path for path in rows + cols)
    assert extract(rows, cols, {10}, 2, 2) == ([0, 1], [0, 1])
    return dict(vertices=len(adjacency), edges=len(edges), maximum_degree=3,
                carrier_avoids_mark=True, mark_strictly_inside_cell=True,
                integer_drawing_checked=True, degree_of_mark=len(adjacency[10]),
                cubic=True, bridgeless=True, tait_colourable=True,
                edges_and_colours=[[*edge, colouring[i]] for i, edge in enumerate(edges)],
                target_counterexample_class=False)


def run():
    cases = []
    for radius in range(3):
        p, q, marks_count = 3, 4, 2
        loss = 3 * marks_count * 4 ** radius
        a, b = p + loss, q + loss
        rows, cols, adjacency = split_grid(a, b)
        assert max(map(len, adjacency.values())) <= 3
        check_family(rows, adjacency)
        check_family(cols, adjacency)
        # Odd-labelled vertices are NOT designated branch vertices.
        marks = {2 * ((a // 3) * b + b // 3) + 1,
                 2 * ((2 * a // 3) * b + 2 * b // 3) + 1}
        forbidden = closed(adjacency, marks, radius)
        assert len(forbidden) <= marks_count * 4 ** radius
        rr, cc = extract(rows, cols, forbidden, p, q)
        for i in rr:
            assert not set(rows[i]) & forbidden
        for j in cc:
            assert not set(cols[j]) & forbidden
        for i in rr:
            positions = [rows[i].index(2 * (i * b + j)) for j in cc]
            assert positions == sorted(set(positions))
        for j in cc:
            positions = [cols[j].index(2 * (i * b + j)) for i in rr]
            assert positions == sorted(set(positions))
        assert all(v % 2 == 1 for v in marks)
        assert all(any(v in path for path in rows) for v in marks)
        cases.append(dict(radius=radius, source=[a, b], target=[p, q],
                          vertices=len(adjacency), forbidden_vertices=len(forbidden),
                          loss_bound=loss, selected_rows=rr, selected_columns=cc))
    return dict(schema='fourcolor-protected-mesh-gate-v2', cases=cases,
                branch_only_avoidance_sufficient=False, full_path_avoidance=True,
                enclosed_mark_control=enclosed_mark_control(),
                scope='ordered path carrier, not a disk interior or a complete separator; no physical reduction supplied')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--check', type=Path)
    args = parser.parse_args()
    result = json.loads(json.dumps(run()))
    if args.check:
        assert result == json.loads(args.check.read_text())
    if args.output:
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
