#!/usr/bin/env python3
"""Check source fidelity of the Lean rule-pair example against the saved graph.

Lean separately checks cyclicity, triangularity and full rule matches. This
program also records which observations the unsuccessful straddling-core
candidate was missing; absence from a reading is not an impossibility theorem.
"""

from hashlib import sha256
import json
from pathlib import Path
import re

from probe_flat_pairs import geometry, read_rules, reading


def audit():
    here = Path(__file__).resolve().parent
    repo = here.parents[2]
    fixture_path = here / 'flat-pair-probe.json'
    fixture = json.loads(fixture_path.read_text())
    _, neighbors, nexts, prevs = geometry(fixture['faces'])
    rows = []
    for u in range(fixture['vertices']):
        row, v = [], min(neighbors[u])
        while v not in row:
            row.append(v)
            v = nexts[u, v]
        assert v == row[0] and set(row) == neighbors[u]
        rows.append(' '.join(map(str, row)))
    expected = '\n'.join(rows) + '\n'
    lean_path = repo / 'lean/fourcolor-classical/MettapediaFourColor/RulePairExampleData.lean'
    match = re.search(r'def source : String := ("(?:[^"\\]|\\.)*")', lean_path.read_text())
    assert match and json.loads(match[1]) == expected
    cached = re.findall(r'^  \| (\d+) => ("(?:[^"\\]|\\.)*")$',
                        lean_path.read_text(), re.MULTILINE)
    assert [(int(i), json.loads(row)) for i, row in cached] == [
        (i, row + '\n') for i, row in enumerate(rows)]
    rules, revision = read_rules(here)
    assert revision == fixture['rule_revision']
    assert rules[4][0] == 'rule003_2.rule' and rules[5][0] == 'rule004_1.rule'
    root = (25, 18)
    second = (prevs[18, prevs[18, 25]], 18)
    assert second == (28, 18)
    left = reading(rules[4], *root, neighbors, nexts, prevs)
    right = reading(rules[5], *second, neighbors, nexts, prevs)
    assert left == [25, 18, 5, 26] and right == [28, 18, 5, 19, 1]
    assert len(neighbors[root[0]]) == 5 and len(neighbors[left[2]]) == 6
    cycle, v = [], left[3]
    for _ in range(6):
        cycle.append(v)
        v = nexts[left[2], v]
    assert cycle == [26, 25, 18, 28, 19, 1] and v == 26
    diamond = (26, 5)
    assert [len(neighbors[vertex]) for vertex in
            [*diamond, nexts[diamond], prevs[diamond]]] == [5, 6, 5, 5]
    collision_root = (41, 39)
    collision_second = (prevs[39, prevs[39, 41]], 39)
    collision_left = reading(rules[4], *collision_root, neighbors, nexts, prevs)
    collision_right = reading(rules[5], *collision_second, neighbors, nexts, prevs)
    assert collision_left == [41, 39, 32, 30]
    assert collision_second == (9, 39) and collision_right == [9, 39, 32, 4, 30]
    collision_edge = (30, 32)
    assert [len(neighbors[v]) for v in
            [*collision_edge, nexts[collision_edge], prevs[collision_edge]]] == [5] * 4
    collisions = []
    for u in sorted(neighbors):
        for v in sorted(neighbors[u]):
            x = reading(rules[4], u, v, neighbors, nexts, prevs)
            if x is None or len(neighbors[u]) != 5 or len(neighbors[x[2]]) != 5:
                continue
            scan_second = (prevs[v, prevs[v, u]], v)
            y = reading(rules[5], *scan_second, neighbors, nexts, prevs)
            if y is None:
                continue
            assert x[3] == y[4]
            outer_degree = len(neighbors[y[3]])
            assert outer_degree in (5, 6)
            if outer_degree == 5:
                edge = x[3], x[2]
                assert [len(neighbors[z]) for z in
                        [*edge, nexts[edge], prevs[edge]]] == [5] * 4
            collisions.append({'root': [u, v], 'left_images': x, 'right_images': y,
                               'outer_degree': outer_degree})
    assert len(collisions) == 11
    assert sum(item['outer_degree'] == 5 for item in collisions) == 4
    observed = set()
    for centre in fixture['pair']:
        for neighbor in neighbors[centre]:
            for a, b in [(centre, neighbor), (neighbor, centre)]:
                for rule in rules:
                    images = reading(rule, a, b, neighbors, nexts, prevs)
                    if images is not None:
                        observed.update(images)
    straddling_core = [38, 39, 36, 27]
    unobserved = sorted(set(straddling_core) - observed)
    assert unobserved == [38]
    return {
        'fixture_sha256': sha256(fixture_path.read_bytes()).hexdigest(),
        'rotation_source_sha256': sha256(expected.encode()).hexdigest(),
        'source_fidelity': 'All 42 cyclic stars exactly match the saved oriented faces.',
        'rule_revision': revision,
        'left_rule': {'index': 4, 'source': rules[4][0], 'root': root, 'images': left},
        'right_rule': {'index': 5, 'source': rules[5][0], 'root': second, 'images': right},
        'shared_vertex_cycle': cycle,
        'mixed_edge': diamond,
        'flanking_vertices': [nexts[diamond], prevs[diamond]],
        'collision_example': {
            'root': collision_root, 'second_root': collision_second,
            'left_images': collision_left, 'right_images': collision_right,
            'identified_vertex': collision_left[3], 'shared_vertex': collision_left[2],
            'pentagonal_edge': collision_edge,
            'flanking_vertices': [nexts[collision_edge], prevs[collision_edge]]},
        'bounded_collision_scan': {
            'degree_five_pairs': len(collisions),
            'pentagonal_guards_satisfied': 4, 'residual_five_six_profiles': 7,
            'readings': collisions,
            'scope': 'Program check on one saved graph. A residual profile is not an obstruction to all other reductions.'},
        'scope': 'Lean certifies the cyclic/triangular rotation and complete rule checks with degree guards for both examples; shared structural theorems supply the mixed and pentagonal patterns. Flat charge, spherical flip history and the exhaustive collision scan remain program evidence.',
        'discarded_candidate': {
            'straddling_core': straddling_core,
            'vertices_not_in_any_positive_incident_rule_reading': unobserved,
            'conclusion': 'Positive rule readings do not directly supply every vertex of this particular core. This is not a refutation of classification using other geometry or negative rule information.'
        }
    }


if __name__ == '__main__':
    print(json.dumps(audit(), indent=2))
