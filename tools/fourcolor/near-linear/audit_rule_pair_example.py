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
    charge_root = (7, 11)
    charge_second = (prevs[11, prevs[11, 7]], 11)
    charge_left = reading(rules[4], *charge_root, neighbors, nexts, prevs)
    charge_right = reading(rules[5], *charge_second, neighbors, nexts, prevs)
    charge_joined = reading(rules[9], *charge_second, neighbors, nexts, prevs)
    assert charge_second == (9, 11)
    assert charge_left == [7, 11, 36, 27]
    assert charge_right == [9, 11, 36, 39, 27]
    assert charge_joined == [9, 11, 39, 36, 7, 27]
    assert charge_left[3] == charge_right[4]
    assert [len(neighbors[v]) for v in charge_joined] == [6, 8, 6, 5, 5, 5]
    for index in (2, 5, 9):
        assert reading(rules[index], *charge_second, neighbors, nexts, prevs) is not None
        assert rules[index][1][0][3] == 1
    def sent(u, v):
        if v not in neighbors[u]:
            return 0
        return sum(rule[1][0][3] for rule in rules
                   if reading(rule, u, v, neighbors, nexts, prevs) is not None)
    second_net = sent(*charge_second) - sent(*reversed(charge_second))
    rest_net = sum(sent(w, 11) - sent(11, w) for w in neighbors if w != 9)
    assert second_net == 3 and rest_net == 17
    assert 10 * (6 - len(neighbors[11])) + second_net + rest_net == 0
    paired = []
    for item in collisions:
        u, v = item['root']
        if item['outer_degree'] != 6 or len(neighbors[v]) < 7:
            continue
        w = prevs[v, prevs[v, u]]
        assert u != w
        second_degree = len(neighbors[w])
        assert second_degree in (5, 6)
        lower = 8 if second_degree == 5 else 7
        first_net = sent(u, v) - sent(v, u)
        other_net = sent(w, v) - sent(v, w)
        assert first_net >= 4 and first_net + other_net >= lower
        remainder = sum(sent(z, v) - sent(v, z) for z in neighbors if z not in (u, w))
        paired.append({
            **item, 'second_root': [w, v], 'second_sender_degree': second_degree,
            'certified_joint_lower_bound': lower,
            'program_net_first': first_net, 'program_net_second': other_net,
            'program_remaining_supply': remainder,
            'program_final_charge': 10 * (6 - len(neighbors[v])) + first_net + other_net + remainder})
    assert {tuple(item['root']) for item in paired} == {(7, 11), (4, 16)}
    assert {item['second_sender_degree'] for item in paired} == {5, 6}
    five_example = next(item for item in paired if item['second_sender_degree'] == 5)
    assert five_example['left_images'] == [4, 16, 6, 30]
    assert five_example['right_images'] == [37, 16, 6, 31, 30]
    rerooted = []
    for u in sorted(neighbors):
        for v in sorted(neighbors[u]):
            y = reading(rules[5], u, v, neighbors, nexts, prevs)
            if y is None or [len(neighbors[y[i]]) for i in (0, 2, 3)] != [5, 5, 6]:
                continue
            edge = y[2], y[3]
            assert [nexts[edge], prevs[edge]] == [y[4], y[0]]
            assert [len(neighbors[z]) for z in (*edge, nexts[edge], prevs[edge])] == [5, 6, 5, 5]
            rerooted.append({'root': [u, v], 'reading': y, 'mixed_edge': edge,
                             'flanks': [nexts[edge], prevs[edge]]})
    assert len(rerooted) == 8
    assert any(item['root'] == [37, 16] for item in rerooted)
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
        'charge_example': {
            'root': charge_root, 'second_root': charge_second,
            'left_images': charge_left, 'right_images': charge_right,
            'joined_rule': rules[9][0], 'joined_images': charge_joined,
            'distinct_contributing_rules': [rules[i][0] for i in (2, 5, 9)],
            'certified_charge_lower_bound': 3,
            'program_net_charge': second_net,
            'program_remaining_supply': rest_net,
            'program_final_charge': 0,
            'scope': 'RulePairChargeExample checks the two original readings and degree guards; the uniform gluing theorem supplies the third rule and the charge bound.'},
        'paired_budget_examples': paired,
        'rerooted_mixed_scan': {
            'instances': rerooted,
            'scope': 'Program scan of all rooted right rules in the saved graph. RulePairResidual proves the generic law; RulePairResidualExample consumes it at the degree-five budget instance.'},
        'scope': 'Lean certifies the cyclic/triangular rotation and complete local readings for the mixed, pentagonal and two residual instances. Uniform laws give reductions or charge lower bounds. Total charge, exact remainders, spherical flip history and the exhaustive collision scan remain program evidence.',
        'discarded_candidate': {
            'straddling_core': straddling_core,
            'vertices_not_in_any_positive_incident_rule_reading': unobserved,
            'conclusion': 'Positive rule readings do not directly supply every vertex of this particular core. This is not a refutation of classification using other geometry or negative rule information.'
        }
    }


if __name__ == '__main__':
    print(json.dumps(audit(), indent=2))
