#!/usr/bin/env python3
"""Check cyclic charge counts against all exact signed incident rule matches.

The general bound is proved in CyclicCharge.lean. These finite checks retain
the actual shared outer tips and compare two independent rule matchers.
"""

import argparse
from hashlib import sha256
import json
from pathlib import Path

from audit_diamond_sources import require
from probe_flat_pairs import geometry, read_rules, reading, breadth_first_reading


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    manifest = here / 'cyclic-charge-examples.json'
    data = json.loads(manifest.read_text())
    raw = (here / data['fixture']).read_bytes()
    require(sha256(raw).hexdigest() == data['fixture_sha256'], 'Fixture differs')
    fixture = json.loads(raw)
    _, neighbors, forward, reverse = geometry(fixture['faces'])
    nexts, prevs = reverse, forward
    rules, revision = read_rules(here)
    require(revision == fixture['rule_revision'], 'Rule revision differs')
    examples, total_checks = [], 0
    for expected in data['centres']:
        v = expected['vertex']
        degree = len(neighbors[v])
        require(degree >= 7, 'Receiver degree is low')
        require(all(5 <= len(neighbors[w]) <= 6 for w in neighbors[v]),
                'Low-neighbour guard fails')
        fives = sorted(w for w in neighbors[v] if len(neighbors[w]) == 5)
        wedges = [dict(sender=w, other=nexts[w, v], tip=nexts[w, nexts[w, v]])
                  for w in sorted(neighbors[v])]
        good_tips = [x for x in wedges if len(neighbors[x['tip']]) == 5]
        # Wedges, rather than distinct tip vertices, are the counted objects.
        k, m = len(fives), len(good_tips)
        transfers, observations, first_five = {}, [], 0
        for w in sorted(neighbors[v]):
            for a, b in ((w, v), (v, w)):
                matches = []
                for i, rule in enumerate(rules):
                    compiled = reading(rule, a, b, neighbors, nexts, prevs)
                    independent = breadth_first_reading(rule[1], a, b, neighbors, nexts, prevs)
                    require(compiled == independent, 'Independent matchers disagree')
                    total_checks += 1
                    if compiled is not None:
                        matches.append(dict(index=i, amount=rule[1][0][3], vertices=compiled))
                transfers[a, b] = sum(x['amount'] for x in matches)
                if b == v:
                    first_five += sum(x['amount'] for x in matches if x['index'] < 5)
                observations.append(dict(edge=[a, b], sent=transfers[a, b], matches=matches))
        require(all(transfers[v, w] == 0 for w in neighbors[v]), 'Nonzero reverse transfer')
        require(first_five == 4*k + 2*m, 'First-five-rule incidence count differs')
        charge = 10*(6-degree) + sum(transfers[w, v] - transfers[v, w] for w in neighbors[v])
        lower = 10*(6-degree) + 4*k + 2*m
        measured = dict(vertex=v, degree=degree, fives=k, tips=m, lower=lower, charge=charge)
        require(measured == expected, 'Measured record differs')
        require(lower <= charge, 'Lower bound fails')
        examples.append(dict(**measured, five_vertices=fives, counted_wedges=good_tips,
                             first_five_rule_supply=first_five, incident_rules=observations))
    # A nonempty single-five residual is obtained by two further legal flips.
    # Its second centre is flat, but its original centre is not; this does
    # not refute a theorem using flatness at both centres or minimality.
    residual = data['residual']
    faces = [list(face) for face in fixture['faces']]
    for a, b, c, d in residual['flips']:
        darts, neighbors, _, _ = geometry(faces)
        i, old_c = darts[a, b]
        j, old_d = darts[b, a]
        require((c, d) == (old_c, old_d), 'Residual flip differs')
        require(d not in neighbors[c], 'Residual flip duplicates an edge')
        faces[i], faces[j] = [c, d, b], [d, c, a]
    _, neighbors, forward, reverse = geometry(faces)
    nexts, prevs = reverse, forward
    require(min(map(len, neighbors.values())) >= 5, 'Residual minimum degree differs')
    u, h = residual['root']
    cycle = [h]
    while (w := nexts[u, cycle[-1]]) != h:
        require(w not in cycle, 'Residual star fails to close')
        cycle.append(w)
    require(len(cycle) == 6, 'Residual sender is not six-valent')
    require([len(neighbors[w]) for w in cycle] == [7, 5, 5, 7, 6, 5],
            'Residual shared fan differs')
    require(all(reading(rules[i], u, h, neighbors, nexts, prevs) is not None for i in (2, 4)),
            'Residual source rules are absent')
    a = cycle[3]
    require(a == residual['second_centre'], 'Residual second centre differs')
    require(cycle[2] == residual['unique_five'], 'Retained five differs')
    require(sorted(w for w in neighbors[a] if len(neighbors[w]) == 5) == [cycle[2]],
            'Residual unique five differs')
    require(all(len(neighbors[w]) == 6 for w in neighbors[a] if w != cycle[2]),
            'Residual non-five neighbour differs')
    residual_centres = []
    for v, expected_charge in ((h, residual['original_charge']), (a, residual['second_charge'])):
        transfers, observations = {}, []
        for w in sorted(neighbors[v]):
            for x, y in ((w, v), (v, w)):
                matches = []
                for i, rule in enumerate(rules):
                    compiled = reading(rule, x, y, neighbors, nexts, prevs)
                    independent = breadth_first_reading(rule[1], x, y, neighbors, nexts, prevs)
                    require(compiled == independent, 'Residual matchers disagree')
                    total_checks += 1
                    if compiled is not None:
                        matches.append(dict(index=i, amount=rule[1][0][3], vertices=compiled))
                transfers[x, y] = sum(t['amount'] for t in matches)
                observations.append(dict(edge=[x, y], sent=transfers[x, y], matches=matches))
        charge = 10*(6-len(neighbors[v])) + sum(
            transfers[w, v] - transfers[v, w] for w in neighbors[v])
        require(charge == expected_charge, 'Residual charge differs')
        residual_centres.append(dict(vertex=v, charge=charge, incident_rules=observations))
    lean = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor'
    report = dict(evidence='Independent exact program checks; the uniform lower bound is Lean proved.',
                  source_manifest='discharging-sources.json', rule_revision=revision,
                  fixture=data['fixture'], fixture_sha256=data['fixture_sha256'],
                  manifest_sha256=sha256(manifest.read_bytes()).hexdigest(),
                  verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                  lean_source_sha256={name: sha256((lean / (name + '.lean')).read_bytes()).hexdigest()
                                      for name in ('CyclicCharge', 'CyclicFanContinuation',
                                                   'CyclicChargeExample')},
                  independent_rule_checks=total_checks, disagreements=0, examples=examples,
                  residual=dict(flips=residual['flips'], sender_cycle=cycle, centres=residual_centres,
                                scope='Program evidence only. Second centre flat; original centre positive. '
                                      'No minimality or joint-flatness claim.'),
                  scope='Finite checks. No minimality, flat-neighbourhood coverage or termination claim.')
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(dict(examples=len(examples), independent_rule_checks=total_checks,
                          disagreements=0, bounds=[x['lower'] for x in examples],
                          charges=[x['charge'] for x in examples])))


if __name__ == '__main__':
    main()
