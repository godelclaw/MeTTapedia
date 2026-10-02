#!/usr/bin/env python3
"""Check all three same-root rule-fan branches on the retained triangulation.

This is an independent program check. RuleFanSupplyExample separately checks
the source rules and the three geometric consumers in Lean's kernel.
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
    fixture = here / 'chain-boundary-example.json'
    raw = fixture.read_bytes()
    old_audit = json.loads((here / 'chain-boundary-audit.json').read_text())
    require(sha256(raw).hexdigest() == old_audit['example_sha256'], 'Fixture differs from replay')
    data = json.loads(raw)
    _, neighbors, forward, reverse = geometry(data['faces'])
    rules, revision = read_rules(here)
    require(revision == data['rule_revision'], 'Rule revision differs')
    require(rules[2][0] == 'rule002_2.rule' and rules[4][0] == 'rule003_2.rule', 'Rule indices differ')
    # The retained Lean star rotation reverses the source triangle orientation.
    nexts, prevs = reverse, forward
    expected = [
        ('diamond', (59, 26), [26, 58, 3, 57, 21, 128], [7, 5, 5, 5, 6, 5]),
        ('eight', (122, 76), [76, 124, 121, 68, 70, 33], [7, 5, 5, 6, 5, 5]),
        ('nine', (94, 159), [159, 95, 10, 96, 160, 37], [7, 5, 5, 6, 6, 5]),
    ]
    cases = []
    for branch, (u, v), expected_cycle, expected_degrees in expected:
        require(len(neighbors[u]) == 6, 'Sender is not six-valent')
        cycle = [v]
        for _ in range(5):
            cycle.append(nexts[u, cycle[-1]])
        require(nexts[u, cycle[-1]] == v and len(set(cycle)) == 6, 'Star does not close exactly')
        degrees = [len(neighbors[w]) for w in cycle]
        require(cycle == expected_cycle and degrees == expected_degrees, 'Cycle observations differ')
        images = []
        for index in (2, 4):
            compiled = reading(rules[index], u, v, neighbors, nexts, prevs)
            propagated = breadth_first_reading(rules[index][1], u, v, neighbors, nexts, prevs)
            require(compiled is not None and compiled == propagated, 'Independent rule checks differ')
            images.append(compiled)
        require(images[0] == [u, v, cycle[5]] and images[1] == [u, v, cycle[1], cycle[2]],
                'The two rules do not read the same star')
        require(all(degrees[i] == 5 for i in (1, 2, 5)), 'Fixed fan differs')
        if branch == 'diamond':
            tip = cycle[2]
            require(len(neighbors[tip]) == 5 and len(neighbors[nexts[tip, u]]) == 5
                    and len(neighbors[prevs[tip, u]]) == 5, 'Mixed diamond differs')
        else:
            require(degrees[2:6] == ([5, 6, 5, 5] if branch == 'eight' else [5, 6, 6, 5]),
                    'Chain degree word differs')
        cases.append(dict(branch=branch, root=[u, v], cycle=cycle, degrees=degrees,
                          rule2_images=images[0], rule4_images=images[1]))
    report = dict(evidence='Independent program check, separately kernel-certified examples.',
                  fixture=fixture.name, fixture_sha256=sha256(raw).hexdigest(),
                  rule_revision=revision, vertices=len(neighbors), cases=cases,
                  independent_rule_checks=6, disagreements=0,
                  verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                  scope='Three same-root source-rule examples; no minimality or universal coverage claim.')
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(dict(branches=[c['branch'] for c in cases],
                         independent_rule_checks=6, disagreements=0)))


if __name__ == '__main__':
    main()
