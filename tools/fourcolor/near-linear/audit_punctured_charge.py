#!/usr/bin/env python3
"""Check exact low-neighbour charge while retaining signed high-edge transfers.

The finite spherical fixture checks the local formula and exposes the actual
remaining high-edge term. It does not establish universal flat coverage.
"""
import argparse
from hashlib import sha256
import json
import re
from pathlib import Path

from audit_diamond_sources import require
from audit_seven_pair_example import verify as verify_sphere
from probe_flat_pairs import geometry, read_rules, reading, breadth_first_reading


def verify(here):
    sphere = verify_sphere(here)
    path = here / 'seven-pair-four-triangle-example.json'
    _, ns, nx, pv = geometry(json.loads(path.read_text())['faces'])
    rules, revision = read_rules(here)
    cache = {}

    def matches(a, b):
        if (a, b) not in cache:
            values = []
            for rule in rules:
                x = reading(rule, a, b, ns, nx, pv)
                y = breadth_first_reading(rule[1], a, b, ns, nx, pv)
                require(x == y, 'Independent rule matchers disagree')
                values.append(x is not None)
            cache[a, b] = values
        return cache[a, b]

    def sent(a, b):
        return sum(rule[1][0][3] for rule, yes in zip(rules, matches(a, b)) if yes)

    def low(a):
        return 5 <= len(ns[a]) <= 6

    def five(a):
        return int(len(ns[a]) == 5)

    def tip(v, a):
        return nx[a, nx[a, v]]

    edge_tests, profiles = 0, []
    for v in sorted(ns):
        if len(ns[v]) < 7:
            continue
        require(all(len(ns[a]) >= 5 for a in ns[v]), 'Neighbour degree floor fails')
        low_total = 0
        for a in sorted(ns[v]):
            if not low(a):
                continue
            forward, backward = pv[v, a], nx[v, a]
            predicted = [bool(five(a)), bool(five(forward)), bool(five(backward)),
                         low(backward) and bool(five(tip(v, backward))),
                         low(forward) and bool(five(tip(v, a)))]
            actual = matches(a, v)
            require(predicted == actual[:5], 'A local source-rule equivalence fails')
            require(not any(actual[13:]), 'A high-sender rule was counted at a low sender')
            amount = 2 * int(predicted[0]) + sum(predicted[1:]) + sum(actual[5:13])
            require(amount == sent(a, v), 'The low-edge sum differs')
            require(sent(v, a) == 0, 'A high-to-low transfer survives')
            low_total += amount
            edge_tests += 1
        boundary = [[a, sent(a, v) - sent(v, a)] for a in sorted(ns[v]) if not low(a)]
        charge = 10 * (6 - len(ns[v])) + sum(sent(a, v) - sent(v, a) for a in ns[v])
        require(charge == 10 * (6 - len(ns[v])) + low_total + sum(x[1] for x in boundary),
                'The retained-boundary identity fails')
        profiles.append(dict(vertex=v, degree=len(ns[v]), low_budget=low_total,
                             high_boundary=boundary, final_charge=charge))
    selected = {p['vertex']: p for p in profiles if p['vertex'] in [39, 90]}
    require(selected[39]['low_budget'] == 12 and selected[39]['high_boundary'] == [[90, -2]],
            'The first retained centre differs')
    require(selected[90]['low_budget'] == 9 and
            selected[90]['high_boundary'] == [[39, 2], [89, -1]], 'The second centre differs')
    require(all(p['final_charge'] == 0 for p in selected.values()), 'The pair is not flat')
    # This is the distinct finite rotation used by the Lean example. Retain
    # exact source rows, rather than identifying it with the flat-pair fixture.
    chain_path = here / 'chain-boundary-example.json'
    chain_raw = chain_path.read_bytes()
    manifest = json.loads((here / 'cyclic-charge-examples.json').read_text())
    require(sha256(chain_raw).hexdigest() == manifest['fixture_sha256'], 'Chain fixture differs')
    _, cn, forward, reverse = geometry(json.loads(chain_raw)['faces'])
    cx, cp = reverse, forward
    lean = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor/ChainBoundaryGeometry.lean'
    rows = {int(v): list(map(int, row.split()))
            for v, row in re.findall(r'  \| (\d+) => "([0-9 ]+)\\n"', lean.read_text())}
    require(len(rows) == 162, 'Incomplete Lean source rows')
    for v, row in rows.items():
        require(set(row) == cn[v], 'Lean adjacency differs')
        require(all(cx[v, w] == row[(i + 1) % len(row)] for i, w in enumerate(row)),
                'Lean rotation differs')
    chain_cache = {}

    def chain_sent(a, b):
        if (a, b) not in chain_cache:
            actual = []
            for r, rule in enumerate(rules):
                x = reading(rule, a, b, cn, cx, cp)
                y = breadth_first_reading(rule[1], a, b, cn, cx, cp)
                require(x == y, 'Chain rule matchers disagree')
                if x is not None:
                    actual.append(r)
            chain_cache[a, b] = actual
        return sum(rules[r][1][0][3] for r in chain_cache[a, b])

    chain_examples = []
    for v, q, incoming, outgoing, expected in [(107,104,3,1,5), (41,32,0,2,1)]:
        require(len(cn[v]) == 7 and len(cn[q]) >= 7 and q in cn[v], 'Root geometry differs')
        require(all(5 <= len(cn[w]) <= 6 for w in cn[v] if w != q), 'Low star differs')
        budget = sum(chain_sent(w, v) for w in cn[v] if w != q)
        require(all(chain_sent(v, w) == 0 for w in cn[v] if w != q), 'Unexpected low output')
        require(budget == 13 and chain_sent(q, v) == incoming and
                chain_sent(v, q) == outgoing, 'Concrete transfers differ')
        charge = -10 + budget + incoming - outgoing
        require(charge == expected, 'Concrete charge differs')
        chain_examples.append(dict(root=[v,q], low_budget=budget, incoming=incoming,
                                   outgoing=outgoing, net=incoming-outgoing, final_charge=charge))
    return dict(evidence='Independent finite source-rule and spherical checks.',
                fixture_sha256=sha256(path.read_bytes()).hexdigest(), rule_revision=revision,
                low_edge_tests=edge_tests, high_receivers=len(profiles),
                independent_rule_tests=84 * len(cache), selected_profiles=list(selected.values()),
                paired_low_budget=21, internal_high_exchange=0, external_high_exchange=-1,
                paired_deficit=20, sphere_obstructing_cycles=sphere['obstructing_short_cycles'],
                scope='The pair is flat, but the full original radius-three ball is not asserted flat.',
                chain_fixture_sha256=sha256(chain_raw).hexdigest(),
                chain_independent_rule_tests=84 * len(chain_cache),
                chain_examples=chain_examples,
                chain_evidence='Numerical rule sums are program checks; Lean retains them symbolically.',
                verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parent)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
