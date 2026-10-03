#!/usr/bin/env python3
"""Replay a surviving flat-pair example and the joint rules supplying its tripod.

This is an independent finite check. Three flat vertices do not imply a
flat radius-three ball. The Lean rule theorem applies to arbitrary actual
minimal-map readings and does not assume this fixture is a counterexample.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path

from audit_chain_boundary import distances
from audit_diamond_sources import require
from audit_four_triangle_sources import verify as verify_sources
from audit_seven_pair_example import verify as verify_sphere
from probe_flat_pairs import geometry, read_rules, reading, breadth_first_reading


def verify(here):
    source = verify_sources(here)
    sphere = verify_sphere(here)
    path = here / 'seven-pair-four-triangle-example.json'
    fixture = json.loads(path.read_text())
    _, ns, nx, pv = geometry(fixture['faces'])
    rules, revision = read_rules(here)
    checks = 0

    def match(index, a, b):
        nonlocal checks
        one = reading(rules[index], a, b, ns, nx, pv)
        two = breadth_first_reading(rules[index][1], a, b, ns, nx, pv)
        require(one == two, 'Independent matchers disagree')
        checks += 1
        return one

    sender, receiver, first, second = 85, 8, 39, 90
    star = [receiver]
    for _ in range(5):
        star.append(nx[sender, star[-1]])
    require(star == [8, 111, 35, 154, 39, 86], 'Shared fan differs')
    require([len(ns[v]) for v in star] == [7, 5, 5, 6, 7, 5], 'Fan degrees differ')
    require({v for v in ns[first] if len(ns[v]) >= 7} == {second}, 'High neighbour differs')
    require(nx[star[4], star[3]] == second, 'The tip is not the retained second centre')
    require(match(2, sender, receiver) is not None and match(4, sender, receiver) is not None,
            'Original source rules absent')
    profiles = []
    for v in [sender, first, second]:
        charge = 10 * (6 - len(ns[v]))
        transfers = []
        for w in sorted(ns[v]):
            for a, b, sign in [(w, v, 1), (v, w, -1)]:
                for index, rule in enumerate(rules):
                    if match(index, a, b) is not None:
                        amount = sign * rule[1][0][3]
                        charge += amount
                        transfers.append([index, a, b, amount])
        require(charge == 0, 'Selected vertex is not flat')
        profiles.append(dict(vertex=v, degree=len(ns[v]), final_charge=charge, transfers=transfers))
    x, y, z = match(3, 52, first), match(1, 52, first), match(2, 125, first)
    require(x == [52, 39, 125, 17] and y == [52, 39, 134] and z == [125, 39, 86],
            'Joint rule readings differ')
    require(nx[first, 52] == 125, 'Adjacent dart differs')
    require([len(ns[v]) for v in [52, first, 125]] == [6, 7, 6], 'Joint degree guard differs')
    require(all(rules[i][1][0][3] == 1 for i in (1, 3, 2)), 'Transfer amounts differ')
    images = [x[3], x[2], x[0], x[1], y[2], z[2]]
    source_hit = next(h for h in fixture['source_occurrences'] if h['name'] == 'D0052.conf')
    require(images == source_hit['images'][10:], 'Recognized core differs from checked occurrence')
    radius = distances(ns, receiver)
    # A fixed receiver with nonzero final charge is already enough to refute the full ball guard.
    total = 10 * (6 - len(ns[receiver]))
    for w in ns[receiver]:
        for a, b, sign in [(w, receiver, 1), (receiver, w, -1)]:
            for index, rule in enumerate(rules):
                if match(index, a, b) is not None:
                    total += sign * rule[1][0][3]
    require(total != 0, 'Expected a witness separating three flat vertices from a flat ball')
    return dict(evidence='Independent spherical and rule checks; no universal coverage claim.',
        fixture_sha256=sha256(path.read_bytes()).hexdigest(),
        rule_revision=revision, configuration_revision=source['revision'],
        profiles=profiles, fan_root=[sender, receiver], free_degrees=[6, 7], tip=second,
        root=[52, first], adjacent_root=[125, first], rules=[1, 3, 2],
        common_rule_images=[y, x, z], core_images=images, joint_units=3,
        core_radius_from_pair=max(min(distances(ns, first)[v], distances(ns, second)[v]) for v in images),
        full_ball_counterobservation=dict(vertex=receiver, radius=radius[receiver], final_charge=total),
        independent_rule_tests=checks, sphere_obstructing_cycles=sphere['obstructing_short_cycles'],
        verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parent)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'profiles'}, indent=2))


if __name__ == '__main__':
    main()
