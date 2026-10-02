#!/usr/bin/env python3
"""Replay complete charge identities and both single-five residual budgets."""

import argparse
from hashlib import sha256
import json
from pathlib import Path

from audit_diamond_sources import require
from generate_rule_traces import compile_traces
from probe_flat_pairs import geometry, read_rules, reading, breadth_first_reading


def spherical_geometry(faces):
    require(all(len(set(face)) == 3 for face in faces), 'Degenerate face')
    result = geometry(faces)
    darts, neighbours, _, _ = result
    require(all((v, u) in darts for u, v in darts), 'Unpaired dart')
    reached, pending = set(), [min(neighbours)]
    while pending:
        v = pending.pop()
        if v not in reached:
            reached.add(v)
            pending.extend(neighbours[v] - reached)
    require(reached == set(neighbours), 'Disconnected surface')
    # geometry checks one cycle per vertex and Euler characteristic two.
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    manifest = here / 'exact-charge-examples.json'
    data = json.loads(manifest.read_text())
    raw = (here / data['fixture']).read_bytes()
    require(sha256(raw).hexdigest() == data['fixture_sha256'], 'Fixture differs')
    fixture = json.loads(raw)
    rules, revision = read_rules(here)
    require(revision == fixture['rule_revision'], 'Rule revision differs')
    checks = 0

    def checked(rule, a, b, ns, nx, pv):
        nonlocal checks
        first = reading(rule, a, b, ns, nx, pv)
        second = breadth_first_reading(rule[1], a, b, ns, nx, pv)
        require(first == second, 'Independent rule readings disagree')
        checks += 1
        return first

    def observe(v, ns, nx, pv):
        degree = len(ns[v])
        tips = [(w, nx[w, nx[w, v]]) for w in sorted(ns[v])
                if len(ns[nx[w, nx[w, v]]]) == 5]
        fives = [w for w in sorted(ns[v]) if len(ns[w]) == 5]
        charge, matches = 10 * (6 - degree), []
        for w in sorted(ns[v]):
            for a, b, sign in ((w, v, 1), (v, w, -1)):
                for index, rule in enumerate(rules):
                    im = checked(rule, a, b, ns, nx, pv)
                    if im is not None:
                        charge += sign * rule[1][0][3]
                        matches.append(dict(rule=index, edge=[a, b], sign=sign,
                                            amount=rule[1][0][3], images=im))
        extra = [m for m in matches if m['sign'] == 1 and m['rule'] >= 5]
        low = all(5 <= len(ns[w]) <= 6 for w in ns[v])
        if low:
            require(not any(m['sign'] == -1 for m in matches), 'Unexpected outgoing rule')
            require(all(m['rule'] < 13 for m in matches), 'Unexpected low-sender rule')
            require(charge == 10 * (6 - degree) + 4 * len(fives) + 2 * len(tips) + len(extra),
                    'Exact cyclic identity fails')
        return dict(vertex=v, degree=degree, fives=fives, tips=tips,
                    extra_matches=extra, charge=charge, low_neighbours=low)

    _, ns, pv, nx = spherical_geometry(fixture['faces'])
    bases = []
    for example in data['base_receivers']:
        result = observe(example['vertex'], ns, nx, pv)
        require(result['degree'] == example['degree'] and result['charge'] == example['charge'],
                'Base charge differs')
        require([len(result[key]) for key in ('fives', 'tips', 'extra_matches')] ==
                [example[key] for key in ('fives', 'tips', 'extras')], 'Base counts differ')
        bases.append(result)

    source = data['catalogue_candidate']
    raw = (here / source['file']).read_bytes()
    require(sha256(raw).hexdigest() == source['sha256'], 'Catalogue source differs')
    rows = [[int(x) for x in row.split()] for row in raw.decode().splitlines() if row.strip()]
    n, ring = rows[0]
    core = {row[0]: row[1:] for row in rows[1:]}
    require(n - ring == source['core_vertices'] and ring == source['ring_size'],
            'Catalogue dimensions differ')
    adjacency = {v: set() for v in range(1, n + 1)}
    for a, (_, *vs) in core.items():
        for b in vs:
            adjacency[a].add(b)
            adjacency[b].add(a)
    for a in range(1, ring + 1):
        b = a % ring + 1
        adjacency[a].add(b)
        adjacency[b].add(a)
    pattern = [[n, 14, 15, 0]]
    for a in range(1, n + 1):
        if a in core:
            degree, *vs = core[a]
            pattern.append([a, degree, degree, *vs])
        else:
            pattern.append([a, 0, 0, *[x for b in sorted(adjacency[a]) for x in (b, -1)]])
    candidate = (source['file'], pattern, compile_traces(pattern))
    residuals = []
    for example in data['residuals']:
        faces = [list(f) for f in fixture['faces']]
        for u, v, x, y in example['flips']:
            ds, ns, _, _ = spherical_geometry(faces)
            i, a = ds[u, v]
            j, b = ds[v, u]
            require([a, b] == [x, y] and y not in ns[x], 'Invalid flip')
            faces[i], faces[j] = [x, y, v], [y, x, u]
        _, ns, pv, nx = spherical_geometry(faces)
        require(min(map(len, ns.values())) >= 5, 'Minimum degree differs')
        u, v = data['fan_root']
        cycle = [v]
        while (w := nx[u, cycle[-1]]) != v:
            require(w not in cycle, 'Fan fails to close')
            cycle.append(w)
        require(cycle == data['fan_cycle'], 'Shared fan differs')
        require([len(ns[w]) for w in cycle] == [7, 5, 5, 7, 6, 5], 'Fan degrees differ')
        for index in (2, 4):
            require(checked(rules[index], u, v, ns, nx, pv) is not None, 'Source rule absent')
        observations = [observe(v, ns, nx, pv) for v in example['centres']]
        require([r['charge'] for r in observations] == example['charges'], 'Flatness differs')
        result = observations[1]
        require(result['low_neighbours'] and result['fives'] == [95], 'Residual differs')
        require([len(result[key]) for key in ('fives', 'tips', 'extra_matches')] ==
                [example[key] for key in ('fives', 'tips', 'extras')], 'Residual counts differ')
        marked_absent = not any(m['rule'] == 5 and m['edge'] == [95, 143]
                                for m in result['extra_matches'])
        require(marked_absent == example['marked_rule_absent'], 'Marked exclusion differs')
        # Check the complete source graph, all prescribed core rotations and the induced core.
        hits = []
        for reversed_order, (nexts, prevs) in enumerate(((nx, pv), (pv, nx))):
            im = checked(candidate, 143, 95, ns, nexts, prevs)
            if im is None:
                continue
            require(len(set(im)) == n, 'Source vertices collide')
            require(all((b in adjacency[a]) == (im[b - 1] in ns[im[a - 1]])
                        for a in core for b in core), 'Extra core edge')
            hits.append(dict(reversed_order=bool(reversed_order), images=im))
        require(hits, 'Wheel candidate absent')
        residuals.append(dict(name=example['name'], observations=observations,
                              marked_rule_absent=marked_absent, candidate_occurrences=hits))

    lean = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor'
    report = dict(rule_revision=revision, fixture_sha256=data['fixture_sha256'],
                  manifest_sha256=sha256(manifest.read_bytes()).hexdigest(),
                  verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                  lean_source_sha256={name: sha256((lean / (name + '.lean')).read_bytes()).hexdigest()
                                      for name in ('ExactCyclicCharge', 'ExactFanResidual',
                                                   'ExactChargeExample')},
                  base_receivers=bases, residuals=residuals, catalogue_candidate=source,
                  independent_readings=checks, disagreements=0,
                  scope='Exact program evidence. Lean base instances give 2+E and 8+E; '
                        'their numerical E values are program checked. '
                        'Modified spherical graphs and D3009 source occurrences are program checked. '
                        'No D3009 repair certificate, minimality or universal coverage claim.')
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(dict(base_charges=[r['charge'] for r in bases],
                          residual_budgets=[(r['name'], len(r['observations'][1]['tips']),
                                             len(r['observations'][1]['extra_matches']))
                                            for r in residuals],
                          comparisons=checks, disagreements=0)))


if __name__ == '__main__':
    main()
