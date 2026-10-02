#!/usr/bin/env python3
"""Replay the extra-rule reductions and their jointly flat discovery example."""

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
    manifest = here / 'extra-charge-examples.json'
    data = json.loads(manifest.read_text())
    raw = (here / data['fixture']).read_bytes()
    require(sha256(raw).hexdigest() == data['fixture_sha256'], 'Fixture differs')
    fixture = json.loads(raw)
    rules, revision = read_rules(here)
    require(revision == fixture['rule_revision'], 'Rule revision differs')
    require(rules[5][0] == data['rule_file'], 'Rule index differs')
    _, ns, prev, nxt = geometry(fixture['faces'])

    def checked(index, a, b, neighbors, nexts, prevs):
        im = reading(rules[index], a, b, neighbors, nexts, prevs)
        require(im == breadth_first_reading(rules[index][1], a, b, neighbors, nexts, prevs),
                'Independent rule readings disagree')
        return im

    examples = []
    for e in data['examples']:
        u, v = e['root']
        im = checked(5, u, v, ns, nxt, prev)
        require(im == e['images'], 'Source image differs')
        p = nxt[u, nxt[u, v]]
        require(p == e['companion'], 'Closing companion differs')
        require(len(ns[u]) == len(ns[p]) == 5 and len(ns[im[2]]) == 6, 'Degree guards differ')
        outer = im[3]
        require(len(ns[outer]) == e['outer_degree'], 'Outer degree differs')
        word = [im[4]]
        for _ in range(3):
            word.append(nxt[outer, word[-1]])
        require(word == [im[4], im[2], im[0], p], 'Shared triangle closure differs')
        require([len(ns[x]) for x in word] == [5, 6, 5, 5], 'Reduction word differs')
        examples.append(dict(**e, outer_neighbour_word=word))

    joint = data['joint_flat_example']
    faces = [list(f) for f in fixture['faces']]
    for u, v, x, y in joint['flips']:
        ds, ns, _, _ = geometry(faces)
        i, a = ds[u, v]
        j, b = ds[v, u]
        require([a, b] == [x, y] and y not in ns[x], 'Invalid flip')
        faces[i], faces[j] = [x, y, v], [y, x, u]
    _, ns, prev, nxt = geometry(faces)
    require(min(map(len, ns.values())) >= 5, 'Minimum degree differs')
    u, v = joint['fan_root']
    cycle = [v]
    while (w := nxt[u, cycle[-1]]) != v:
        require(w not in cycle, 'Fan fails to close')
        cycle.append(w)
    require(cycle == joint['fan_cycle'], 'Fan differs')
    require([len(ns[w]) for w in cycle] == [7, 5, 5, 7, 6, 5], 'Fan degrees differ')
    for index in (2, 4):
        require(checked(index, u, v, ns, nxt, prev) is not None, 'Initial source rule absent')
    source = checked(5, *joint['extra_rule_root'], ns, nxt, prev)
    require(source == joint['extra_rule_images'], 'Extra source rule differs')
    outer, tip = joint['chain_root']
    word = [tip]
    for _ in range(3):
        word.append(nxt[outer, word[-1]])
    require(word == joint['chain_vertices'], 'Joint example chain differs')
    require(len(ns[outer]) == 6 and [len(ns[w]) for w in word] == [5, 6, 5, 5],
            'Joint example reduction guards differ')
    observations, checks = [], 5
    for v, expected in zip(joint['centres'], joint['charges']):
        charge = 10 * (6 - len(ns[v]))
        transfers = []
        for w in sorted(ns[v]):
            for a, b, sign in ((w, v, 1), (v, w, -1)):
                hits = []
                for index in range(84):
                    im = checked(index, a, b, ns, nxt, prev)
                    checks += 1
                    if im is not None:
                        hits.append([index, rules[index][1][0][3], im])
                total = sum(hit[1] for hit in hits)
                charge += sign * total
                transfers.append(dict(edge=[a, b], amount=total, rules=hits))
        require(charge == expected, 'Joint flat charge differs')
        observations.append(dict(vertex=v, charge=charge, transfers=transfers))
    lean = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor'
    report = dict(rule_revision=revision, source_manifest='discharging-sources.json',
                  fixture_sha256=data['fixture_sha256'],
                  manifest_sha256=sha256(manifest.read_bytes()).hexdigest(),
                  verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                  lean_source_sha256={n: sha256((lean / (n + '.lean')).read_bytes()).hexdigest()
                                      for n in ('ExtraChargeReduction', 'ExtraChargeExample')},
                  examples=examples, joint_flat_example=observations,
                  independent_rule_comparisons=checks, disagreements=0,
                  scope='Exact program evidence. Two base examples also consume the Lean closure. '
                        'Joint flatness and the modified spherical example are program checked; '
                        'no minimal-counterexample or universal coverage claim.')
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(dict(examples=len(examples), comparisons=checks, disagreements=0,
                          joint_charges=[x['charge'] for x in observations])))


if __name__ == '__main__':
    main()
