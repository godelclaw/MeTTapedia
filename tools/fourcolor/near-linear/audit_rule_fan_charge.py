#!/usr/bin/env python3
"""Replay the fan-charge example and check all signed incident rule matches.

The Lean consumer proves the charge lower bound by the general facial-fan
law. This independent program check also computes the exact final charge.
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
    fixture = here / 'rule-fan-charge-example.json'
    raw = fixture.read_bytes()
    example = json.loads(raw)
    base_raw = (here / example['base_fixture']).read_bytes()
    require(sha256(base_raw).hexdigest() == example['base_sha256'], 'Base fixture differs')
    base = json.loads(base_raw)
    faces = [list(face) for face in base['faces']]
    # Replay each flip in the actual oriented triangulation. Geometry checks
    # distinct triangle endpoints, opposite edge occurrences and Euler's law.
    for a, b, c, d in example['extra_flips']:
        darts, neighbors, _, _ = geometry(faces)
        i, old_c = darts[a, b]
        j, old_d = darts[b, a]
        require((c, d) == (old_c, old_d), 'Flipped triangle differs')
        require(d not in neighbors[c], 'Flip would duplicate an edge')
        faces[i], faces[j] = [c, d, b], [d, c, a]
    darts, neighbors, forward, reverse = geometry(faces)
    require(len(neighbors) == example['vertices'], 'Vertex count differs')
    require(min(map(len, neighbors.values())) >= 5, 'Minimum degree differs')
    rules, revision = read_rules(here)
    require(revision == base['rule_revision'], 'Pinned rule revision differs')
    nexts, prevs = reverse, forward  # The exact orientation of the Lean example.
    u, v = example['root']
    require((u, v) in darts and len(neighbors[u]) == 6, 'Root or sender differs')
    require(len(neighbors[v]) == 7, 'Receiver is not seven-valent')
    require(all(5 <= len(neighbors[w]) <= 6 for w in neighbors[v]), 'Receiver has a high neighbour')
    cycle = [v]
    for _ in range(5):
        cycle.append(nexts[u, cycle[-1]])
    require(nexts[u, cycle[-1]] == v and len(set(cycle)) == 6, 'Sender star does not close')
    require(all(len(neighbors[cycle[i]]) == 5 for i in (1, 2, 4, 5)), 'Four wings differ')
    first = prevs[v, prevs[v, u]]
    window = [first]
    for _ in range(4):
        window.append(nexts[v, window[-1]])
    require(window == example['window'] and len(set(window)) == 5, 'Five senders differ')
    checks = 0
    transfers = {}
    observations = []
    for w in sorted(neighbors[v]):
        for a, b in ((w, v), (v, w)):
            matches = []
            for i, rule in enumerate(rules):
                compiled = reading(rule, a, b, neighbors, nexts, prevs)
                propagated = breadth_first_reading(rule[1], a, b, neighbors, nexts, prevs)
                require(compiled == propagated, 'Independent matchers disagree')
                checks += 1
                if compiled is not None:
                    matches.append(dict(index=i, images=compiled, amount=rule[1][0][3]))
            transfers[a, b] = sum(m['amount'] for m in matches)
            observations.append(dict(edge=[a, b], sent=transfers[a, b], matches=matches))
    incoming = [transfers[w, v] for w in window]
    require(incoming == example['window_incoming'], 'Incoming amounts differ')
    require(all(transfers[v, w] == 0 for w in neighbors[v]), 'Reverse charge is nonzero')
    charge = -10 + sum(transfers[w, v] - transfers[v, w] for w in neighbors[v])
    require(charge == example['receiver_charge'] and charge >= 2, 'Charge differs')
    # Check the modified rows against the small overrides consumed by Lean.
    lean = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor/RuleFanChargeExample.lean'
    source = lean.read_text()
    for w in sorted(set(sum(example['extra_flips'], []))):
        row = [min(neighbors[w])]
        while (nxt := nexts[w, row[-1]]) != row[0]:
            require(nxt not in row, 'Noncyclic star')
            row.append(nxt)
        require(f'| {w} => "' + ' '.join(map(str, row)) + '\\n"' in source,
                'Lean override differs from the replayed rotation')
    report = dict(evidence='Independent exact program check; positive lower bound separately kernel checked.',
                  fixture=fixture.name, fixture_sha256=sha256(raw).hexdigest(),
                  base_sha256=example['base_sha256'], rule_revision=revision,
                  extra_flips=example['extra_flips'], vertices=len(neighbors), sender_cycle=cycle,
                  window=window, incoming=incoming, final_charge=charge,
                  independent_rule_checks=checks, disagreements=0, observations=observations,
                  lean_example_sha256=sha256(lean.read_bytes()).hexdigest(),
                  verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                  scope='Finite positive-charge example; no minimal-counterexample or universal-coverage claim.')
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(dict(vertices=len(neighbors), final_charge=charge,
                         independent_rule_checks=checks, disagreements=0)))


if __name__ == '__main__':
    main()
