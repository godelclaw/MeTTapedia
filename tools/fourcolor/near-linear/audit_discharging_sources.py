#!/usr/bin/env python3
"""Check the complete pinned oriented-rule data against the Lean decoding.

This is an independent source-fidelity check. The Lean kernel separately
proves the local-path facts and the consequences for actual charge.
"""

import argparse
from hashlib import sha256
import json
from pathlib import Path
import re


def require(condition, message):
    if not condition:
        raise ValueError(message)


def rows(text):
    return [[int(x) for x in line.split()]
            for line in text.splitlines() if line.strip()]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    repo = here.parents[2]
    manifest = json.loads((here / 'discharging-sources.json').read_text())
    module = repo / 'lean/fourcolor-classical/MettapediaFourColor/NearLinearRuleData.lean'
    expected_names = [f'rule{i:03d}{suffix}.rule' for i in range(1, 44)
                      for suffix in ([''] if i in (1, 40) else ['_1', '_2'])]
    require([x['file'] for x in manifest['files']] == expected_names,
            'The complete set of 84 oriented rules is required')
    require(sorted(p.name for p in (here / 'discharging-rules').glob('*.rule')) == expected_names,
            'Vendored file set differs')
    literals = re.findall(r'^  \| (\d+) => ("[^\n]+")$', module.read_text(), re.M)
    require([int(i) for i, _ in literals] == list(range(84)), 'Lean rule indices differ')
    vertices = 0
    for item, (_, literal) in zip(manifest['files'], literals):
        raw = (here / 'discharging-rules' / item['file']).read_bytes()
        require(sha256(raw).hexdigest() == item['sha256'], 'Source hash differs')
        data = rows(raw.decode())
        require(rows(json.loads(literal)) == [[0 if x == -1 else x for x in row]
                                               for row in data], 'Lean data differs')
        n, sender, receiver, amount = data[0]
        require(len(data) == n + 1 and 2 <= n <= 12 and amount > 0, 'Invalid header')
        require((sender, receiver) == (1, 2), 'Endpoint convention differs')
        by_vertex = {r[0]: r for r in data[1:]}
        require(list(by_vertex) == list(range(1, n + 1)), 'Wrong vertex rows')
        fives = []
        for v, lower, upper, *neighbors in data[1:]:
            require(5 <= lower and (upper == 0 or lower <= upper), 'Invalid degree bounds')
            require(len(set(neighbors)) == len(neighbors), 'Repeated cyclic entry')
            for w in neighbors:
                require(w == -1 or 1 <= w <= n, 'Invalid neighbor or gap')
                require(w != v, 'Loop')
                if w != -1:
                    require(v in by_vertex[w][3:], 'Asymmetric edge')
            if lower == upper == 5:
                fives.append(v)
        require(fives, 'Rule without a prescribed five')
        require(0 < by_vertex[sender][2] <= 8, 'Sender bound fails')
        for base in (sender, receiver):
            for v in by_vertex:
                if v == base or v in by_vertex[base][3:]:
                    continue
                require(any(w != -1 and 0 < by_vertex[w][2] <= 8 and
                            v in by_vertex[w][3:] for w in by_vertex[base][3:]),
                        'An observation has no bounded two-step path')
        vertices += n
    report = {
        'evidence': 'Independent complete source-fidelity check; Lean certifies the mathematics.',
        'repository': manifest['repository'], 'revision': manifest['revision'],
        'oriented_rules': 84, 'underlying_rules': 43, 'vertex_rows': vertices,
        'all_rules_have_five': True, 'maximum_sender_degree': 8,
        'all_observations_have_bounded_radius_two_paths_from_both_endpoints': True,
        'lean_source_sha256': sha256(module.read_bytes()).hexdigest(),
        'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
        'scope': 'No cartwheel enumeration, unavoidability or runtime is certified by this program.'}
    if args.output:
        args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
