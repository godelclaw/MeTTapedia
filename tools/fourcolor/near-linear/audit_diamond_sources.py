#!/usr/bin/env python3
"""Verify the two vendored inputs and the Lean decoder's literal source data.

This checks source fidelity, not reducibility. The corresponding Lean audit
checks embedded graph transport, colouring reconstruction and shared repair.
"""

import argparse
from hashlib import sha256
import json
from pathlib import Path
import re


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_rows(source):
    result = []
    for line in source.splitlines():
        tokens = line.split()
        if not tokens:
            continue
        require(all(re.fullmatch(r'[0-9]+', token) for token in tokens),
                'Non-natural token in configuration input')
        result.append([int(token) for token in tokens])
    return result


def validate(rows):
    require(len(rows[0]) == 2, 'Expected vertex count and ring size')
    count, ring = rows[0]
    require(3 <= ring <= count, 'Invalid ring size')
    require(len(rows) == count - ring + 1, 'Missing or additional core row')
    adjacency = {}
    for expected, row in zip(range(ring + 1, count + 1), rows[1:]):
        require(len(row) >= 2, 'Missing row header')
        vertex, degree, *neighbors = row
        require(vertex == expected, 'Incorrect internal vertex label')
        require(degree == len(neighbors) == len(set(neighbors)), 'Incorrect degree or repeated neighbor')
        require(all(1 <= w <= count and w != vertex for w in neighbors), 'Invalid neighbor')
        adjacency[vertex] = neighbors
    for v, neighbors in adjacency.items():
        require(all(v in adjacency[w] for w in neighbors if w > ring), 'Nonreciprocal core edge')
    edges = {tuple(sorted((v, v % ring + 1))) for v in range(1, ring + 1)}
    edges.update(tuple(sorted((v, w))) for v, neighbors in adjacency.items() for w in neighbors)
    return {'vertices': count, 'ring': ring, 'core_vertices': count - ring,
            'edges': len(edges), 'prescribed_core_degrees': [row[1] for row in rows[1:]]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    repo = here.parents[2]
    manifest = json.loads((here / 'sources.json').read_text())
    for name, pin in manifest['files'].items():
        require(sha256((here / name).read_bytes()).hexdigest() == pin['sha256'],
                f'Source hash differs: {name}')
    module = repo / 'lean/fourcolor-classical/MettapediaFourColor/NearLinearDiamondData.lean'
    lean = module.read_text()
    entries = []
    for index in ['0000', '0001']:
        match = re.search(r'def input' + index + r' : Input (\d+) (\d+) where\s+source := ("[^\n]+")', lean)
        require(match is not None, f'Missing literal input{index}')
        lean_source = json.loads(match.group(3))
        source = (here / f'D{index}.conf').read_text()
        rows = read_rows(source)
        require(rows == read_rows(lean_source), f'Lean source rows differ: D{index}')
        require(rows[0] == [int(match.group(1)), int(match.group(2))], 'Lean input type differs')
        entries.append({'configuration': f'D{index}', **validate(rows)})
    result = {
        'evidence': 'Independent source-fidelity check; reducibility is checked separately in Lean.',
        'repository': manifest['repository'],
        'revision': manifest['revision'],
        'source_files_verified': len(manifest['files']),
        'configuration_source_rows_verified': len(entries),
        'entries': entries,
        'lean_source_sha256': sha256(module.read_bytes()).hexdigest(),
        'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
