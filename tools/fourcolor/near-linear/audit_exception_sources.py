#!/usr/bin/env python3
"""Verify the exceptional pattern and D1774 source data used by Lean.

This establishes source fidelity only. The Lean theorems separately establish
the forced corner and degree-preserving core reading in actual graph darts.
Neither this program nor a core reading certifies a complete occurrence.
"""

import argparse
from hashlib import sha256
import json
from pathlib import Path
import re

from audit_diamond_sources import read_rows, require, validate


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    repo = here.parents[2]
    manifest = json.loads((here / 'exception-sources.json').read_text())
    excerpt = here / manifest['computer_checks']['local_excerpt']
    require(sha256(excerpt.read_bytes()).hexdigest() ==
            manifest['computer_checks']['excerpt_sha256'], 'getX excerpt hash differs')
    raw = excerpt.read_text()
    rotation_block = re.search(r'17,\s*\{(\{.*?\})\},\s*\{Degree', raw, re.S)
    require(rotation_block is not None, 'Missing getX rotation block')
    rotations = [[int(s) for s in re.findall(r'-?\d+', row)]
                 for row in re.findall(r'\{([^{}]+)\}', rotation_block.group(1))]
    degrees = [int(s) for s in re.findall(r'Degree\((\d+)\)', raw)]
    require(len(rotations) == len(degrees) == 17, 'Wrong source vertex count')
    for i, row in enumerate(rotations):
        require(len(set(row)) == len(row), 'Duplicate source rotation entry')
        for j in row:
            require(-1 <= j < 17 and i != j, 'Invalid source neighbor')
            if j >= 0:
                require(i in rotations[j], 'Asymmetric source edge')

    modules = repo / 'lean/fourcolor-classical/MettapediaFourColor'
    pattern = modules / 'ExceptionalPattern.lean'
    encoded = re.search(r'def source : String := ("[^\n]+")', pattern.read_text())
    require(encoded is not None, 'Missing Lean exceptional source')
    expected = [degrees] + [[j + 1 for j in row] for row in rotations]
    require(read_rows(json.loads(encoded.group(1))) == expected,
            'Lean exceptional source differs, including gaps or cyclic order')

    source = here / manifest['configuration']['local_file']
    require(sha256(source.read_bytes()).hexdigest() == manifest['configuration']['sha256'],
            'D1774 hash differs')
    rows = read_rows(source.read_text())
    core_module = modules / 'ExceptionalCore.lean'
    literal = re.search(r'def input : Input (\d+) (\d+) where\s+source := ("[^\n]+")',
                        core_module.read_text())
    require(literal is not None, 'Missing Lean D1774 input')
    require(rows == read_rows(json.loads(literal.group(3))), 'Lean D1774 rows differ')
    require(rows[0] == [int(literal.group(1)), int(literal.group(2))], 'Input type differs')
    configuration = validate(rows)

    # The first seven core vertices are old source vertices; the eighth is
    # the new corner proved in Lean. Compare every core edge and degree.
    mapping = [14, 3, 16, 5, 13, 15, 4, 17]
    label_literal = re.search(r'def oldLabel.*? := !\[([^\]]+)\]', core_module.read_text())
    require(label_literal is not None, 'Missing Lean oldLabel')
    require([int(s) for s in re.findall(r'\d+', label_literal.group(1))] == mapping[:7],
            'Lean old-label correspondence differs')
    source_edges = {tuple(sorted((i, j))) for i, row in enumerate(rotations)
                    for j in row if j >= 0}
    expanded_edges = source_edges | {(14, 17), (15, 17)}
    selected = set(mapping)
    expected_core = {edge for edge in expanded_edges if set(edge) <= selected}
    actual_core = {tuple(sorted((mapping[i - 12], mapping[j - 12])))
                   for i, _, *neighbors in rows[1:] for j in neighbors if j >= 12}
    require(actual_core == expected_core, 'D1774 core adjacency differs')
    require([row[1] for row in rows[1:]] == [degrees[i] for i in mapping[:7]] + [5],
            'D1774 prescribed core degrees differ')
    result = {
        'evidence': 'Independent source-fidelity and finite core correspondence check; not reducibility.',
        'computer_checks_revision': manifest['computer_checks']['revision'],
        'configuration_revision': manifest['configuration']['revision'],
        'exception_vertices': 17,
        'exception_edges': len(source_edges),
        'configuration': {'name': 'D1774', **configuration},
        'core_edges': len(actual_core),
        'core_to_exception_labels': mapping,
        'new_corner_label': 17,
        'lean_source_sha256': {p.name: sha256(p.read_bytes()).hexdigest()
                               for p in [pattern, core_module]},
        'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
        'shared_parser_sha256': sha256((here / 'audit_diamond_sources.py').read_bytes()).hexdigest(),
        'remaining': ['collision and inducedness analysis',
                      'full cyclic boundary occurrence', 'colouring repair'],
    }
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
