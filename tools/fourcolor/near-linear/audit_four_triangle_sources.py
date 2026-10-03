#!/usr/bin/env python3
"""Check both source cores used by the common four-triangle geometry theorem."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import re

from audit_diamond_sources import read_rows, require, validate


def verify(here):
    manifest = json.loads((here / 'four-triangle-sources.json').read_text())
    for name, pin in manifest['files'].items():
        require(sha256((here / name).read_bytes()).hexdigest() == pin['sha256'],
                f'Source hash differs: {name}')
    module = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor/FourTriangleCore.lean'
    text = module.read_text().split('def source : Fin 2 → String := ![', 1)[1].split('def input', 1)[0]
    literals = [json.loads(s) for s in re.findall(r'"(?:[^"\\]|\\.)*"', text)]
    require(len(literals) == 2, 'Expected both source literals')
    entries = []
    for filename, literal in zip(['D0051.conf', 'D0052.conf'], literals):
        rows = read_rows((here / filename).read_text())
        require(rows == read_rows(literal), f'Lean source differs: {filename}')
        require(rows[0] == [16, 10], 'Wrong source dimensions')
        entries.append({'configuration': filename[:-5], **validate(rows)})
    return {'evidence': 'Independent source-fidelity check; core geometry certified separately in Lean.',
            'repository': manifest['repository'], 'revision': manifest['revision'], 'entries': entries,
            'lean_source_sha256': sha256(module.read_bytes()).hexdigest(),
            'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
            'shared_parser_sha256': sha256((here / 'audit_diamond_sources.py').read_bytes()).hexdigest()}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path)
    args = p.parse_args()
    result = verify(Path(__file__).resolve().parent)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
