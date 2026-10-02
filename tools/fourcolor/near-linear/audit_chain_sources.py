#!/usr/bin/env python3
"""Check pinned source rows consumed by the three-triangle chain transfer."""
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
    manifest = json.loads((here / 'chain-sources.json').read_text())
    for name, pin in manifest['files'].items():
        require(sha256((here / name).read_bytes()).hexdigest() == pin['sha256'],
                f'Source hash differs: {name}')
    module = repo / 'lean/fourcolor-classical/MettapediaFourColor/NearLinearChainData.lean'
    lean = module.read_text()
    entries = []
    for filename in manifest['files']:
        if not filename.endswith('.conf'):
            continue
        index = filename[1:5]
        match = re.search(r'def input' + index + r' : Input (\d+) (\d+) where\s+source := ("[^\n]+")', lean)
        require(match is not None, f'Missing literal input{index}')
        source = read_rows((here / filename).read_text())
        require(source == read_rows(json.loads(match.group(3))), f'Source rows differ: {filename}')
        require(source[0] == [int(match.group(1)), int(match.group(2))], 'Input type differs')
        entries.append({'configuration': filename[:-5], **validate(source)})
    result = {
        'evidence': 'Independent source-fidelity check. Lean checks geometry and repair separately.',
        'repository': manifest['repository'], 'revision': manifest['revision'],
        'entries': entries, 'lean_source_sha256': sha256(module.read_bytes()).hexdigest(),
        'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
        'shared_parser_sha256': sha256((here / 'audit_diamond_sources.py').read_bytes()).hexdigest(),
    }
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
