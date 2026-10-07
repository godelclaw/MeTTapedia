#!/usr/bin/env python3
"""Check the observed-strategy models and audit their theorem dependencies."""

from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    local = Path(__file__).resolve().parent
    canonical = local.parent / 'mettapedia'
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    lib = output / 'lib'
    paths = [lib, canonical / '.lake/build/lib/lean']
    paths += sorted(path for path in
                    (canonical / '.lake/packages').glob('*/.lake/build/lib/lean')
                    if path.is_dir())
    env = dict(os.environ, LEAN_PATH=':'.join(map(str, paths)), LEAN_NUM_THREADS='1')
    toolchain = (canonical / 'lean-toolchain').read_text().strip()
    manifest = hashlib.sha256((canonical / 'lake-manifest.json').read_bytes()).hexdigest()
    results = []
    built = {}

    def source_for(module):
        relative = Path(module.replace('.', '/') + '.lean')
        for root in [local, canonical]:
            if (root / relative).is_file():
                return root / relative
        return None

    def run(label, source, target=None):
        command = ['nice', '-n', '19', 'lean', '+' + toolchain, '-j', '1']
        if target:
            target.parent.mkdir(parents=True, exist_ok=True)
            command += ['-o', str(target)]
        command.append(str(source))
        working = local if source.is_relative_to(local) else canonical
        result = subprocess.run(command, cwd=working, env=env,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                text=True)
        (output / (label.replace('.', '_') + '.log')).write_text(result.stdout)
        return result

    def build(module):
        if module in built:
            return built[module]
        source = source_for(module)
        if source is None:
            return ''  # toolchain or an existing Lake dependency
        dependencies = []
        for line in re.findall(r'^import\s+(.+)$', source.read_text(), re.M):
            for dependency in line.split():
                dependencies.append((dependency, build(dependency)))
        digest = hashlib.sha256(source.read_bytes()).hexdigest()
        fingerprint = hashlib.sha256(json.dumps(
            [toolchain, manifest, digest, dependencies]).encode()).hexdigest()
        target = lib / (module.replace('.', '/') + '.olean')
        stamp = target.with_suffix('.fingerprint')
        if target.exists() and stamp.exists() and stamp.read_text() == fingerprint:
            result = dict(module=module, returncode=0, cached=True, source_sha256=digest)
        else:
            checked = run(module, source, target)
            result = dict(module=module, returncode=checked.returncode, source_sha256=digest)
            if checked.returncode:
                print(checked.stdout[:24000], flush=True)
                results.append(result)
                raise RuntimeError('Lean check failed: ' + module)
            stamp.write_text(fingerprint)
        results.append(result)
        print(json.dumps(result), flush=True)
        built[module] = fingerprint
        return fingerprint

    targets = ['ObservedStrategyChecks', 'IterAuthoring', 'WeakAgentEcology']
    try:
        for module in targets:
            build(module)
        modules = ['IterArchitecture', 'OmegaArchitecture', 'CodingAgent',
                   'Mettapedia.CognitiveArchitecture.Agent.ConversationContinuation',
                   'FeedbackSensitiveBatch', 'ObservedStrategy', 'ObservedStrategyChecks']
        names = []
        for module in modules:
            source = source_for(module)
            namespace = re.search(r'^namespace\s+(\S+)', source.read_text(), re.M).group(1)
            names += [namespace + '.' + name for name in
                      re.findall(r'^theorem\s+(\w+)', source.read_text(), re.M)]
        audit = output / 'StrategyAxiomAudit.lean'
        audit.write_text('import ObservedStrategyChecks\n\n' + '\n'.join(
            '#print axioms ' + name for name in names) + '\n')
        checked = run('axiom-audit', audit)
        audited = re.findall(r"'([^']+)' (?:depends on axioms|does not depend)", checked.stdout)
        used = set()
        for group in re.findall(r'depends on axioms: \[([^\]]*)\]', checked.stdout):
            used.update(word.strip() for word in group.split(',') if word.strip())
        unexpected = used - {'propext', 'Quot.sound', 'Classical.choice'}
        complete = set(audited) == set(names)
        audit_result = dict(check='axiom-audit', returncode=checked.returncode,
                            expected=len(names), audited=len(audited), complete=complete,
                            axioms=sorted(used), unexpected_axioms=sorted(unexpected))
        results.append(audit_result)
        print(json.dumps(audit_result), flush=True)
        if checked.returncode or unexpected or not complete:
            print(checked.stdout[:24000], flush=True)
            raise RuntimeError('Theorem audit failed')
    except RuntimeError as error:
        print(str(error), file=sys.stderr)
        (output / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
        return 1
    (output / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
    return 0


if __name__ == '__main__':
    sys.exit(main())
