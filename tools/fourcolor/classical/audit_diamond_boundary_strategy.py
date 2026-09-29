#!/usr/bin/env python3
"""Independently replay the ten joint-boundary repair steps and their witnesses.

The Lean proofs check the matching covers and actual graph colourings. This
program reads those same small patterns, independently enumerates chromograms
and full graph colourings, and records the strategy's dependency depth. It does
not read an original reducibility certificate or run its checker.
"""

import argparse
from hashlib import sha256
import json
from pathlib import Path
import re

from diamond_coloring_alternatives import colorings, proper, support
from probe_diamond_joint_repair import (
    GEOMETRY, GEOMETRY_SHA256, ROOT, contract_support, literal_graph,
)
from probe_diamond_kempe import PERMS, apply_perm, system

if not __debug__:
    raise SystemExit('Run without Python optimization: assertions are audit checks.')


def code(source, name):
    raw = re.search(r'def ' + name + r' : String :=\s*"([^"]+)"', source)[1]
    return re.sub(r'\\\n\s*', '', raw).split(' ')


def word(text):
    return tuple(map(int, text))


def replay():
    package = Path('lean/fourcolor-classical/MettapediaFourColor')
    paths = [GEOMETRY, package/'KempeAnswerComposition.lean',
             package/'DiamondBoundaryRepair.lean', package/'DiamondJointRepair.lean']
    source = {p.name: (ROOT/p).read_text() for p in paths}
    assert sha256((ROOT/GEOMETRY).read_bytes()).hexdigest() == GEOMETRY_SHA256
    rule = source['DiamondBoundaryRepair.lean']
    terminal = list(map(word, code(rule, 'terminalCodes')))
    starts = set(map(word, code(rule, 'startCodes')))
    witnesses = list(map(word, code(source['DiamondJointRepair.lean'], 'coloringCodes')))
    assert len(terminal) == len(set(terminal)) == len(witnesses) == 23
    adjacency, boundary = literal_graph(source[GEOMETRY.name], 4)
    for trace, colors in zip(terminal, witnesses):
        assert len(colors) == 12 and proper(adjacency, dict(enumerate(colors)))
        assert support(list(range(12)), [colors], boundary) == {trace}

    universe, grams = system(8)
    by_word = {t: [] for t in universe}
    for gram, matches in grams:
        for t in matches:
            by_word[t].append((gram, matches))
    rank = {t: 0 for t in terminal}
    records = []
    blocks = re.findall(r'private theorem repair_([123]{8})(.*?)(?=\nprivate theorem|\nset_option)',
                        rule, re.S)
    assert len(blocks) == 10
    for text, body in blocks:
        t = word(text)
        permutation = word(re.search(r'apply kempeCoclosure_of_map \.e([123]+)', body)[1])
        answers = list(map(word, re.search(r'of_answers \(words "([123 ]+)"\)', body)[1].split()))
        targets = re.findall(r'  · apply kempeCoclosure_of_map \.e([123]+)\n'
                             r'    change KempeCoclosure P \(decode "([123]+)"\)', body)
        assert len(answers) == len(targets)
        oriented = apply_perm(t, permutation)
        assert by_word[oriented]
        for gram, matches in by_word[oriented]:
            assert set(answers) & matches, (text, gram)
        reasons = []
        for answer, (perm, target) in zip(answers, targets):
            target = word(target)
            assert apply_perm(answer, word(perm)) == target
            assert target in rank, (text, target)
            reasons.append(rank[target])
        rank[t] = 1 + max(reasons)
        records.append(dict(trace=text, permutation=''.join(map(str, permutation)),
                            chromograms=len(by_word[oriented]), depth=rank[t],
                            answers=[''.join(map(str, a)) for a in answers],
                            targets=[t for _, t in targets]))
    assert starts <= rank.keys() and max(rank.values()) == 5
    joint = contract_support(adjacency, boundary, [(4, 10), (10, 6), (0, 8), (8, 2)])
    normalized = {min(apply_perm(t, p) for p in PERMS) for t in joint}
    assert normalized == starts and len(joint) == 108 and len(starts) == 18
    vertices, values = colorings(adjacency)
    ordinary = support(vertices, values, boundary)
    assert set(terminal) <= ordinary
    assert len(starts & ordinary) == 12
    # Removing the cross-insertion inequality admits this unhandled trace.
    assert (1,)*8 not in joint and (1,)*8 not in rank
    replay_sources = [*paths, Path(__file__).resolve().relative_to(ROOT),
                      Path('tools/fourcolor/classical/probe_diamond_kempe.py'),
                      Path('tools/fourcolor/classical/probe_diamond_joint_repair.py'),
                      Path('tools/fourcolor/classical/diamond_coloring_alternatives.py')]
    return dict(
        evidence='Independent program replay; theorem validity is checked separately by Lean.',
        source_sha256={str(p): sha256((ROOT/p).read_bytes()).hexdigest() for p in replay_sources},
        terminal_graph_witnesses=len(terminal), normalized_joint_starts=len(starts),
        joint_traces=len(joint), directly_realized_start_types=len(starts & ordinary),
        repair_steps=len(records), longest_dependency_chain=max(rank.values()),
        strategy=records,
        scope='One coupled eight-port boundary law; no claim that longer fans obey the same contract.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.suffix != '.json':
        raise SystemExit('The output must be a JSON report.')
    result = replay()
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('terminal_graph_witnesses',
        'normalized_joint_starts', 'joint_traces', 'repair_steps', 'longest_dependency_chain')}))


if __name__ == '__main__':
    main()
