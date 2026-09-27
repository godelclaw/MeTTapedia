"""Test whether subdivision-generated supports suffice for diamond contracts.

The finite closure uses every balanced chromogram and all six permutations
of the nonzero colours. Saved disjoint closed sets carry a chromogram for
each trace and are checked again after serialization. These are abstract
Kempe-closed predicates, not asserted to be realizable planar exteriors.
"""

import argparse
from copy import deepcopy
from functools import reduce
from hashlib import sha256
from itertools import permutations, product
import json
from operator import xor
from pathlib import Path
import time

from probe_diamond_star import INPUT_HASHES, attach, full_support, orient
from probe_common_support import close_colors, parity, read_input

if not __debug__:
    raise SystemExit('Run without Python optimization: assertions are audit checks.')

PERMS = tuple(permutations((1, 2, 3)))


def apply_perm(word, perm):
    return tuple(perm[c - 1] for c in word)


def grammar(n):
    """Balanced words, with the exact skip/pop1 parity from Chromogram.lean."""
    def visit(left, depth, odd, prefix):
        if left == 0:
            if depth == 0 and not odd:
                yield prefix
            return
        if depth < left:
            yield from visit(left - 1, depth, not odd, prefix + 's')
            yield from visit(left - 1, depth + 1, odd, prefix + '[')
        if depth:
            yield from visit(left - 1, depth - 1, odd, prefix + '0')
            yield from visit(left - 1, depth - 1, not odd, prefix + '1')
    return list(visit(n, 0, False, ''))


def matches(gram):
    """Generate all matches by choosing the colour of each opening chord."""
    current = [((), ())]
    for symbol in gram:
        next_states = []
        for word, stack in current:
            if symbol == 's':
                next_states.append((word + (1,), stack))
            elif symbol == '[':
                for color in (2, 3):
                    next_states.append((word + (color,), stack + (color,)))
            else:
                assert stack
                color = stack[-1] if symbol == '0' else 5 - stack[-1]
                next_states.append((word + (color,), stack[:-1]))
        current = next_states
    assert all(not stack for _, stack in current)
    return frozenset(word for word, _ in current)


def matchg(word, gram):
    """Independent deterministic mirror of the reference's Boolean matcher."""
    if len(word) != len(gram):
        return False
    stack = []
    for color, symbol in zip(word, gram):
        if symbol == 's':
            if color != 1:
                return False
        elif symbol == '[':
            if color not in (2, 3):
                return False
            stack.insert(0, color == 3)
        elif symbol in ('0', '1'):
            if color not in (2, 3) or not stack:
                return False
            want = (color == 3) ^ (symbol == '1')
            if stack.pop(0) != want:
                return False
        else:
            return False
    return not stack


def system(n):
    assert 6 <= n <= 8
    all_words = tuple(product((1, 2, 3), repeat=n))
    universe = frozenset(w for w in all_words if reduce(xor, w, 0) == 0)
    grams = [(w, matches(w)) for w in grammar(n)]
    assert all(words and words <= universe for _, words in grams)
    # Exhaustively compare independent generation and deterministic matching.
    for gram, words in grams:
        assert words == {word for word in all_words if matchg(word, gram)}
    return universe, grams


def closure(universe, grams, good):
    bad = universe - good
    sizes = [len(bad)]
    while True:
        retained = set()
        for _, words in grams:
            if words <= bad:
                retained.update(words)
        nxt = frozenset(word for word in retained
                        if all(apply_perm(word, p) in retained for p in PERMS))
        assert nxt <= bad
        if nxt == bad:
            break
        bad = nxt
        sizes.append(len(bad))
    witnesses = {}
    for gram, words in grams:
        if words <= bad:
            for word in words:
                witnesses.setdefault(word, gram)
    assert set(witnesses) == bad
    return bad, sizes, witnesses


def verify_closed(universe, bad, witnesses, forbidden):
    assert bad <= universe and bad.isdisjoint(forbidden)
    assert set(witnesses) == bad
    for word in bad:
        assert all(apply_perm(word, p) in bad for p in PERMS)
        gram = witnesses[word]
        assert matchg(word, gram)
        assert all(other in bad for other in universe if matchg(other, gram))


def check_saved(systems, entry):
    universe, _ = systems[entry['ring']]
    bad = frozenset(tuple(row['word']) for row in entry['closed'])
    witnesses = {tuple(row['word']): row['gram'] for row in entry['closed']}
    assert len(witnesses) == len(entry['closed'])
    forbidden = frozenset(map(tuple, entry['forbidden']))
    verify_closed(universe, bad, witnesses, forbidden)


def negative_controls(systems, entry):
    if not entry['closed']:
        return 0
    wrong_gram = deepcopy(entry)
    wrong_gram['closed'][0]['gram'] = ''
    duplicate = deepcopy(entry)
    duplicate['closed'].append(deepcopy(duplicate['closed'][0]))
    bad_disjointness = deepcopy(entry)
    bad_disjointness['closed'].append(dict(word=entry['forbidden'][0], gram=''))
    for bad in (wrong_gram, duplicate, bad_disjointness):
        try:
            check_saved(systems, bad)
        except AssertionError:
            continue
        raise AssertionError('Corrupted closed-set witness was accepted')
    return 3


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--inputs', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--witnesses', type=Path, required=True)
    args = parser.parse_args()
    outputs = {args.output.resolve(), args.witnesses.resolve()}
    assert len(outputs) == 2
    assert not outputs & {(args.inputs / f'{i-1}.in').resolve() for i in INPUT_HASHES}
    start = time.monotonic()
    supports, contracts = {}, {}
    reports, saved = [], []
    for ordinal in INPUT_HASHES:
        path = args.inputs / f'{ordinal - 1}.in'
        n, good, digest = full_support(path)
        assert digest == INPUT_HASHES[ordinal]
        _, _, ctr, _ = read_input(path)
        supports[ordinal] = good
        contracts[ordinal] = {tuple(map(int, parity(w) + w)) for w in close_colors(ctr)}
    systems = {n: system(n) for n in (6, 7, 8)}
    candidates = [('original', i, supports[i]) for i in INPUT_HASHES]
    source = supports[1]
    for left, right, port, rotation in [(1, 2, 2, 5), (2, 4, 4, 0)]:
        seed = attach(source, port) & orient(supports[right], rotation, False)
        seed = orient(seed, len(next(iter(seed))) - rotation, False)
        assert seed <= supports[right]
        candidates.append(('chosen_subdivision_chain', right, seed))
        source = seed
    for kind, ordinal, good in candidates:
        n = len(next(iter(good)))
        universe, grams = systems[n]
        bad, sizes, witnesses = closure(universe, grams, good)
        verify_closed(universe, bad, witnesses, good)
        report = dict(kind=kind, ordinal=ordinal, ring=n, proper=len(universe),
                      balanced_chromograms=len(grams), good=len(good),
                      fixed_point_sizes=sizes, closed_obstruction=len(bad),
                      contract=len(contracts[ordinal]),
                      blocked_contract=len(bad & contracts[ordinal]),
                      blocked_contract_witness=list(min(bad & contracts[ordinal]))
                      if bad & contracts[ordinal] else None)
        reports.append(report)
        saved.append(dict(kind=kind, ordinal=ordinal, ring=n,
                          forbidden=[list(w) for w in sorted(good)],
                          closed=[dict(word=list(w), gram=witnesses[w]) for w in sorted(bad)]))
    args.witnesses.write_text(json.dumps(saved, indent=2) + '\n')
    reread = json.loads(args.witnesses.read_text())
    rejected = 0
    for entry in reread:
        check_saved(systems, entry)
        rejected += negative_controls(systems, entry)
    output = dict(evidence='Finite program evidence; no Lean or actual-exterior claim.',
                  source_hashes=INPUT_HASHES,
                  script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                  witnesses_sha256=sha256(args.witnesses.read_bytes()).hexdigest(),
                  reports=reports, negative_controls_rejected=rejected,
                  elapsed_seconds=round(time.monotonic() - start, 3))
    args.output.write_text(json.dumps(output, indent=2) + '\n')
    print(json.dumps(output, indent=2))


if __name__ == '__main__':
    main()
