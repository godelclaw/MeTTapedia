#!/usr/bin/env python3
"""Generate a shared joint-profile ranking for the three diamond cores.

The finite game answers every exterior chromogram. Its ranks depend only on
boundary length and the four joint available-colour sets, modulo colour
renaming and exchanges within the two centres or the two tips. The output
contains finite proof data; theorem validity requires the separate Lean check.
"""

import argparse
from collections import defaultdict
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import time

from diamond_coloring_alternatives import colorings, support
from probe_diamond_joint_repair import GEOMETRY, GEOMETRY_SHA256, ROOT, literal_graph
from probe_diamond_kempe import PERMS, apply_perm, system

if not __debug__:
    raise SystemExit('Run without Python optimization: assertions are audit checks.')


def model(left, right):
    n = 6 + left + right
    graph = {v: set() for v in range(n + 4)}
    def add(a, b):
        graph[a].add(b)
        graph[b].add(a)
    for v in range(n):
        add(v, (v + 1) % n)
    for a, b in ((0, 1), (0, 2), (0, 3), (1, 2), (2, 3)):
        add(n + a, n + b)
    neighbors = [range(left + 2), (left + 1, left + 2, left + 3),
                 range(left + 3, left + right + 5),
                 (left + right + 4, left + right + 5, 0)]
    for i, ns in enumerate(neighbors):
        for v in ns:
            add(n + i, v)
    return graph, tuple(tuple(ns) for ns in neighbors)


def boundary(word):
    result = [0]
    for c in word[:-1]:
        result.append(result[-1] ^ c)
    assert result[-1] ^ result[0] == word[-1]
    return result


def palette(word, neighbors):
    colors = boundary(word)
    return tuple(15 - sum(1 << c for c in {colors[v] for v in ns}) for ns in neighbors)


def key(word, neighbors):
    p = palette(word, neighbors)
    codes = []
    for roles in ((0, 1, 2, 3), (0, 3, 2, 1), (2, 1, 0, 3), (2, 3, 0, 1)):
        columns = sorted(sum(1 << i for i, j in enumerate(roles) if p[j] >> c & 1)
                         for c in range(4))
        codes.append(sum(d << (4 * i) for i, d in enumerate(columns)))
    return 65536 * (len(word) - 6) + min(codes)


def extends(p):
    return any(p[0] >> a & 1 and p[2] >> b & 1 and a != b and
               p[1] & ~((1 << a) | (1 << b)) and p[3] & ~((1 << a) | (1 << b))
               for a in range(4) for b in range(4))


def canonical(word):
    return min(apply_perm(word, p) for p in PERMS)


def base36(n, width):
    chars = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ'
    result = ''
    for _ in range(width):
        result = chars[n % 36] + result
        n //= 36
    assert n == 0
    return result


def lean_rows(name, records):
    """Flat string records avoid repeatedly decoding the entire data stream."""
    return (f'def {name} : Nat → String\n' +
            ''.join(f'  | {i} => "{row}"\n' for i, row in enumerate(records)) +
            '  | _ => ""\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-output', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    assert args.lean_output.suffix == '.lean' and args.report.suffix == '.json'
    start = time.monotonic()
    raw = (ROOT / GEOMETRY).read_bytes()
    assert sha256(raw).hexdigest() == GEOMETRY_SHA256
    source, rows, owners, base = raw.decode(), [], defaultdict(list), set()
    for ordinal, (left, right) in zip((1, 2, 4), ((0, 0), (1, 0), (1, 1))):
        graph, neighbors = model(left, right)
        actual, _ = literal_graph(source, ordinal)
        assert graph == actual
        n = 6 + left + right
        universe, grams = system(n)
        vertices, values = colorings(graph)
        good = support(vertices, values, list(range(n)))
        assert good == {w for w in universe if extends(palette(w, neighbors))}
        keys = {w: key(w, neighbors) for w in universe}
        by_word = defaultdict(list)
        for _, words in grams:
            for w in words:
                by_word[w].append(words)
        i = len(rows)
        for w, p in keys.items():
            owners[p].append((i, w))
            if w in good:
                base.add(p)
        rows.append(dict(ordinal=ordinal, n=n, neighbors=neighbors, universe=universe,
                         good=good, keys=keys, by_word=by_word))
    assert all(w in rows[i]['good'] for p in base for i, w in owners[p])
    ranks, stages = {p: 1 for p in base}, [len(base)]
    while True:
        following = []
        for p, states in owners.items():
            if p in ranks:
                continue
            if all(any(all(any(rows[i]['keys'][answer] in ranks for answer in words)
                           for words in rows[i]['by_word'][apply_perm(w, perm)])
                       for perm in PERMS) for i, w in states):
                following.append(p)
        if not following:
            break
        ranks.update((p, len(stages) + 1) for p in following)
        stages.append(len(ranks))
    assert stages == [51, 62, 68, 75, 83, 89, 92]
    records, reports = [], []
    max_answers = 0
    for row in rows:
        keys, by_word = row['keys'], row['by_word']
        representatives = sorted({canonical(w) for w in row['universe'] if keys[w] in ranks})
        indices = {w: i for i, w in enumerate(representatives)}
        steps = []
        for w in representatives:
            r = ranks[keys[w]]
            if r == 1:
                assert w in row['good']
                steps.append((w, []))
                continue
            options = []
            for perm in PERMS:
                oriented = apply_perm(w, perm)
                grams = by_word[oriented]
                covered = defaultdict(set)
                for g, words in enumerate(grams):
                    for answer in words:
                        if 0 < ranks.get(keys[answer], 0) < r:
                            covered[answer].add(g)
                pending, selected = set(range(len(grams))), []
                while pending:
                    answer = min(covered, key=lambda a: (
                        -len(covered[a] & pending), ranks[keys[a]], a), default=None)
                    if answer is None or not covered[answer] & pending:
                        break
                    selected.append(answer)
                    pending -= covered[answer]
                if not pending:
                    options.append((len(selected), perm, oriented, selected))
            assert options
            _, _, oriented, answers = min(options)
            assert keys[oriented] == keys[w]
            steps.append((oriented, answers))
            max_answers = max(max_answers, len(answers))
        encoded = []
        for oriented, answers in steps:
            indices_and_perms = []
            for answer in answers:
                j = indices[canonical(answer)]
                perm = next(p for p in PERMS if apply_perm(answer, p) == steps[j][0])
                assert ranks[keys[steps[j][0]]] < ranks[keys[oriented]]
                indices_and_perms.append((j, PERMS.index(perm)))
            assert ranks[keys[oriented]] == 1 or all(
                any(a in words for a in answers) for words in by_word[oriented])
            encoded.append((oriented, indices_and_perms))
        if row['n'] < 8:
            assert {canonical(w) for w in row['universe']} == indices.keys()
        else:
            starts = set()
            for a, b, x, y, z, w in product(range(4), repeat=6):
                if a == b or x == a or z == b or y in (a, b) or w in (a, b):
                    continue
                cs = (a, x, a, y, b, z, b, w)
                starts.add(tuple(cs[i] ^ cs[(i + 1) % 8] for i in range(8)))
            assert len(starts) == 108
            assert {canonical(w) for w in starts} <= indices.keys()
        reports.append(dict(configuration=row['ordinal'], ring=row['n'],
                            proper_traces=len(row['universe']), ordinary_traces=len(row['good']),
                            certified_traces=sum(keys[w] in ranks for w in row['universe']),
                            state_orbits=len(encoded), terminal_states=sum(not a for _, a in encoded)))
        records.extend(encoded)
    words = [''.join(map(str, w)).ljust(8, '0') for w, _ in records]
    answers = [str(len(ans)) + ''.join(base36(i, 2) + str(p) for i, p in ans).ljust(3 * max_answers, '0')
               for _, ans in records]
    rank_words = [base36(p, 4) + str(ranks[p]) for p in sorted(ranks)]
    text = '''/-!
# Shared diamond profile certificate data

Generated by `generate_diamond_profile_certificate.py`. Words use digits 0--3;
answer indices and profile keys use base 36. These are untrusted finite data
until the profile, graph witnesses and Kempe covers have been checked in Lean.
-/

namespace FourColor.DiamondProfileData

'''
    text += f'def maxAnswers : Nat := {max_answers}\n\n'
    text += lean_rows('wordCodes', words) + '\n'
    text += lean_rows('answerCodes', answers) + '\n'
    text += lean_rows('rankCodes', rank_words)
    text += '\nend FourColor.DiamondProfileData\n'
    args.lean_output.write_text(text)
    report = dict(evidence='Finite candidate generation and program validation; Lean checks are separate.',
                  geometry_sha256=GEOMETRY_SHA256,
                  generator_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                  data_sha256=sha256(text.encode()).hexdigest(),
                  profile='boundary length plus joint available-colour sets, modulo colour names and centre/tip exchanges',
                  profiles=len(owners), ranked_profiles=len(ranks), terminal_profiles=len(base),
                  nonterminal_profiles=len(ranks) - len(base), stages=stages,
                  maximum_descent_stages=max(ranks.values()) - 1, maximum_answers=max_answers,
                  states=len(records), answers=sum(len(a) for _, a in records), cores=reports,
                  scope='Three finite core shapes. No longer-fan repair, geometric coverage or executable exterior recolouring is asserted.',
                  elapsed_seconds=round(time.monotonic() - start, 3))
    args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report), flush=True)


if __name__ == '__main__':
    main()
