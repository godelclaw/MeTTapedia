#!/usr/bin/env python3
"""Generate untrusted D1774 joint-chord repair certificates for Lean checking.

The source catalogue and its MIT notice are retained beside this script.
Noncrossing pairings are enumerated independently of Lean's stack-labelled
chord signatures. Each repair uses one or two whole chords of the same
exterior. Terminal records contain genuine full core-colouring witnesses.
"""

import argparse
from collections import Counter
from functools import lru_cache
from hashlib import sha256
from itertools import combinations, permutations
import json
from pathlib import Path
import time

SOURCE_SHA256 = '694db4afd81219890d3b84c453f2c2dbb55e1a8b5b60ac57577470e50013b196'
PERMS = tuple(permutations((1, 2, 3)))


def canonical(word):
    names = {}
    return tuple(names.setdefault(c, len(names) + 1) for c in word)


def permute(word, perm):
    return tuple(perm[c - 1] if c else 0 for c in word)


def traces(size):
    def visit(word, acc, largest):
        if len(word) == size - 1:
            if acc and acc <= min(3, largest + 1):
                yield tuple(word + [acc])
        else:
            for c in range(1, min(3, largest + 1) + 1):
                yield from visit(word + [c], acc ^ c, max(largest, c))
    return list(visit([], 0, 0))


def boundary(word):
    out = [0]
    for c in word[:-1]:
        out.append(out[-1] ^ c)
    assert out[-1] ^ out[0] == word[-1]
    return out


@lru_cache(None)
def pairings(count, start=0):
    if count == 0:
        return ((),)
    return tuple(((start, start + j),) + a + b
                 for j in range(1, count, 2)
                 for a in pairings(j - 1, start + 1)
                 for b in pairings(count - j - 1, start + j + 1))


def cases(word, anchors):
    slots = [i for i, c in enumerate(word) if c != 1]
    seen, result = set(), []
    for pairs in pairings(len(slots)):
        signature = tuple(next(e for e in pairs if a in e) for a in anchors)
        if signature in seen:
            continue
        seen.add(signature)
        masks = {frozenset(e) for e in signature}
        masks.update(frozenset(a + b) for a, b in combinations(signature, 2))
        answers = set()
        for mask in masks:
            answer = list(word)
            for i in mask:
                answer[slots[i]] ^= 1
            answers.add(tuple(answer))
        result.append(answers)
    return result


def cover(options, allowed):
    chosen, pending = [], list(options)
    while pending:
        counts = Counter(a for row in pending for a in row if allowed(a))
        if not counts:
            return None
        a = min(counts, key=lambda a: (-counts[a], a))
        chosen.append(a)
        pending = [row for row in pending if a not in row]
    return chosen


def cases_for_pairing(word, pairs):
    slots = [i for i, c in enumerate(word) if c != 1]
    result = set()
    for selected in [(e,) for e in pairs] + list(combinations(pairs, 2)):
        answer = list(word)
        for e in selected:
            for j in e:
                answer[slots[j]] ^= 1
        result.add(tuple(answer))
    return result


def code(n, width=1):
    out = ''
    for _ in range(width):
        out = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ'[n % 36] + out
        n //= 36
    assert n == 0
    return out


def lean_blocks(name, data, block):
    blocks = [''.join(data[i:i + block]) for i in range(0, len(data), block)]
    def branch(lo, hi, indent):
        if hi == lo + 1:
            return ' ' * indent + '"' + blocks[lo] + '"'
        mid = (lo + hi) // 2
        return (' ' * indent + f'if i < {mid} then\n' + branch(lo, mid, indent + 2) +
                '\n' + ' ' * indent + 'else\n' + branch(mid, hi, indent + 2))
    parts = (len(blocks) + 63) // 64
    out = ''.join(f'private def {name}Part{k} (i : Nat) : String :=\n' +
                  branch(k * 64, min((k + 1) * 64, len(blocks)), 2) + '\n\n'
                  for k in range(parts))
    def dispatch(lo, hi, indent):
        if hi == lo + 1:
            return ' ' * indent + f'{name}Part{lo} i'
        mid = (lo + hi) // 2
        return (' ' * indent + f'if i < {64 * mid} then\n' + dispatch(lo, mid, indent + 2) +
                '\n' + ' ' * indent + 'else\n' + dispatch(mid, hi, indent + 2))
    return out + (f'def {name} (i : Nat) : String :=\n  if i < {len(blocks)} then\n' +
                  dispatch(0, parts, 4) + '\n  else ""\n\n')


def lean_checks():
    text = '''import MettapediaFourColor.ExceptionalRepairCertificate

/-! # Kernel checks of every D1774 repair record and every proper input

Generated finite obligations are split into bounded blocks. Each declaration
uses kernel reduction. The final theorems quantify over all certificate
records and all eleven-port proper zero-sum traces.
-/

namespace FourColor.ExceptionalRepairCertificate

set_option maxRecDepth 65536

def checkAt (n : ℕ) : Bool := check ⟨n % ExceptionalRepairData.count, Nat.mod_lt _ (by decide)⟩
def inputAt (n : ℕ) : Bool := inputCheck (n % (3 ^ 10))

'''
    for name, checker, block, count in [('record', 'checkAt', 64, 116),
                                         ('input', 'inputAt', 256, 231)]:
        for k in range(count):
            text += ('set_option maxHeartbeats 2000000 in\n'
                     '-- Validate a bounded block of the finite certificate.\n'
                     f'theorem {name}Block{k} : ∀ j : Fin {block}, '
                     f'{checker} ({block * k} + j.val) = true := by decide +kernel\n\n')
        text += (f'theorem {name}Blocks (b : Fin {count}) (j : Fin {block}) :\n'
                 f'    {checker} ({block} * b.val + j.val) = true := by\n'
                 '  fin_cases b\n' + ''.join(f'  · exact {name}Block{k} j\n' for k in range(count)) + '\n')
    text += '''theorem checked (i : State) : check i = true := by
  have hi : i.val < 7381 := i.isLt
  have h := recordBlocks ⟨i.val / 64, by omega⟩ ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
  change checkAt (64 * (i.val / 64) + i.val % 64) = true at h
  have hn : 64 * (i.val / 64) + i.val % 64 = i.val := by omega
  simpa only [hn, checkAt, Nat.mod_eq_of_lt i.isLt] using h

theorem coverage (i : Fin (3 ^ 10)) : inputCheck i = true := by
  have hi : i.val < 59049 := i.isLt
  have h := inputBlocks ⟨i.val / 256, by omega⟩ ⟨i.val % 256, Nat.mod_lt _ (by decide)⟩
  change inputAt (256 * (i.val / 256) + i.val % 256) = true at h
  have hn : 256 * (i.val / 256) + i.val % 256 = i.val := by omega
  simpa only [hn, inputAt, Nat.mod_eq_of_lt i.isLt] using h

/-- Every proper eleven-port zero-sum trace admits compatible D1774 repair. -/
theorem repair : KempeBoundarySplit.Repairs Supports 11 := repair_of_checks checked coverage

end FourColor.ExceptionalRepairCertificate
'''
    return text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--checks', type=Path)
    args = parser.parse_args()
    started = time.monotonic()
    source = Path(__file__).with_name('D1774.conf')
    assert sha256(source.read_bytes()).hexdigest() == SOURCE_SHA256
    rows = [list(map(int, line.split())) for line in source.read_text().splitlines()
            if line.strip()]
    n, r = rows[0]
    assert (n, r) == (19, 11)
    edges = {tuple(sorted((i, (i + 1) % r))) for i in range(r)}
    for v, degree, *neighbors in rows[1:]:
        assert len(neighbors) == degree
        edges.update(tuple(sorted((v - 1, w - 1))) for w in neighbors)
    core = [{b - r if a == i + r else a - r for a, b in edges
             if min(a, b) >= r and i + r in (a, b)} for i in range(8)]
    outer = [sorted(a for a, b in edges if a < r and b == i + r) for i in range(8)]
    colors, current = [], [-1] * 8
    order = [0, 6, 4, 1, 3, 5, 2, 7]

    def enumerate_colors(k):
        if k == 8:
            colors.append(tuple(current))
            return
        v = order[k]
        for c in range(4):
            if all(current[w] != c for w in core[v]):
                current[v] = c
                enumerate_colors(k + 1)
                current[v] = -1
    enumerate_colors(0)
    assert len(colors) == 768

    @lru_cache(None)
    def witness(word):
        b = boundary(word)
        return next((cs for cs in colors
                     if all(cs[i] != b[j] for i in range(8) for j in outer[i])), None)

    words = traces(r)
    index = {w: i for i, w in enumerate(words)}
    assert len(words) == 7381
    ranked = {i: 0 for i, w in enumerate(words) if witness(w) is not None}
    stages = [len(ranked)]
    # All chords are observed during discovery. At this width, any subset,
    # up to global renaming, has a representative with at most two chords.
    options = []
    for w in words:
        row = []
        for fixed in range(1, 4):
            p = next(p for p in PERMS if p[fixed - 1] == 1)
            oriented = permute(w, p)
            anchors = tuple(range(sum(c != 1 for c in oriented)))
            row.append([{index[canonical(a)] for a in choices}
                        for choices in cases(oriented, anchors)])
        options.append(row)
    while True:
        known = set(ranked)
        added = [i for i in range(len(words)) if i not in known and
                 any(all(choices & known for choices in row) for row in options[i])]
        if not added:
            break
        ranked.update((i, len(stages)) for i in added)
        stages.append(len(ranked))
        print('rank stage', len(stages) - 1, len(ranked), flush=True)
    assert len(ranked) == len(words)

    records = []
    for i, w in enumerate(words):
        if ranked[i] == 0:
            records.append((w, (), (), witness(w), 0))
            continue
        allowed = lambda a: ranked[index[canonical(a)]] < ranked[i]
        candidates = []
        for fixed in range(1, 4):
            if not all(any(ranked[j] < ranked[i] for j in choices)
                       for choices in options[i][fixed - 1]):
                continue
            p = next(p for p in PERMS if p[fixed - 1] == 1)
            oriented = permute(w, p)
            count = sum(c != 1 for c in oriented)
            patterns = [(0,), (0, 1), (0, 2), (0, count - 1),
                        (0, 1, 2), (0, 1, count - 1), tuple(range(count))]
            for anchors in patterns:
                if max(anchors) >= count:
                    continue
                cs = cases(oriented, anchors)
                answers = cover(cs, allowed)
                if answers:
                    candidates.append((len(cs) * (1 + len(anchors)), len(answers),
                                       oriented, anchors, tuple(answers), len(cs)))
                    break
        assert candidates
        _, _, oriented, anchors, answers, classifications = min(candidates)
        records.append((oriented, anchors, answers, (), classifications))

    # Store a particular whole-chord answer for each unsigned skeleton. The
    # checker verifies the supplied mask, rather than searching for a mask.
    max_answers = max(len(a) for _, _, a, _, _ in records)
    width = 24
    encoded, chord_records = [], []
    for i, (w, anchors, answers, cs, _) in enumerate(records):
        row = ''.join(map(str, w)) + code(ranked[i])
        row += ''.join(map(str, cs)).ljust(8, '0')
        row += code(len(chord_records), 4)
        assert len(row) == width
        encoded.append(row)
        chord_data = ''
        if answers:
            slots = [k for k, c in enumerate(w) if c != 1]
            ordered = []
            for pairs in pairings(len(slots)):
                ds = tuple(any(a == k for a, _ in pairs) for k in range(len(slots)))
                ordered.append((ds, pairs))
            for ds, pairs in sorted(ordered):
                choices = cases_for_pairing(w, pairs)
                a = next(a for a in answers if a in choices)
                mask = sum(1 << k for k, slot in enumerate(slots) if w[slot] != a[slot])
                assert all(bool(mask >> x & 1) == bool(mask >> y & 1) for x, y in pairs)
                j = index[canonical(a)]
                p = next(p for p in PERMS if permute(a, p) == records[j][0])
                assert ranked[j] < ranked[i]
                chord_data += code(mask, 2) + code(j, 3) + code(PERMS.index(p))
        chord_records.extend(chord_data[k:k + 6] for k in range(0, len(chord_data), 6))
        if cs:
            full = boundary(w) + list(cs)
            assert all(full[a] != full[b] for a, b in edges)
    lookup = []
    for j in range(3 ** 10):
        partial = tuple(1 + (j // 3 ** k) % 3 for k in range(10))
        last = 0
        for c in partial:
            last ^= c
        if last == 0:
            lookup.append('0000')
            continue
        w = partial + (last,)
        i = index[canonical(w)]
        p = next(p for p in PERMS if permute(w, p) == records[i][0])
        lookup.append(code(i, 3) + code(PERMS.index(p)))
    text = '''/-!
# D1774 joint-chord repair data

Generated by tools/fourcolor/near-linear/generate_exceptional_repair.py.
These flat strings are untrusted certificates. The Lean checker validates
source colourings, complete joint chord coverage, strict descent and input
coverage. Catalogue source and MIT notice: tools/fourcolor/near-linear.
-/

namespace FourColor.ExceptionalRepairData

'''
    text += f'def count : Nat := {len(records)}\ndef width : Nat := {width}\n\n'
    for name, data, block in [('records', encoded, 1), ('chords', chord_records, 4),
                              ('lookup', lookup, 4)]:
        text += lean_blocks(name, data, block)
    text += 'end FourColor.ExceptionalRepairData\n'
    args.output.write_text(text)
    if args.checks:
        args.checks.write_text(lean_checks())
    report = dict(evidence='Untrusted generated certificate; requires the separate Lean check.',
                  source_sha256=SOURCE_SHA256, states=len(words), terminal_states=stages[0],
                  rank_stages=stages, maximum_answers=max_answers, record_width=width,
                  anchor_counts=dict(sorted(Counter(len(a) for _, a, _, _, _ in records).items())),
                  joint_classifications=sum(k for _, _, _, _, k in records),
                  checked_unsigned_skeletons=len(chord_records),
                  edges=len(edges), core_colorings=len(colors),
                  output_sha256=sha256(text.encode()).hexdigest(),
                  seconds=round(time.monotonic() - started, 3))
    args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2), flush=True)


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Assertions are certificate-generation checks; do not use -O.')
    main()
