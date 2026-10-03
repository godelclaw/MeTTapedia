#!/usr/bin/env python3
"""Test one-round reuse of the checked D0092 seed strategy.

This is untrusted exploration, not a Lean certificate. It tests the eight
symbolic three-run boundary words against direct extension and the retained
seed states. Failed unsigned matchings need not be realized by an exterior
graph. They refute only this abstract one-round transfer contract.
"""
import argparse
from functools import lru_cache
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import re

from audit_five_triangle_collapse import graph
from audit_two_port_core import eliminate
from generate_exceptional_repair import boundary, canonical, pairings


def probe():
    here = Path(__file__).resolve().parent
    root = here.parents[2]
    receipt = json.loads((here / 'residual-seed-repair-measurements.json').read_text())
    pin = next(m for m in receipt['modules']
               if m['module'] == 'MettapediaFourColor.ResidualSeedRepairData')
    data = root / 'lean/fourcolor-classical/MettapediaFourColor/ResidualSeedRepairData.lean'
    raw = data.read_bytes()
    assert sha256(raw).hexdigest() == pin['source_sha256']
    # Read exactly the existing checked words; do not run strategy discovery.
    section = raw.decode().split('private def recordsPart0', 1)[1].split('\ndef records (', 1)[0]
    packed = ''.join(re.findall(r'"([0-9A-Z]+)"', section))
    assert len(packed) == 22 * 41
    retained = {canonical(tuple(map(int, packed[i:i + 11])))
                for i in range(0, len(packed), 22)}
    assert len(retained) == 41

    fixture = json.loads((here / 'component-detach-example.json').read_text())
    source = (here / fixture['configuration']).read_bytes()
    assert sha256(source).hexdigest() == fixture['configuration_sha256']
    ring, g = graph(source)
    assert (len(g), ring) == (18, 11)

    def independent_extension(ports):
        """Backtrack over seven core vertices, independently of elimination."""
        colours = dict(enumerate(ports))

        def visit():
            if len(colours) == len(g):
                return True
            choices = {v: set(range(4)) - {colours[w] for w in g[v] if w in colours}
                       for v in range(ring, len(g)) if v not in colours}
            v = min(choices, key=lambda u: (len(choices[u]), u))
            for c in sorted(choices[v]):
                colours[v] = c
                if visit():
                    del colours[v]
                    return True
            colours.pop(v, None)
            return False

        return visit()

    @lru_cache(None)
    def direct(word):
        ports = boundary(word)
        result = eliminate(g, ring, ports)[0] is not None
        assert result == independent_extension(ports)
        return result

    def accepted(word):
        return word in retained or direct(word)

    def switched(word, fixed, pairs):
        slots = [i for i, c in enumerate(word) if c != fixed]
        # Include every subset, including empty and full selections.
        out = set()
        for mask in range(1 << len(pairs)):
            changed = list(word)
            for k, (a, b) in enumerate(pairs):
                if mask >> k & 1:
                    changed[slots[a]] ^= fixed
                    changed[slots[b]] ^= fixed
            out.add(canonical(changed))
        return sorted(out)

    def rounds(word):
        result = []
        for fixed in (1, 2, 3):
            slots = [i for i, c in enumerate(word) if c != fixed]
            cases = pairings(len(slots))
            failed = []
            for pairs in cases:
                targets = switched(word, fixed, pairs)
                if not any(accepted(w) for w in targets):
                    failed.append({'pairs_on_active_slots': pairs, 'targets': targets})
            result.append({'fixed_edge_colour': fixed, 'active_positions': slots,
                           'matching_cases': len(cases), 'failed_cases': len(failed),
                           'first_failure': failed[0] if failed else None})
        return result

    classes = []
    for a, b, c in product((False, True), repeat=3):
        ports = (1, 3, 2 * (not a), 3, 1, 2 * b, 3,
                 2 * c, 2 * (not c), 2 * c, 2 * (not c))
        word = canonical(tuple(x ^ y for x, y in zip(ports, ports[1:] + ports[:1])))
        extends = direct(word)
        assert extends == (a == b and b != c)
        classes.append({'choices': [a, b, c], 'vertex_word': ports,
                        'canonical_trace': word, 'direct_extension': extends,
                        'retained_seed_state': word in retained})
    uncovered = sorted({c['canonical_trace'] for c in classes
                        if not c['direct_extension'] and not c['retained_seed_state']})
    tests = [{'word': w, 'rounds': rounds(w)} for w in uncovered]
    # Test only the intermediate states exposed by the first failing
    # fixed-colour-1 matching, not all possible two-round strategies.
    intermediates = sorted({tuple(w) for t in tests
                            for w in t['rounds'][0]['first_failure']['targets']})
    intermediate_tests = [{'word': w, 'rounds': rounds(w)} for w in intermediates]
    return {
        'status': 'UNTRUSTED_BOUNDED_TRANSFER_PROBE',
        'source_sha256': sha256(source).hexdigest(),
        'checked_seed_data_sha256': pin['source_sha256'],
        'retained_seed_states': len(retained),
        'acceptance_set': 'Direct source extension or a colour permutation of an existing checked seed state.',
        'symbolic_classes': classes,
        'uncovered_canonical_classes': tests,
        'selected_intermediate_tests': intermediate_tests,
        'limits': [
            'No claim that the failed unsigned matching is realized by a planar exterior.',
            'Does not exclude longer or differently chosen mixed-pair strategies.',
            'Does not refute D0092 reducibility, compact family repair, or compositional proofs.',
            'No new repair data, Lean theorem, or catalogue saving.'
        ]
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    report = probe()
    def compact(value):
        if isinstance(value, dict):
            return {k: ''.join(map(str, v)) if k in ('word', 'vertex_word', 'canonical_trace')
                    else [''.join(map(str, w)) for w in v] if k == 'targets'
                    else compact(v) for k, v in value.items()}
        if isinstance(value, (list, tuple)):
            return [compact(v) for v in value]
        return value

    report['word_encoding'] = 'Ordered colour digits; no port or edge is omitted.'
    args.output.write_text(json.dumps(compact(report), indent=2) + '\n')
    for case in report['uncovered_canonical_classes']:
        print(case['word'], [(r['fixed_edge_colour'], r['failed_cases'], r['matching_cases'])
                            for r in case['rounds']])


if __name__ == '__main__':
    main()
