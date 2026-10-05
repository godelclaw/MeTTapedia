#!/usr/bin/env python3
"""Measure the exact region-labelled interface on the pinned D0099 source.

The transport and reconstruction laws have separate Lean proofs. This
finite census measures report fibres; it emits no repair strategy table.
"""
import argparse
from collections import Counter
from hashlib import sha256
from itertools import permutations
import json
from pathlib import Path
import time

from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_strip_fan_repair import domain
from audit_strip_response import verify as verify_obstruction
from generate_exceptional_repair import boundary


def verify(here):
    start = time.monotonic()
    source = verify_obstruction(here)
    _, adj = graph((here / 'D0099.conf').read_bytes())
    attachments = source['boundary_attachments']
    profiles, common, unpartitioned = Counter(), Counter(), Counter()
    inputs = set()
    for word in domain(11)[0]:
        raw = boundary(word)
        for perm in permutations((1, 2, 3)):
            colours = tuple(0 if c == 0 else perm[c - 1] for c in raw)
            require(colours not in inputs, 'Duplicate labelled boundary')
            inputs.add(colours)
            require(all(colours[i] != colours[j] for i in range(11)
                        for j in adj[i] if j < 11), 'Improper source boundary')
            profile = tuple(sum({1 << colours[i] for i in ns
                                 if (2 <= i <= 9) == cell})
                            for ns in attachments for cell in (False, True))
            flat = tuple(profile[2 * i] | profile[2 * i + 1] for i in range(8))
            profiles[profile] += 1
            common_profile = tuple(sum({1 << colours[i] for i in ns
                                        if ((2 <= i <= 9), i == 5) == cell})
                                   for ns in attachments
                                   for cell in ((False, False), (False, True),
                                                (True, False), (True, True)))
            common[common_profile] += 1
            unpartitioned[flat] += 1
    require(len(inputs) == (3 ** 11 - 3) // 4 == 44286,
            'The labelled proper-cycle census is incomplete')
    require(len(profiles) == 39543 and len(unpartitioned) == 39543,
            'The exact report census differs')
    require(Counter(profiles.values()) == {1: 35286, 2: 3771, 3: 486},
            'The report fibre sizes differ')
    require(source['exact_retained_relations_equal'] and
            source['cases'][0]['updated_extends'] and
            not source['cases'][1]['updated_extends'], 'Source obstruction differs')
    return {
        'evidence': 'Finite report census; transport and source reconstruction separately Lean checked.',
        'source_sha256': source['source_sha256'],
        'dcalculus_revision': '3b432626d1b8ca6c7f3ec8b9b69b15431023a34b',
        'proper_boundary_colours_with_first_port_zero': len(inputs),
        'partitioned_profiles': len(profiles),
        'common_refinement_profiles': len(common),
        'unpartitioned_profiles': len(unpartitioned),
        'largest_partitioned_fibre': max(profiles.values()),
        'partitioned_fibre_sizes': dict(Counter(profiles.values())),
        'common_refinement_fibre_sizes': dict(Counter(common.values())),
        'naive_boundary_colour_bits_with_first_port_fixed': 20,
        'naive_partitioned_mask_bits': 64,
        'naive_common_refinement_mask_bits': 128,
        'evaluated_relation_snapshot_predicts_updated_extension': False,
        'source_witnesses_reused': True,
        'new_colouring_witness_table_bytes': 0,
        'catalogue_entries_removed': 0,
        'certificate_dependencies_removed': 0,
        'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
        'seconds': time.monotonic() - start,
        'limits': [
            'The exact update domain keeps one fixed partition of boundary vertices.',
            'Kempe repair requires the actual selected component and its admissibility.',
            'No smaller bit representation, kernel saving, strict reduction or coverage is established.',
            'The census fixes boundary vertex 0 to colour 0 and retains labelled palette values.',
            'The two source inputs have their own abstract chromograms; no common physical exterior is constructed.'
        ]
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    payload = json.dumps(verify(Path(__file__).resolve().parent), indent=2) + '\n'
    if args.output:
        args.output.write_text(payload)
    print(payload, end='')
