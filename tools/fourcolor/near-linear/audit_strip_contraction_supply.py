#!/usr/bin/env python3
"""Replay the small witnesses excluding a single-contraction domain supplier.

The Lean theorem checks thirteen actual quotient colourings, source
nonextension and exclusion from two specified repair-stage families. This
independent program also measures the finite boundary domain. The census
is program evidence, not a kernel-certified coverage theorem.
"""
import argparse
from hashlib import sha256
from itertools import permutations, product
import json
from pathlib import Path
import re

from audit_diamond_sources import require
from audit_five_triangle_collapse import graph, trace
from audit_independent_repair import complete_patch
from audit_two_port_core import eliminate


def proper(adj, colours):
    return all(colours[u] != colours[v] for u in range(len(colours))
               for v in adj[u] if v < len(colours))


def palette_class(word):
    return min(tuple((0, *p)[c] for c in word) for p in permutations((1, 2, 3)))


def normal(word):
    names = {}
    return tuple(names.setdefault(c, len(names)) for c in word)


def words(prefix, ring):
    """One representative of each proper cycle word modulo vertex palettes."""
    if len(prefix) == ring:
        if prefix[-1] != prefix[0]:
            yield tuple(prefix)
        return
    for c in range(min(3, max(prefix) + 1) + 1):
        if c != prefix[-1]:
            yield from words([*prefix, c], ring)


def colour_rows(text):
    return [tuple(map(int, re.findall(r'c([0-3])', row)))
            for row in re.findall(r'=> !\[([^]]+)\]', text)]


def verify(here):
    root = here.parents[2]
    lean = root / 'lean/fourcolor-classical/MettapediaFourColor'
    source = here / 'D0099.conf'
    source_hash = sha256(source.read_bytes()).hexdigest()
    require(source_hash == '932265e50ca2493734dc03f20b4259d6506e968b6cbd8bc16b48f9f53083ae82',
            'D0099 source pin changed')
    ring, adj = graph(source.read_bytes())
    require((ring, len(adj)) == (11, 19), 'Unexpected source carrier')
    module = lean / 'StripContractionSupply.lean'
    text = module.read_text()
    edges = [tuple(map(int, pair)) for pair in re.findall(
        r'\((\d+),(\d+)\)', text.split('theorem edge_bounds')[0])]
    actual = [(u, v) for u in range(ring, len(adj)) for v in sorted(adj[u]) if u < v]
    require(edges == actual and len(edges) == 13, 'Internal edges are not exhaustive')
    boundaries = colour_rows(text.split('def boundary')[1].split('def selected')[0])
    require(len(boundaries) == 3 and all(len(b) == ring for b in boundaries),
            'Invalid boundary witnesses')
    selected = list(map(int, re.search(r'def selected[^\n]*:= !\[([^]]+)\]', text)[1].split(',')))
    data = re.search(r'def data : String := "([0-3]+)"', text)[1]
    require(len(selected) == 13 and set(selected) == {0, 1, 2} and len(data) == 91,
            'Invalid quotient witness data')
    stages, stage_counts = set(), {}
    for name, count in [('StripSixJointRepair', 16), ('StripChainRepair', 11)]:
        rows = colour_rows((lean / (name + '.lean')).read_text().split('def anchors')[0])
        require(len(rows) == count and all(len(w) == ring for w in rows),
                'Repair-stage shape changed')
        stages.update(map(palette_class, rows))
        stage_counts[name] = count
    for b in boundaries:
        require(proper(adj, b), 'Boundary is not proper')
        require(eliminate(adj, ring, b)[0] is None and complete_patch(adj, b) is None,
                'Boundary extends to the source')
        require(palette_class(trace(b, ring)) not in stages, 'Witness is in the stage domain')
    for e, (left, right) in enumerate(edges):
        image = [left if v == right else v if v < right else v - 1 for v in range(len(adj))]
        require(set(image) == set(range(18)), 'Quotient is not surjective')
        require(all((image[u] == image[v]) == (u == v or {u, v} == {left, right})
                    for u in range(19) for v in range(19)), 'Unexpected quotient fibre')
        quotient = [set() for _ in range(18)]
        for u, ns in enumerate(adj):
            for v in ns:
                if image[u] != image[v]:
                    quotient[image[u]].add(image[v])
        colours = [*boundaries[selected[e]], *map(int, data[7 * e:7 * (e + 1)])]
        require(proper(quotient, colours), 'Stored quotient colouring is not proper')
        require(tuple(colours[image[v]] for v in range(ring)) == boundaries[selected[e]],
                'Quotient boundary correspondence changed')
    lists_text = (lean / 'StripSingletonRepair.lean').read_text().split('def before')[1].split('def after')[0]
    lists = [tuple(map(int, re.findall(r'c([0-3])', row)))
             for row in re.findall(r'\{([^}]+)\}', lists_text)]
    require(len(lists) == ring, 'Before-list interface changed')
    list_domain = {normal(b) for b in product(*lists) if proper(adj, b)}
    census = {'proper_colour_classes': 0, 'direct_extension_classes': 0,
              'nonextension_classes': 0, 'nonextension_in_before_list_domain': 0,
              'nonextension_outside_selected_stages': 0}
    for b in words([0, 1], ring):
        if not proper(adj, b):
            continue
        census['proper_colour_classes'] += 1
        if eliminate(adj, ring, b)[0] is not None:
            census['direct_extension_classes'] += 1
        else:
            census['nonextension_classes'] += 1
            census['nonextension_in_before_list_domain'] += b in list_domain
            census['nonextension_outside_selected_stages'] += palette_class(trace(b, ring)) not in stages
    return {'status': 'independent program replay passed', 'source': source.name,
            'source_sha256': source_hash, 'lean_source_sha256': sha256(module.read_bytes()).hexdigest(),
            'internal_edges': edges, 'quotient_vertices': 18, 'source_vertices': 19,
            'boundary_witnesses': boundaries, 'quotient_colour_digits': len(data),
            'verified_quotient_colourings': len(edges), 'selected_stage_counts': stage_counts,
            'before_list_domain_classes': len(list_domain), 'program_census': census,
            'scope': 'Fixed ordered ports, modulo colour renaming. Every single internal edge contraction has a colouring outside direct extension and the selected 27 stages. No obstruction to further Kempe repair, other replacements, or compact compositional coverage is claimed.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    report = verify(Path(__file__).resolve().parent)
    payload = json.dumps(report, indent=2) + '\n'
    if args.output:
        args.output.write_text(payload)
    print(payload, end='')


if __name__ == '__main__':
    main()
