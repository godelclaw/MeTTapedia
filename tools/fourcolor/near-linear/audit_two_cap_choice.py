#!/usr/bin/env python3
"""Test component selection through two retained D0099 caps.

The palette is chosen before an original exterior matching. The three
restricted policies differ in when the joint cap witnesses and one of four
anchor edges are chosen. Every transition reconstructs all prefix edges;
the terminal condition is actual extension to the full source graph.
"""
import argparse
from collections import Counter
from hashlib import sha256
import itertools
import json
from pathlib import Path
import time
from audit_diamond_sources import read_rows, require
from audit_five_triangle_collapse import graph
from audit_strip_fan import SOURCE_SHA256, consecutive
from audit_strip_fan_repair import domain, code
from generate_exceptional_repair import boundary, pairings

def verify(here):
    raw = (here / 'D0099.conf').read_bytes()
    require(sha256(raw).hexdigest() == SOURCE_SHA256, 'Pinned source changed')
    (_, G) = graph(raw)
    VERTICES = [*range(12), 14, 16, 18]
    CORE = [12, 13, 15, 17]
    INSERTIONS = [(11, [6, 7, 8]), (14, [4, 5, 6, 11]), (18, [10, 0, 1]), (16, [18, 1, 2, 3])]
    PORTS = [18, 16, 3, 4, 14, 11, 8, 9, 10]
    FACES = [(11, 6, 7), (11, 7, 8), (14, 4, 5), (14, 5, 6), (14, 6, 11), (18, 10, 0), (18, 0, 1), (16, 18, 1), (16, 1, 2), (16, 2, 3)]
    CORE_EDGES = [(u, v) for u in CORE for v in CORE if u < v and v in G[u]]
    (WORDS, INDICES) = domain(11)

    def completes(col):
        lists = [set(range(4)) - {col[u] for u in G[v] if u in col} for v in CORE]
        if any((not s for s in lists)):
            return False
        for cs in itertools.product(*lists):
            f = dict(zip(CORE, cs))
            if all((f[u] != f[v] for (u, v) in CORE_EDGES)):
                return True
        return False
    prefixes = {}
    good = set()
    start = time.monotonic()
    for (idx, word) in enumerate(WORDS):
        colors = dict(enumerate(boundary(word)))
        local = []

        def insert(k):
            if k == len(INSERTIONS):
                local.append(dict(colors))
                return
            (v, ns) = INSERTIONS[k]
            for c in set(range(4)) - {colors[u] for u in ns}:
                colors[v] = c
                insert(k + 1)
            colors.pop(v, None)
        insert(0)
        if any((completes(c) for c in local)):
            good.add(idx)
        elif local:
            prefixes[idx] = local

    # A nonextending core can fail jointly even when every vertex has a colour.
    local_saturation = Counter()
    diamond_obstructions = Counter()
    for variants in prefixes.values():
        empty = []
        for col in variants:
            a, b, c, d = [set(range(4)) - {col[u] for u in G[v] if u in col}
                          for v in CORE]
            left = {(x, y) for x in b for y in c if x != y and a - {x, y}}
            right = {(x, y) for x in b for y in c if x != y and d - {x, y}}
            assert not left & right
            empty.append(not all((a, b, c, d)))
            if empty[-1]:
                kind = 'empty_vertex_list'
            elif not left or not right:
                kind = 'empty_triangle_relation'
            else:
                common_b = {x for x, y in left} & {x for x, y in right}
                common_c = {y for x, y in left} & {y for x, y in right}
                kind = ('joint_conflict_with_compatible_marginals' if common_b and common_c
                        else 'shared_vertex_marginal_conflict')
            diamond_obstructions[kind] += 1
        if all(empty):
            local_saturation['every_cap_choice_has_empty_list'] += 1
        elif any(empty):
            local_saturation['some_cap_choice_has_empty_list'] += 1
        else:
            local_saturation['no_cap_choice_has_empty_list'] += 1

    def edge(a, b):
        return tuple(sorted((a, b)))

    def cycle(vs):
        return [edge(a, b) for (a, b) in zip(vs, vs[1:] + vs[:1])]
    edges = sorted({edge(v, w) for v in VERTICES for w in G[v] if w in VERTICES})
    ei = {e: i for (i, e) in enumerate(edges)}
    old = [ei[e] for e in cycle(list(range(11)))]
    new = {ei[e] for e in cycle(PORTS)}
    tri = [[ei[e] for e in cycle(list(t))] for t in FACES]
    anchors = [(3, 4), (8, 9), (11, 14), (16, 18)]
    aids = [ei[e] for e in anchors]
    rotations = {v - 1: [w - 1 for w in ns] for (v, _, *ns) in read_rows(raw.decode())[1:]}
    ports = list(range(11))
    seen = set(ports)
    steps = []
    for (fresh, neighbours) in INSERTIONS:
        rotation = next((i for i in range(len(ports)) if (ports[i:] + ports[:i])[:len(neighbours)] == neighbours))
        require(G[fresh] & seen == set(neighbours), 'Missing or extra old neighbour')
        require(consecutive(rotations[fresh], neighbours), 'Source cyclic order differs')
        ports = ports[rotation:] + ports[:rotation]
        ports = [ports[0], fresh, *ports[len(neighbours) - 1:]]
        seen.add(fresh)
        require(len(ports) == len(set(ports)), 'Repeated boundary vertex')
        require(all((b in G[a] for (a, b) in zip(ports, ports[1:] + ports[:1]))), 'Boundary is not a cycle')
        steps.append({'inserted_vertex': fresh, 'neighbours': neighbours, 'boundary': ports.copy()})
    require(ports == PORTS and seen == set(VERTICES), 'Wrong two-cap source')
    require(CORE_EDGES == [(12, 13), (12, 15), (13, 15), (13, 17), (15, 17)], 'Residual core differs')
    require(len(edges) == 25, 'Prefix adjacency differs')
    expected_faces = {tuple(sorted((v, a, b))) for (v, ns) in INSERTIONS for (a, b) in zip(ns, ns[1:])}
    require({tuple(sorted(f)) for f in FACES} == expected_faces, 'Cap triangles differ')
    choices = {}
    anchored = {}
    adaptive = {}
    cap_first = {}
    layouts_count = 0
    tested = 0
    for idx, variants in prefixes.items():
        oldword = WORDS[idx]
        encoded = code(oldword)
        allpalettes = []
        anchor_palettes = []
        adaptive_palettes = []
        cap_first_palettes = []
        for fixed in (1, 2, 3):
            active_old = [i for (i, e) in enumerate(oldword) if e != fixed]
            allrows = []
            anchor_rows = [[] for _ in aids]
            adaptive_rows = []
            known = []
            for col in variants:
                labels = [col[a] ^ col[b] for (a, b) in edges]
                links = []
                for triangle in tri:
                    active = [i for i in triangle if labels[i] != fixed]
                    assert len(active) == 2
                    links.append(active)
                known.append((labels, links))
            cap_first_rows = [[] for _ in known]
            for matching in pairings(len(active_old)):
                exterior = [[old[active_old[a]], old[active_old[b]]] for (a, b) in matching]
                outcomes = set()
                anchor_outcomes = [set() for _ in aids]
                for (variant, (labels, links)) in enumerate(known):
                    network = {i: set() for (i, c) in enumerate(labels) if c != fixed}
                    for (a, b) in links + exterior:
                        network[a].add(b)
                        network[b].add(a)
                    assert all((len(ns) == (1 if i in new else 2) for (i, ns) in network.items()))
                    components = []
                    todo = set(network)
                    while todo:
                        root = min(todo)
                        component = {root}
                        pending = [root]
                        while pending:
                            for j in network[pending.pop()] - component:
                                component.add(j)
                                pending.append(j)
                        todo -= component
                        components.append(component)
                    # Reconstruct the entire prefix, using the same original matching.
                    targets = []
                    for comp in components:
                        mask = sum((fixed << 2 * i for (i, e) in enumerate(old) if e in comp))
                        target_idx = INDICES[encoded ^ mask]
                        changed = [c ^ fixed if i in comp else c for (i, c) in enumerate(labels)]
                        c = dict(enumerate(boundary([changed[i] for i in old])))
                        for (v, u) in ((11, 8), (14, 4), (18, 10), (16, 3)):
                            c[v] = c[u] ^ changed[ei[edge(v, u)]]
                        assert all((c[a] ^ c[b] == changed[i] for (i, (a, b)) in enumerate(edges)))
                        assert target_idx in good or target_idx in prefixes
                        target = -1 if target_idx in good else target_idx
                        targets.append(target)
                        outcomes.add(target)
                        tested += 1
                    one_cap_outcomes = set()
                    for (j, a) in enumerate(aids):
                        target = next((t for (comp, t) in zip(components, targets) if a in comp), idx)
                        anchor_outcomes[j].add(target)
                        one_cap_outcomes.add(target)
                    cap_first_rows[variant].append(frozenset(one_cap_outcomes))
                allrows.append(frozenset(outcomes))
                combined = set().union(*anchor_outcomes)
                assert combined <= outcomes | {idx}
                adaptive_rows.append(frozenset(combined))
                for j in range(len(aids)):
                    anchor_rows[j].append(frozenset(anchor_outcomes[j]))
                layouts_count += 1
            allpalettes.append(set(allrows))
            anchor_palettes.extend((set(rows) for rows in anchor_rows))
            adaptive_palettes.append(set(adaptive_rows))
            cap_first_palettes.extend((set(rows) for rows in cap_first_rows))
        choices[idx] = allpalettes
        anchored[idx] = anchor_palettes
        adaptive[idx] = adaptive_palettes
        cap_first[idx] = cap_first_palettes

    def prune(choices):
        """Choose a policy, then meet every matching with an earlier target."""
        remaining = set(prefixes)
        rounds = []
        while True:
            drop = {i for i in remaining if any((all((not row <= remaining for row in palette)) for palette in choices[i]))}
            if not drop:
                return {'rounds': rounds, 'survivors': len(remaining), 'sample': sorted(remaining)[:5]}
            remaining -= drop
            rounds.append(len(drop))
    report = {
        'boundary_states': len(prefixes),
        'direct_source_boundary_classes': len(good),
        'all_components': prune(choices),
        'four_fixed_anchors': prune(anchored),
        'four_anchors_after_matching': prune(adaptive),
        'cap_before_matching_anchor_after': prune(cap_first),
        'scope': ('Finite original-boundary game; terminal means full source extension '
                  'with compatible cap witnesses. No Lean theorem or physical obstruction.'),
        'layouts': layouts_count,
        'component_tests': tested,
        'local_saturation': dict(local_saturation),
        'diamond_obstructions_by_cap_colouring': dict(diamond_obstructions),
        'seconds': time.monotonic() - start,
    }
    require(len(prefixes) == 3768 and len(good) == 1587, 'Boundary classification differs')
    require(report['four_fixed_anchors']['survivors'] == 2950, 'Fixed-anchor result differs')
    for key in ('all_components', 'four_anchors_after_matching', 'cap_before_matching_anchor_after'):
        require(report[key]['survivors'] == 0, 'Retained obstruction in ' + key)
    report.update({
        'source_sha256': SOURCE_SHA256,
        'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
        'dependency_sha256': {
            name: sha256((here / name).read_bytes()).hexdigest()
            for name in ['audit_five_triangle_collapse.py', 'audit_strip_fan_repair.py',
                         'generate_exceptional_repair.py', 'audit_diamond_sources.py',
                         'audit_strip_fan.py']
        },
        'insertions': steps,
        'anchors': anchors,
        'joint_cap_choices_on_tested_states': sum(map(len, prefixes.values())),
        'excluded_original_words_without_cap_prefix': len(WORDS) - len(prefixes) - len(good),
        'quantifiers': {
            'four_fixed_anchors': ('choose palette and anchor; for every original '
                                   'matching choose both cap witnesses jointly'),
            'four_anchors_after_matching': ('choose palette; for every original matching '
                                           'choose both cap witnesses and anchor jointly'),
            'cap_before_matching_anchor_after': ('choose palette and both cap witnesses; '
                                                'for every original matching choose anchor'),
        },
        'limits': [
            'Discovery computation, not a Lean progress theorem.',
            'Cap colours may be reselected between rounds and at final extension.',
            'Original words without a cap prefix still need fan preparation.',
            'An abstract exterior matching may change each round; round counts are not physical runtime bounds.',
            'No strategy table, certificate replacement, strict reduction or coverage theorem is produced.',
        ],
    })
    return report
if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    report = verify(Path(__file__).resolve().parent)
    text = json.dumps(report, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end='')
