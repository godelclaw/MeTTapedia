#!/usr/bin/env python3
"""Cross-check exact cut transport and test joint-anchor progress measures.

Source list-summary obstructions and the refined transport law are proved
in Lean. Defect costs, bounded repair rounds and profile-ordering results
are program evidence in the abstract noncrossing-matching game. No complete
boundary strategy or colouring table is saved.
"""
import argparse
from collections import defaultdict
from hashlib import sha256
from itertools import combinations, permutations, product
import json
from pathlib import Path
import re
from audit_adaptive_chords import flip
from audit_diamond_sources import require
from audit_five_triangle_collapse import graph
from audit_strip_partial import partial
from audit_triangle_strip_lists import PINS, propagate, reconstruct
from generate_exceptional_repair import boundary, canonical, pairings, traces
INF = 99

def profile_test(here, name, anchors):
    """Exact tree DP with anchors fixed; state four deletes a forest vertex.

    A joint cost is the least number of non-anchor vertices omitted while
    keeping those two colours. Every zero-cost outcome is independently
    checked by the direct list-colouring solver. Subsequent rounds allow
    arbitrary subsets of a single supplied noncrossing matching.
    """
    raw = (here / (name + '.conf')).read_bytes()
    require(sha256(raw).hexdigest() == PINS[name], 'Source pin differs')
    (ring, g) = graph((here / (name + '.conf')).read_bytes())
    n = len(g) - ring
    require(ring + anchors[1] not in g[ring + anchors[0]], 'Anchors must be independent')
    words = traces(ring)
    index = {w: i for (i, w) in enumerate(words)}
    rest = set(range(n)) - set(anchors)
    parent = {}
    children = {v: [] for v in rest}
    order = []

    def visit(v, p):
        assert v not in parent
        parent[v] = p
        for u in sorted(rest):
            if u != p and ring + u in g[ring + v]:
                children[v].append(u)
                visit(u, v)
        order.append(v)
    for v in sorted(rest):
        if v not in parent:
            visit(v, None)
    roots = [v for v in rest if parent[v] is None]
    profiles = []
    potentials = []
    for w in words:
        b = boundary(w)
        masks = [set(range(4)) - {b[u] for u in g[ring + v] if u < ring} for v in range(n)]
        costs = []
        for choice in product(range(4), repeat=2):
            if any((a not in masks[v] for (v, a) in zip(anchors, choice))):
                costs.append(INF)
                continue
            dp = {}
            for v in order:
                allowed = masks[v] - {a for (x, a) in zip(anchors, choice) if ring + x in g[ring + v]}
                d = [INF] * 5
                d[4] = 1 + sum((min(dp[u]) for u in children[v]))
                for a in allowed:
                    d[a] = sum((min((dp[u][c] for c in range(5) if c != a)) for u in children[v]))
                dp[v] = d
            costs.append(sum((min(dp[v]) for v in roots)))
        require((min(costs) == 0) == (partial(g, ring, b, []) is not None), 'Anchor DP disagrees with independent extension search')
        profiles.append(tuple(costs))
        optimum = min(costs)
        potentials.append((optimum, -costs.count(optimum)))
    responses = []
    for (i, w) in enumerate(words):
        queries = []
        for fixed in (1, 2, 3):
            slots = [j for (j, c) in enumerate(w) if c != fixed]
            rows = []
            for m in pairings(len(slots)):
                cs = [(slots[a], slots[b]) for (a, b) in m]
                out = {i} | {index[canonical(flip(w, fixed, ss))] for k in range(1, len(cs) + 1) for ss in combinations(cs, k)}
                rows.append((cs, out))
            queries.append(rows)
        responses.append(queries)

    def pre(known):
        return known | {i for (i, qs) in enumerate(responses) if i not in known and any((all((out & known for (cs, out) in ms)) for ms in qs))}
    done = {i for (i, p) in enumerate(potentials) if p[0] == 0}
    metrics = {'minimum_anchor_defect': [p[0] for p in potentials], 'defect_then_joint_choices': potentials}
    results = {}
    for (label, values) in metrics.items():
        domain = sorted(set((values[i] for i in range(len(words)) if i not in done)))
        stats = []
        failures = {}
        for value in domain:
            group = {i for (i, v) in enumerate(values) if v == value and i not in done}
            smaller = done | {i for (i, v) in enumerate(values) if v < value}
            known = smaller
            counts = []
            for k in range(1, 5):
                known = pre(known)
                counts.append(len(group & known))
            row = dict(value=value, inputs=len(group), improved_by_round=counts)
            stats.append(row)
            known2 = pre(pre(smaller))
            bad = sorted(group - known2)
            if bad:
                failures[str(value)] = [''.join(map(str, words[i])) for i in bad[:3]]
        results[label] = dict(groups=stats, first_two_round_failures=failures)
    perms = list(permutations(range(4)))

    def canonical_profile(p):
        return min((tuple((p[4 * a + b] for a in q for b in q)) for q in perms))
    # A ranking may depend on the entire joint-cost profile, up to colour
    # names. A class is admitted only when all its inputs can reach earlier
    # classes within the round allowance; queries may inspect the full input.
    groups = defaultdict(set)
    for (i, p) in enumerate(profiles):
        if i not in done:
            groups[canonical_profile(p)].add(i)
    for rounds in (1, 2):
        known = set(done)
        remaining = dict(groups)
        layers = []
        while remaining:
            ready = known
            for _ in range(rounds):
                ready = pre(ready)
            won = {key for (key, ids) in remaining.items() if ids <= ready}
            if not won:
                break
            for key in won:
                known |= remaining.pop(key)
            layers.append([len(won), len(known)])
        row = dict(rounds=rounds, groups=len(groups), remaining_groups=len(remaining), unresolved_inputs=sum(map(len, remaining.values())), layers=layers)
        results['profile_quotient_' + str(rounds)] = row
    out = dict(source=name, inputs=len(words), profiles=len(groups), results=results)
    return out

def verify(here):
    src = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor/StripListTransport.lean'
    text = src.read_text()
    block = text.split('def boundary :', 1)[1].split('def cut', 1)[0]
    bs = {(s, t): tuple(map(int, re.findall('c([0-3])', row))) for (s, t, row) in re.findall('\\| (false|true), (false|true) => !\\[([^\\]]+)\\]', block)}
    require(len(bs) == 4, 'Source boundary examples differ')
    cases = []
    for (flag, name, anchors) in [('false', 'D0063', (1, 3)), ('true', 'D0099', (1, 6))]:
        raw = (here / (name + '.conf')).read_bytes()
        require(sha256(raw).hexdigest() == PINS[name], 'Source pin differs')
        (ring, g) = graph(raw)
        n = len(g) - ring
        edges = [(v, u) for v in range(n) for u in range(n) if ring + u in g[ring + v]]

        def lists(b):
            return [set(range(4)) - {b[u] for u in g[ring + v] if u < ring} for v in range(n)]
        before = [bs[flag, t] for t in ['false', 'true']]
        after = [tuple((a ^ 1 if i == 6 else a for (i, a) in enumerate(b))) for b in before]
        require(lists(before[0]) == lists(before[1]), 'Original lists differ')
        require(all((partial(g, ring, b, []) is None for b in before)), 'Original boundary extends')
        require(partial(g, ring, after[0], []) is None, 'Negative update extends')
        refined = []
        for (b, changed) in zip(before, after):
            require(all((b[u] != b[v] and changed[u] != changed[v] for u in range(ring) for v in g[u] if v < ring)), 'Boundary is improper')
            q = [({b[u] for u in g[ring + v] if u < ring and u != 6}, {b[u] for u in g[ring + v] if u == 6}) for v in range(n)]
            transported = [set(range(4)) - (fixed | {a ^ 1 for a in moving}) for (fixed, moving) in q]
            require(transported == lists(changed), 'Refined update failed')
            word = tuple((b[i] ^ b[(i + 1) % ring] for i in range(ring)))
            require(flip(word, 1, [(5, 6)]) == tuple((changed[i] ^ changed[(i + 1) % ring] for i in range(ring))), 'Local update/edge switch differs')
            refined.append(q)
        require(refined[0] != refined[1], 'Refined summary still identifies the examples')
        (residual, steps) = propagate(lists(after[1]), anchors, (0, 0), edges)
        require(residual is not None and steps <= 2, 'Shared forest guard failed')
        reconstruct(g, ring, after[1], anchors, (0, 0), residual)
        cases.append(dict(source=name, source_sha256=PINS[name], boundaries=before, original_lists=[sorted(a) for a in lists(before[0])], updated_boundaries=after, full_extension_after=[False, True], moving_port=6, palette_xor=1, shared_anchor_choice=[0, 0], forest_sweeps=steps))
    tests = [profile_test(here, name, anchors) for (name, anchors) in [('D0063', (1, 3)), ('D0099', (1, 6))]]
    require([t['results']['profile_quotient_2']['unresolved_inputs'] for t in tests] == [0, 5242], 'Two-round profile test differs')
    require([t['results']['profile_quotient_2']['remaining_groups'] for t in tests] == [0, 155], 'Two-round profile class count differs')
    return dict(classification='CHECKED_SOURCE_TRANSPORT_WITH_PROGRAM_PROGRESS_TESTS', catalogue_revision='c2ce7a96e35256201526e2abb51a39d04a588b53', source_examples=cases, program_only_progress_tests=tests, program_scope='Each round chooses a colour pair, receives a fresh adverse noncrossing matching and selects a batch of its components. Responses need not be jointly physically realizable. The lexicographic measure minimizes anchor-preserving vertex deletions, then maximizes the number of optimal joint anchor assignments. Profile ordering groups the complete sixteen joint costs up to colour permutation.', limits=['No kernel proof of the complete profile census or rank obstruction.', 'No assertion that a particular physical exterior allows the displayed update.', 'No geometric supply, strict ambient reduction or uniform source progress theorem.', 'The refined summary transports operations on a retained cut; a new cut may require additional observations.'], whole_boundary_strategy_exported=False, whole_colour_table_exported=False, new_coverage_entries_removed=0, new_original_certificates_removed=0, lean_source_sha256=sha256(src.read_bytes()).hexdigest())
if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.dumps(verify(Path(__file__).resolve().parent), indent=2) + '\n'
    if args.output:
        args.output.write_text(result)
    print(result, end='')
