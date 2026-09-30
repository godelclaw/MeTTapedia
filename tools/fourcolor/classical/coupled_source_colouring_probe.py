#!/usr/bin/env python3
"""Test the structural source-colouring domain on the saved residuals.

No saved source colour word is read. A suitable neighbour pair is coloured
alike, and a reverse rooted order supplies the other choices. The existing
independent literal reconstruction checks the actual target rotations.
Connectivity checks here are program evidence; the general structural law
and the cube consumer are proved separately in Lean.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path

import networkx as nx

from alternating_lobe_probe import data
from dual_truncate_colouring import examine

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are replay checks.")


def structural_colouring(graph):
    """Retain the joint pair while colouring the reverse-distance order."""
    assert all(graph.degree(v) <= 3 for v in graph)
    assert nx.is_connected(graph)
    candidate = next(
        (a, b, root)
        for root in sorted(graph)
        for a, b in itertools.combinations(sorted(graph[root]), 2)
        if not graph.has_edge(a, b)
        and nx.is_connected(graph.subgraph(set(graph) - {a, b}))
    )
    a, b, root = candidate
    retained = graph.subgraph(set(graph) - {a, b})
    distance = dict(nx.single_source_shortest_path_length(retained, root))
    assert set(distance) == set(retained)
    order = sorted(retained, key=lambda v: (-distance[v], v))
    assert order[-1] == root
    colour = {a: 1, b: 1}
    maximum_used = 0
    for v in order:
        if v != root:
            assert any(w not in colour for w in graph[v])
        else:
            assert colour[a] == colour[b]
        used = {colour[w] for w in graph[v] if w in colour}
        assert len(used) <= 2
        maximum_used = max(maximum_used, len(used))
        colour[v] = min({1, 2, 3} - used)
    assert set(colour) == set(graph)
    assert all(colour[u] != colour[v] for u, v in graph.edges())
    return candidate, order, colour, maximum_used


def run():
    source_path = HERE / "family-supply-fixtures.json"
    target_path = HERE / "family-supply-probe.json"
    sources = {m["id"]: m for m in json.loads(source_path.read_text())["maps"]}
    saved = json.loads(target_path.read_text())
    targets = {m["id"]: m for m in saved["maps"]}
    results = []
    for target_id in saved["failed_map_ids"]:
        source_id = target_id.removeprefix("dual-truncate-")
        source, target = sources[source_id], targets[target_id]
        graph, _, _, _ = data(source["rotation"])
        pair, order, colour, maximum = structural_colouring(graph)
        deletion_pairs = list(itertools.combinations(sorted(graph), 2))
        disconnected = [
            [a, b] for a, b in deletion_pairs
            if not nx.is_connected(graph.subgraph(set(graph) - {a, b}))
        ]
        word = "".join(str(colour[v]) for v in sorted(graph))
        replay = examine(source, target, {"vertex_colour_word": word})
        results.append(dict(
            source=source_id, target=target_id,
            source_vertices=len(graph), target_vertices=replay["target_vertices"],
            initial_pair=list(pair[:2]), closing_vertex=pair[2],
            rooted_order_sha256=hashlib.sha256(json.dumps(order).encode()).hexdigest(),
            generated_source_colour_sha256=hashlib.sha256(word.encode()).hexdigest(),
            maximum_prior_colours=maximum,
            pair_deletions_checked=len(deletion_pairs),
            disconnected_pair_deletions=disconnected,
            literal_target_darts_checked=replay["target_darts_checked"],
            source_rotation_sha256=replay["source_rotation_sha256"],
            target_rotation_sha256=replay["target_rotation_sha256"],
            source_colour_word_supplied=False,
            kernel_structural_domain_certificate=False,
        ))
    paths = [source_path, target_path, Path(__file__),
             HERE / "alternating_lobe_probe.py", HERE / "alternating_cycle_probe.py",
             HERE / "dual_truncate_colouring.py"]
    return dict(
        status="independent program replay",
        scope="All five saved residual sources meet the tested structural domain; this is not a kernel certificate of their connectivity.",
        source_colour_words_read=0,
        maps=results,
        total_pair_deletions_checked=sum(m["pair_deletions_checked"] for m in results),
        kernel_input_rotations_previously_certified=True,
        kernel_structural_domain_certificates=False,
        new_catalogue_replacements=0,
        global_coverage_proved=False,
        input_sha256={p.relative_to(REPO).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in paths},
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE / "coupled-source-colouring-probe.json")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = json.dumps(run(), indent=2, sort_keys=True) + "\n"
    if args.check:
        assert args.output.read_text() == result, "Structural replay receipt differs."
    else:
        args.output.write_text(result)
    print("Checked structural source choices and literal reconstruction on five residual maps.")


if __name__ == "__main__":
    main()
