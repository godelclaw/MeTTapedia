#!/usr/bin/env python3
"""Audit the source's four-block-edge Lift condition on plane cubic maps.

Addendum IX weakens the per-fibre Seed Lemma: the five block classes of the
good-word graph are connected once menu-B witnesses realize at least four of
the five adjacent block edges.  This audit keeps the two majority pairs
separate, assigns each cap-correct menu-B witness to its block edge, and tests
that weaker source condition.

The generated maps and opened annuli are supplied by
``v24_plantri_seed_audit``.  SAT witnesses are independently replayed by a
literal component traversal.  Finite success is evidence only; failure is a
counterexample to the four-block-edge condition at the tested annulus.
"""

from __future__ import annotations

import argparse
import hashlib
from itertools import combinations
from pathlib import Path
from typing import Any

import z3

from v24_annular_census import atomic_write_json
from v24_goldberg_seed_sat import GOOD_WORDS, cap_extension, proper_colouring_solver
from v24_plantri_seed_audit import (
    generated_embeddings,
    graph_record,
    open_face_annulus,
    parse_ascii_graph,
)


SCHEMA = "fourcolor-v24-plantri-lift-bridge-audit-v1"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plantri", type=Path, required=True)
    parser.add_argument("--min-primal-vertices", type=int, default=20)
    parser.add_argument("--max-primal-vertices", type=int, default=36)
    parser.add_argument("--minimum-face-length", type=int, choices=(3, 4, 5), default=5)
    parser.add_argument(
        "--triangulation-connectivity", type=int, choices=(3, 4, 5), default=5
    )
    parser.add_argument("--connected-only", action="store_true")
    parser.add_argument("--stop-on-first", action="store_true")
    parser.add_argument(
        "--max-graphs-per-size",
        type=int,
        default=None,
        help="audit only the first N generated maps at each order (explicitly partial)",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("results/fourcolor/v24_plantri_lift_bridge_audit.json"),
    )
    return parser.parse_args()


def good_block_start(word: tuple[int, ...]) -> int:
    counts = {colour: word.count(colour) for colour in set(word)}
    majorities = [colour for colour, count in counts.items() if count == 3]
    if len(majorities) != 1:
        raise AssertionError("a good word must have one majority colour")
    majority = majorities[0]
    starts = [
        start
        for start in range(5)
        if all(word[(start + offset) % 5] == majority for offset in range(3))
    ]
    if len(starts) != 1:
        raise AssertionError("a good word must have one consecutive majority block")
    return starts[0]


def block_start(word: tuple[int, ...]) -> int:
    if word.count(0) != 3:
        raise AssertionError("the audit representatives must have majority colour zero")
    return good_block_start(word)


def block_edge_for_pair(word: tuple[int, ...], other: int) -> int:
    """Return e for the block-cycle edge {e,e+1} installed by this pair."""
    if other not in (1, 2):
        raise ValueError("the normalized majority pairs are (0,1) and (0,2)")
    inactive = [index for index, colour in enumerate(word) if colour not in (0, other)]
    if len(inactive) != 1:
        raise AssertionError("a majority pair must have one inactive singleton position")
    start = block_start(word)
    expected = {(start + 3) % 5, (start + 4) % 5}
    if inactive[0] not in expected:
        raise AssertionError("the inactive position is not adjacent to the majority block")
    # If the inactive singleton is at start+4, the move joins start to start+1;
    # if it is at start+3, it joins start-1 to start.  Both are inactive+1 mod 5.
    return (inactive[0] + 1) % 5


def cap_blocks_for_pair(word: tuple[int, ...], other: int) -> list[set[int]]:
    """Compute the two active-position blocks directly from the restored cap."""
    cap_colours = cap_extension(word)
    active = {index for index, colour in enumerate(word) if colour in (0, other)}
    # A selected cap path may pass through the unique inactive cap vertex:
    # its spoke is outside the pair, but both of its cycle edges are inside.
    adjacency = {index: set() for index in range(5)}
    for index, colour in enumerate(cap_colours):
        left, right = index, (index + 1) % 5
        if colour in (0, other):
            adjacency[left].add(right)
            adjacency[right].add(left)
    blocks: list[set[int]] = []
    unseen = set(range(5))
    cap_components: list[set[int]] = []
    while unseen:
        seed = unseen.pop()
        component = {seed}
        stack = [seed]
        while stack:
            position = stack.pop()
            for neighbour in adjacency[position] & unseen:
                unseen.remove(neighbour)
                component.add(neighbour)
                stack.append(neighbour)
        cap_components.append(component)
    blocks = [component & active for component in cap_components if component & active]
    if sorted(map(len, blocks)) != [2, 2]:
        raise AssertionError("a good pentagonal cap must give two two-position blocks")
    return blocks


def validate_block_edge_formula() -> None:
    """Check the five-block coordinate against all literal cap matchings."""
    for word in GOOD_WORDS:
        source = block_start(word)
        for other in (1, 2):
            edge = block_edge_for_pair(word, other)
            expected_targets = {edge, (edge + 1) % 5}
            if source not in expected_targets:
                raise AssertionError("the source block is not incident with its claimed edge")
            target = next(block for block in expected_targets if block != source)
            for cap_block in cap_blocks_for_pair(word, other):
                switched = list(word)
                for position in cap_block:
                    if switched[position] == 0:
                        switched[position] = other
                    elif switched[position] == other:
                        switched[position] = 0
                    else:
                        raise AssertionError("a cap block contains an inactive position")
                if good_block_start(tuple(switched)) != target:
                    raise AssertionError("a literal cap-class flip reached the wrong block")


validate_block_edge_formula()


def restored_cap_data(
    edges: list[tuple[int, int]],
    incidence: list[list[int]],
    colours: list[z3.IntNumRef],
    inner_cap: list[int],
    word: tuple[int, ...],
) -> tuple[list[tuple[int, int]], list[list[int]], list[z3.ArithRef | int]]:
    full_edges = list(edges)
    full_incidence = [list(row) for row in incidence]
    full_colours: list[z3.ArithRef | int] = list(colours)
    for index, colour in enumerate(cap_extension(word)):
        edge_index = len(full_edges)
        left, right = inner_cap[index], inner_cap[(index + 1) % 5]
        full_edges.append((left, right))
        full_colours.append(colour)
        full_incidence[left].append(edge_index)
        full_incidence[right].append(edge_index)
    return full_edges, full_incidence, full_colours


def menu_b_for_pair_formula(
    edges: list[tuple[int, int]],
    incidence: list[list[int]],
    colours: list[z3.IntNumRef],
    inner_spokes: list[int],
    inner_cap: list[int],
    word: tuple[int, ...],
    other: int,
    tag: str,
) -> z3.BoolRef:
    full_edges, full_incidence, full_colours = restored_cap_data(
        edges, incidence, colours, inner_cap, word
    )
    labels = [
        z3.Bool(f"lift_side_{tag}_{''.join(map(str, word))}_{other}_{edge}")
        for edge in range(len(full_edges))
    ]

    def allowed(edge: int) -> z3.BoolRef:
        colour = full_colours[edge]
        if isinstance(colour, int):
            return z3.BoolVal(colour in (0, other))
        return z3.Or(colour == 0, colour == other)

    constraints = [
        z3.Implies(
            z3.And(allowed(left), allowed(right)), labels[left] == labels[right]
        )
        for incident in full_incidence
        for left, right in combinations(incident, 2)
    ]
    active = [
        inner_spokes[index]
        for index, colour in enumerate(word)
        if colour in (0, other)
    ]
    if len(active) != 4:
        raise AssertionError("a majority pair must activate four spokes")
    separated = z3.Or(
        *(labels[left] != labels[right] for left, right in combinations(active, 2))
    )
    return z3.And(*constraints, separated)


def literal_menu_b_for_pair(
    colouring: tuple[int, ...],
    edges: list[tuple[int, int]],
    incidence: list[list[int]],
    inner_spokes: list[int],
    inner_cap: list[int],
    word: tuple[int, ...],
    other: int,
) -> bool:
    full_edges = list(edges)
    full_incidence = [list(row) for row in incidence]
    full_colours = list(colouring)
    for index, colour in enumerate(cap_extension(word)):
        edge_index = len(full_edges)
        left, right = inner_cap[index], inner_cap[(index + 1) % 5]
        full_edges.append((left, right))
        full_colours.append(colour)
        full_incidence[left].append(edge_index)
        full_incidence[right].append(edge_index)

    unseen = {
        edge_index
        for edge_index, colour in enumerate(full_colours)
        if colour in (0, other)
    }
    component_of: dict[int, int] = {}
    component = 0
    while unseen:
        seed = unseen.pop()
        stack = [seed]
        component_of[seed] = component
        while stack:
            edge = stack.pop()
            for vertex in full_edges[edge]:
                for adjacent in full_incidence[vertex]:
                    if adjacent in unseen:
                        unseen.remove(adjacent)
                        component_of[adjacent] = component
                        stack.append(adjacent)
        component += 1
    active = [
        inner_spokes[index]
        for index, colour in enumerate(word)
        if colour in (0, other)
    ]
    return len({component_of[edge] for edge in active}) >= 2


def audit_annulus(graph: dict[str, Any], outer_face: int, inner_face: int) -> dict[str, Any]:
    edges, incidence, inner_spokes, inner_cap, connected = open_face_annulus(
        graph, outer_face, inner_face
    )
    tag = f"lift_g{graph['frequency']}_o{outer_face}_i{inner_face}"
    solver, colours = proper_colouring_solver(edges, incidence, tag)
    nonempty_words: list[str] = []
    pair_witnesses: list[dict[str, int | str]] = []
    realized_edges: set[int] = set()
    for word in GOOD_WORDS:
        word_key = "".join(map(str, word))
        solver.push()
        solver.add(*(colours[edge] == colour for edge, colour in zip(inner_spokes, word)))
        status = solver.check()
        if status == z3.unknown:
            raise RuntimeError(f"SAT returned unknown on {tag}, word {word_key}")
        if status == z3.sat:
            nonempty_words.append(word_key)
            for other in (1, 2):
                solver.push()
                solver.add(
                    menu_b_for_pair_formula(
                        edges,
                        incidence,
                        colours,
                        inner_spokes,
                        inner_cap,
                        word,
                        other,
                        tag,
                    )
                )
                pair_status = solver.check()
                if pair_status == z3.unknown:
                    raise RuntimeError(
                        f"SAT returned unknown on pair ({0},{other}) for {tag}, {word_key}"
                    )
                if pair_status == z3.sat:
                    model = solver.model()
                    colouring = tuple(model.eval(colour).as_long() for colour in colours)
                    if not literal_menu_b_for_pair(
                        colouring,
                        edges,
                        incidence,
                        inner_spokes,
                        inner_cap,
                        word,
                        other,
                    ):
                        raise AssertionError(
                            f"pair witness failed literal replay: {tag}, {word_key}, {other}"
                        )
                    edge = block_edge_for_pair(word, other)
                    realized_edges.add(edge)
                    pair_witnesses.append(
                        {"word": word_key, "other_colour": other, "block_edge": edge}
                    )
                solver.pop()
        solver.pop()
    return {
        "outer_face": outer_face,
        "outer_length": len(graph["face_cycles"][outer_face]),
        "inner_face": inner_face,
        "connected": connected,
        "nonempty_good_words": nonempty_words,
        "pair_witnesses": pair_witnesses,
        "realized_block_edges": sorted(realized_edges),
        "four_block_edge_condition": len(realized_edges) >= 4,
    }


def run(args: argparse.Namespace) -> dict[str, Any]:
    sizes: list[dict[str, Any]] = []
    first_failure: dict[str, Any] | None = None
    for primal_vertices in range(args.min_primal_vertices, args.max_primal_vertices + 1, 2):
        embeddings = list(
            generated_embeddings(
                args.plantri,
                primal_vertices,
                args.minimum_face_length,
                args.triangulation_connectivity,
            )
        )
        generated_count = len(embeddings)
        if args.max_graphs_per_size is not None:
            embeddings = embeddings[: args.max_graphs_per_size]
        row = {
            "primal_vertices": primal_vertices,
            "graphs_generated": generated_count,
            "graphs_audited": len(embeddings),
            "annuli_audited": 0,
            "connected_annuli_audited": 0,
            "annuli_with_nonempty_good_fibre": 0,
            "four_block_edge_successes": 0,
            "four_block_edge_failures": 0,
        }
        stop = False
        for graph_index, embedding in enumerate(embeddings):
            graph = graph_record(parse_ascii_graph(embedding), graph_index)
            faces = graph["face_cycles"]
            for outer_face in range(len(faces)):
                for inner_face in graph["pentagon_face_ids"]:
                    if outer_face == inner_face or set(faces[outer_face]) & set(faces[inner_face]):
                        continue
                    annulus = audit_annulus(graph, outer_face, inner_face)
                    row["annuli_audited"] += 1
                    if annulus["connected"]:
                        row["connected_annuli_audited"] += 1
                    if not annulus["nonempty_good_words"]:
                        continue
                    if args.connected_only and not annulus["connected"]:
                        continue
                    row["annuli_with_nonempty_good_fibre"] += 1
                    if annulus["four_block_edge_condition"]:
                        row["four_block_edge_successes"] += 1
                    else:
                        row["four_block_edge_failures"] += 1
                        if first_failure is None:
                            first_failure = {
                                "primal_vertices": primal_vertices,
                                "graph_index": graph_index,
                                "graph_hash": graph["graph_hash"],
                                "ascii_embedding": graph["ascii_embedding"],
                                "face_cycles": faces,
                                "annulus": annulus,
                            }
                        if args.stop_on_first:
                            stop = True
                            break
                if stop:
                    break
            if stop:
                break
        sizes.append(row)
        print(
            f"V={primal_vertices} graphs={row['graphs_audited']}/{row['graphs_generated']} "
            f"annuli={row['annuli_with_nonempty_good_fibre']} "
            f"lift4={row['four_block_edge_successes']} "
            f"fail={row['four_block_edge_failures']}",
            flush=True,
        )
        if stop:
            break
    return {
        "schema": SCHEMA,
        "generator": {
            "name": "plantri",
            "arguments": (
                f"-a -d -m{args.minimum_face_length} "
                f"-c{args.triangulation_connectivity} (V/2+2)"
            ),
            "binary_sha256": hashlib.sha256(args.plantri.read_bytes()).hexdigest(),
        },
        "solver": f"z3-{z3.get_version_string()}",
        "target": (
            "at least four of the five good-word block-cycle edges have a "
            "cap-correct menu-B witness for some majority pair"
        ),
        "block_edge_index": (
            "edge e joins majority-run block e to e+1 modulo five; for a pair, "
            "e is one plus its inactive singleton position modulo five"
        ),
        "connected_only": args.connected_only,
        "partial_graph_limit": args.max_graphs_per_size,
        "sizes": sizes,
        "first_failure": first_failure,
        "scope_warning": (
            "Finite success is evidence only.  A failure refutes this sufficient "
            "four-block-edge condition for the recorded annulus, not necessarily "
            "the exact realized-word connectivity predicate."
        ),
    }


def main() -> int:
    args = parse_args()
    result = run(args)
    atomic_write_json(args.output, result)
    print(f"certificate={args.output}")
    return 1 if result["first_failure"] is not None else 0


if __name__ == "__main__":
    raise SystemExit(main())
