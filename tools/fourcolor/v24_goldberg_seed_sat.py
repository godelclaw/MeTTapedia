#!/usr/bin/env python3
"""SAT-audit the cap-correct Seed predicate on Goldberg fullerenes.

For every ordered pair of vertex-disjoint pentagonal faces of GP(k,0), and
for every good inner word modulo a global colour permutation, this program
checks two existential statements:

* the open two-cap tangle has a proper Tait colouring with that inner word;
* some such colouring is menu B after the inner pentagonal cap is restored.

Menu B is encoded without bounding path length.  For a majority colour pair,
Boolean component labels are constrained to be constant across adjacent
edges of that two-colour subgraph.  Two active spokes can receive different
labels exactly when they lie in different Kempe components.  Thus a SAT model
is a checkable witness to the literal, cap-restored Menu-B condition.

The run is evidence on a generated family, not a proof of the Seed Lemma.
"""

from __future__ import annotations

import argparse
from collections import Counter
from itertools import combinations, permutations, product
from pathlib import Path
from typing import Any

import z3

from v24_annular_census import atomic_write_json
from v24_goldberg import cap_distances, make_goldberg_graph


SCHEMA = "fourcolor-v24-goldberg-seed-sat-v1"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-frequency", type=int, default=3)
    parser.add_argument(
        "--far-representative-frequencies",
        type=int,
        nargs="*",
        default=[],
        help="also audit one maximally separated ordered cap pair at each frequency",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("results/fourcolor/v24_goldberg_seed_sat.json"),
    )
    return parser.parse_args()


def good_word(word: tuple[int, ...]) -> bool:
    counts = Counter(word)
    if sorted(counts.values()) != [1, 1, 3]:
        return False
    majority = next(colour for colour, count in counts.items() if count == 3)
    return any(
        all(word[(start + offset) % 5] == majority for offset in range(3))
        for start in range(5)
    )


GOOD_WORDS = sorted(
    word
    for word in set(permutations((0, 0, 0, 1, 2)))
    if good_word(word)
)
assert len(GOOD_WORDS) == 10


def cap_extension(word: tuple[int, ...]) -> tuple[int, ...]:
    extensions = [
        internal
        for internal in product(range(3), repeat=5)
        if all(
            {word[index], internal[index - 1], internal[index]} == {0, 1, 2}
            for index in range(5)
        )
    ]
    if len(extensions) != 1:
        raise AssertionError("a good pentagonal word must have one cap extension")
    return extensions[0]


def open_two_cap_tangle(
    graph: dict[str, Any], outer_face: int, inner_face: int
) -> tuple[list[tuple[int, int]], list[list[int]], list[int], list[int]]:
    faces = graph["face_cycles"]
    outer_cap = faces[outer_face]
    inner_cap = faces[inner_face]
    if set(outer_cap) & set(inner_cap):
        raise ValueError("the two caps are not vertex-disjoint")
    removed = {
        tuple(sorted((cap[index], cap[(index + 1) % 5])))
        for cap in (outer_cap, inner_cap)
        for index in range(5)
    }
    edges = [
        tuple(edge)
        for edge in graph["primal_edges"]
        if tuple(edge) not in removed
    ]
    incidence = [[] for _ in range(graph["primal_vertex_count"])]
    for edge_index, (left, right) in enumerate(edges):
        incidence[left].append(edge_index)
        incidence[right].append(edge_index)
    inner_set = set(inner_cap)
    inner_spokes = []
    for vertex in inner_cap:
        candidates = [
            edge_index
            for edge_index in incidence[vertex]
            if any(endpoint not in inner_set for endpoint in edges[edge_index])
        ]
        if len(candidates) != 1:
            raise AssertionError("an inner cap vertex does not have one spoke")
        inner_spokes.append(candidates[0])
    return edges, incidence, inner_spokes, inner_cap


def proper_colouring_solver(
    edges: list[tuple[int, int]], incidence: list[list[int]], tag: str
) -> tuple[z3.Solver, list[z3.IntNumRef]]:
    solver = z3.Solver()
    colours = [z3.Int(f"c_{tag}_{edge}") for edge in range(len(edges))]
    solver.add(*(z3.And(0 <= colour, colour < 3) for colour in colours))
    for incident in incidence:
        for left, right in combinations(incident, 2):
            solver.add(colours[left] != colours[right])
    return solver, colours


def menu_b_formula(
    edges: list[tuple[int, int]],
    incidence: list[list[int]],
    colours: list[z3.IntNumRef],
    inner_spokes: list[int],
    inner_cap: list[int],
    word: tuple[int, ...],
    tag: str,
) -> z3.BoolRef:
    cap_colours = cap_extension(word)
    full_edges = list(edges)
    full_colours: list[z3.ArithRef | int] = list(colours)
    full_incidence = [list(row) for row in incidence]
    for index, colour in enumerate(cap_colours):
        edge_index = len(full_edges)
        left, right = inner_cap[index], inner_cap[(index + 1) % 5]
        full_edges.append((left, right))
        full_colours.append(colour)
        full_incidence[left].append(edge_index)
        full_incidence[right].append(edge_index)

    witnesses: list[z3.BoolRef] = []
    majority = 0
    for other in (1, 2):
        labels = [
            z3.Bool(f"side_{tag}_{''.join(map(str, word))}_{other}_{edge}")
            for edge in range(len(full_edges))
        ]
        constraints: list[z3.BoolRef] = []

        def allowed(edge: int) -> z3.BoolRef:
            colour = full_colours[edge]
            if isinstance(colour, int):
                return z3.BoolVal(colour in (majority, other))
            return z3.Or(colour == majority, colour == other)

        for incident in full_incidence:
            for left, right in combinations(incident, 2):
                constraints.append(
                    z3.Implies(
                        z3.And(allowed(left), allowed(right)),
                        labels[left] == labels[right],
                    )
                )
        active = [
            inner_spokes[index]
            for index, colour in enumerate(word)
            if colour in (majority, other)
        ]
        if len(active) != 4:
            raise AssertionError("a majority pair must activate four spokes")
        separated = z3.Or(
            *(labels[left] != labels[right] for left, right in combinations(active, 2))
        )
        witnesses.append(z3.And(*constraints, separated))
    return z3.Or(*witnesses)


def literal_menu_b(
    colouring: tuple[int, ...],
    edges: list[tuple[int, int]],
    incidence: list[list[int]],
    inner_spokes: list[int],
    inner_cap: list[int],
    word: tuple[int, ...],
) -> bool:
    """Recheck a SAT witness by an independent component traversal."""
    full_edges = list(edges)
    full_colours = list(colouring)
    full_incidence = [list(row) for row in incidence]
    for index, colour in enumerate(cap_extension(word)):
        edge_index = len(full_edges)
        left, right = inner_cap[index], inner_cap[(index + 1) % 5]
        full_edges.append((left, right))
        full_colours.append(colour)
        full_incidence[left].append(edge_index)
        full_incidence[right].append(edge_index)

    for other in (1, 2):
        allowed = {
            edge_index
            for edge_index, colour in enumerate(full_colours)
            if colour in (0, other)
        }
        component_of: dict[int, int] = {}
        component = 0
        while allowed:
            seed = allowed.pop()
            reached = [seed]
            component_of[seed] = component
            while reached:
                edge = reached.pop()
                for vertex in full_edges[edge]:
                    for adjacent in full_incidence[vertex]:
                        if adjacent in allowed:
                            allowed.remove(adjacent)
                            component_of[adjacent] = component
                            reached.append(adjacent)
            component += 1
        active = [
            inner_spokes[index]
            for index, colour in enumerate(word)
            if colour in (0, other)
        ]
        if len({component_of[edge] for edge in active}) >= 2:
            return True
    return False


def audit_annulus(
    graph: dict[str, Any], outer_face: int, inner_face: int
) -> dict[str, Any]:
    edges, incidence, inner_spokes, inner_cap = open_two_cap_tangle(
        graph, outer_face, inner_face
    )
    tag = f"k{graph['frequency']}_o{outer_face}_i{inner_face}"
    solver, colours = proper_colouring_solver(edges, incidence, tag)
    nonempty: list[str] = []
    seeded: list[str] = []
    seedless: list[str] = []
    for word in GOOD_WORDS:
        word_key = "".join(map(str, word))
        solver.push()
        solver.add(
            *(colours[edge] == colour for edge, colour in zip(inner_spokes, word))
        )
        plain_status = solver.check()
        if plain_status == z3.unknown:
            raise RuntimeError(f"Z3 returned unknown on {tag}, word {word_key}")
        if plain_status == z3.sat:
            nonempty.append(word_key)
            solver.push()
            solver.add(
                menu_b_formula(
                    edges,
                    incidence,
                    colours,
                    inner_spokes,
                    inner_cap,
                    word,
                    tag,
                )
            )
            menu_status = solver.check()
            if menu_status == z3.unknown:
                raise RuntimeError(f"Z3 returned unknown on Menu B for {tag}, word {word_key}")
            if menu_status == z3.sat:
                model = solver.model()
                colouring = tuple(model.eval(colour).as_long() for colour in colours)
                if not literal_menu_b(
                    colouring,
                    edges,
                    incidence,
                    inner_spokes,
                    inner_cap,
                    word,
                ):
                    raise AssertionError(
                        f"the SAT Menu-B witness failed literal replay: {tag}, {word_key}"
                    )
                seeded.append(word_key)
            else:
                seedless.append(word_key)
            solver.pop()
        solver.pop()
    return {
        "outer_face": outer_face,
        "inner_face": inner_face,
        "nonempty_good_words": nonempty,
        "seeded_good_words": seeded,
        "seedless_good_words": seedless,
    }


def audit_frequency(frequency: int) -> dict[str, Any]:
    graph = make_goldberg_graph(frequency)
    pentagons = graph["pentagon_face_ids"]
    rows = []
    for outer_face in pentagons:
        for inner_face in pentagons:
            if outer_face == inner_face:
                continue
            if set(graph["face_cycles"][outer_face]) & set(
                graph["face_cycles"][inner_face]
            ):
                continue
            rows.append(audit_annulus(graph, outer_face, inner_face))
    return {
        "frequency": frequency,
        "primal_vertex_count": graph["primal_vertex_count"],
        "graph_hash": graph["graph_hash"],
        "ordered_annuli": len(rows),
        "nonempty_good_fibres": sum(len(row["nonempty_good_words"]) for row in rows),
        "seeded_good_fibres": sum(len(row["seeded_good_words"]) for row in rows),
        "seedless_good_fibres": sum(len(row["seedless_good_words"]) for row in rows),
        "annuli": rows,
    }


def audit_far_representative(frequency: int) -> dict[str, Any]:
    graph = make_goldberg_graph(frequency)
    candidates = []
    for outer_face in graph["pentagon_face_ids"]:
        distances = cap_distances(graph, outer_face)
        for inner_face in graph["pentagon_face_ids"]:
            if outer_face == inner_face:
                continue
            if set(graph["face_cycles"][outer_face]) & set(
                graph["face_cycles"][inner_face]
            ):
                continue
            separation = min(
                distances[vertex] for vertex in graph["face_cycles"][inner_face]
            )
            candidates.append((separation, -outer_face, -inner_face))
    if not candidates:
        raise AssertionError("the Goldberg graph has no disjoint pentagonal caps")
    separation, negative_outer, negative_inner = max(candidates)
    outer_face, inner_face = -negative_outer, -negative_inner
    row = audit_annulus(graph, outer_face, inner_face)
    return {
        "frequency": frequency,
        "primal_vertex_count": graph["primal_vertex_count"],
        "graph_hash": graph["graph_hash"],
        "cap_vertex_separation": separation,
        **row,
    }


def run(max_frequency: int, far_representative_frequencies: list[int]) -> dict[str, Any]:
    if max_frequency < 1:
        raise ValueError("the maximum frequency must be positive")
    rows = [audit_frequency(frequency) for frequency in range(1, max_frequency + 1)]
    return {
        "schema": SCHEMA,
        "solver": f"z3-{z3.get_version_string()}",
        "good_word_representatives": ["".join(map(str, word)) for word in GOOD_WORDS],
        "colour_symmetry": "majority fixed to 0; all global colour permutations represented",
        "frequencies": rows,
        "far_representatives": [
            audit_far_representative(frequency)
            for frequency in far_representative_frequencies
        ],
        "scope_warning": (
            "Finite SAT evidence on generated Goldberg annuli only; not a proof "
            "of the universal Seed Lemma or of the global corridor theorem."
        ),
    }


def main() -> int:
    args = parse_args()
    result = run(args.max_frequency, args.far_representative_frequencies)
    atomic_write_json(args.output, result)
    for row in result["frequencies"]:
        print(
            f"k={row['frequency']} V={row['primal_vertex_count']} "
            f"annuli={row['ordered_annuli']} "
            f"nonempty={row['nonempty_good_fibres']} "
            f"seeded={row['seeded_good_fibres']} "
            f"seedless={row['seedless_good_fibres']}"
        )
    for row in result["far_representatives"]:
        print(
            f"far k={row['frequency']} V={row['primal_vertex_count']} "
            f"separation={row['cap_vertex_separation']} "
            f"nonempty={len(row['nonempty_good_words'])} "
            f"seeded={len(row['seeded_good_words'])} "
            f"seedless={len(row['seedless_good_words'])}"
        )
    print(f"certificate={args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
