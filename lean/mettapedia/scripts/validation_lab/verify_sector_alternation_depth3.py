#!/usr/bin/env python3
"""Verify one transparent counterexample to universal chord drainage.

The certificate is one transparent colored annular cubic graph.  The checker
reconstructs total bichromatic closure, the two rail
paths, the two face sectors, a depth-three same-sector chord nest, and a
specific third-color edge that remains inside the outer chord interval.

The witness has boundary counts (3,2,0), so it refutes the universal drainage
claim tested on the cited census annuli, but not a separately strengthened
theorem restricted to good (3,1,1) boundary words.
"""

from __future__ import annotations

from collections import Counter, defaultdict
import json
from pathlib import Path


CERTIFICATE = Path(__file__).with_name("sector_alternation_depth3_certificate.json")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def components(vertices, adjacency):
    unseen = set(vertices)
    result = []
    while unseen:
        root = min(unseen)
        unseen.remove(root)
        todo = [root]
        component = {root}
        while todo:
            current = todo.pop()
            for neighbor in adjacency[current]:
                if neighbor in unseen:
                    unseen.remove(neighbor)
                    component.add(neighbor)
                    todo.append(neighbor)
        result.append(component)
    return result


def edge_components(edge_ids, edges):
    by_vertex = defaultdict(list)
    for edge_id in edge_ids:
        for vertex in edges[edge_id]:
            by_vertex[vertex].append(edge_id)
    adjacency = {edge_id: set() for edge_id in edge_ids}
    for incident in by_vertex.values():
        for edge_id in incident:
            adjacency[edge_id].update(set(incident) - {edge_id})
    return components(edge_ids, adjacency)


def main() -> None:
    data = json.loads(CERTIFICATE.read_text(encoding="utf-8"))
    vertex_count = data["vertices"]
    edges = [tuple(edge) for edge in data["edges"]]
    colors = data["colors"]
    inner_cap = data["inner_cap"]
    outer_cap = data["outer_cap"]
    cap_vertices = set(inner_cap) | set(outer_cap)
    rails = data["rails"]
    faces = data["annular_face_cells"]
    alpha = data["alpha_color"]

    require(isinstance(vertex_count, int) and vertex_count > 0, "bad vertex count")
    require(len(colors) == len(edges), "one color is required per edge")
    require(set(colors) <= {0, 1, 2}, "edge colors must lie in {0,1,2}")
    require(len(set(edges)) == len(edges), "duplicate oriented edges")
    require(
        len({frozenset(edge) for edge in edges}) == len(edges),
        "duplicate unoriented edges",
    )
    for edge_id, (left, right) in enumerate(edges):
        require(left != right, f"loop at edge {edge_id}")
        require(
            0 <= left < vertex_count and 0 <= right < vertex_count,
            f"edge {edge_id} has an out-of-range endpoint",
        )
    require(len(cap_vertices) == 10, "the two five-port boundaries must be disjoint")

    incident = defaultdict(list)
    edge_by_endpoints = {}
    for edge_id, (left, right) in enumerate(edges):
        incident[left].append(edge_id)
        incident[right].append(edge_id)
        edge_by_endpoints[frozenset((left, right))] = edge_id

    for vertex in range(vertex_count):
        degree = len(incident[vertex])
        expected_degree = 1 if vertex in cap_vertices else 3
        require(degree == expected_degree, f"vertex {vertex}: degree {degree}, expected {expected_degree}")
        local_colors = [colors[edge_id] for edge_id in incident[vertex]]
        require(
            len(local_colors) == len(set(local_colors)),
            f"Tait colors repeat at vertex {vertex}",
        )

    inner_spokes = [incident[vertex][0] for vertex in inner_cap]
    outer_spokes = [incident[vertex][0] for vertex in outer_cap]
    inner_colors = [colors[edge_id] for edge_id in inner_spokes]
    observed_counts = [inner_colors.count(color) for color in range(3)]
    require(observed_counts == data["scope"]["inner_word_counts"], "inner word counts disagree")
    require(data["scope"]["good_word"] is False, "this certificate must retain its bad-word scope")

    # A totally closed web contains every bichromatic component meeting the
    # inner boundary.  Every edge belongs to the two color pairs containing
    # its own color; both corresponding components must meet an inner spoke.
    inner_spoke_set = set(inner_spokes)
    closed_memberships = Counter()
    web_edges = set()
    component_summary = {}
    for first, second in ((0, 1), (0, 2), (1, 2)):
        pair_edges = {edge_id for edge_id, color in enumerate(colors) if color in (first, second)}
        pair_components = edge_components(pair_edges, edges)
        touching = [component for component in pair_components if component & inner_spoke_set]
        component_summary[(first, second)] = [len(component) for component in touching]
        for component in touching:
            web_edges.update(component)
            closed_memberships.update(component)
    require(web_edges == set(range(len(edges))), "the inner-generated web is not totally closed")
    require(
        all(closed_memberships[edge_id] == 2 for edge_id in web_edges),
        "an edge is missing one of its two inner-generated bichromatic components",
    )

    rail_vertices = set()
    rail_edge_ids = set()
    rail_position = {}
    for rail_id, rail in enumerate(rails):
        require(len(rail) == len(set(rail)), f"rail {rail_id} repeats a vertex")
        require(rail[0] in outer_cap and rail[-1] in inner_cap, f"rail {rail_id} has bad endpoints")
        require(not (rail_vertices & set(rail)), "rails share a vertex")
        rail_vertices.update(rail)
        for position, vertex in enumerate(rail):
            rail_position[vertex] = (rail_id, position)
        for left, right in zip(rail, rail[1:]):
            edge_id = edge_by_endpoints.get(frozenset((left, right)))
            require(edge_id is not None, f"rail {rail_id} uses a non-edge {left}-{right}")
            require(colors[edge_id] != alpha, f"rail {rail_id} uses alpha edge {edge_id}")
            rail_edge_ids.add(edge_id)
    require(
        rail_vertices - cap_vertices == set(range(vertex_count)) - cap_vertices,
        "the two rails do not cover exactly the internal vertices",
    )

    face_incidence = defaultdict(list)
    for face_id, boundary in enumerate(faces):
        require(len(boundary) >= 3, f"face {face_id} is too short")
        require(len(boundary) == len(set(boundary)), f"face {face_id} repeats an edge")
        for edge_id in boundary:
            require(0 <= edge_id < len(edges), f"face {face_id} cites bad edge {edge_id}")
            face_incidence[edge_id].append(face_id)
    require(set(face_incidence) == set(range(len(edges))), "face cells omit an edge")
    require(
        all(len(face_incidence[edge_id]) == 2 for edge_id in range(len(edges))),
        "each annular-map edge must border exactly two face cells",
    )

    dual = {face_id: set() for face_id in range(len(faces))}
    for edge_id, incident_faces in face_incidence.items():
        if edge_id not in rail_edge_ids:
            left, right = incident_faces
            dual[left].add(right)
            dual[right].add(left)
    sectors = components(range(len(faces)), dual)
    require(len(sectors) == 2, f"the rail complement has {len(sectors)} face sectors")
    sector_of_face = {
        face_id: sector_id
        for sector_id, sector in enumerate(sectors)
        for face_id in sector
    }
    for edge_id in rail_edge_ids:
        left, right = face_incidence[edge_id]
        require(
            sector_of_face[left] != sector_of_face[right],
            f"rail edge {edge_id} does not separate the two sectors",
        )

    chords = {}
    spokes = set(inner_spokes) | set(outer_spokes)
    for edge_id, (left, right) in enumerate(edges):
        if colors[edge_id] != alpha or edge_id in rail_edge_ids or edge_id in spokes:
            continue
        if left not in rail_position or right not in rail_position:
            continue
        left_rail, left_position = rail_position[left]
        right_rail, right_position = rail_position[right]
        if left_rail != right_rail:
            continue
        interval = tuple(sorted((left_position, right_position)))
        incident_sectors = {sector_of_face[face_id] for face_id in face_incidence[edge_id]}
        require(len(incident_sectors) == 1, f"chord {edge_id} does not lie in one sector")
        chords[edge_id] = (left_rail, interval, incident_sectors.pop())

    expected = data["expected_nested_chord_edges"]
    require(set(chords) == set(expected), "unexpected same-rail alpha chord set")
    outer, middle, inner = (chords[edge_id] for edge_id in expected)
    require(outer[0] == middle[0] == inner[0], "nested chords are not on one rail")
    require(outer[2] == middle[2] == inner[2], "nested chords are not in one sector")
    for enclosing, enclosed in ((outer, middle), (middle, inner)):
        require(
            enclosing[1][0] < enclosed[1][0] < enclosed[1][1] < enclosing[1][1],
            "expected chord intervals are not strictly nested",
        )

    failure = data["expected_drainage_failure"]
    outer_edge = failure["outer_chord_edge"]
    nested_edge = failure["nested_alpha_edge"]
    interior_vertex = failure["interior_vertex"]
    far_vertex = failure["far_vertex"]
    require(set(edges[nested_edge]) == {interior_vertex, far_vertex}, "bad drainage edge endpoints")
    require(colors[nested_edge] == alpha, "the nested drainage witness is not alpha-colored")
    rail_id, outer_interval, outer_sector = chords[outer_edge]
    for vertex in (interior_vertex, far_vertex):
        vertex_rail, position = rail_position[vertex]
        require(vertex_rail == rail_id, f"vertex {vertex} lies on the other rail")
        require(
            outer_interval[0] < position < outer_interval[1],
            f"vertex {vertex} is not strictly inside the outer chord interval",
        )
    require(chords[nested_edge][2] == outer_sector, "the drainage edge changes sector")

    print("PASS: proper cubic annular Tait coloring")
    print(f"PASS: totally closed web ({len(web_edges)} edges; component sizes {component_summary})")
    print(f"PASS: two vertex-disjoint rails and two face sectors ({len(rail_edge_ids)} separating rail edges)")
    print(f"PASS: same-sector chord nest {expected} has strict depth 3")
    print(
        "PASS: universal drainage fails: "
        f"edge {nested_edge} carries interior vertex {interior_vertex} to interior vertex {far_vertex}"
    )
    print("SCOPE: boundary counts are (3,2,0); this is not a good-word counterexample")


if __name__ == "__main__":
    main()
