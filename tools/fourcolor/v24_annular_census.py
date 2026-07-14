#!/usr/bin/env python3
"""Independent, resumable C30/C40 annular Tait-coloring census.

The construction and search in this file do not import the v24 reference
toolchain.  Each root-color shard is written atomically and can be resumed.
The merged certificate contains enough graph and search metadata for a second
implementation, and eventually Lean, to replay the finite computation.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, Iterable


SHARD_SCHEMA = "fourcolor-v24-annular-tait-census-shard-v1"
MERGED_SCHEMA = "fourcolor-v24-annular-tait-census-v1"
COLOR_COUNT = 3
COLOR_MASK = (1 << COLOR_COUNT) - 1
DIGEST_MODULUS = 1 << 256


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Reproduce the v24 C30/C40 annular Tait-coloring censuses."
    )
    parser.add_argument(
        "--graph", choices=("C30", "C40", "all"), default="all"
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("results/fourcolor/v24_annular_census"),
    )
    parser.add_argument(
        "--shard-color",
        type=int,
        choices=range(COLOR_COUNT),
        help="Run only the shard fixing the first tangle edge to this color.",
    )
    parser.add_argument(
        "--force", action="store_true", help="Recompute valid existing shards."
    )
    return parser.parse_args()


def atomic_write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    with tmp.open("w", encoding="utf-8") as handle:
        json.dump(payload, handle, indent=2, sort_keys=True)
        handle.write("\n")
    tmp.replace(path)


def load_json(path: Path) -> dict[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        value = json.load(handle)
    if not isinstance(value, dict):
        raise ValueError(f"certificate is not an object: {path}")
    return value


def canonical_hash(value: Any) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def tube_dual_triangles(hexagon_rings: int) -> tuple[list[tuple[int, int, int]], int]:
    """Triangulated dual of the (5,0) tube with one or two hexagon rings."""
    if hexagon_rings not in (1, 2):
        raise ValueError("the v24 census uses one or two hexagon rings")

    next_vertex = 0

    def allocate_ring() -> list[int]:
        nonlocal next_vertex
        ring = list(range(next_vertex, next_vertex + 5))
        next_vertex += 5
        return ring

    north = next_vertex
    next_vertex += 1
    south = next_vertex
    next_vertex += 1
    top = allocate_ring()
    middle = [allocate_ring() for _ in range(hexagon_rings)]
    bottom = allocate_ring()

    triangles: list[tuple[int, int, int]] = []
    for i in range(5):
        triangles.append(tuple(sorted((north, top[i], top[(i + 1) % 5]))))
        triangles.append(tuple(sorted((south, bottom[i], bottom[(i + 1) % 5]))))

    rings = [top, *middle, bottom]
    for upper, lower in zip(rings, rings[1:]):
        for i in range(5):
            triangles.append(
                tuple(sorted((upper[i], lower[i], lower[(i + 1) % 5])))
            )
            triangles.append(
                tuple(sorted((upper[i], upper[(i + 1) % 5], lower[(i + 1) % 5])))
            )

    triangles.sort()
    if len(set(triangles)) != len(triangles):
        raise AssertionError("dual triangulation contains a repeated triangle")
    if len(triangles) != 2 * next_vertex - 4:
        raise AssertionError("dual triangulation violates the spherical face count")
    return triangles, next_vertex


def triangle_edges(triangle: tuple[int, int, int]) -> Iterable[tuple[int, int]]:
    a, b, c = triangle
    yield (a, b)
    yield (a, c)
    yield (b, c)


def dualize_triangulation(
    triangles: list[tuple[int, int, int]], dual_vertex_count: int
) -> tuple[list[tuple[int, int]], list[list[int]]]:
    """Return the cubic primal graph whose vertices are dual triangles."""
    incident: dict[tuple[int, int], list[int]] = defaultdict(list)
    for triangle_index, triangle in enumerate(triangles):
        for edge in triangle_edges(triangle):
            incident[edge].append(triangle_index)

    expected_dual_edges = 3 * dual_vertex_count - 6
    if len(incident) != expected_dual_edges:
        raise AssertionError("dual edge count does not match a sphere triangulation")
    if any(len(adjacent) != 2 for adjacent in incident.values()):
        raise AssertionError("the dual triangulation is not closed")

    primal_edges = sorted(tuple(sorted(adjacent)) for adjacent in incident.values())
    if len(set(primal_edges)) != len(primal_edges):
        raise AssertionError("dualization produced parallel primal edges")

    neighbors = [[] for _ in triangles]
    for u, v in primal_edges:
        neighbors[u].append(v)
        neighbors[v].append(u)
    for adjacent in neighbors:
        adjacent.sort()
    if any(len(adjacent) != 3 for adjacent in neighbors):
        raise AssertionError("dualization did not produce a cubic graph")
    return primal_edges, neighbors


def induced_cycle_order(face_vertices: set[int], neighbors: list[list[int]]) -> list[int]:
    face_neighbors = {
        vertex: sorted(set(neighbors[vertex]) & face_vertices)
        for vertex in face_vertices
    }
    if any(len(adjacent) != 2 for adjacent in face_neighbors.values()):
        raise AssertionError("a pole face is not an induced cycle")

    start = min(face_vertices)
    previous = start
    current = face_neighbors[start][0]
    order = [start]
    while current != start:
        if current in order:
            raise AssertionError("pole face traversal repeated a vertex")
        order.append(current)
        choices = [vertex for vertex in face_neighbors[current] if vertex != previous]
        if len(choices) != 1:
            raise AssertionError("pole face traversal is not deterministic")
        previous, current = current, choices[0]
    if set(order) != face_vertices:
        raise AssertionError("pole face traversal did not cover the face")
    return order


def make_instance(name: str) -> dict[str, Any]:
    hexagon_rings = {"C30": 1, "C40": 2}[name]
    triangles, dual_vertex_count = tube_dual_triangles(hexagon_rings)
    primal_edges, neighbors = dualize_triangulation(triangles, dual_vertex_count)

    north_face = {i for i, triangle in enumerate(triangles) if 0 in triangle}
    south_face = {i for i, triangle in enumerate(triangles) if 1 in triangle}
    if len(north_face) != 5 or len(south_face) != 5 or north_face & south_face:
        raise AssertionError("the distinguished pole pentagons are invalid")

    outer_order = induced_cycle_order(north_face, neighbors)
    inner_order = induced_cycle_order(south_face, neighbors)
    removed = {
        edge
        for edge in primal_edges
        if (edge[0] in north_face and edge[1] in north_face)
        or (edge[0] in south_face and edge[1] in south_face)
    }
    if len(removed) != 10:
        raise AssertionError("cutting the two pole pentagons did not remove ten edges")
    tangle_edges = [edge for edge in primal_edges if edge not in removed]

    incident_edges = [[] for _ in triangles]
    for edge_index, (u, v) in enumerate(tangle_edges):
        incident_edges[u].append(edge_index)
        incident_edges[v].append(edge_index)

    def spokes(face_order: list[int]) -> list[int]:
        result = []
        for vertex in face_order:
            if len(incident_edges[vertex]) != 1:
                raise AssertionError("a cut-open pole vertex does not have one spoke")
            result.append(incident_edges[vertex][0])
        return result

    outer_spokes = spokes(outer_order)
    inner_spokes = spokes(inner_order)
    graph_payload = {
        "name": name,
        "hexagon_rings": hexagon_rings,
        "dual_vertex_count": dual_vertex_count,
        "dual_triangles": [list(triangle) for triangle in triangles],
        "primal_edges": [list(edge) for edge in primal_edges],
        "outer_face_vertices": outer_order,
        "inner_face_vertices": inner_order,
        "removed_face_edges": [list(edge) for edge in sorted(removed)],
        "tangle_edges": [list(edge) for edge in tangle_edges],
        "outer_spokes": outer_spokes,
        "inner_spokes": inner_spokes,
    }
    return {
        **graph_payload,
        "graph_hash": canonical_hash(graph_payload),
        "incident_edges": incident_edges,
    }


class CensusSearch:
    def __init__(
        self, instance: dict[str, Any], root_color: int, collect_solutions: bool = False
    ):
        self.instance = instance
        self.edges = [tuple(edge) for edge in instance["tangle_edges"]]
        self.incident_edges = instance["incident_edges"]
        self.outer_spokes = instance["outer_spokes"]
        self.inner_spokes = instance["inner_spokes"]
        self.colors = [-1] * len(self.edges)
        self.used_masks = [0] * len(self.incident_edges)
        self.solution_count = 0
        self.search_node_count = 0
        self.dead_end_count = 0
        self.boundary_histogram: Counter[str] = Counter()
        self.digest_sum = 0
        self.digest_xor = 0
        self.solutions: list[bytes] | None = [] if collect_solutions else None
        self.assign(0, root_color)

    def domain_mask(self, edge_index: int) -> int:
        u, v = self.edges[edge_index]
        return COLOR_MASK & ~(self.used_masks[u] | self.used_masks[v])

    def assign(self, edge_index: int, color: int) -> None:
        if not (self.domain_mask(edge_index) & (1 << color)):
            raise AssertionError("attempted an illegal edge color")
        u, v = self.edges[edge_index]
        self.colors[edge_index] = color
        self.used_masks[u] |= 1 << color
        self.used_masks[v] |= 1 << color

    def unassign(self, edge_index: int, color: int) -> None:
        u, v = self.edges[edge_index]
        self.colors[edge_index] = -1
        self.used_masks[u] ^= 1 << color
        self.used_masks[v] ^= 1 << color

    def choose_edge(self) -> tuple[int | None, int]:
        best_edge: int | None = None
        best_mask = 0
        best_size = COLOR_COUNT + 1
        for edge_index, color in enumerate(self.colors):
            if color != -1:
                continue
            mask = self.domain_mask(edge_index)
            size = mask.bit_count()
            if size < best_size:
                best_edge, best_mask, best_size = edge_index, mask, size
                if size == 0:
                    break
        return best_edge, best_mask

    def record_solution(self) -> None:
        for incident in self.incident_edges:
            assigned = [self.colors[edge] for edge in incident]
            if len(assigned) != len(set(assigned)):
                raise AssertionError("search emitted an improper edge coloring")
        outer = "".join(str(self.colors[edge]) for edge in self.outer_spokes)
        inner = "".join(str(self.colors[edge]) for edge in self.inner_spokes)
        self.boundary_histogram[f"{outer}|{inner}"] += 1
        solution = bytes(self.colors)
        digest = int.from_bytes(hashlib.sha256(solution).digest(), "big")
        self.digest_sum = (self.digest_sum + digest) % DIGEST_MODULUS
        self.digest_xor ^= digest
        if self.solutions is not None:
            self.solutions.append(solution)
        self.solution_count += 1

    def search(self) -> None:
        self.search_node_count += 1
        edge_index, mask = self.choose_edge()
        if edge_index is None:
            self.record_solution()
            return
        if mask == 0:
            self.dead_end_count += 1
            return
        for color in range(COLOR_COUNT):
            if mask & (1 << color):
                self.assign(edge_index, color)
                self.search()
                self.unassign(edge_index, color)

    def certificate(self, root_color: int) -> dict[str, Any]:
        self.search()
        return {
            "schema": SHARD_SCHEMA,
            "algorithm": "deterministic-mrv-exhaustive-edge-coloring-v1",
            "graph": self.instance["name"],
            "graph_hash": self.instance["graph_hash"],
            "root_edge_index": 0,
            "root_edge": self.instance["tangle_edges"][0],
            "root_color": root_color,
            "color_count": COLOR_COUNT,
            "solution_count": self.solution_count,
            "search_node_count": self.search_node_count,
            "dead_end_count": self.dead_end_count,
            "boundary_pair_count": len(self.boundary_histogram),
            "boundary_pair_histogram": dict(sorted(self.boundary_histogram.items())),
            "solution_digest_sum": f"{self.digest_sum:064x}",
            "solution_digest_xor": f"{self.digest_xor:064x}",
        }


def shard_path(output_dir: Path, graph: str, color: int) -> Path:
    return output_dir / f"{graph.lower()}_root_color_{color}.json"


def shard_is_reusable(
    certificate: dict[str, Any], instance: dict[str, Any], color: int
) -> bool:
    histogram = certificate.get("boundary_pair_histogram")
    if not isinstance(histogram, dict):
        return False
    try:
        solution_count = int(certificate["solution_count"])
        histogram_total = sum(int(count) for count in histogram.values())
        boundary_pair_count = int(certificate["boundary_pair_count"])
    except (KeyError, TypeError, ValueError):
        return False
    digests = (
        certificate.get("solution_digest_sum"),
        certificate.get("solution_digest_xor"),
    )
    digests_valid = all(
        isinstance(digest, str)
        and len(digest) == 64
        and all(character in "0123456789abcdef" for character in digest)
        for digest in digests
    )
    return (
        certificate.get("schema") == SHARD_SCHEMA
        and certificate.get("algorithm")
        == "deterministic-mrv-exhaustive-edge-coloring-v1"
        and certificate.get("graph") == instance["name"]
        and certificate.get("graph_hash") == instance["graph_hash"]
        and certificate.get("root_edge_index") == 0
        and certificate.get("root_edge") == instance["tangle_edges"][0]
        and certificate.get("root_color") == color
        and certificate.get("color_count") == COLOR_COUNT
        and solution_count >= 0
        and histogram_total == solution_count
        and boundary_pair_count == len(histogram)
        and digests_valid
    )


def run_shard(
    instance: dict[str, Any], color: int, output_dir: Path, force: bool
) -> dict[str, Any]:
    path = shard_path(output_dir, instance["name"], color)
    if path.exists() and not force:
        existing = load_json(path)
        if shard_is_reusable(existing, instance, color):
            return existing
    certificate = CensusSearch(instance, color).certificate(color)
    atomic_write_json(path, certificate)
    return certificate


def merge_shards(
    instance: dict[str, Any], shards: list[dict[str, Any]]
) -> dict[str, Any]:
    colors = sorted(int(shard["root_color"]) for shard in shards)
    if colors != list(range(COLOR_COUNT)):
        raise ValueError("a merged census requires exactly the three root-color shards")
    if any(
        not shard_is_reusable(shard, instance, int(shard["root_color"]))
        for shard in shards
    ):
        raise ValueError("shard metadata does not match the graph instance")

    histogram: Counter[str] = Counter()
    for shard in shards:
        histogram.update(
            {key: int(value) for key, value in shard["boundary_pair_histogram"].items()}
        )
    digest_sum = sum(int(shard["solution_digest_sum"], 16) for shard in shards)
    digest_xor = 0
    for shard in shards:
        digest_xor ^= int(shard["solution_digest_xor"], 16)
    root_counts = {
        str(shard["root_color"]): int(shard["solution_count"])
        for shard in sorted(shards, key=lambda item: int(item["root_color"]))
    }
    graph_fields = {
        key: value
        for key, value in instance.items()
        if key != "incident_edges"
    }
    return {
        "schema": MERGED_SCHEMA,
        "algorithm": "deterministic-mrv-exhaustive-edge-coloring-v1",
        "graph": graph_fields,
        "root_color_solution_counts": root_counts,
        "root_color_counts_equal": len(set(root_counts.values())) == 1,
        "solution_count": sum(root_counts.values()),
        "search_node_count": sum(int(shard["search_node_count"]) for shard in shards),
        "dead_end_count": sum(int(shard["dead_end_count"]) for shard in shards),
        "boundary_pair_count": len(histogram),
        "boundary_pair_histogram": dict(sorted(histogram.items())),
        "solution_digest_sum": f"{digest_sum % DIGEST_MODULUS:064x}",
        "solution_digest_xor": f"{digest_xor:064x}",
        "shard_files": [
            shard_path(Path("."), instance["name"], color).name
            for color in range(COLOR_COUNT)
        ],
    }


def run_graph(
    name: str, output_dir: Path, only_color: int | None, force: bool
) -> dict[str, Any] | None:
    instance = make_instance(name)
    colors = [only_color] if only_color is not None else list(range(COLOR_COUNT))
    shards = [run_shard(instance, color, output_dir, force) for color in colors]
    for shard in shards:
        print(
            f"{name} root color {shard['root_color']}: "
            f"{shard['solution_count']} colorings"
        )
    if only_color is not None:
        return None
    merged = merge_shards(instance, shards)
    merged_path = output_dir / f"{name.lower()}_annular_census.json"
    atomic_write_json(merged_path, merged)
    print(
        f"{name}: {merged['solution_count']} colorings; "
        f"certificate {merged_path}"
    )
    return merged


def main() -> int:
    args = parse_args()
    names = ("C30", "C40") if args.graph == "all" else (args.graph,)
    for name in names:
        run_graph(name, args.output_dir, args.shard_color, args.force)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
