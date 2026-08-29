#!/usr/bin/env python3
"""Generate a small Lean proof of the K6 doily potential criterion.

The generator obtains the 15 perfect matchings from the canonical local
enumerator, verifies the incidence regularity, and serializes the resulting
three-term line sums.  Lean proves the only algebraic identity by `ring`.
"""

from __future__ import annotations

import os
import argparse
import hashlib
import sys
from pathlib import Path


SHARED = Path(os.environ.get("KRENN_ARTIFACTS", "artifacts"))
if str(SHARED) not in sys.path:
    sys.path.insert(0, str(SHARED))

from krenn_exact import perfect_matchings  # noqa: E402


def sha(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def vector(lines: list[str]) -> str:
    return "![\n" + ",\n".join("  " + line for line in lines) + "\n]"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    vertices = tuple(range(6))
    edges = tuple((left, right) for left in vertices for right in vertices
                  if left < right)
    edge_index = {edge: index for index, edge in enumerate(edges)}
    matchings = tuple(tuple(sorted(edge_index[tuple(sorted(edge))]
                                   for edge in matching))
                      for matching in perfect_matchings(6))
    if len(edges) != 15 or len(matchings) != 15:
        raise ValueError("K6 edge or perfect-matching census drift")
    if any(len(matching) != 3 for matching in matchings):
        raise ValueError("non-three-edge perfect matching")
    lines_for_edge = [
        [matching_index for matching_index, matching in enumerate(matchings)
         if edge_index in matching]
        for edge_index in range(15)
    ]
    if any(len(line) != 3 for line in lines_for_edge):
        raise ValueError("PM-edge incidence regularity drift")
    if any(sum(edge in matching for edge in range(15)) != 3
           for matching in matchings):
        raise ValueError("matching incidence drift")

    edge_potentials = [f"s {left} + s {right}" for left, right in edges]
    line_sums = [" + ".join(f"m {matching}" for matching in line)
                 for line in lines_for_edge]
    matching_products = [" * ".join(f"d {edge}" for edge in matching)
                         for matching in matchings]
    co_sums = [
        " + ".join(
            " * ".join(f"d {other}" for other in matchings[matching_index]
                       if other != edge)
            for matching_index in line
        )
        for edge, line in enumerate(lines_for_edge)
    ]
    total_s = " + ".join(f"s {vertex}" for vertex in vertices)
    total_m = " + ".join(f"m {matching}" for matching in range(15))
    source = [
        "import Mathlib",
        "",
        "/-!",
        "The finite K6 doily potential criterion.",
        "",
        "A `lineSum` is the sum of the three perfect-matching products through",
        "an edge.  A vertex potential assigns `s u + s v` to edge `{u,v}`.",
        "Double-counting a matching's three edges gives the identity below.",
        "It turns P-kills supported on a nonzero-mean potential into a direct",
        "contradiction with monochromatic normalization.",
        "-/",
        "",
        "namespace Krenn.DoilyPotential",
        "",
        "open BigOperators",
        "",
        "/-- The fifteen edge coefficients induced by six vertex potentials. -/",
        "def edgePotential {R : Type*} [AddCommMonoid R]",
        "    (s : Fin 6 → R) : Fin 15 → R := " + vector(edge_potentials),
        "",
        "/-- The three matching products through each of the fifteen K6 edges. -/",
        "def lineSum {R : Type*} [AddCommMonoid R]",
        "    (m : Fin 15 → R) : Fin 15 → R := " + vector(line_sums),
        "",
        "/-- The product of the three diagonal edge weights in each matching. -/",
        "def matchingProduct {R : Type*} [CommMonoid R]",
        "    (d : Fin 15 → R) : Fin 15 → R := " + vector(matching_products),
        "",
        "/-- The K4 diagonal co-sum `P^(e)` at every K6 edge. -/",
        "def coSum {R : Type*} [CommSemiring R]",
        "    (d : Fin 15 → R) : Fin 15 → R := " + vector(co_sums),
        "",
        "def totalPotential {R : Type*} [AddCommMonoid R] (s : Fin 6 → R) : R :=",
        "  " + total_s,
        "",
        "def totalMatching {R : Type*} [AddCommMonoid R] (m : Fin 15 → R) : R :=",
        "  " + total_m,
        "",
        "def potentialLineTotal {R : Type*} [CommRing R]",
        "    (s : Fin 6 → R) (m : Fin 15 → R) : R :=",
        "  ∑ edge, edgePotential s edge * lineSum m edge",
        "",
        "set_option maxRecDepth 100000 in",
        "/-- Exact K6 perfect-matching/edge double count. -/",
        "theorem potential_line_identity {R : Type*} [CommRing R]",
        "    (s : Fin 6 → R) (m : Fin 15 → R) :",
        "    potentialLineTotal s m = totalPotential s * totalMatching m := by",
        "  simp [potentialLineTotal, edgePotential, lineSum, totalPotential,",
        "    totalMatching, Fin.sum_univ_succ]",
        "  ring",
        "",
        "/-- The exact diagonal deflation identity `D_e * P^(e) =",
        "sum_{M contains e} m_M`, checked for all fifteen K6 edges. -/",
        "theorem lineSum_factor {R : Type*} [CommRing R]",
        "    (d : Fin 15 → R) (edge : Fin 15) :",
        "    lineSum (matchingProduct d) edge = d edge * coSum d edge := by",
        "  fin_cases edge <;> simp [lineSum, matchingProduct, coSum] <;> ring",
        "",
        "/-- If every edge carrying a nonzero vertex potential has a dead P-line,",
        "then the total matching product is annihilated by the potential sum. -/",
        "theorem potential_kills_force_total_zero {R : Type*} [CommRing R]",
        "    (s : Fin 6 → R) (diagonal p m : Fin 15 → R)",
        "    (hfactor : ∀ edge, lineSum m edge = diagonal edge * p edge)",
        "    (hdead : ∀ edge, edgePotential s edge ≠ 0 → p edge = 0) :",
        "    totalPotential s * totalMatching m = 0 := by",
        "  rw [← potential_line_identity]",
        "  unfold potentialLineTotal",
        "  apply Finset.sum_eq_zero",
        "  intro edge _",
        "  rw [hfactor edge]",
        "  by_cases hpotential : edgePotential s edge = 0",
        "  · simp [hpotential]",
        "  · rw [hdead edge hpotential]",
        "    ring",
        "",
        "/-- The usable contradiction form: a mean-one potential supported on",
        "P-kills is incompatible with monochromatic normalization. -/",
        "theorem no_normalized_witness_of_potential_kills",
        "    {R : Type*} [CommRing R] [Nontrivial R]",
        "    (s : Fin 6 → R) (diagonal p m : Fin 15 → R)",
        "    (hfactor : ∀ edge, lineSum m edge = diagonal edge * p edge)",
        "    (hdead : ∀ edge, edgePotential s edge ≠ 0 → p edge = 0)",
        "    (hpotential : totalPotential s = 1)",
        "    (hmono : totalMatching m = 1) : False := by",
        "  have hzero := potential_kills_force_total_zero s diagonal p m hfactor hdead",
        "  rw [hpotential, hmono] at hzero",
        "  have honezero : (1 : R) = 0 := by simpa only [one_mul] using hzero",
        "  exact one_ne_zero honezero",
        "",
        "/-- Fully diagonal-specialized form of the potential criterion. -/",
        "theorem no_normalized_diagonal_witness_of_potential_kills",
        "    {R : Type*} [CommRing R] [Nontrivial R]",
        "    (s : Fin 6 → R) (d : Fin 15 → R)",
        "    (hdead : ∀ edge, edgePotential s edge ≠ 0 → coSum d edge = 0)",
        "    (hpotential : totalPotential s = 1)",
        "    (hmono : totalMatching (matchingProduct d) = 1) : False := by",
        "  exact no_normalized_witness_of_potential_kills",
        "    s d (coSum d) (matchingProduct d) (lineSum_factor d) hdead",
        "    hpotential hmono",
        "",
        "#print axioms Krenn.DoilyPotential.potential_line_identity",
        "#print axioms Krenn.DoilyPotential.lineSum_factor",
        "#print axioms Krenn.DoilyPotential.no_normalized_witness_of_potential_kills",
        "#print axioms Krenn.DoilyPotential.no_normalized_diagonal_witness_of_potential_kills",
        "",
        "end Krenn.DoilyPotential",
        "",
    ]
    rendered = "\n".join(source)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(rendered, encoding="utf-8")
    print(
        "{" + f'"edges":15,"matchings":15,"output_sha256":"{sha(rendered)}"' + "}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
