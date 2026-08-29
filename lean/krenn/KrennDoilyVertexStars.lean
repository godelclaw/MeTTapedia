import KrennDoilyPotential
import Mathlib

/-!
Uniform vertex-star endpoints for the K6 doily potential criterion.

For every vertex, the five incident `P`-kills are enough to contradict the
monochromatic normalization.  This is the reusable endpoint needed by a
non-collapse harvest argument: an adjugate slot already supplies two of the
five incident kills, and a balanced-layer lemma need only supply the other
three.
-/

namespace Krenn.DoilyVertexStars

open Krenn.DoilyPotential

universe u

/-- The five edge indices incident to a vertex in the fixed lexicographic
K6 edge order used by `KrennDoilyPotential`. -/
def vertexStarEdges : Fin 6 → Finset (Fin 15) := ![
  {0, 1, 2, 3, 4},
  {0, 5, 6, 7, 8},
  {1, 5, 9, 10, 11},
  {2, 6, 9, 12, 13},
  {3, 7, 10, 12, 14},
  {4, 8, 11, 13, 14}
]

/-- The vertex potential concentrated at one vertex. -/
def vertexStarPotential {R : Type u} [Zero R] [One R]
    (vertex : Fin 6) : Fin 6 → R :=
  fun other => if other = vertex then 1 else 0

/-- A nonzero coefficient of a vertex-star potential occurs only on an
incident edge. -/
theorem edgePotential_nonzero_implies_vertexStar
    {R : Type u} [CommRing R] [Nontrivial R]
    (vertex : Fin 6) (edge : Fin 15) :
    edgePotential (vertexStarPotential (R := R) vertex) edge ≠ 0 →
      edge ∈ vertexStarEdges vertex := by
  intro nonzero
  fin_cases vertex <;> fin_cases edge <;>
    simp [edgePotential, vertexStarPotential, vertexStarEdges] at nonzero ⊢

/-- The concentrated potential has total coefficient one. -/
theorem totalPotential_vertexStar
    {R : Type u} [CommRing R] (vertex : Fin 6) :
    totalPotential (vertexStarPotential (R := R) vertex) = 1 := by
  fin_cases vertex <;>
    simp [totalPotential, vertexStarPotential]

/-- All five incident diagonal co-sum kills at any vertex contradict a
normalized diagonal K6 witness. -/
theorem no_normalized_diagonal_witness_of_vertex_star_kills
    {R : Type u} [CommRing R] [Nontrivial R]
    (vertex : Fin 6) (diagonal : Fin 15 → R)
    (kills : ∀ edge, edge ∈ vertexStarEdges vertex → coSum diagonal edge = 0)
    (mono : totalMatching (matchingProduct diagonal) = 1) : False := by
  refine no_normalized_diagonal_witness_of_potential_kills
    (vertexStarPotential (R := R) vertex) diagonal ?_
    (totalPotential_vertexStar (R := R) vertex) mono
  intro edge nonzero
  exact kills edge
    (edgePotential_nonzero_implies_vertexStar (R := R) vertex edge nonzero)

#print axioms Krenn.DoilyVertexStars.edgePotential_nonzero_implies_vertexStar
#print axioms Krenn.DoilyVertexStars.totalPotential_vertexStar
#print axioms Krenn.DoilyVertexStars.no_normalized_diagonal_witness_of_vertex_star_kills

end Krenn.DoilyVertexStars
