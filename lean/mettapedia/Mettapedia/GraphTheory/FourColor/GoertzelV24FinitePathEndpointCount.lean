import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Endpoint count in a finite path-like component

A finite connected graph in which every vertex has degree one or two, and at
least one vertex has degree one, has exactly two degree-one vertices.  This is
the graph-theoretic counting core of the statement that a bichromatic Kempe
component meeting an open boundary is a two-ended strand.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FinitePathEndpointCount

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Degree-one vertices of a finite graph. -/
def degreeOneVertices : Finset V :=
  Finset.univ.filter fun vertex => G.degree vertex = 1

omit [DecidableEq V] in
@[simp] theorem mem_degreeOneVertices_iff (vertex : V) :
    vertex ∈ degreeOneVertices G ↔ G.degree vertex = 1 := by
  simp [degreeOneVertices]

omit [DecidableEq V] in
/-- **Finite path endpoint count.**  Connectivity and the degree set
`{1,2}` force exactly two endpoints as soon as one endpoint exists. -/
theorem card_degreeOneVertices_eq_two
    (hconnected : G.Connected)
    (hdegree : ∀ vertex : V,
      G.degree vertex = 1 ∨ G.degree vertex = 2)
    (root : V) (hroot : G.degree root = 1) :
    (degreeOneVertices G).card = 2 := by
  classical
  let endpoints := degreeOneVertices G
  have hpoint (vertex : V) :
      G.degree vertex + (if G.degree vertex = 1 then 1 else 0) = 2 := by
    rcases hdegree vertex with hone | htwo
    · simp [hone]
    · simp [htwo]
  have hsum :
      (∑ vertex : V, G.degree vertex) + endpoints.card =
        2 * Fintype.card V := by
    calc
      (∑ vertex : V, G.degree vertex) + endpoints.card =
          (∑ vertex : V, G.degree vertex) +
            ∑ vertex : V, if G.degree vertex = 1 then 1 else 0 := by
              congr 1
              simp [endpoints, degreeOneVertices]
      _ = ∑ vertex : V,
          (G.degree vertex +
            (if G.degree vertex = 1 then 1 else 0)) := by
              rw [Finset.sum_add_distrib]
      _ = ∑ _vertex : V, 2 := by
              apply Finset.sum_congr rfl
              intro vertex _
              exact hpoint vertex
      _ = 2 * Fintype.card V := by simp [Nat.mul_comm]
  have hedgeCount :
      2 * G.edgeFinset.card + endpoints.card =
        2 * Fintype.card V := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    exact hsum
  have hconnectedCount :
      Fintype.card V ≤ G.edgeFinset.card + 1 := by
    simpa [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card] using
      hconnected.card_vert_le_card_edgeSet_add_one
  have hendpointsLe : endpoints.card ≤ 2 := by omega
  have hrootMem : root ∈ endpoints := by
    exact (mem_degreeOneVertices_iff G root).2 hroot
  have hendpointsPos : 0 < endpoints.card :=
    Finset.card_pos.mpr ⟨root, hrootMem⟩
  have hoddIff (vertex : V) :
      Odd (G.degree vertex) ↔ G.degree vertex = 1 := by
    rcases hdegree vertex with hone | htwo
    · simp [hone]
    · simp [htwo]
  have heven : Even endpoints.card := by
    have hhandshake := G.even_card_odd_degree_vertices
    simp_rw [hoddIff] at hhandshake
    simpa [endpoints, degreeOneVertices] using hhandshake
  have hnotOne : endpoints.card ≠ 1 := by
    intro hone
    apply Nat.not_even_one
    rwa [← hone]
  have hcases :
      endpoints.card = 0 ∨ endpoints.card = 1 ∨ endpoints.card = 2 := by
    omega
  rcases hcases with hzero | hone | htwo
  · exact False.elim ((Nat.ne_of_gt hendpointsPos) hzero)
  · exact False.elim (hnotOne hone)
  · exact htwo

end GoertzelV24FinitePathEndpointCount

end Mettapedia.GraphTheory.FourColor
