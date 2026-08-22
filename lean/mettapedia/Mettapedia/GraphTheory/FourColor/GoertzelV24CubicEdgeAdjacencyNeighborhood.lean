import Mettapedia.GraphTheory.FourColor.RotationSystemEdgeColoring

/-!
# Bounded edge-adjacency neighborhoods in a cubic rotation system

An edge has two endpoints, and each endpoint of a cubic rotation system has
three incident edges.  Hence its edge-adjacency neighborhood has at most six
edges.  This deliberately loose bound is stable in the presence of parallel
edges and is sufficient for finite local transfer carriers.
-/

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

noncomputable section

namespace RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- The adjacent edges, represented directly inside the finite edge carrier.
This avoids requiring a separate local-finiteness instance for the graph. -/
def edgeAdjacencyFinset (RS : RotationSystem V E) (edge : E) : Finset E :=
  by
    classical
    exact Finset.univ.filter fun neighbor =>
      RS.edgeAdjacencyGraph.Adj edge neighbor

@[simp]
theorem mem_edgeAdjacencyFinset_iff
    (RS : RotationSystem V E) (edge neighbor : E) :
    neighbor ∈ RS.edgeAdjacencyFinset edge ↔
      RS.edgeAdjacencyGraph.Adj edge neighbor := by
  classical
  simp [edgeAdjacencyFinset]

/-- Every edge adjacent to `edge` is incident to one of its two endpoints. -/
theorem edgeAdjacencyFinset_subset_endpointIncidentEdges
    (RS : RotationSystem V E) (edge : E) :
    RS.edgeAdjacencyFinset edge ⊆
      (RS.endpoints edge).biUnion RS.incidentEdges := by
  intro neighbor hneighbor
  have hadj : RS.edgeAdjacencyGraph.Adj edge neighbor := by
    exact (RS.mem_edgeAdjacencyFinset_iff edge neighbor).1 hneighbor
  rcases (RS.edgeAdjacencyGraph_adj_iff).1 hadj with
    ⟨_ne, endpoint, hedge, hneighborEndpoint⟩
  apply Finset.mem_biUnion.2
  exact ⟨endpoint, hedge,
    (RS.mem_endpoints_iff_mem_incidentEdges).1 hneighborEndpoint⟩

/-- If every vertex has at most three incident edges, one edge has at most six
adjacent edges.  The loose endpoint-union bound is stable under parallel edges. -/
theorem edgeAdjacencyFinset_card_le_six_of_incidentEdges_card_le_three
    (RS : RotationSystem V E)
    (hdegree : ∀ vertex, (RS.incidentEdges vertex).card ≤ 3)
    (edge : E) :
    (RS.edgeAdjacencyFinset edge).card ≤ 6 := by
  calc
    (RS.edgeAdjacencyFinset edge).card ≤
        ((RS.endpoints edge).biUnion RS.incidentEdges).card :=
      Finset.card_le_card
        (RS.edgeAdjacencyFinset_subset_endpointIncidentEdges edge)
    _ ≤ (RS.endpoints edge).card * 3 := by
      apply Finset.card_biUnion_le_card_mul
      intro endpoint _hendpoint
      exact hdegree endpoint
    _ = 6 := by rw [RS.endpoints_card_two]

/-- A cubic edge has at most six adjacent edges.  The sharp bound is four;
six avoids choosing its endpoints and is all the finite-state use needs. -/
theorem edgeAdjacencyFinset_card_le_six
    (RS : RotationSystem V E) (hcubic : RS.IsCubic) (edge : E) :
    (RS.edgeAdjacencyFinset edge).card ≤ 6 := by
  exact RS.edgeAdjacencyFinset_card_le_six_of_incidentEdges_card_le_three
    (fun vertex => le_of_eq
      (RS.incidentEdges_card_eq_three_of_isCubic hcubic vertex)) edge

/-- A finite edge set together with every edge adjacent to it. -/
def edgeAdjacencyClosedCarrier
    (RS : RotationSystem V E) (boundary : Finset E) : Finset E :=
  boundary ∪ boundary.biUnion RS.edgeAdjacencyFinset

theorem mem_edgeAdjacencyClosedCarrier_iff
    (RS : RotationSystem V E) (boundary : Finset E) (edge : E) :
    edge ∈ RS.edgeAdjacencyClosedCarrier boundary ↔
      edge ∈ boundary ∨
        ∃ boundaryEdge ∈ boundary,
          RS.edgeAdjacencyGraph.Adj edge boundaryEdge := by
  simp only [edgeAdjacencyClosedCarrier, Finset.mem_union,
    Finset.mem_biUnion, mem_edgeAdjacencyFinset_iff]
  constructor
  · rintro (hedge | ⟨boundaryEdge, hboundary, hadj⟩)
    · exact Or.inl hedge
    · exact Or.inr ⟨boundaryEdge, hboundary, hadj.symm⟩
  · rintro (hedge | ⟨boundaryEdge, hboundary, hadj⟩)
    · exact Or.inl hedge
    · exact Or.inr ⟨boundaryEdge, hboundary, hadj.symm⟩

/-- Under a uniform incident-edge bound of three, the closed edge-adjacency
carrier has at most seven times the number of boundary edges. -/
theorem edgeAdjacencyClosedCarrier_card_le_seven_mul_of_incidentEdges_card_le_three
    (RS : RotationSystem V E)
    (hdegree : ∀ vertex, (RS.incidentEdges vertex).card ≤ 3)
    (boundary : Finset E) :
    (RS.edgeAdjacencyClosedCarrier boundary).card ≤ 7 * boundary.card := by
  calc
    (RS.edgeAdjacencyClosedCarrier boundary).card ≤
        boundary.card +
          (boundary.biUnion RS.edgeAdjacencyFinset).card := by
      exact Finset.card_union_le _ _
    _ ≤ boundary.card + boundary.card * 6 := by
      exact Nat.add_le_add_left
        (Finset.card_biUnion_le_card_mul _ _ _ fun edge _hedge =>
          RS.edgeAdjacencyFinset_card_le_six_of_incidentEdges_card_le_three
            hdegree edge)
        boundary.card
    _ = 7 * boundary.card := by omega

/-- The closed edge-adjacency carrier of a cubic boundary has at most seven
times the number of boundary edges. -/
theorem edgeAdjacencyClosedCarrier_card_le_seven_mul
    (RS : RotationSystem V E) (hcubic : RS.IsCubic) (boundary : Finset E) :
    (RS.edgeAdjacencyClosedCarrier boundary).card ≤ 7 * boundary.card := by
  exact
    RS.edgeAdjacencyClosedCarrier_card_le_seven_mul_of_incidentEdges_card_le_three
      (fun vertex => le_of_eq
        (RS.incidentEdges_card_eq_three_of_isCubic hcubic vertex)) boundary

end RotationSystem

end

end Mettapedia.GraphTheory.FourColor
