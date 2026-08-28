import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationCycleSpace

/-!
# Walk parity on a rotation-system multigraph

A walk in the computed primal simple graph remembers only its consecutive
vertices.  When the rotation system has parallel edges, each step is therefore
lifted to one chosen literal dart witnessing that adjacency.  The resulting
literal-edge parity vector still has incidence boundary equal to the two walk
endpoints.  This is the exact multigraph replacement for the graph-backed walk
lemma used by the Tait potential.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationWalkCycleParity

open GoertzelV24FaceDualConnectedness
open GoertzelV24RotationCycleSpace
open SimpleGraph

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- A literal dart witnessing one adjacency of the computed primal graph. -/
def adjacencyDart (RS : RotationSystem V E) {left right : V}
    (hadj : (rotationPrimalGraph RS).Adj left right) : RS.D :=
  Classical.choose ((rotationPrimalGraph_adj_iff RS).1 hadj)

theorem adjacencyDart_left (RS : RotationSystem V E) {left right : V}
    (hadj : (rotationPrimalGraph RS).Adj left right) :
    RS.vertOf (adjacencyDart RS hadj) = left :=
  (Classical.choose_spec ((rotationPrimalGraph_adj_iff RS).1 hadj)).1

theorem adjacencyDart_right (RS : RotationSystem V E) {left right : V}
    (hadj : (rotationPrimalGraph RS).Adj left right) :
    RS.vertOf (RS.alpha (adjacencyDart RS hadj)) = right :=
  (Classical.choose_spec ((rotationPrimalGraph_adj_iff RS).1 hadj)).2

/-- The literal edge chosen for one primal-graph step. -/
def adjacencyEdge (RS : RotationSystem V E) {left right : V}
    (hadj : (rotationPrimalGraph RS).Adj left right) : E :=
  RS.edgeOf (adjacencyDart RS hadj)

/-- Mod-two traversal parity on the literal rotation edge carrier. -/
def walkEdgeParity (RS : RotationSystem V E) {start finish : V} :
    (rotationPrimalGraph RS).Walk start finish → E → F2
  | .nil => 0
  | .cons hadj tail =>
      Pi.single (adjacencyEdge RS hadj) 1 + walkEdgeParity RS tail

@[simp] theorem walkEdgeParity_nil (RS : RotationSystem V E) (vertex : V) :
    walkEdgeParity RS
      (Walk.nil :
        (rotationPrimalGraph RS).Walk vertex vertex) = 0 := rfl

theorem walkEdgeParity_cons (RS : RotationSystem V E)
    {start next finish : V}
    (hadj : (rotationPrimalGraph RS).Adj start next)
    (tail : (rotationPrimalGraph RS).Walk next finish) :
    walkEdgeParity RS (Walk.cons hadj tail) =
      Pi.single (adjacencyEdge RS hadj) 1 + walkEdgeParity RS tail := rfl

/-- One literal edge basis vector has the two endpoint indicators as its
incidence boundary. -/
theorem incidenceMatrix_mulVec_single_edge
    (RS : RotationSystem V E) (dart : RS.D) :
    (incidenceMatrix RS).mulVecLin (Pi.single (RS.edgeOf dart) 1) =
      Pi.single (RS.vertOf dart) 1 +
        Pi.single (RS.vertOf (RS.alpha dart)) 1 := by
  funext vertex
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  change (if RS.edgeOf dart ∈ RS.incidentEdges vertex then 1 else 0) = _
  have hends := RS.endpoints_eq_pair_of_mem
    (e := RS.edgeOf dart) (d := dart) (RS.mem_dartsOn.2 rfl)
  have hincident :
      RS.edgeOf dart ∈ RS.incidentEdges vertex ↔
        vertex = RS.vertOf dart ∨ vertex = RS.vertOf (RS.alpha dart) := by
    rw [← RS.mem_endpoints_iff_mem_incidentEdges, hends]
    simp
  simp only [hincident]
  have hne : RS.vertOf dart ≠ RS.vertOf (RS.alpha dart) :=
    RS.no_self_loops dart
  by_cases hleft : vertex = RS.vertOf dart
  · by_cases hright : vertex = RS.vertOf (RS.alpha dart)
    · exact (RS.no_self_loops dart (hleft.symm.trans hright)).elim
    · simp [hleft, hne]
  · by_cases hright : vertex = RS.vertOf (RS.alpha dart) <;>
      simp [hleft, hright, hne.symm]

/-- The incidence boundary of a chosen adjacency step is its two named
vertices. -/
theorem incidenceMatrix_mulVec_single_adjacencyEdge
    (RS : RotationSystem V E) {left right : V}
    (hadj : (rotationPrimalGraph RS).Adj left right) :
    (incidenceMatrix RS).mulVecLin
        (Pi.single (adjacencyEdge RS hadj) 1) =
      Pi.single left 1 + Pi.single right 1 := by
  rw [show adjacencyEdge RS hadj =
      RS.edgeOf (adjacencyDart RS hadj) by rfl,
    incidenceMatrix_mulVec_single_edge]
  rw [adjacencyDart_left, adjacencyDart_right]

/-- The boundary of a lifted walk parity vector is exactly its endpoint
pair. -/
theorem incidenceMatrix_mulVec_walkEdgeParity
    (RS : RotationSystem V E) {start finish : V}
    (walk : (rotationPrimalGraph RS).Walk start finish) :
    (incidenceMatrix RS).mulVecLin (walkEdgeParity RS walk) =
      Pi.single start 1 + Pi.single finish 1 := by
  induction walk with
  | nil =>
      funext vertex
      simp [walkEdgeParity, Matrix.mulVec,
        dotProduct, zmod2_add_self]
  | @cons start next finish hadj tail ih =>
      rw [walkEdgeParity_cons, LinearMap.map_add,
        incidenceMatrix_mulVec_single_adjacencyEdge, ih]
      funext vertex
      simp only [Pi.add_apply]
      let leftValue : F2 :=
        (Pi.single start (1 : F2) : V → F2) vertex
      let middleValue : F2 :=
        (Pi.single next (1 : F2) : V → F2) vertex
      let rightValue : F2 :=
        (Pi.single finish (1 : F2) : V → F2) vertex
      change (leftValue + middleValue) + (middleValue + rightValue) =
        leftValue + rightValue
      calc
        (leftValue + middleValue) + (middleValue + rightValue) =
            leftValue + (middleValue + middleValue) + rightValue := by abel
        _ = leftValue + rightValue := by
          rw [zmod2_add_self]
          simp

/-- A closed lifted walk is a cycle in the literal multigraph edge space. -/
theorem walkEdgeParity_mem_cycleSpace_of_closed
    (RS : RotationSystem V E) {vertex : V}
    (walk : (rotationPrimalGraph RS).Walk vertex vertex) :
    walkEdgeParity RS walk ∈ cycleSpace RS := by
  rw [cycleSpace, LinearMap.mem_ker,
    incidenceMatrix_mulVec_walkEdgeParity]
  funext other
  simp [zmod2_add_self]

end

end GoertzelV24RotationWalkCycleParity

end Mettapedia.GraphTheory.FourColor
