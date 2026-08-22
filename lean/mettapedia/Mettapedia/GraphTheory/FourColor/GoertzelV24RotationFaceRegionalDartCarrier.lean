import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationFaceRegionalDartSeam

/-!
# Finite literal-dart carriers around selected facial edges

A face edge has two literal darts, even when both occurrences belong to the
same face.  This file forms the closed face-permutation neighbourhood of the
darts over a finite edge set and proves the uniform factor-six bound.

The construction is deliberately independent of any two-sidedness premise.
It is generic rotation-system infrastructure for finite facial transition
codes.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationFaceRegionalDartCarrier

open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- All literal dart occurrences over a selected finite edge set. -/
def dartsOnEdges (RS : RotationSystem V E) (edges : Finset E) :
    Finset RS.D :=
  edges.biUnion RS.dartsOn

@[simp]
theorem mem_dartsOnEdges_iff (RS : RotationSystem V E) (edges : Finset E)
    (dart : RS.D) :
    dart ∈ dartsOnEdges RS edges ↔ RS.edgeOf dart ∈ edges := by
  constructor
  · intro hdart
    rcases Finset.mem_biUnion.1 hdart with ⟨edge, hedge, hdartOn⟩
    simpa [(RS.mem_dartsOn).1 hdartOn] using hedge
  · intro hedge
    exact Finset.mem_biUnion.2
      ⟨RS.edgeOf dart, hedge, (RS.mem_dartsOn).2 rfl⟩

/-- Two darts per edge, with no facial two-sidedness assumption. -/
theorem dartsOnEdges_card_le_two_mul
    (RS : RotationSystem V E) (edges : Finset E) :
    (dartsOnEdges RS edges).card ≤ 2 * edges.card := by
  calc
    (dartsOnEdges RS edges).card ≤ edges.card * 2 := by
      apply Finset.card_biUnion_le_card_mul
      intro edge _hedge
      exact le_of_eq (RS.dartsOn_card_two edge)
    _ = 2 * edges.card := by omega

/-- The predecessor and successor face-permutation neighbours of one dart. -/
def faceDartNeighbors (RS : RotationSystem V E) (dart : RS.D) :
    Finset RS.D :=
  {RS.phi dart, RS.phi.symm dart}

@[simp]
theorem mem_faceDartNeighbors_iff (RS : RotationSystem V E)
    (dart neighbor : RS.D) :
    neighbor ∈ faceDartNeighbors RS dart ↔
      neighbor = RS.phi dart ∨ neighbor = RS.phi.symm dart := by
  simp [faceDartNeighbors]

/-- Closed face-permutation neighbourhood of the darts over selected edges. -/
def closedDartCarrier (RS : RotationSystem V E) (edges : Finset E) :
    Finset RS.D :=
  (dartsOnEdges RS edges).biUnion fun dart =>
    insert dart (faceDartNeighbors RS dart)

/-- Two darts per edge and three positions per closed neighbourhood give the
uniform factor six. -/
theorem closedDartCarrier_card_le_six_mul
    (RS : RotationSystem V E) (edges : Finset E) :
    (closedDartCarrier RS edges).card ≤ 6 * edges.card := by
  calc
    (closedDartCarrier RS edges).card ≤
        (dartsOnEdges RS edges).card * 3 := by
      apply Finset.card_biUnion_le_card_mul
      intro dart _hdart
      calc
        (insert dart (faceDartNeighbors RS dart)).card ≤
            (faceDartNeighbors RS dart).card + 1 :=
          Finset.card_insert_le _ _
        _ ≤ 2 + 1 := by
          exact Nat.add_le_add_right (Finset.card_le_two) 1
        _ = 3 := by omega
    _ ≤ (2 * edges.card) * 3 :=
      Nat.mul_le_mul_right 3 (dartsOnEdges_card_le_two_mul RS edges)
    _ = 6 * edges.card := by omega

/-- A selected dart belongs to its closed carrier. -/
theorem mem_closedDartCarrier_of_edge_mem
    (RS : RotationSystem V E) (edges : Finset E) (dart : RS.D)
    (hdart : RS.edgeOf dart ∈ edges) :
    dart ∈ closedDartCarrier RS edges := by
  apply Finset.mem_biUnion.2
  exact ⟨dart, (mem_dartsOnEdges_iff RS edges dart).2 hdart,
    Finset.mem_insert_self _ _⟩

/-- Either face-permutation neighbour of a selected dart belongs to the same
closed carrier. -/
theorem mem_closedDartCarrier_of_face_neighbor_of_edge_mem
    (RS : RotationSystem V E) (edges : Finset E) (dart neighbor : RS.D)
    (hdart : RS.edgeOf dart ∈ edges)
    (hneighbor : neighbor = RS.phi dart ∨ neighbor = RS.phi.symm dart) :
    neighbor ∈ closedDartCarrier RS edges := by
  apply Finset.mem_biUnion.2
  refine ⟨dart, (mem_dartsOnEdges_iff RS edges dart).2 hdart, ?_⟩
  exact Finset.mem_insert.2
    (Or.inr ((mem_faceDartNeighbors_iff RS dart neighbor).2 hneighbor))

end

end GoertzelV24RotationFaceRegionalDartCarrier

end Mettapedia.GraphTheory.FourColor
