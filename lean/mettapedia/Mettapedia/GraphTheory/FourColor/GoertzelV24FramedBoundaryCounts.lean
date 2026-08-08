import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedTrail

/-!
# Exact framed-boundary degree counting

This is the convention-independent first half of playbook flag L9.  In the
Lean graph model, the missing edge leaves two degree-two defect vertices and
the frozen outward interface ends at degree-one stub vertices; every other
vertex is cubic.  The resulting degree identity is proved before introducing
any face-count or annular Euler convention.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedBoundaryCounts

open SimpleGraph
open GoertzelV24FramedTrail

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The incident-edge representation used by the framed model has graph
degree as its cardinality. -/
theorem incidentEdgeFinset_card_eq_degree (vertex : V) :
    (incidentEdgeFinset G vertex).card = G.degree vertex := by
  have hmap :
      (incidentEdgeFinset G vertex).map
          (Function.Embedding.subtype (fun edge : Sym2 V => edge ∈ G.edgeSet)) =
        G.incidenceFinset vertex := by
    rw [SimpleGraph.incidenceFinset_eq_filter]
    ext edge
    simp [incidentEdgeFinset, and_comm]
  calc
    (incidentEdgeFinset G vertex).card =
        ((incidentEdgeFinset G vertex).map
          (Function.Embedding.subtype
            (fun edge : Sym2 V => edge ∈ G.edgeSet))).card := by simp
    _ = (G.incidenceFinset vertex).card := by rw [hmap]
    _ = G.degree vertex := by simp

/-- The two distinguished degree-two vertices as an actual finite boundary
set. -/
def defectVertices (data : FramedTrailData G) : Finset V :=
  {data.defectVertex 0, data.defectVertex 1}

/-- Every vertex outside the two defects and frozen degree-one stubs. -/
def cubicInteriorVertices (data : FramedTrailData G) : Finset V :=
  Finset.univ \
    (defectVertices data ∪ data.frozenInterfaceStubVertices)

/-- The two defect vertices are distinct, so their finite set has cardinality
two. -/
theorem defectVertices_card
    (data : FramedTrailData G) (hdata : data.WellFormed) :
    (defectVertices data).card = 2 := by
  have hne : data.defectVertex 0 ≠ data.defectVertex 1 := by
    intro heq
    have : (0 : Fin 2) = 1 := hdata.defectVertex_injective heq
    omega
  simp [defectVertices, hne]

/-- Defects and frozen stubs are disjoint boundary classes. -/
theorem defectVertices_disjoint_frozenInterfaceStubVertices
    (data : FramedTrailData G) (hdata : data.WellFormed) :
    Disjoint (defectVertices data) data.frozenInterfaceStubVertices := by
  rw [Finset.disjoint_left]
  intro vertex hdefect hstub
  have hcases :
      vertex = data.defectVertex 0 ∨
        vertex = data.defectVertex 1 := by
    simpa [defectVertices] using hdefect
  rcases hcases with rfl | rfl
  · exact hdata.defectVertex_not_stub 0 hstub
  · exact hdata.defectVertex_not_stub 1 hstub

omit [DecidableRel G.Adj] in
/-- The three vertex classes—two defects, frozen stubs, and cubic interior—
partition the framed graph. -/
theorem boundary_partition
    (data : FramedTrailData G) :
    Finset.univ =
      (defectVertices data ∪ data.frozenInterfaceStubVertices) ∪
        cubicInteriorVertices data := by
  ext vertex
  simp [cubicInteriorVertices]

/-- Exact framed feet/degree identity.  If `s` is the number of frozen
degree-one interface stubs, then

`2 |E| + 2 + 2 s = 3 |V|`.

The correction term `2` is exactly the contribution of replacing two cubic
vertices by the two degree-two missing-edge defects. -/
theorem twice_edgeCount_add_two_add_twice_frozenStubCount
    (data : FramedTrailData G) (hdata : data.WellFormed) :
    2 * G.edgeFinset.card + 2 +
        2 * data.frozenInterfaceStubVertices.card =
      3 * Fintype.card V := by
  let defects := defectVertices data
  let stubs := data.frozenInterfaceStubVertices
  let interior := cubicInteriorVertices data
  have hdefectsStubs : Disjoint defects stubs := by
    exact defectVertices_disjoint_frozenInterfaceStubVertices data hdata
  have hboundaryInterior : Disjoint (defects ∪ stubs) interior := by
    rw [Finset.disjoint_left]
    intro vertex hboundary hinterior
    exact (Finset.mem_sdiff.mp hinterior).2 hboundary
  have hpartition : Finset.univ = (defects ∪ stubs) ∪ interior := by
    exact boundary_partition data
  have hdefectCard : defects.card = 2 := by
    exact defectVertices_card data hdata
  have hcardPartition :
      Fintype.card V = defects.card + stubs.card + interior.card := by
    have hcard := congrArg Finset.card hpartition
    rw [Finset.card_univ,
      Finset.card_union_of_disjoint hboundaryInterior,
      Finset.card_union_of_disjoint hdefectsStubs] at hcard
    omega
  have hcardPartition' :
      Fintype.card V =
        2 + data.frozenInterfaceStubVertices.card + interior.card := by
    rw [hdefectCard] at hcardPartition
    simpa [stubs] using hcardPartition
  have hdegreeZero : G.degree (data.defectVertex 0) = 2 := by
    rw [← incidentEdgeFinset_card_eq_degree]
    exact hdata.defect_degree_two 0
  have hdegreeOne : G.degree (data.defectVertex 1) = 2 := by
    rw [← incidentEdgeFinset_card_eq_degree]
    exact hdata.defect_degree_two 1
  have hdefectSum : ∑ vertex ∈ defects, G.degree vertex = 4 := by
    have hne : data.defectVertex 0 ≠ data.defectVertex 1 := by
      intro heq
      have : (0 : Fin 2) = 1 := hdata.defectVertex_injective heq
      omega
    simp [defects, defectVertices, hne, hdegreeZero, hdegreeOne]
  have hstubSum : ∑ vertex ∈ stubs, G.degree vertex = stubs.card := by
    calc
      (∑ vertex ∈ stubs, G.degree vertex) = ∑ _vertex ∈ stubs, 1 := by
        apply Finset.sum_congr rfl
        intro vertex hstub
        rw [← incidentEdgeFinset_card_eq_degree]
        exact hdata.frozen_stub_degree_one vertex hstub
      _ = stubs.card := by simp
  have hinteriorSum :
      ∑ vertex ∈ interior, G.degree vertex = 3 * interior.card := by
    calc
      (∑ vertex ∈ interior, G.degree vertex) = ∑ _vertex ∈ interior, 3 := by
        apply Finset.sum_congr rfl
        intro vertex hinterior
        have hnotBoundary := (Finset.mem_sdiff.mp hinterior).2
        rw [← incidentEdgeFinset_card_eq_degree]
        apply hdata.cubic_elsewhere vertex
        · intro i
          fin_cases i
          · intro heq
            apply hnotBoundary
            exact Finset.mem_union_left _ (by simp [defectVertices, heq])
          · intro heq
            apply hnotBoundary
            exact Finset.mem_union_left _ (by simp [defectVertices, heq])
        · intro hstub
          apply hnotBoundary
          exact Finset.mem_union_right _ hstub
      _ = 3 * interior.card := by simp [Nat.mul_comm]
  have hdegreePartition :
      (∑ vertex : V, G.degree vertex) =
        (∑ vertex ∈ defects, G.degree vertex) +
          (∑ vertex ∈ stubs, G.degree vertex) +
            ∑ vertex ∈ interior, G.degree vertex := by
    rw [hpartition,
      Finset.sum_union hboundaryInterior,
      Finset.sum_union hdefectsStubs]
  have hhandshake :
      (∑ vertex : V, G.degree vertex) = 2 * G.edgeFinset.card := by
    simpa using G.sum_degrees_eq_twice_card_edges
  rw [hdefectSum, hstubSum, hinteriorSum] at hdegreePartition
  have hdegreeCount :
      2 * G.edgeFinset.card =
        4 + data.frozenInterfaceStubVertices.card + 3 * interior.card := by
    calc
      2 * G.edgeFinset.card = ∑ vertex : V, G.degree vertex := hhandshake.symm
      _ = 4 + stubs.card + 3 * interior.card := hdegreePartition
      _ = 4 + data.frozenInterfaceStubVertices.card +
          3 * interior.card := by simp [stubs]
  omega

end GoertzelV24FramedBoundaryCounts

end Mettapedia.GraphTheory.FourColor
