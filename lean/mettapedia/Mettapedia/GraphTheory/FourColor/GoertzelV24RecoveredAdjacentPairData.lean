import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferPrimalCutCollarChordCrossingRecovery
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairCyclicOrder

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RecoveredAdjacentPairData

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FaceDualConnectedness
open GoertzelV24FourDefectBoundary
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance recoveredAdjacentPairEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance recoveredAdjacentPairNeighborSetFintype (vertex : V) :
    Fintype (G.neighborSet vertex) :=
  Subtype.fintype _

local instance recoveredAdjacentPairRetainedVertexSetFintype
    (first second : V) :
    Fintype (retainedVertexSet first second) :=
  retainedVertexSetFintype first second

local instance recoveredAdjacentPairRetainedVertexSetDecidableEq
    (first second : V) :
    DecidableEq (retainedVertexSet first second) :=
  retainedVertexSetDecidableEq first second

/-- The directed central edge of an adjacent pair. -/
def centralDart {first second : V} (hadj : G.Adj first second) : G.Dart :=
  ⟨(first, second), hadj⟩

/-- The four external darts obtained by reading the two cubic rotations
from the directed central edge. -/
def rotationPortDart (graphData : Data G) {first second : V}
    (hadj : G.Adj first second) : Fin 4 → G.Dart
  | 0 => graphData.toRotationSystem.rho (centralDart hadj)
  | 1 => graphData.toRotationSystem.rho
      (graphData.toRotationSystem.rho (centralDart hadj))
  | 2 => graphData.toRotationSystem.rho
      (graphData.toRotationSystem.alpha (centralDart hadj))
  | 3 => graphData.toRotationSystem.rho
      (graphData.toRotationSystem.rho
        (graphData.toRotationSystem.alpha (centralDart hadj)))

/-- The endpoint of a rotation port outside the adjacent pair. -/
def rotationPortVertex (graphData : Data G) {first second : V}
    (hadj : G.Adj first second) (port : Fin 4) : V :=
  (rotationPortDart graphData hadj port).snd

theorem rotationPortDart_fst
    (graphData : Data G) {first second : V}
    (hadj : G.Adj first second) (port : Fin 4) :
    (rotationPortDart graphData hadj port).fst =
      if port = 0 ∨ port = 1 then first else second := by
  let RS := graphData.toRotationSystem
  let central := centralDart hadj
  have hcentral : RS.vertOf central = first := rfl
  have hopposite : RS.vertOf (RS.alpha central) = second := rfl
  fin_cases port
  · simpa [rotationPortDart, RS, central] using
      (RS.vert_rho central).trans hcentral
  · simpa [rotationPortDart, RS, central] using
      (RS.vert_rho (RS.rho central)).trans
        ((RS.vert_rho central).trans hcentral)
  · simpa [rotationPortDart, RS, central] using
      (RS.vert_rho (RS.alpha central)).trans hopposite
  · simpa [rotationPortDart, RS, central] using
      (RS.vert_rho (RS.rho (RS.alpha central))).trans
        ((RS.vert_rho (RS.alpha central)).trans hopposite)

theorem first_adj_rotationPortVertex
    (graphData : Data G) {first second : V}
    (hadj : G.Adj first second) {port : Fin 4}
    (hport : port = 0 ∨ port = 1) :
    G.Adj first (rotationPortVertex graphData hadj port) := by
  have h := (rotationPortDart graphData hadj port).adj
  rw [rotationPortDart_fst graphData hadj port, if_pos hport] at h
  exact h

theorem second_adj_rotationPortVertex
    (graphData : Data G) {first second : V}
    (hadj : G.Adj first second) {port : Fin 4}
    (hport : port = 2 ∨ port = 3) :
    G.Adj second (rotationPortVertex graphData hadj port) := by
  have h := (rotationPortDart graphData hadj port).adj
  rw [rotationPortDart_fst graphData hadj port,
    if_neg (by rcases hport with rfl | rfl <;> decide)] at h
  exact h

theorem rotationPortVertex_zero_ne_one
    (graphData : Data G) {first second : V}
    (hadj : G.Adj first second)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    rotationPortVertex graphData hadj 0 ≠
      rotationPortVertex graphData hadj 1 := by
  intro hendpoint
  have hdarts := rho_triple_pairwise_ne graphData.toRotationSystem
    hcubic hrotation (centralDart hadj)
  apply hdarts.2.2
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · simpa [rotationPortDart] using
      (rotationPortDart_fst graphData hadj 0).trans
        (rotationPortDart_fst graphData hadj 1).symm
  · simpa [rotationPortVertex, rotationPortDart] using hendpoint

theorem rotationPortVertex_two_ne_three
    (graphData : Data G) {first second : V}
    (hadj : G.Adj first second)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    rotationPortVertex graphData hadj 2 ≠
      rotationPortVertex graphData hadj 3 := by
  intro hendpoint
  have hdarts := rho_triple_pairwise_ne graphData.toRotationSystem
    hcubic hrotation
      (graphData.toRotationSystem.alpha (centralDart hadj))
  apply hdarts.2.2
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · simpa [rotationPortDart] using
      (rotationPortDart_fst graphData hadj 2).trans
        (rotationPortDart_fst graphData hadj 3).symm
  · simpa [rotationPortVertex, rotationPortDart] using hendpoint

theorem rotationPortVertex_ne_first
    (graphData : Data G) {first second : V}
    (hadj : G.Adj first second)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (port : Fin 4) :
    rotationPortVertex graphData hadj port ≠ first := by
  let RS := graphData.toRotationSystem
  have hopposite := rho_triple_pairwise_ne RS hcubic hrotation
    (RS.alpha (centralDart hadj))
  fin_cases port
  · intro heq
    apply (rotationPortDart graphData hadj 0).fst_ne_snd
    exact (rotationPortDart_fst graphData hadj 0).trans heq.symm
  · intro heq
    apply (rotationPortDart graphData hadj 1).fst_ne_snd
    exact (rotationPortDart_fst graphData hadj 1).trans heq.symm
  · intro heq
    apply hopposite.1
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · simpa [rotationPortDart, RS, centralDart] using
        (rotationPortDart_fst graphData hadj 2).symm
    · simpa [rotationPortDart, rotationPortVertex, RS, centralDart] using
        heq.symm
  · intro heq
    apply hopposite.2.1
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · simpa [rotationPortDart, RS, centralDart] using
        (rotationPortDart_fst graphData hadj 3).symm
    · simpa [rotationPortDart, rotationPortVertex, RS, centralDart] using
        heq.symm

theorem rotationPortVertex_ne_second
    (graphData : Data G) {first second : V}
    (hadj : G.Adj first second)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (port : Fin 4) :
    rotationPortVertex graphData hadj port ≠ second := by
  let RS := graphData.toRotationSystem
  have hcentral := rho_triple_pairwise_ne RS hcubic hrotation
    (centralDart hadj)
  fin_cases port
  · intro heq
    apply hcentral.1
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · simpa [rotationPortDart, RS, centralDart] using
        (rotationPortDart_fst graphData hadj 0).symm
    · simpa [rotationPortDart, rotationPortVertex, RS, centralDart] using
        heq.symm
  · intro heq
    apply hcentral.2.1
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · simpa [rotationPortDart, RS, centralDart] using
        (rotationPortDart_fst graphData hadj 1).symm
    · simpa [rotationPortDart, rotationPortVertex, RS, centralDart] using
        heq.symm
  · intro heq
    apply (rotationPortDart graphData hadj 2).fst_ne_snd
    exact (rotationPortDart_fst graphData hadj 2).trans heq.symm
  · intro heq
    apply (rotationPortDart graphData hadj 3).fst_ne_snd
    exact (rotationPortDart_fst graphData hadj 3).trans heq.symm

theorem firstPort_ne_secondPort
    (graphData : Data G) {first second : V}
    (hadj : G.Adj first second)
    (hnoCommon : ∀ common,
      G.Adj first common → G.Adj second common → False)
    {firstPort secondPort : Fin 4}
    (hfirst : firstPort = 0 ∨ firstPort = 1)
    (hsecond : secondPort = 2 ∨ secondPort = 3) :
    rotationPortVertex graphData hadj firstPort ≠
      rotationPortVertex graphData hadj secondPort := by
  intro heq
  exact hnoCommon (rotationPortVertex graphData hadj firstPort)
    (first_adj_rotationPortVertex graphData hadj hfirst)
    (heq ▸ second_adj_rotationPortVertex graphData hadj hsecond)

theorem rotationPortVertex_injective
    (graphData : Data G) {first second : V}
    (hadj : G.Adj first second)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (hnoCommon : ∀ common,
      G.Adj first common → G.Adj second common → False) :
    Function.Injective (rotationPortVertex graphData hadj) := by
  intro left right heq
  fin_cases left <;> fin_cases right
  · rfl
  · exact False.elim
      (rotationPortVertex_zero_ne_one graphData hadj hcubic hrotation heq)
  · exact False.elim
      (firstPort_ne_secondPort graphData hadj hnoCommon
        (by left; rfl) (by left; rfl) heq)
  · exact False.elim
      (firstPort_ne_secondPort graphData hadj hnoCommon
        (by left; rfl) (by right; rfl) heq)
  · exact False.elim
      (rotationPortVertex_zero_ne_one graphData hadj hcubic hrotation heq.symm)
  · rfl
  · exact False.elim
      (firstPort_ne_secondPort graphData hadj hnoCommon
        (by right; rfl) (by left; rfl) heq)
  · exact False.elim
      (firstPort_ne_secondPort graphData hadj hnoCommon
        (by right; rfl) (by right; rfl) heq)
  · exact False.elim
      (firstPort_ne_secondPort graphData hadj hnoCommon
        (by left; rfl) (by left; rfl) heq.symm)
  · exact False.elim
      (firstPort_ne_secondPort graphData hadj hnoCommon
        (by right; rfl) (by left; rfl) heq.symm)
  · rfl
  · exact False.elim
      (rotationPortVertex_two_ne_three graphData hadj hcubic hrotation heq)
  · exact False.elim
      (firstPort_ne_secondPort graphData hadj hnoCommon
        (by left; rfl) (by right; rfl) heq.symm)
  · exact False.elim
      (firstPort_ne_secondPort graphData hadj hnoCommon
        (by right; rfl) (by right; rfl) heq.symm)
  · exact False.elim
      (rotationPortVertex_two_ne_three graphData hadj hcubic hrotation heq.symm)
  · rfl

theorem firstNeighbors_eq
    (graphData : Data G) {first second : V}
    (hadj : G.Adj first second)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    G.neighborSet first =
      ({second, rotationPortVertex graphData hadj 0,
        rotationPortVertex graphData hadj 1} : Set V) := by
  let port := rotationPortVertex graphData hadj
  have hsubset : ({second, port 0, port 1} : Finset V) ⊆
      G.neighborFinset first := by
    intro vertex hvertex
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvertex
    rcases hvertex with rfl | rfl | rfl
    · simpa using hadj
    · simpa [port] using first_adj_rotationPortVertex graphData hadj
        (by left; rfl : (0 : Fin 4) = 0 ∨ (0 : Fin 4) = 1)
    · simpa [port] using first_adj_rotationPortVertex graphData hadj
        (by right; rfl : (1 : Fin 4) = 0 ∨ (1 : Fin 4) = 1)
  have hfinset : ({second, port 0, port 1} : Finset V) =
      G.neighborFinset first := by
    apply Finset.eq_of_subset_of_card_le hsubset
    have hregular := graphData.toRotationSystem_isCubic_iff.mp hcubic
    rw [SimpleGraph.card_neighborFinset_eq_degree, hregular.degree_eq]
    have hsecondZero : second ≠ port 0 :=
      (rotationPortVertex_ne_second graphData hadj hcubic hrotation 0).symm
    have hsecondOne : second ≠ port 1 :=
      (rotationPortVertex_ne_second graphData hadj hcubic hrotation 1).symm
    have hzeroOne : port 0 ≠ port 1 :=
      rotationPortVertex_zero_ne_one graphData hadj hcubic hrotation
    simp [hsecondZero, hsecondOne, hzeroOne]
  ext vertex
  simpa [port] using (Finset.ext_iff.mp hfinset vertex).symm

theorem secondNeighbors_eq
    (graphData : Data G) {first second : V}
    (hadj : G.Adj first second)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    G.neighborSet second =
      ({first, rotationPortVertex graphData hadj 2,
        rotationPortVertex graphData hadj 3} : Set V) := by
  let port := rotationPortVertex graphData hadj
  have hsubset : ({first, port 2, port 3} : Finset V) ⊆
      G.neighborFinset second := by
    intro vertex hvertex
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvertex
    rcases hvertex with rfl | rfl | rfl
    · simpa using hadj.symm
    · simpa [port] using second_adj_rotationPortVertex graphData hadj
        (by left; rfl : (2 : Fin 4) = 2 ∨ (2 : Fin 4) = 3)
    · simpa [port] using second_adj_rotationPortVertex graphData hadj
        (by right; rfl : (3 : Fin 4) = 2 ∨ (3 : Fin 4) = 3)
  have hfinset : ({first, port 2, port 3} : Finset V) =
      G.neighborFinset second := by
    apply Finset.eq_of_subset_of_card_le hsubset
    have hregular := graphData.toRotationSystem_isCubic_iff.mp hcubic
    rw [SimpleGraph.card_neighborFinset_eq_degree, hregular.degree_eq]
    have hfirstTwo : first ≠ port 2 :=
      (rotationPortVertex_ne_first graphData hadj hcubic hrotation 2).symm
    have hfirstThree : first ≠ port 3 :=
      (rotationPortVertex_ne_first graphData hadj hcubic hrotation 3).symm
    have htwoThree : port 2 ≠ port 3 :=
      rotationPortVertex_two_ne_three graphData hadj hcubic hrotation
    simp [hfirstTwo, hfirstThree, htwoThree]
  ext vertex
  simpa [port] using (Finset.ext_iff.mp hfinset vertex).symm

/-- In a cubic rotation map, an adjacent pair with no common neighbor has a
canonical ordered four-port deletion boundary. -/
def adjacentPairData
    (graphData : Data G) {first second : V}
    (hadj : G.Adj first second)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (hnoCommon : ∀ common,
      G.Adj first common → G.Adj second common → False) :
    AdjacentPairData G where
  firstVertex := first
  secondVertex := second
  portVertex := rotationPortVertex graphData hadj
  centralAdjacent := hadj
  portInjective := rotationPortVertex_injective graphData hadj hcubic
    hrotation hnoCommon
  portNeFirst := rotationPortVertex_ne_first graphData hadj hcubic hrotation
  portNeSecond := rotationPortVertex_ne_second graphData hadj hcubic hrotation
  firstNeighbors := firstNeighbors_eq graphData hadj hcubic hrotation
  secondNeighbors := secondNeighbors_eq graphData hadj hcubic hrotation

/-- The canonical adjacent-pair boundary enters the existing planar square
reduction and supplies its exact compatible deleted coloring. -/
theorem exists_cyclicallyOrdered_deletedColoring_of_no_common_neighbor
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {first second : V} (hadj : G.Adj first second)
    (hnoCommon : ∀ common,
      G.Adj first common → G.Adj second common → False) :
    ∃ ordered : AdjacentPairData G,
      ordered.firstVertex = first ∧
      ordered.secondVertex = second ∧
      ordered.PortsFollowCyclicDeletedBoundaryOrder graphData ∧
      ∃ deletedColoring :
          (DeletedAdjacentPairGraph G ordered.firstVertex
            ordered.secondVertex).EdgeColoring Color,
        IsTaitEdgeColoring
            (DeletedAdjacentPairGraph G ordered.firstVertex
              ordered.secondVertex)
            deletedColoring ∧
          SquareReductionSide.join01_23.Compatible
            (ordered.degreeTwoBoundaryData.colorWord deletedColoring) := by
  let data := adjacentPairData graphData hadj minimal.spherical.cubic
    minimal.vertexRotationCyclic hnoCommon
  rcases data.exists_cyclicallyOrdered_deletedColoring_join01_23_compatible
      graphData minimal with
    ⟨ordered, hfirst, hsecond, horder, coloring, htait, hcompatible⟩
  exact ⟨ordered, hfirst, hsecond, horder, coloring, htait, hcompatible⟩

end

end GoertzelV24RecoveredAdjacentPairData

end Mettapedia.GraphTheory.FourColor
