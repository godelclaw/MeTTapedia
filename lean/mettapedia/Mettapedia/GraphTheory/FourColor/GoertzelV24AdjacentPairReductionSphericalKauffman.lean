import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairReductionKempeSquare
import Mettapedia.GraphTheory.FourColor.GoertzelV24BridgelessFaceTwoSided
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalTriangleFree
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationSystemKauffmanParity

/-!
# Exact spherical Kauffman parity for the canonical square cap

The `01|23` adjacent-pair cap joins the two ports at the first deleted vertex
and the two ports at the second deleted vertex.  In a least Tait
counterexample neither joined pair can already be adjacent: such an edge,
together with the corresponding deleted vertex, would form a triangle.
Consequently the cap has no parallel seam and admits the canonical simple
graph presentation.  The exact spherical rotation-system Kauffman theorem can
then replace the older abstract cross-curve receipt.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AdjacentPairBoundary.AdjacentPairData

open GoertzelV24AdjacentPairBoundary
open GoertzelV24BridgelessFaceTwoSided
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceDualConnectedness
open GoertzelV24MinimalTriangleFree
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationEdgeBridge
open GoertzelV24RotationSystemKauffmanParity
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance sphericalKauffmanRetainedVertexSetFintype
    (first second : V) : Fintype (retainedVertexSet first second) :=
  reductionExtensionRetainedVertexSetFintype first second

local instance sphericalKauffmanRetainedVertexSetDecidableEq
    (first second : V) : DecidableEq (retainedVertexSet first second) :=
  reductionExtensionRetainedVertexSetDecidableEq first second

/-- The two endpoints joined by either seam of the `01|23` cap are not
adjacent in a least counterexample. -/
theorem not_adj_join01_23_paired_ports
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G) (step : Fin 2) :
    ¬ G.Adj
      (data.portVertex (SquareReductionSide.join01_23.leftPort step))
      (data.portVertex (SquareReductionSide.join01_23.rightPort step)) := by
  fin_cases step
  · intro hadj
    exact no_common_neighbor_of_vertexMinimalTaitCounterexample
      graphData minimal hadj data.firstVertex
        (by simpa using data.first_adj_port_one.symm)
        (by simpa using data.first_adj_port_zero.symm)
  · intro hadj
    exact no_common_neighbor_of_vertexMinimalTaitCounterexample
      graphData minimal hadj data.secondVertex
        (by simpa using data.second_adj_port_two.symm)
        (by simpa using data.second_adj_port_three.symm)

/-- No old retained edge has the same endpoint pair as a seam of the
`01|23` cap. -/
theorem endpoints_reductionEdgeOfDeletedEdge_ne_join01_23_seam
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (old : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) (step : Fin 2) :
    (data.reductionRotationSystem graphData
        SquareReductionSide.join01_23).endpoints
          (data.reductionEdgeOfDeletedEdge graphData
            SquareReductionSide.join01_23 old) ≠
      (data.reductionRotationSystem graphData
        SquareReductionSide.join01_23).endpoints
          (data.reductionSeamEdge graphData
            SquareReductionSide.join01_23 step) := by
  intro hends
  let side := SquareReductionSide.join01_23
  let left := data.retainedPort (side.leftPort step)
  let right := data.retainedPort (side.rightPort step)
  have hleftCap : data.reductionVertexOfDeletedVertex left ∈
      (data.reductionRotationSystem graphData side).endpoints
        (data.reductionSeamEdge graphData side step) :=
    data.reductionLeftPort_mem_endpoints_reductionSeamEdge
      graphData side step
  have hrightCap : data.reductionVertexOfDeletedVertex right ∈
      (data.reductionRotationSystem graphData side).endpoints
        (data.reductionSeamEdge graphData side step) :=
    data.reductionRightPort_mem_endpoints_reductionSeamEdge
      graphData side step
  have hleftOldEndpoint : data.reductionVertexOfDeletedVertex left ∈
      (data.reductionRotationSystem graphData side).endpoints
        (data.reductionEdgeOfDeletedEdge graphData side old) := by
    rw [hends]
    exact hleftCap
  have hrightOldEndpoint : data.reductionVertexOfDeletedVertex right ∈
      (data.reductionRotationSystem graphData side).endpoints
        (data.reductionEdgeOfDeletedEdge graphData side old) := by
    rw [hends]
    exact hrightCap
  have hleftOld : left ∈ (old.1 : Sym2 _) :=
    (data.reductionVertex_mem_endpoints_reductionEdgeOfDeletedEdge_iff
      graphData side old left).1 hleftOldEndpoint
  have hrightOld : right ∈ (old.1 : Sym2 _) :=
    (data.reductionVertex_mem_endpoints_reductionEdgeOfDeletedEdge_iff
      graphData side old right).1 hrightOldEndpoint
  have hleftRight : left ≠ right := by
    apply data.retainedPort_injective.ne
    exact side.leftPort_ne_rightPort step step
  have hedgeValue : old.1 = s(left, right) :=
    Sym2.eq_of_ne_mem hleftRight hleftOld hrightOld
      (Sym2.mem_mk_left _ _) (Sym2.mem_mk_right _ _)
  have hadjDeleted :
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).Adj
        left right :=
    (SimpleGraph.mem_edgeSet
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)).1
        (by simpa [hedgeValue] using old.2)
  have hadjAmbient : G.Adj
      (data.portVertex (side.leftPort step))
      (data.portVertex (side.rightPort step)) := hadjDeleted
  exact data.not_adj_join01_23_paired_ports graphData minimal step
    (by simpa [side, left, right] using hadjAmbient)

/-- Endpoint pairs of the two seams of either square cap identify their seam
positions. -/
theorem reductionSeamEndpoints_injective
    (graphData : Data G) (data : AdjacentPairData G)
    (side : SquareReductionSide) :
    Function.Injective (fun step =>
      (data.reductionRotationSystem graphData side).endpoints
        (data.reductionSeamEdge graphData side step)) := by
  intro first second hends
  have hmember : data.reductionVertexOfDeletedVertex
        (data.retainedPort (side.leftPort first)) ∈
      (data.reductionRotationSystem graphData side).endpoints
        (data.reductionSeamEdge graphData side second) := by
    change (data.reductionRotationSystem graphData side).endpoints
        (data.reductionSeamEdge graphData side first) =
      (data.reductionRotationSystem graphData side).endpoints
        (data.reductionSeamEdge graphData side second) at hends
    rw [← hends]
    exact data.reductionLeftPort_mem_endpoints_reductionSeamEdge
      graphData side first
  rcases (data.mem_endpoints_reductionSeamEdge_iff graphData side second
      (data.reductionVertexOfDeletedVertex
        (data.retainedPort (side.leftPort first)))).1 hmember with
    hleft | hright
  · apply side.leftPort_injective
    apply data.retainedPort_injective
    apply data.reductionVertexOfDeletedVertex_injective
    exact hleft
  · exfalso
    apply side.leftPort_ne_rightPort first second
    apply data.retainedPort_injective
    apply data.reductionVertexOfDeletedVertex_injective
    exact hright

/-- The canonical `01|23` cap of a least counterexample is endpoint-simple,
so it has a canonical simple-graph presentation. -/
theorem reductionRotationSystem_endpoints_injective_join01_23
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G) :
    Function.Injective
      (data.reductionRotationSystem graphData
        SquareReductionSide.join01_23).endpoints := by
  let side := SquareReductionSide.join01_23
  intro firstEdge secondEdge hends
  rcases data.reductionEdge_old_or_seam graphData side firstEdge with
    ⟨firstOld, rfl⟩ | ⟨firstStep, rfl⟩
  · rcases data.reductionEdge_old_or_seam graphData side secondEdge with
      ⟨secondOld, rfl⟩ | ⟨secondStep, rfl⟩
    · apply congrArg (data.reductionEdgeOfDeletedEdge graphData side)
      apply Subtype.ext
      apply Sym2.ext
      intro vertex
      rw [← data.reductionVertex_mem_endpoints_reductionEdgeOfDeletedEdge_iff
          graphData side firstOld vertex,
        ← data.reductionVertex_mem_endpoints_reductionEdgeOfDeletedEdge_iff
          graphData side secondOld vertex,
        hends]
    · exact False.elim
        (data.endpoints_reductionEdgeOfDeletedEdge_ne_join01_23_seam
          graphData minimal firstOld secondStep (by simpa [side] using hends))
  · rcases data.reductionEdge_old_or_seam graphData side secondEdge with
      ⟨secondOld, rfl⟩ | ⟨secondStep, rfl⟩
    · exact False.elim
        (data.endpoints_reductionEdgeOfDeletedEdge_ne_join01_23_seam
          graphData minimal secondOld firstStep
            (by simpa [side] using hends.symm))
    · exact congrArg (data.reductionSeamEdge graphData side)
        (data.reductionSeamEndpoints_injective graphData side hends)

/-- The capped realization of a same-side open Kempe switch preserves exact
spherical formation parity.  Unlike the older consumer, this theorem has no
abstract `CrossCurveParityPrinciple` receipt. -/
theorem exists_cappedKempeSwitch_with_restriction_and_sphericalFormationParity
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (hretainedConnected :
      (G.induce {vertex |
        deletedRegionKeep data.deletedVertices vertex}).Connected)
    (horder : data.PortsFollowCyclicDeletedBoundaryOrder graphData)
    (hbridgeFree : EdgeBridgeFree
      (data.reductionRotationSystem graphData
        SquareReductionSide.join01_23))
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (hcompatible : SquareReductionSide.join01_23.Compatible
      (data.degreeTwoBoundaryData.colorWord C))
    {a b : Color} (hab : ValidColorPair a b)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (fixed : Fin 2)
    (hsupport : data.degreeTwoBoundaryData.kempePortSupport C a b K =
      ({SquareReductionSide.join01_23.leftPort fixed,
        SquareReductionSide.join01_23.rightPort fixed} : Finset (Fin 4)))
    (hfixedSelected :
      data.degreeTwoBoundaryData.colorWord C
          (SquareReductionSide.join01_23.leftPort fixed) = a ∨
        data.degreeTwoBoundaryData.colorWord C
          (SquareReductionSide.join01_23.leftPort fixed) = b) :
    let capped := data.reductionExtensionColoring graphData
      (incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
        graphData minimal.spherical.cubic)
      C hC SquareReductionSide.join01_23 hcompatible
    ∃ Kcap : (capped.bicoloredSubgraph a b).ConnectedComponent,
      data.reductionSeamEdge graphData SquareReductionSide.join01_23 fixed ∈
          capped.kempeComponentSet a b Kcap ∧
        data.reductionDeletedColoring graphData
            SquareReductionSide.join01_23
            (capped.swapOnKempeComponent a b Kcap) =
          C.swapOnKempeComponent a b K ∧
        GoertzelV24KauffmanParity.formationParity
            (capped.swapOnKempeComponent a b Kcap) a b (a + b) =
          GoertzelV24KauffmanParity.formationParity capped a b (a + b) := by
  dsimp only
  let hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  let capped := data.reductionExtensionColoring graphData hcubic C hC
    SquareReductionSide.join01_23 hcompatible
  rcases data.exists_cappedKempeComponent_restricts_sameSideSwitch
      graphData hcubic C hC SquareReductionSide.join01_23 hcompatible hab K
        fixed hsupport hfixedSelected with
    ⟨Kcap, hseam, hrestrict⟩
  refine ⟨Kcap, hseam, hrestrict, ?_⟩
  let cappedClass :=
    data.reductionBridgelessSphericalCubicMapData graphData minimal
      hretainedConnected horder SquareReductionSide.join01_23 hbridgeFree
  exact GoertzelV24RotationSystemKauffmanParity.formationParity_swapOnKempeComponent_spherical
    (data.reductionRotationSystem graphData SquareReductionSide.join01_23)
    (data.reductionRotationSystem_endpoints_injective_join01_23
      graphData minimal)
    cappedClass
    (GoertzelV24BridgelessFaceTwoSided.BridgelessSphericalCubicMapData.orbitFacesTwoSided
      _ cappedClass)
    capped
    (data.reductionExtensionColoring_isTait graphData hcubic C hC
      SquareReductionSide.join01_23 hcompatible)
    hab Kcap

end

end GoertzelV24AdjacentPairBoundary.AdjacentPairData

namespace GoertzelV24AdjacentPairReductionSphericalKauffman

alias reductionRotationSystem_endpoints_injective_join01_23 :=
  GoertzelV24AdjacentPairBoundary.AdjacentPairData.reductionRotationSystem_endpoints_injective_join01_23

alias exists_cappedKempeSwitch_with_restriction_and_sphericalFormationParity :=
  GoertzelV24AdjacentPairBoundary.AdjacentPairData.exists_cappedKempeSwitch_with_restriction_and_sphericalFormationParity

end GoertzelV24AdjacentPairReductionSphericalKauffman

end Mettapedia.GraphTheory.FourColor
