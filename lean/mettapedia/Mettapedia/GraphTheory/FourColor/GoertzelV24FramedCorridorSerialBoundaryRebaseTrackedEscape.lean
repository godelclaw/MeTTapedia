import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseOldBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialPrefixTrackedBoundary

/-!
# Tracked escape from the old side of a serial boundary rebase

A tracked rebase seam has one endpoint in the accumulated literal prefix and
one newly displayed successor edge outside it.  The outside neighbor removes
at least one of the old endpoint's two ambient tracked continuations.  Hence
the endpoint is either isolated in the old regional graph or has regional
degree one.  In the latter case regional handshaking reaches a distinct true
prefix crossing, which the source geometry classifies as a historical literal
Cell interface.

This is the parity reduction needed before internal historical interfaces are
absorbed to the two displayed old ports.  It does not perform that absorption.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TerminalProfileSeamResidual
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseTrackedEscapeEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Graph degree is independent of the finite presentation chosen for the
same neighbor set. -/
private theorem degree_eq_of_graph_eq {W : Type*}
    {H K : SimpleGraph W} (hHK : H = K) (vertex : W)
    (hH : Fintype (H.neighborSet vertex))
    (hK : Fintype (K.neighborSet vertex)) :
    @SimpleGraph.degree W H vertex hH =
      @SimpleGraph.degree W K vertex hK := by
  subst K
  apply congrArg Finset.card
  ext neighbor
  simp

/-- Removing a displayed ambient neighbor strictly lowers the degree in the
regional tracked graph. -/
theorem regionalTrackedEdgeGraph_degree_lt_of_adj_not_mem_region
    {E : Type*} [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (region : Finset E)
    (color : E → Color) (first second : Color) {edge outside : E}
    (hadj : (RS.trackedEdgeGraph color first second).Adj edge outside)
    (houtside : outside ∉ region) :
    (regionalTrackedEdgeGraph RS region color first second).degree edge <
      (RS.trackedEdgeGraph color first second).degree edge := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro neighbor hneighbor
    rw [SimpleGraph.mem_neighborFinset] at hneighbor ⊢
    exact hneighbor.1
  · intro heq
    have houtsideAmbient : outside ∈
        (RS.trackedEdgeGraph color first second).neighborFinset edge := by
      rw [SimpleGraph.mem_neighborFinset]
      exact hadj
    have houtsideRegional : outside ∈
        (regionalTrackedEdgeGraph RS region color first second).neighborFinset
          edge := by
      rw [heq]
      exact houtsideAmbient
    rw [SimpleGraph.mem_neighborFinset] at houtsideRegional
    exact houtside houtsideRegional.2.2

namespace SourceTrail

namespace AnnularEmbedding

/-- Every tracked boundary-rebase adjacency has an oriented old endpoint.  In
the old regional graph that endpoint is either isolated, or its component
reaches a distinct input/output crossing of a historical literal Cell.

The second alternative is deliberately not yet identified with one of the
two displayed old-profile ports. -/
theorem sourceCorridorSerialBoundaryRebaseTrackedSeamAt_adj_oldEndpoint_isolated_or_reaches_historicalCellCrossing
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcolor : embedded.cellulation.rotation.toRotationSystem
      |>.IsTaitEdgeColoring color)
    {first second : Color} (hpair : ValidColorPair first second)
    {x y : G.edgeSet}
    (hadj : (sourceCorridorSerialBoundaryRebaseTrackedSeamAt realization
      hcubic hrotation htwoSided hunique offset hnext color first second).Adj
        x y) :
    ∃ old new : G.edgeSet,
      (embedded.cellulation.rotation.toRotationSystem.trackedEdgeGraph
        color first second).Adj old new ∧
      old ∈ (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionEdges ∧
      new ∉ (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionEdges ∧
      (∃ historical : Fin (blockLength - 3),
        historical.val < offset.val + 1 ∧
        ((∃ step : Fin 2,
            old = (sourceSlabInterfaceAt realization hcubic hrotation
              htwoSided hunique historical).localLayerPrefixCrossing step) ∨
          ∃ step : Fin 2,
            old = (sourceSlabInterfaceAt realization hcubic hrotation
              htwoSided hunique historical).nextLocalLayerPrefixCrossing
                step)) ∧
      (((regionalTrackedEdgeGraph
          embedded.cellulation.rotation.toRotationSystem
          (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
            htwoSided hunique offset).regionEdges
          color first second).degree old = 0) ∨
        ∃ finish : G.edgeSet, finish ≠ old ∧
          (∃ historical : Fin (blockLength - 3),
            historical.val < offset.val + 1 ∧
            ((∃ step : Fin 2,
                finish = (sourceSlabInterfaceAt realization hcubic hrotation
                  htwoSided hunique historical).localLayerPrefixCrossing step) ∨
              ∃ step : Fin 2,
                finish = (sourceSlabInterfaceAt realization hcubic hrotation
                  htwoSided hunique historical).nextLocalLayerPrefixCrossing
                    step)) ∧
          (regionalTrackedEdgeGraph
            embedded.cellulation.rotation.toRotationSystem
            (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
              htwoSided hunique offset).regionEdges
            color first second).Reachable old finish) := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let oldRegion :=
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
  let oldGraph := regionalTrackedEdgeGraph RS oldRegion color first second
  have holdBoundary :=
    sourceCorridorSerialBoundaryRebaseTrackedSeamAt_adj_oldEndpoint_mem_truePrefixCrossing
      realization hcubic hrotation htwoSided hunique offset hnext color first
        second hadj
  have hraw := (regionalTrackedSeamGraph_adj_iff RS oldRegion
    (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic hrotation
      htwoSided hunique offset hnext) color first second x y).1 hadj
  have finish_or_isolated
      (old new : G.edgeSet)
      (hadjAmbient : (RS.trackedEdgeGraph color first second).Adj old new)
      (hold : old ∈ oldRegion) (hnew : new ∉ oldRegion) :
      oldGraph.degree old = 0 ∨
        ∃ finish : G.edgeSet, finish ≠ old ∧
          (∃ historical : Fin (blockLength - 3),
            historical.val < offset.val + 1 ∧
            ((∃ step : Fin 2,
                finish = (sourceSlabInterfaceAt realization hcubic hrotation
                  htwoSided hunique historical).localLayerPrefixCrossing step) ∨
              ∃ step : Fin 2,
                finish = (sourceSlabInterfaceAt realization hcubic hrotation
                  htwoSided hunique historical).nextLocalLayerPrefixCrossing
                    step)) ∧
          oldGraph.Reachable old finish := by
    have hselected : IsTrackedColor first second (color old) :=
      hadjAmbient.2.1
    have hambientDegreeRaw :=
      trackedEdgeGraph_degree_eq_two_of_cubic_tait
        embedded.cellulation.rotation hcubic color hcolor hpair old hselected
    have hambientDegree :
        (RS.trackedEdgeGraph color first second).degree old = 2 :=
      by
        rw [degree_eq_of_graph_eq rfl old _ _]
        exact hambientDegreeRaw
    have hdegreeLt : oldGraph.degree old <
        (RS.trackedEdgeGraph color first second).degree old :=
      regionalTrackedEdgeGraph_degree_lt_of_adj_not_mem_region RS oldRegion
        color first second hadjAmbient hnew
    by_cases hzero : oldGraph.degree old = 0
    · exact Or.inl hzero
    · have hone : oldGraph.degree old = 1 := by omega
      have hodd : Odd (oldGraph.degree old) := by simp [hone]
      have hoddExplicit : Odd ((regionalTrackedEdgeGraph
          embedded.cellulation.rotation.toRotationSystem
          (sourceCorridorSerialPrefixRegion realization hcubic hrotation
            htwoSided hunique (offset.val + 1))
          color first second).degree old) := by
        rw [← degree_eq_of_graph_eq rfl old _ _]
        simpa [oldGraph, oldRegion, RS,
          sourceCorridorSerialPrefixCutDataAt,
          regionalBoundaryGraphCutData] using hodd
      exact Or.inr
        (exists_distinct_reachable_historicalCellCrossing_of_odd_degree
          realization hcubic hrotation htwoSided hunique (offset.val + 1)
          color hcolor hpair old hoddExplicit)
  rcases hraw.2 with hforward | hbackward
  · have hxBoundary : x ∈
        sourceCorridorSerialPrefixTrueCrossingEdges realization hcubic
          hrotation htwoSided hunique (offset.val + 1) := by
      rcases holdBoundary with hx | hy
      · exact hx.2
      · exact False.elim (hforward.2.2.2 hy.1)
    have hxHistorical :=
      sourceCorridorSerialPrefixTrueCrossingEdge_eq_cell_input_or_output
        realization hcubic hrotation htwoSided hunique (offset.val + 1)
          hxBoundary
    refine ⟨x, y, hraw.1, hforward.1, hforward.2.2.2, hxHistorical, ?_⟩
    exact finish_or_isolated x y hraw.1 hforward.1 hforward.2.2.2
  · have hyBoundary : y ∈
        sourceCorridorSerialPrefixTrueCrossingEdges realization hcubic
          hrotation htwoSided hunique (offset.val + 1) := by
      rcases holdBoundary with hx | hy
      · exact False.elim (hbackward.2.1 hx.1)
      · exact hy.2
    have hyHistorical :=
      sourceCorridorSerialPrefixTrueCrossingEdge_eq_cell_input_or_output
        realization hcubic hrotation htwoSided hunique (offset.val + 1)
          hyBoundary
    refine ⟨y, x, hraw.1.symm, hbackward.2.2.1, hbackward.2.1,
      hyHistorical, ?_⟩
    exact finish_or_isolated y x hraw.1.symm hbackward.2.2.1 hbackward.2.1

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
