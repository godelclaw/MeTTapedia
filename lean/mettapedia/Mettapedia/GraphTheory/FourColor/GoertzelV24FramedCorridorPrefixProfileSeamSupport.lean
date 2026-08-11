import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicFaceBoundaryAdjacency
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixProfileSeamCorners

/-!
# Support localization for a source corridor-prefix seam

An edge of the cumulative old prefix that is adjacent to an edge of the new
Cell cannot come from an earlier corridor face.  Otherwise the generic cubic
corner theorem would make that earlier face dual-adjacent to the new Cell,
contradicting inducedness of the corridor.  Thus every residual seam turn is
localized at the immediately preceding source hexagon.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CubicFaceBoundaryAdjacency
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorColorTransfer
open GoertzelV24HexCorridorPrefixProfile
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexCorridorSlab
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabSideAdjacency
open GoertzelV24OrbitFaceTwoSided
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorPrefixProfileSeamSupportEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- At a cubic vertex, three distinct known incident edges exhaust the
incident-edge fiber. -/
private theorem incidentEdge_eq_first_or_second_or_third
    (RS : RotationSystem V G.edgeSet) (hcubic : RS.IsCubic)
    {vertex : V} {first second third edge : G.edgeSet}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hfirst : first ∈ RS.incidentEdges vertex)
    (hsecond : second ∈ RS.incidentEdges vertex)
    (hthird : third ∈ RS.incidentEdges vertex)
    (hedge : edge ∈ RS.incidentEdges vertex) :
    edge = first ∨ edge = second ∨ edge = third := by
  have hsubset : ({first, second, third} : Finset G.edgeSet) ⊆
      RS.incidentEdges vertex := by
    intro candidate hcandidate
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcandidate
    rcases hcandidate with rfl | rfl | rfl
    · exact hfirst
    · exact hsecond
    · exact hthird
  have hcard : ({first, second, third} : Finset G.edgeSet).card = 3 := by
    simp [hfirstSecond, hfirstThird, hsecondThird]
  have hexhaust : ({first, second, third} : Finset G.edgeSet) =
      RS.incidentEdges vertex := by
    apply Finset.eq_of_subset_of_card_le hsubset
    rw [RS.incidentEdges_card_eq_three_of_isCubic hcubic, hcard]
  have hedge' : edge ∈ ({first, second, third} : Finset G.edgeSet) := by
    rw [hexhaust]
    exact hedge
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hedge'

namespace SourceTrail

namespace AnnularEmbedding

namespace SourceConsecutiveSlabInterface

variable {source : SourceTrail G}
  {embedded : source.AnnularEmbedding} {blockLength : Nat}
  {realization : BoundaryCleanCorridorRealization embedded blockLength}
  {htwoSided : OrbitFacesTwoSided
    embedded.cellulation.rotation.toRotationSystem}
  {hunique : PairwiseUniqueSharedInteriorEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
  {leftInterior : CorridorInterior blockLength}
  {hnext : leftInterior.center.val + 2 < blockLength}

/-- Any old-prefix edge adjacent to an edge of the newly exposed Cell already
lies on the immediately preceding corridor face.  Earlier prefix faces are
excluded by the corridor's inducedness in the full facial dual. -/
theorem leftPrefixEdge_mem_previousFaceBoundary_of_adj_cellBoundary
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    {leftEdge rightEdge : G.edgeSet}
    (hleft : leftEdge ∈ interface.localLayerLeftPrefixRegion)
    (hright : rightEdge ∈ interface.localLayerCellBoundaryRegion)
    (hadj : embedded.cellulation.rotation.toRotationSystem.edgeAdjacencyGraph.Adj
      leftEdge rightEdge) :
    leftEdge ∈ orbitFaceBoundary
      embedded.cellulation.rotation.toRotationSystem
      (realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
        |>.faceAt leftInterior.center).1 := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let corridor := realization.toCleanOrbitHexCorridorSkeleton
    |>.toOrbitHexCorridorSkeleton
  have hleftPrefix : leftEdge ∈ corridorPrefixEdgeRegion corridor
      (leftInterior.center.val + 1) := by
    simpa [localLayerLeftPrefixRegion, corridor] using hleft
  have hrightCell : rightEdge ∈ orbitFaceBoundary RS
      (corridor.faceAt (nextCorridorInterior leftInterior hnext).center).1 := by
    simpa [localLayerCellBoundaryRegion, nextCenterLayerFace, RS, corridor]
      using hright
  rw [mem_corridorPrefixEdgeRegion_iff] at hleftPrefix
  rcases hleftPrefix with ⟨position, hposition, hleftPosition⟩
  by_cases hcenter : position = leftInterior.center
  · subst position
    exact hleftPosition
  · have hbefore : position.val < leftInterior.center.val := by omega
    have hseparated : position.val + 1 <
        (nextCorridorInterior leftInterior hnext).center.val := by
      change position.val + 1 < leftInterior.center.val + 1
      omega
    have hfacesNe : (corridor.faceAt position).1 ≠
        (corridor.faceAt
          (nextCorridorInterior leftInterior hnext).center).1 := by
      intro hfaces
      have hindices := corridor.faceAt_injective (Subtype.ext hfaces)
      have hvalues := congrArg Fin.val hindices
      change position.val = leftInterior.center.val + 1 at hvalues
      omega
    have hdual := interiorDualGraph_adj_of_edgeAdjacencyGraph_adj
      RS hcubic hrotation htwoSided hfacesNe hleftPosition hrightCell hadj
    exact (corridor.separated_not_adjacent position
      (nextCorridorInterior leftInterior hnext).center hseparated hdual).elim

/-- An adjacency crossing exclusively from the old prefix into the new Cell
is localized at an endpoint of their unique shared rung. -/
theorem exists_sharedRung_endpoint_of_left_only_right_only_adj
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    {leftEdge rightEdge : G.edgeSet}
    (hleft : leftEdge ∈ interface.localLayerLeftPrefixRegion)
    (hleftNotCell : leftEdge ∉ interface.localLayerCellBoundaryRegion)
    (hright : rightEdge ∈ interface.localLayerCellBoundaryRegion)
    (hrightNotLeft : rightEdge ∉ interface.localLayerLeftPrefixRegion)
    (hadj : embedded.cellulation.rotation.toRotationSystem.edgeAdjacencyGraph.Adj
      leftEdge rightEdge) :
    ∃ vertex : V,
      vertex ∈ embedded.cellulation.rotation.toRotationSystem.endpoints
        interface.localLayerSharedRungEdge ∧
      leftEdge ∈ embedded.cellulation.rotation.toRotationSystem.incidentEdges vertex ∧
      rightEdge ∈ embedded.cellulation.rotation.toRotationSystem.incidentEdges vertex := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let corridor := realization.toCleanOrbitHexCorridorSkeleton
    |>.toOrbitHexCorridorSkeleton
  let rightInterior := nextCorridorInterior leftInterior hnext
  have hfaces : (corridor.faceAt leftInterior.center).1 ≠
      (corridor.faceAt rightInterior.center).1 := by
    intro hface
    have hindices := corridor.faceAt_injective (Subtype.ext hface)
    have hvalues := congrArg Fin.val hindices
    change leftInterior.center.val = leftInterior.center.val + 1 at hvalues
    omega
  have hshared : interface.localLayerSharedRungEdge ∈
      sharedInteriorEdges (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))
        (corridor.faceAt leftInterior.center).1
        (corridor.faceAt rightInterior.center).1 := by
    simpa [SourceConsecutiveSlabInterface.localLayerSharedRungEdge,
      OrbitHexCorridorSkeleton.rungEdge, rightInterior,
      nextCorridorInterior, RS, corridor] using
      (sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_sharedInteriorEdges
        (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS)) hunique
        (corridor.consecutive_adjacent leftInterior.outgoing.left
          leftInterior.outgoing.right rfl))
  have hleftFace : leftEdge ∈ orbitFaceBoundary RS
      (corridor.faceAt leftInterior.center).1 := by
    exact interface.leftPrefixEdge_mem_previousFaceBoundary_of_adj_cellBoundary
      hcubic hrotation hleft hright hadj
  have hleftNotRightFace : leftEdge ∉ orbitFaceBoundary RS
      (corridor.faceAt rightInterior.center).1 := by
    simpa [SourceConsecutiveSlabInterface.localLayerCellBoundaryRegion,
      SourceConsecutiveSlabInterface.nextCenterLayerFace,
      rightInterior, RS, corridor] using hleftNotCell
  have hrightFace : rightEdge ∈ orbitFaceBoundary RS
      (corridor.faceAt rightInterior.center).1 := by
    simpa [SourceConsecutiveSlabInterface.localLayerCellBoundaryRegion,
      SourceConsecutiveSlabInterface.nextCenterLayerFace,
      rightInterior, RS, corridor] using hright
  have hrightNotLeftFace : rightEdge ∉ orbitFaceBoundary RS
      (corridor.faceAt leftInterior.center).1 := by
    intro hrightFaceLeft
    apply hrightNotLeft
    apply corridorFaceBoundary_subset_prefixEdgeRegion corridor
      (leftInterior.center.val + 1) leftInterior.center (by omega)
    exact hrightFaceLeft
  exact exists_sharedEdge_endpoint_of_exclusive_adjacent_edges
    RS hcubic hrotation htwoSided hunique hfaces hshared
      hleftFace hleftNotRightFace hrightFace hrightNotLeftFace hadj

end SourceConsecutiveSlabInterface

namespace SourceCornerAlignedSlabInterface

variable {source : SourceTrail G}
  {embedded : source.AnnularEmbedding} {blockLength : Nat}
  {realization : BoundaryCleanCorridorRealization embedded blockLength}
  {htwoSided : OrbitFacesTwoSided
    embedded.cellulation.rotation.toRotationSystem}
  {hunique : PairwiseUniqueSharedInteriorEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
  {leftInterior : CorridorInterior blockLength}
  {hnext : leftInterior.center.val + 2 < blockLength}

/-- Every adjacency crossing exclusively from the old cumulative prefix into
the new source Cell is one of the two source-ordered turns at the endpoints
of their common rung. -/
theorem exists_crossing_step_of_left_only_right_only_adj
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    {leftEdge rightEdge : G.edgeSet}
    (hleft : leftEdge ∈ aligned.toInterface.localLayerLeftPrefixRegion)
    (hleftNotCell : leftEdge ∉
      aligned.toInterface.localLayerCellBoundaryRegion)
    (hright : rightEdge ∈ aligned.toInterface.localLayerCellBoundaryRegion)
    (hrightNotLeft : rightEdge ∉
      aligned.toInterface.localLayerLeftPrefixRegion)
    (hadj : embedded.cellulation.rotation.toRotationSystem.edgeAdjacencyGraph.Adj
      leftEdge rightEdge) :
    ∃ step : Fin 2,
      leftEdge = aligned.toInterface.localLayerPrefixCrossing step ∧
      rightEdge = aligned.toInterface.nextLocalLayerPrefixCrossing step := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let corridor := realization.toCleanOrbitHexCorridorSkeleton
    |>.toOrbitHexCorridorSkeleton
  let placement := realization.slabPlacementAt htwoSided hunique leftInterior
  let sideDart := faceCycleDart RS placement.root
    aligned.toInterface.leftBeforePos.1
  let outgoingDart := faceCycleDart RS placement.root
    placement.outgoingPosition
  rcases aligned.toInterface.exists_sharedRung_endpoint_of_left_only_right_only_adj
      hcubic hrotation hleft hleftNotCell hright hrightNotLeft hadj with
    ⟨common, hcommonShared, hcommonLeft, hcommonRight⟩
  have houtgoingEdge : RS.edgeOf outgoingDart =
      aligned.toInterface.localLayerSharedRungEdge := by
    simpa [RS, outgoingDart, faceCycleEdge,
      SourceConsecutiveSlabInterface.localLayerSharedRungEdge,
      placement, corridor] using placement.outgoing_edge
  have houtgoingOn : outgoingDart ∈ RS.dartsOn
      aligned.toInterface.localLayerSharedRungEdge := by
    exact (RS.mem_dartsOn).2 houtgoingEdge
  have hendpointPair := RS.endpoints_eq_pair_of_mem houtgoingOn
  rw [hendpointPair] at hcommonShared
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcommonShared
  rcases hcommonShared with hbefore | hafter
  · subst common
    have hdarts : outgoingDart = RS.phi sideDart :=
      faceCycleDart_successor_of_modEq RS placement.root placement.orbit_card
        aligned.toInterface.leftBeforePos.1 placement.outgoingPosition
        aligned.leftBefore_precedesOutgoing
    have hcorner := cornerEdges_pairwise_ne_and_incident
      RS hcubic hrotation sideDart
    have hfirstEq : RS.edgeOf sideDart =
        aligned.toInterface.localLayerPrefixCrossing (0 : Fin 2) := by
      rw [aligned.localLayerPrefixCrossing_zero_eq_leftBeforeEdge]
      rfl
    have hsecondEq : RS.edgeOf (RS.phi sideDart) =
        aligned.toInterface.localLayerSharedRungEdge := by
      rw [← hdarts]
      exact houtgoingEdge
    have hthirdEq : RS.edgeOf (RS.rho (RS.phi sideDart)) =
        aligned.toInterface.nextLocalLayerPrefixCrossing (0 : Fin 2) := by
      rw [← hdarts]
      simpa [RS, beforeOutgoingCornerEdge, outgoingDart, placement] using
        aligned.nextLocalLayerPrefixCrossing_zero_eq_beforeOutgoingCornerEdge.symm
    rw [hfirstEq, hsecondEq, hthirdEq] at hcorner
    rw [hdarts] at hcommonLeft hcommonRight
    have hleftCases := incidentEdge_eq_first_or_second_or_third
      RS hcubic hcorner.1 hcorner.2.1 hcorner.2.2.1
        hcorner.2.2.2.1 hcorner.2.2.2.2.1 hcorner.2.2.2.2.2 hcommonLeft
    have hrightCases := incidentEdge_eq_first_or_second_or_third
      RS hcubic hcorner.1 hcorner.2.1 hcorner.2.2.1
        hcorner.2.2.2.1 hcorner.2.2.2.2.1 hcorner.2.2.2.2.2 hcommonRight
    have hleftEq : leftEdge =
        aligned.toInterface.localLayerPrefixCrossing (0 : Fin 2) := by
      rcases hleftCases with hleftEq | hleftShared | hleftRight
      · exact hleftEq
      · exact (hleftNotCell (hleftShared.symm ▸
          aligned.toInterface.localLayerSharedRungEdge_mem_cellBoundary)).elim
      · exact (hleftNotCell (hleftRight.symm ▸
          aligned.nextLocalLayerPrefixCrossing_mem_cellBoundaryRegion 0)).elim
    have hrightEq : rightEdge =
        aligned.toInterface.nextLocalLayerPrefixCrossing (0 : Fin 2) := by
      rcases hrightCases with hrightLeft | hrightShared | hrightEq
      · exact (hrightNotLeft (hrightLeft.symm ▸
          aligned.localLayerPrefixCrossing_mem_leftPrefixRegion 0)).elim
      · exact (hrightNotLeft (hrightShared.symm ▸
          aligned.toInterface.localLayerSharedRungEdge_mem_leftPrefix)).elim
      · exact hrightEq
    exact ⟨0, hleftEq, hrightEq⟩
  · subst common
    let afterDart := faceCycleDart RS placement.root
      aligned.toInterface.leftAfterPos.1
    have hdartsAfter : afterDart = RS.phi outgoingDart :=
      faceCycleDart_successor_of_modEq RS placement.root placement.orbit_card
        placement.outgoingPosition aligned.toInterface.leftAfterPos.1
        aligned.leftAfter_followsOutgoing
    have hcorner := cornerEdges_pairwise_ne_and_incident
      RS hcubic hrotation outgoingDart
    have hfirstEq : RS.edgeOf outgoingDart =
        aligned.toInterface.localLayerSharedRungEdge := houtgoingEdge
    have hsecondEq : RS.edgeOf (RS.phi outgoingDart) =
        aligned.toInterface.localLayerPrefixCrossing (1 : Fin 2) := by
      rw [← hdartsAfter]
      rw [aligned.localLayerPrefixCrossing_one_eq_leftAfterEdge]
      rfl
    have hthirdEq : RS.edgeOf (RS.rho (RS.phi outgoingDart)) =
        aligned.toInterface.nextLocalLayerPrefixCrossing (1 : Fin 2) := by
      simpa [RS, afterOutgoingCornerEdge, outgoingDart, placement] using
        aligned.nextLocalLayerPrefixCrossing_one_eq_afterOutgoingCornerEdge.symm
    rw [hfirstEq, hsecondEq, hthirdEq] at hcorner
    rw [← RS.vert_phi_eq_vert_alpha outgoingDart] at hcommonLeft hcommonRight
    have hleftCases := incidentEdge_eq_first_or_second_or_third
      RS hcubic hcorner.1 hcorner.2.1 hcorner.2.2.1
        hcorner.2.2.2.1 hcorner.2.2.2.2.1 hcorner.2.2.2.2.2 hcommonLeft
    have hrightCases := incidentEdge_eq_first_or_second_or_third
      RS hcubic hcorner.1 hcorner.2.1 hcorner.2.2.1
        hcorner.2.2.2.1 hcorner.2.2.2.2.1 hcorner.2.2.2.2.2 hcommonRight
    have hleftEq : leftEdge =
        aligned.toInterface.localLayerPrefixCrossing (1 : Fin 2) := by
      rcases hleftCases with hleftShared | hleftEq | hleftRight
      · exact (hleftNotCell (hleftShared.symm ▸
          aligned.toInterface.localLayerSharedRungEdge_mem_cellBoundary)).elim
      · exact hleftEq
      · exact (hleftNotCell (hleftRight.symm ▸
          aligned.nextLocalLayerPrefixCrossing_mem_cellBoundaryRegion 1)).elim
    have hrightEq : rightEdge =
        aligned.toInterface.nextLocalLayerPrefixCrossing (1 : Fin 2) := by
      rcases hrightCases with hrightShared | hrightLeft | hrightEq
      · exact (hrightNotLeft (hrightShared.symm ▸
          aligned.toInterface.localLayerSharedRungEdge_mem_leftPrefix)).elim
      · exact (hrightNotLeft (hrightLeft.symm ▸
          aligned.localLayerPrefixCrossing_mem_leftPrefixRegion 1)).elim
      · exact hrightEq
    exact ⟨1, hleftEq, hrightEq⟩

/-- The exact tracked seam support consists of the two source-ordered corner
turns, in either graph orientation, whenever their endpoint colors are among
the tracked pair. -/
theorem localLayerTrackedSeamGraph_adj_iff_exists_crossing_step
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (C : G.edgeSet → Color) (a b : Color) (x y : G.edgeSet) :
    (aligned.toInterface.localLayerTrackedSeamGraph C a b).Adj x y ↔
      ∃ step : Fin 2,
        IsTrackedColor a b
            (C (aligned.toInterface.localLayerPrefixCrossing step)) ∧
          IsTrackedColor a b
            (C (aligned.toInterface.nextLocalLayerPrefixCrossing step)) ∧
          ((x = aligned.toInterface.localLayerPrefixCrossing step ∧
              y = aligned.toInterface.nextLocalLayerPrefixCrossing step) ∨
            (x = aligned.toInterface.nextLocalLayerPrefixCrossing step ∧
              y = aligned.toInterface.localLayerPrefixCrossing step)) := by
  unfold SourceConsecutiveSlabInterface.localLayerTrackedSeamGraph
  rw [GoertzelV24TerminalProfileSeamResidual.regionalTrackedSeamGraph_adj_iff]
  constructor
  · rintro ⟨⟨hadj, hxColor, hyColor⟩, hcross⟩
    rcases hcross with hforward | hbackward
    · rcases aligned.exists_crossing_step_of_left_only_right_only_adj
        hcubic hrotation hforward.1 hforward.2.1 hforward.2.2.1
          hforward.2.2.2 hadj with ⟨step, hx, hy⟩
      subst x
      subst y
      exact ⟨step, hxColor, hyColor, Or.inl ⟨rfl, rfl⟩⟩
    · rcases aligned.exists_crossing_step_of_left_only_right_only_adj
        hcubic hrotation hbackward.2.2.1 hbackward.2.2.2 hbackward.1
          hbackward.2.1 hadj.symm with ⟨step, hy, hx⟩
      subst x
      subst y
      exact ⟨step, hyColor, hxColor, Or.inr ⟨rfl, rfl⟩⟩
  · rintro ⟨step, hleftColor, hrightColor, horientation⟩
    rcases horientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (GoertzelV24TerminalProfileSeamResidual.regionalTrackedSeamGraph_adj_iff
        embedded.cellulation.rotation.toRotationSystem
        aligned.toInterface.localLayerLeftPrefixRegion
        aligned.toInterface.localLayerCellBoundaryRegion C a b _ _).1
          (aligned.localLayerTrackedSeamGraph_adj_crossings
            hcubic hrotation C a b step hleftColor hrightColor)
    · exact (GoertzelV24TerminalProfileSeamResidual.regionalTrackedSeamGraph_adj_iff
        embedded.cellulation.rotation.toRotationSystem
        aligned.toInterface.localLayerLeftPrefixRegion
        aligned.toInterface.localLayerCellBoundaryRegion C a b _ _).1
          (aligned.localLayerTrackedSeamGraph_adj_crossings
            hcubic hrotation C a b step hleftColor hrightColor).symm

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
