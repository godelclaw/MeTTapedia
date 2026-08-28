import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedCellRebaseInteractionCarrier
import Mettapedia.GraphTheory.FourColor.GoertzelV24SquareGraphComposition
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphSupResidual

/-!
# Exact facial recurrence for a pointwise-selected boundary rebase

Pointwise selection replaces the invalid global shared-edge selector by one
selector on each annular interior face.  The regional edge sets before and
after a boundary rebase still differ only on the four finite rebase roles.

This file transports the exact facial collar recurrence to that corrected
geometry.  The successor regional face graph is the union of the unchanged
core and a residual supported on the established twenty-four-dart collar.
No colouring or global face-pair uniqueness assumption occurs.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24RotationFaceRegionalDartGraph
open GoertzelV24SimpleGraphSupResidual
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedBoundaryRebaseFaceRecurrenceEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Formation

open Instance.LocalLayerFormation

/-- The common old/new region after removing the four rebase roles. -/
noncomputable def pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCoreRegionAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) : Finset G.edgeSet :=
  pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation
      corridor hinterior offset \
    pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt formation corridor
      hinterior offset hnext

/-- Removing the switch from either regional presentation gives the same
literal core. -/
theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCoreRegionAt_eq_next_sdiff
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCoreRegionAt formation
        corridor hinterior offset hnext =
      pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
          corridor hinterior (sourceLocalLayerNextOffset offset hnext) \
        pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt formation
          corridor hinterior offset hnext := by
  ext edge
  simp only [pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCoreRegionAt,
    Finset.mem_sdiff]
  by_cases hswitch : edge ∈
      pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt formation corridor
        hinterior offset hnext
  · simp [hswitch]
  · simp only [hswitch, not_false_eq_true, and_true]
    exact
      pointwiseSelectedSourceLocalLayerSerialPreRebaseOutput_mem_iff_nextTerminalInput_of_not_mem_switch
        formation corridor hinterior offset hnext edge hswitch

/-- Every changed dart belongs to the selected one-step face collar. -/
theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseChangedFaceDartsAt_subset_collar
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    pointwiseSelectedSourceLocalLayerBoundaryRebaseChangedFaceDartsAt formation
        corridor hinterior offset hnext ⊆
      pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt formation
        corridor hinterior offset hnext := by
  intro dart hdart
  rw [pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt,
    Finset.mem_biUnion]
  exact ⟨dart, hdart, by simp⟩

theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt_phi_mem
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    {dart : formation.annular.RS.D}
    (hdart : dart ∈
      pointwiseSelectedSourceLocalLayerBoundaryRebaseChangedFaceDartsAt
        formation corridor hinterior offset hnext) :
    formation.annular.RS.phi dart ∈
      pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt formation
        corridor hinterior offset hnext := by
  rw [pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt,
    Finset.mem_biUnion]
  exact ⟨dart, hdart, by simp⟩

theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt_phi_symm_mem
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    {dart : formation.annular.RS.D}
    (hdart : dart ∈
      pointwiseSelectedSourceLocalLayerBoundaryRebaseChangedFaceDartsAt
        formation corridor hinterior offset hnext) :
    formation.annular.RS.phi.symm dart ∈
      pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt formation
        corridor hinterior offset hnext := by
  rw [pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt,
    Finset.mem_biUnion]
  exact ⟨dart, hdart, by simp⟩

/-- If one endpoint of a regional facial adjacency lies over a changed edge,
both endpoints lie in the one-step selected collar. -/
theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt_of_adj_of_changed
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (region : Finset G.edgeSet) {left right : formation.annular.RS.D}
    (hadj : (faceRegionalDartGraph formation.annular.RS region).Adj left right)
    (hchanged : formation.annular.RS.edgeOf left ∈
      pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt formation corridor
        hinterior offset hnext) :
    left ∈ pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt formation
        corridor hinterior offset hnext ∧
      right ∈ pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt
        formation corridor hinterior offset hnext := by
  have hleftChanged : left ∈
      pointwiseSelectedSourceLocalLayerBoundaryRebaseChangedFaceDartsAt
        formation corridor hinterior offset hnext := by
    simpa [pointwiseSelectedSourceLocalLayerBoundaryRebaseChangedFaceDartsAt]
      using hchanged
  have hleftCollar :=
    pointwiseSelectedSourceLocalLayerBoundaryRebaseChangedFaceDartsAt_subset_collar
      formation corridor hinterior offset hnext hleftChanged
  rcases (faceRegionalDartGraph_adj formation.annular.RS region left right).1
      hadj with ⟨_hne, hstep, _hleftRegion, _hrightRegion⟩
  refine ⟨hleftCollar, ?_⟩
  rcases hstep with hforward | hbackward
  · subst right
    exact
      pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt_phi_mem
        formation corridor hinterior offset hnext hleftChanged
  · have hsymm : formation.annular.RS.phi.symm left = right := by
      apply formation.annular.RS.phi.injective
      simp [hbackward]
    rw [← hsymm]
    exact
      pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt_phi_symm_mem
        formation corridor hinterior offset hnext hleftChanged

/-- The literal selected successor regional face graph. -/
noncomputable def pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    SimpleGraph formation.annular.RS.D :=
  faceRegionalDartGraph formation.annular.RS
    (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
      corridor hinterior (sourceLocalLayerNextOffset offset hnext))

/-- The unchanged selected face graph on the common core. -/
noncomputable def pointwiseSelectedSourceLocalLayerBoundaryRebaseCoreFaceGraphAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    SimpleGraph formation.annular.RS.D :=
  faceRegionalDartGraph formation.annular.RS
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCoreRegionAt formation
      corridor hinterior offset hnext)

/-- The canonical selected successor residual not already in the common core. -/
noncomputable def pointwiseSelectedSourceLocalLayerBoundaryRebaseLocalFaceGraphAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    SimpleGraph formation.annular.RS.D :=
  supResidual
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt
      formation corridor hinterior offset hnext)
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseCoreFaceGraphAt formation
      corridor hinterior offset hnext)
    ⊥

theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseCoreFaceGraphAt_le_successor
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    pointwiseSelectedSourceLocalLayerBoundaryRebaseCoreFaceGraphAt formation
        corridor hinterior offset hnext ≤
      pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt
        formation corridor hinterior offset hnext := by
  intro left right hadj
  simp only [pointwiseSelectedSourceLocalLayerBoundaryRebaseCoreFaceGraphAt,
    pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt,
    faceRegionalDartGraph_adj] at hadj ⊢
  refine ⟨hadj.1, hadj.2.1, ?_, ?_⟩
  · rw [pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCoreRegionAt_eq_next_sdiff
      formation corridor hinterior offset hnext] at hadj
    exact (Finset.mem_sdiff.mp hadj.2.2.1).1
  · rw [pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCoreRegionAt_eq_next_sdiff
      formation corridor hinterior offset hnext] at hadj
    exact (Finset.mem_sdiff.mp hadj.2.2.2).1

/-- The selected successor is exactly its common core plus the local residual. -/
theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseCore_sup_local_eq_successor
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    pointwiseSelectedSourceLocalLayerBoundaryRebaseCoreFaceGraphAt formation
          corridor hinterior offset hnext ⊔
        pointwiseSelectedSourceLocalLayerBoundaryRebaseLocalFaceGraphAt formation
          corridor hinterior offset hnext =
      pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt
        formation corridor hinterior offset hnext := by
  have h := sup_sup_supResidual_eq
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt
      formation corridor hinterior offset hnext)
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseCoreFaceGraphAt formation
      corridor hinterior offset hnext)
    (⊥ : SimpleGraph formation.annular.RS.D)
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseCoreFaceGraphAt_le_successor
      formation corridor hinterior offset hnext)
    bot_le
  simpa [pointwiseSelectedSourceLocalLayerBoundaryRebaseLocalFaceGraphAt] using h

/-- Every dart touched by the genuinely local selected residual belongs to
the bounded selected collar. -/
theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseLocalFaceGraphAt_support_subset_collar
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseLocalFaceGraphAt formation
      corridor hinterior offset hnext).support ⊆
      pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt formation
        corridor hinterior offset hnext := by
  intro dart hdart
  rcases (SimpleGraph.mem_support _).1 hdart with ⟨other, hadj⟩
  have hresidual := (supResidual_adj
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt
      formation corridor hinterior offset hnext)
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseCoreFaceGraphAt formation
      corridor hinterior offset hnext)
    ⊥ dart other).1 hadj
  have hwhole := hresidual.1
  have hnotCore := hresidual.2.1
  have hchanged : formation.annular.RS.edgeOf dart ∈
        pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt formation
          corridor hinterior offset hnext ∨
      formation.annular.RS.edgeOf other ∈
        pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt formation
          corridor hinterior offset hnext := by
    by_contra hnot
    have hdartNot : formation.annular.RS.edgeOf dart ∉
        pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt formation
          corridor hinterior offset hnext := fun h => hnot (Or.inl h)
    have hotherNot : formation.annular.RS.edgeOf other ∉
        pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt formation
          corridor hinterior offset hnext := fun h => hnot (Or.inr h)
    apply hnotCore
    simp only [pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt,
      pointwiseSelectedSourceLocalLayerBoundaryRebaseCoreFaceGraphAt,
      faceRegionalDartGraph_adj] at hwhole ⊢
    refine ⟨hwhole.1, hwhole.2.1, ?_, ?_⟩
    · rw [pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCoreRegionAt_eq_next_sdiff
        formation corridor hinterior offset hnext]
      exact Finset.mem_sdiff.mpr ⟨hwhole.2.2.1, hdartNot⟩
    · rw [pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCoreRegionAt_eq_next_sdiff
        formation corridor hinterior offset hnext]
      exact Finset.mem_sdiff.mpr ⟨hwhole.2.2.2, hotherNot⟩
  rcases hchanged with hdartChanged | hotherChanged
  · apply
      pointwiseSelectedSourceLocalLayerBoundaryRebaseChangedFaceDartsAt_subset_collar
        formation corridor hinterior offset hnext
    simpa [pointwiseSelectedSourceLocalLayerBoundaryRebaseChangedFaceDartsAt]
      using hdartChanged
  · exact
      (pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt_of_adj_of_changed
        formation corridor hinterior offset hnext
        (pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
          corridor hinterior (sourceLocalLayerNextOffset offset hnext))
        hwhole.symm hotherChanged).2

/-- Exact selected successor reachability on the bounded collar. -/
theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessor_reachable_iff_collarComponentClosure
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (left right : formation.annular.RS.D)
    (hleft : left ∈
      pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt formation
        corridor hinterior offset hnext)
    (hright : right ∈
      pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt formation
        corridor hinterior offset hnext) :
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt
      formation corridor hinterior offset hnext).Reachable left right ↔
      Relation.ReflTransGen
        (fun first second : Subtype (fun dart =>
            dart ∈
              pointwiseSelectedSourceLocalLayerBoundaryRebaseFaceCollarAt
                formation corridor hinterior offset hnext) =>
          (pointwiseSelectedSourceLocalLayerBoundaryRebaseCoreFaceGraphAt
            formation corridor hinterior offset hnext).Reachable first.1
              second.1 ∨
          (pointwiseSelectedSourceLocalLayerBoundaryRebaseLocalFaceGraphAt
            formation corridor hinterior offset hnext).Reachable first.1
              second.1)
        ⟨left, hleft⟩ ⟨right, hright⟩ := by
  rw [← pointwiseSelectedSourceLocalLayerBoundaryRebaseCore_sup_local_eq_successor
    formation corridor hinterior offset hnext]
  apply reachable_sup_iff_subtype_componentClosure
  intro x middle y _hx hmiddleY _hcore hlocal
  apply
    pointwiseSelectedSourceLocalLayerBoundaryRebaseLocalFaceGraphAt_support_subset_collar
      formation corridor hinterior offset hnext
  exact SimpleGraph.mem_support_of_reachable hmiddleY hlocal

end Formation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
