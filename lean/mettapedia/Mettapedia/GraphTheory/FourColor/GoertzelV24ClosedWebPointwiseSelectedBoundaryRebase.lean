import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedSerialTerminalProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebase

/-!
# Boundary rebase for pointwise-selected source Cells

After adjoining a pointwise-selected literal Cell, the cumulative region is
unchanged away from four finite roles: the consumed rung, the successor's two
incoming crossings, and the successor rung.  This file ports the exact set
locality theorem to the corrected selected geometry, using only annular-
interior uniqueness.

The finite role type is shared with the established boundary-rebase ABI.  No
colouring, global unique-shared-edge hypothesis, or profile encoding occurs in
this geometric layer.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24RegionalBoundaryProfileFiniteState
open SimpleGraphDartRotation
open scoped symmDiff

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedBoundaryRebaseEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Formation

open Instance.LocalLayerFormation

/-- Interpret an established finite rebase role in the corrected pointwise-
selected source geometry. -/
noncomputable def pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    SourceLocalLayerBoundaryRebaseRole → G.edgeSet
  | .inl _ => pointwiseSelectedSourceLocalLayerSharedRungAt formation corridor
      hinterior offset
  | .inr (.inl step) => pointwiseSelectedSourceLocalLayerLeftCrossingAt
      formation corridor hinterior (sourceLocalLayerNextOffset offset hnext)
      step
  | .inr (.inr _) => pointwiseSelectedSourceLocalLayerSharedRungAt formation
      corridor hinterior (sourceLocalLayerNextOffset offset hnext)

/-- The complete finite support on which the pointwise-selected boundary
rebase may change regional membership. -/
noncomputable def pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) : Finset G.edgeSet :=
  Finset.univ.image
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation corridor
      hinterior offset hnext)

theorem mem_pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt_iff
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) (edge : G.edgeSet) :
    edge ∈ pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt formation
        corridor hinterior offset hnext ↔
      ∃ role : SourceLocalLayerBoundaryRebaseRole,
        pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation corridor
          hinterior offset hnext role = edge := by
  simp [pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt]

/-- The selected rebase switch has at most the four ABI roles.  Coincident
roles only make its ambient support smaller. -/
theorem card_pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt_le_four
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt formation corridor
      hinterior offset hnext).card ≤ 4 := by
  calc
    (pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt formation corridor
        hinterior offset hnext).card ≤
        (Finset.univ : Finset SourceLocalLayerBoundaryRebaseRole).card := by
      exact Finset.card_image_le
    _ = 4 := by simp [SourceLocalLayerBoundaryRebaseRole]

/-- Outside the four-role switch, the current pre-rebase output and the next
terminal-aware input have exactly the same regional membership. -/
theorem pointwiseSelectedSourceLocalLayerSerialPreRebaseOutput_mem_iff_nextTerminalInput_of_not_mem_switch
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) (edge : G.edgeSet)
    (hout : edge ∉ pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt
      formation corridor hinterior offset hnext) :
    edge ∈ pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt
        formation corridor hinterior offset ↔
      edge ∈ pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt
        formation corridor hinterior
          (sourceLocalLayerNextOffset offset hnext) := by
  have holdRung : edge ≠ pointwiseSelectedSourceLocalLayerSharedRungAt
      formation corridor hinterior offset := by
    intro heq
    apply hout
    rw [mem_pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt_iff]
    exact ⟨.inl (0 : Fin 1), by
      simpa [pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt] using
        heq.symm⟩
  have hnextCrossing : ∀ step : Fin 2,
      edge ≠ pointwiseSelectedSourceLocalLayerLeftCrossingAt formation corridor
        hinterior (sourceLocalLayerNextOffset offset hnext) step := by
    intro step heq
    apply hout
    rw [mem_pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt_iff]
    exact ⟨.inr (.inl step), by
      simpa [pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt] using
        heq.symm⟩
  have hnextRung : edge ≠ pointwiseSelectedSourceLocalLayerSharedRungAt
      formation corridor hinterior
        (sourceLocalLayerNextOffset offset hnext) := by
    intro heq
    apply hout
    rw [mem_pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt_iff]
    exact ⟨.inr (.inr (0 : Fin 1)), by
      simpa [pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt] using
        heq.symm⟩
  simp only [pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt,
    pointwiseSelectedSourceLocalLayerSerialOutputRegionAt,
    pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt,
    pointwiseSelectedSourceLocalLayerSerialInputRegionAt, Finset.mem_union,
    Finset.mem_singleton, holdRung, or_false, hnextRung]
  have hcrossing : edge ∉ indexedCrossingEdgeSet
      (pointwiseSelectedSourceLocalLayerLeftCrossingAt formation corridor
        hinterior (sourceLocalLayerNextOffset offset hnext)) := by
    rw [mem_indexedCrossingEdgeSet_iff]
    rintro ⟨step, heq⟩
    exact hnextCrossing step heq.symm
  simp only [hcrossing, or_false]
  rfl

/-- Equivalently, the two selected regional presentations differ only on the
four-role switch. -/
theorem pointwiseSelectedSourceLocalLayerSerialBoundaryRebase_symmDiff_subset_switch
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation
          corridor hinterior offset ∆
        pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
          corridor hinterior (sourceLocalLayerNextOffset offset hnext) ⊆
      pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt formation corridor
        hinterior offset hnext := by
  intro edge hdiff
  by_contra hout
  have hagree :=
    pointwiseSelectedSourceLocalLayerSerialPreRebaseOutput_mem_iff_nextTerminalInput_of_not_mem_switch
      formation corridor hinterior offset hnext edge hout
  rw [Finset.mem_symmDiff] at hdiff
  rcases hdiff with ⟨hleft, hright⟩ | ⟨hright, hleft⟩
  · exact hright (hagree.1 hleft)
  · exact hleft (hagree.2 hright)

end Formation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
