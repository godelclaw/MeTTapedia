import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialTerminalProfile
import Mathlib.Data.Finset.SymmDiff

/-!
# Finite boundary rebase between consecutive actual source Cells

After one literal Cell is adjoined, the cumulative region is unchanged away
from a finite seam switch: the old shared rung is forgotten, the next two
crossings are exposed, and the next shared rung becomes the terminal.  This
file gives those four roles a fixed finite coordinate and proves that the
pre-rebase and next-input regions agree outside its image.

This is the carrier localization required by the finite five-coordinate
rebase.  It does not yet assert equality of the profiles across the switch or
provide a semantic transition without the corresponding connectivity and face
updates.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

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

local instance closedWebLocalLayerSerialBoundaryRebaseEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- The next literal Cell index when the current one is not terminal. -/
def sourceLocalLayerNextOffset {blockLength : Nat}
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) : Fin (blockLength - 3) :=
  ⟨offset.val + 1, hnext⟩

@[simp]
theorem sourceLocalLayerNextOffset_val {blockLength : Nat}
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    (sourceLocalLayerNextOffset offset hnext).val = offset.val + 1 :=
  rfl

/-- Four stable names for the only edges whose regional status can change at
one boundary rebase. -/
abbrev SourceLocalLayerBoundaryRebaseRole := Fin 1 ⊕ (Fin 2 ⊕ Fin 1)

/-- Interpret one finite rebase role as its literal ambient edge. -/
noncomputable def sourceLocalLayerBoundaryRebaseEdgeAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    SourceLocalLayerBoundaryRebaseRole → G.edgeSet
  | .inl _ => sourceLocalLayerSharedRungAt corridor hunique offset
  | .inr (.inl step) => sourceLocalLayerLeftCrossingAt corridor hunique
      (sourceLocalLayerNextOffset offset hnext) step
  | .inr (.inr _) => sourceLocalLayerSharedRungAt corridor hunique
      (sourceLocalLayerNextOffset offset hnext)

/-- The complete finite support on which the boundary rebase may change the
regional presentation. -/
noncomputable def sourceLocalLayerBoundaryRebaseSwitchAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) : Finset G.edgeSet :=
  Finset.univ.image
    (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext)

theorem mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) (edge : G.edgeSet) :
    edge ∈ sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext ↔
      ∃ role : SourceLocalLayerBoundaryRebaseRole,
        sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role = edge := by
  simp [sourceLocalLayerBoundaryRebaseSwitchAt]

/-- The switch has at most four literal edges; coincident role names only make
the support smaller. -/
theorem card_sourceLocalLayerBoundaryRebaseSwitchAt_le_four
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    (sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext).card ≤ 4 := by
  calc
    (sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext).card ≤
        (Finset.univ : Finset SourceLocalLayerBoundaryRebaseRole).card := by
      exact Finset.card_image_le
    _ = 4 := by simp [SourceLocalLayerBoundaryRebaseRole]

/-- Outside the four-role switch, the immediate successor and the next
terminal-aware input have exactly the same regional membership. -/
theorem sourceLocalLayerSerialPreRebaseOutput_mem_iff_nextTerminalInput_of_not_mem_switch
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) (edge : G.edgeSet)
    (hout : edge ∉ sourceLocalLayerBoundaryRebaseSwitchAt
      corridor hunique offset hnext) :
    edge ∈ sourceLocalLayerSerialPreRebaseOutputRegionAt
        corridor hunique offset ↔
      edge ∈ sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) := by
  have holdRung : edge ≠ sourceLocalLayerSharedRungAt corridor hunique offset := by
    intro heq
    apply hout
    rw [mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff]
    exact ⟨.inl (0 : Fin 1), by
      simpa [sourceLocalLayerBoundaryRebaseEdgeAt] using heq.symm⟩
  have hnextCrossing : ∀ step : Fin 2,
      edge ≠ sourceLocalLayerLeftCrossingAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) step := by
    intro step heq
    apply hout
    rw [mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff]
    exact ⟨.inr (.inl step), by
      simpa [sourceLocalLayerBoundaryRebaseEdgeAt] using heq.symm⟩
  have hnextRung : edge ≠ sourceLocalLayerSharedRungAt corridor hunique
      (sourceLocalLayerNextOffset offset hnext) := by
    intro heq
    apply hout
    rw [mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff]
    exact ⟨.inr (.inr (0 : Fin 1)), by
      simpa [sourceLocalLayerBoundaryRebaseEdgeAt] using heq.symm⟩
  simp only [sourceLocalLayerSerialPreRebaseOutputRegionAt,
    sourceLocalLayerSerialOutputRegionAt,
    sourceLocalLayerSerialTerminalInputRegionAt,
    sourceLocalLayerSerialInputRegionAt, Finset.mem_union,
    Finset.mem_singleton, holdRung, or_false, hnextRung]
  have hcrossing : edge ∉ indexedCrossingEdgeSet
      (sourceLocalLayerLeftCrossingAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)) := by
    rw [mem_indexedCrossingEdgeSet_iff]
    rintro ⟨step, heq⟩
    exact hnextCrossing step heq.symm
  simp only [hcrossing, or_false]
  rfl

/-- Equivalently, the symmetric difference of the two regional presentations
is contained in the four-role switch. -/
theorem sourceLocalLayerSerialBoundaryRebase_symmDiff_subset_switch
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset ∆
        sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext) ⊆
      sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext := by
  intro edge hdiff
  by_contra hout
  have hagree :=
    sourceLocalLayerSerialPreRebaseOutput_mem_iff_nextTerminalInput_of_not_mem_switch
      corridor hunique offset hnext edge hout
  rw [Finset.mem_symmDiff] at hdiff
  rcases hdiff with ⟨hleft, hright⟩ | ⟨hright, hleft⟩
  · exact hright (hagree.1 hleft)
  · exact hleft (hagree.2 hright)

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
