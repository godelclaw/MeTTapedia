import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFaceCollarCode

/-!
# Successor boundary fragments in the bounded rebase face code

The two displayed crossings of the successor terminal-aware cut are among the
four literal rebase edges.  Consequently every canonical dart representative
of a successor boundary fragment lies in the at-most-twenty-four-dart facial
collar.  This file gives those fragments fixed slots and transports them into
the collar code.

The final theorem is exact and occurrence-sensitive: the closure computed by
the bounded two-factor code connects two canonical successor-fragment
coordinates if and only if the actual regional fragments are equal.  This is
the component-coordinate bridge needed by the finite successor face receipt;
ambient orbit-face equality, port incidence, and capped progress remain
separate fields.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialBoundaryRebaseFaceCollarFragmentEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- The actual occurrence-sensitive boundary fragments displayed by the next
terminal-aware input cut. -/
abbrev SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :=
  BoundaryRegionalFragment web.annular.RS
    (indexedCrossingEdgeSet
      (sourceLocalLayerLeftCrossingAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)))
    (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
      (sourceLocalLayerNextOffset offset hnext))

/-- Two displayed successor crossings expose at most four literal regional
face fragments. -/
theorem sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt_card_le_four
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    Fintype.card (SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt
      corridor hunique offset hnext) ≤ 4 := by
  simpa using
    (regionalBoundaryGraphCutData_fragmentCount_le_two_mul
      web.annular.RS
      (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext))
      (sourceLocalLayerLeftCrossingAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)))

/-- Fixed four-slot name of one actual successor boundary fragment. -/
noncomputable def sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt corridor hunique
        offset hnext → Fin 4 :=
  fun fragment => Fin.castLE
    (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt_card_le_four
      corridor hunique offset hnext)
    (Fintype.equivFin _ fragment)

/-- Decode an occupied successor-fragment slot. -/
noncomputable def sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtSlot?
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    Fin 4 → Option
      (SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt corridor hunique
        offset hnext) :=
  fun slot =>
    if hslot : slot.val < Fintype.card
        (SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt corridor hunique
          offset hnext) then
      some ((Fintype.equivFin _).symm ⟨slot.val, hslot⟩)
    else none

@[simp]
theorem sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtSlot?_slot
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (fragment : SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt
      corridor hunique offset hnext) :
    sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtSlot? corridor hunique
        offset hnext
        (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt corridor
          hunique offset hnext fragment) = some fragment := by
  simp [sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAtSlot?,
    sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentSlotAt]

/-- The canonical literal dart occurrence of a successor boundary fragment. -/
noncomputable def sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentDartAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (fragment : SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt
      corridor hunique offset hnext) : web.annular.RS.D :=
  (boundaryRegionalFragmentDartOccurrence web.annular.RS
    (indexedCrossingEdgeSet
      (sourceLocalLayerLeftCrossingAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)))
    (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
      (sourceLocalLayerNextOffset offset hnext)) fragment).1

/-- Every successor boundary-fragment representative lies over one of the two
new crossing edges and hence belongs to the finite rebase collar. -/
theorem sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentDartAt_mem_collar
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (fragment : SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt
      corridor hunique offset hnext) :
    sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentDartAt corridor hunique
        offset hnext fragment ∈
      sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique offset
        hnext := by
  apply sourceLocalLayerBoundaryRebaseChangedFaceDartsAt_subset_collar corridor
    hunique offset hnext
  rw [mem_sourceLocalLayerBoundaryRebaseChangedFaceDartsAt_iff,
    mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff]
  have hcut := (boundaryRegionalFragmentDartOccurrence web.annular.RS
    (indexedCrossingEdgeSet
      (sourceLocalLayerLeftCrossingAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)))
    (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
      (sourceLocalLayerNextOffset offset hnext)) fragment).2
  rw [mem_indexedCrossingEdgeSet_iff] at hcut
  rcases hcut with ⟨step, hstep⟩
  exact ⟨.inr (.inl step), by
    simpa [sourceLocalLayerBoundaryRebaseEdgeAt,
      sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentDartAt] using hstep⟩

/-- Coordinate of one actual successor boundary fragment in the common
bounded facial code. -/
noncomputable def sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentCoordinateAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (fragment : SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt
      corridor hunique offset hnext) :
    Fin (sourceLocalLayerBoundaryRebaseFaceCollarCodeAt corridor hunique offset
      hnext).vertexCount.val :=
  carrierCoordinate
    (sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique offset hnext)
    ⟨sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentDartAt corridor hunique
      offset hnext fragment,
      sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentDartAt_mem_collar
        corridor hunique offset hnext fragment⟩

/-- The bounded two-factor closure recognizes the actual successor regional
fragment partition exactly. -/
theorem sourceLocalLayerBoundaryRebaseFaceCollarCode_fragmentClosure_iff_eq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (left right : SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt
      corridor hunique offset hnext) :
    Relation.ReflTransGen
        (fun first second : Fin
            (sourceLocalLayerBoundaryRebaseFaceCollarCodeAt corridor hunique
              offset hnext).vertexCount.val =>
          ((sourceLocalLayerBoundaryRebaseFaceCollarCodeAt corridor hunique
            offset hnext).graph false).Reachable first second ∨
          ((sourceLocalLayerBoundaryRebaseFaceCollarCodeAt corridor hunique
            offset hnext).graph true).Reachable first second)
        (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentCoordinateAt
          corridor hunique offset hnext left)
        (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentCoordinateAt
          corridor hunique offset hnext right) ↔
      left = right := by
  let leftDart :=
    sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentDartAt corridor hunique
      offset hnext left
  let rightDart :=
    sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentDartAt corridor hunique
      offset hnext right
  have hleft :=
    sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentDartAt_mem_collar
      corridor hunique offset hnext left
  have hright :=
    sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentDartAt_mem_collar
      corridor hunique offset hnext right
  change Relation.ReflTransGen
      (fun first second : Fin
          (sourceLocalLayerBoundaryRebaseFaceCollarCodeAt corridor hunique
            offset hnext).vertexCount.val =>
        ((sourceLocalLayerBoundaryRebaseFaceCollarCodeAt corridor hunique offset
          hnext).graph false).Reachable first second ∨
        ((sourceLocalLayerBoundaryRebaseFaceCollarCodeAt corridor hunique offset
          hnext).graph true).Reachable first second)
      (carrierCoordinate
        (sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique offset hnext)
        ⟨leftDart, hleft⟩)
      (carrierCoordinate
        (sourceLocalLayerBoundaryRebaseFaceCollarAt corridor hunique offset hnext)
        ⟨rightDart, hright⟩) ↔ left = right
  rw [← sourceLocalLayerBoundaryRebaseSuccessor_reachable_iff_faceCollarCode
    corridor hunique offset hnext leftDart rightDart hleft hright]
  exact boundaryRegionalFragmentDartOccurrence_reachable_iff_eq
    web.annular.RS
    (indexedCrossingEdgeSet
      (sourceLocalLayerLeftCrossingAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)))
    (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique
      (sourceLocalLayerNextOffset offset hnext)) left right

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
