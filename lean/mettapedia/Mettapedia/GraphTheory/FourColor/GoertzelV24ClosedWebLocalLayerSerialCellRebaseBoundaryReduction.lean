import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseSharedRungBoundary

/-!
# Reduce facial Cell-rebase locality to the two successor roles

The fixed facial occurrence receipt contains old predecessor coordinates and
the three-dart collars of the four rebase edges.  Old coordinates cannot be
genuinely promoted.  Among the four rebase roles, the consumed rung is already
boundary-local.  Consequently the complete finite locality obligation reduces
exactly to the two successor-crossing roles and the successor-rung role.

This file is only the finite case split.  It adds no geometric premise and
makes no claim about the two remaining successor cases.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cellRebaseBoundaryReductionEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- Every switch occurrence lies over the consumed rung, one of the two
successor crossings, or the successor rung.  This is the semantic elimination
principle for the four-role finite switch. -/
theorem sourceLocalLayerBoundaryRebaseFaceOccurrence_edge_cases
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (occurrence : SourceLocalLayerBoundaryRebaseFaceOccurrenceAt corridor
      hunique offset hnext) :
    web.annular.RS.edgeOf occurrence.1 =
        sourceLocalLayerSharedRungAt corridor hunique offset ∨
      (∃ step : Fin 2,
        web.annular.RS.edgeOf occurrence.1 =
          sourceLocalLayerLeftCrossingAt corridor hunique
            (sourceLocalLayerNextOffset offset hnext) step) ∨
      web.annular.RS.edgeOf occurrence.1 =
        sourceLocalLayerSharedRungAt corridor hunique
          (sourceLocalLayerNextOffset offset hnext) := by
  have hswitch := occurrence.property
  rw [mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff] at hswitch
  rcases hswitch with ⟨role, hrole⟩
  rcases role with consumed | successor
  · exact Or.inl (by
      simpa [sourceLocalLayerBoundaryRebaseEdgeAt] using hrole.symm)
  · rcases successor with crossing | rung
    · exact Or.inr (Or.inl ⟨crossing, by
        simpa [sourceLocalLayerBoundaryRebaseEdgeAt] using hrole.symm⟩)
    · exact Or.inr (Or.inr (by
        simpa [sourceLocalLayerBoundaryRebaseEdgeAt] using hrole.symm))

/-- The complete expanded-receipt locality obligation follows once it is
proved for collars rooted at successor crossings and at the successor rung.
The old summand and the consumed-rung collars are discharged here. -/
theorem sourceLocalLayerSerialCellRebase_expandedFace_boundaryLocal_of_successor
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (hcrossing : ∀
      (occurrence : SourceLocalLayerBoundaryRebaseFaceOccurrenceAt corridor
        hunique offset hnext)
      (step : Fin 2),
      web.annular.RS.edgeOf occurrence.1 =
          sourceLocalLayerLeftCrossingAt corridor hunique
            (sourceLocalLayerNextOffset offset hnext) step →
      ∀ direction : SourceLocalLayerSerialCellRebaseFaceCollarDirection,
        web.annular.RS.edgeOf
            (sourceLocalLayerSerialCellRebaseFaceCollarDartAt web.annular.RS
              occurrence.1 direction) ∈
            sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
              offset →
        sourceLocalLayerSerialCellRebaseFaceCollarDartAt web.annular.RS
            occurrence.1 direction ∉
          sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
            offset →
        ∃ oldDart : {dart // dart ∈
            sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
              offset},
          (faceRegionalDartGraph web.annular.RS
            (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
              offset)).Adj oldDart.1
                (sourceLocalLayerSerialCellRebaseFaceCollarDartAt
                  web.annular.RS occurrence.1 direction))
    (hrung : ∀
      (occurrence : SourceLocalLayerBoundaryRebaseFaceOccurrenceAt corridor
        hunique offset hnext),
      web.annular.RS.edgeOf occurrence.1 =
          sourceLocalLayerSharedRungAt corridor hunique
            (sourceLocalLayerNextOffset offset hnext) →
      ∀ direction : SourceLocalLayerSerialCellRebaseFaceCollarDirection,
        web.annular.RS.edgeOf
            (sourceLocalLayerSerialCellRebaseFaceCollarDartAt web.annular.RS
              occurrence.1 direction) ∈
            sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
              offset →
        sourceLocalLayerSerialCellRebaseFaceCollarDartAt web.annular.RS
            occurrence.1 direction ∉
          sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
            offset →
        ∃ oldDart : {dart // dart ∈
            sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
              offset},
          (faceRegionalDartGraph web.annular.RS
            (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
              offset)).Adj oldDart.1
                (sourceLocalLayerSerialCellRebaseFaceCollarDartAt
                  web.annular.RS occurrence.1 direction)) :
    ∀ slot dart,
      sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor hunique
          offset hnext hcell slot = some dart →
      web.annular.RS.edgeOf dart ∈
          sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
            offset →
      dart ∉ sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
          offset →
      ∃ oldDart : {dart // dart ∈
          sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
            offset},
        (faceRegionalDartGraph web.annular.RS
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
            offset)).Adj oldDart.1 dart := by
  intro slot dart hdecode hpresent hnew
  rcases slot with oldSlot | ⟨occurrenceSlot, direction⟩
  · unfold sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? at hdecode
    cases hsource : sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor
        hunique offset hcell oldSlot with
    | none => simp [hsource] at hdecode
    | some oldDart =>
        simp only [hsource, Option.map_some, Option.some.injEq] at hdecode
        subst dart
        exact (hnew oldDart.2).elim
  · unfold sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? at hdecode
    cases hsource : sourceLocalLayerBoundaryRebaseFaceOccurrenceAtSlot?
        corridor hunique offset hnext occurrenceSlot with
    | none => simp [hsource] at hdecode
    | some occurrence =>
        simp only [hsource, Option.map_some, Option.some.injEq] at hdecode
        subst dart
        rcases sourceLocalLayerBoundaryRebaseFaceOccurrence_edge_cases corridor
            hunique offset hnext occurrence with
          hconsumed | hsuccessorCrossing | hsuccessorRung
        · exact
            sourceLocalLayerSerialCellRebase_sharedRung_collar_exists_oldNeighbor
              corridor hunique offset hnext occurrence hconsumed direction
                hpresent hnew
        · rcases hsuccessorCrossing with ⟨step, hedge⟩
          exact hcrossing occurrence step hedge direction hpresent hnew
        · exact hrung occurrence hsuccessorRung direction hpresent hnew

/-- Finite Boolean boundary locality therefore follows from the two
successor-role geometric premises above. -/
theorem sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_boundaryLocal_of_successor
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (hcrossing : ∀
      (occurrence : SourceLocalLayerBoundaryRebaseFaceOccurrenceAt corridor
        hunique offset hnext)
      (step : Fin 2),
      web.annular.RS.edgeOf occurrence.1 =
          sourceLocalLayerLeftCrossingAt corridor hunique
            (sourceLocalLayerNextOffset offset hnext) step →
      ∀ direction : SourceLocalLayerSerialCellRebaseFaceCollarDirection,
        web.annular.RS.edgeOf
            (sourceLocalLayerSerialCellRebaseFaceCollarDartAt web.annular.RS
              occurrence.1 direction) ∈
            sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
              offset →
        sourceLocalLayerSerialCellRebaseFaceCollarDartAt web.annular.RS
            occurrence.1 direction ∉
          sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
            offset →
        ∃ oldDart : {dart // dart ∈
            sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
              offset},
          (faceRegionalDartGraph web.annular.RS
            (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
              offset)).Adj oldDart.1
                (sourceLocalLayerSerialCellRebaseFaceCollarDartAt
                  web.annular.RS occurrence.1 direction))
    (hrung : ∀
      (occurrence : SourceLocalLayerBoundaryRebaseFaceOccurrenceAt corridor
        hunique offset hnext),
      web.annular.RS.edgeOf occurrence.1 =
          sourceLocalLayerSharedRungAt corridor hunique
            (sourceLocalLayerNextOffset offset hnext) →
      ∀ direction : SourceLocalLayerSerialCellRebaseFaceCollarDirection,
        web.annular.RS.edgeOf
            (sourceLocalLayerSerialCellRebaseFaceCollarDartAt web.annular.RS
              occurrence.1 direction) ∈
            sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
              offset →
        sourceLocalLayerSerialCellRebaseFaceCollarDartAt web.annular.RS
            occurrence.1 direction ∉
          sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
            offset →
        ∃ oldDart : {dart // dart ∈
            sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
              offset},
          (faceRegionalDartGraph web.annular.RS
            (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
              offset)).Adj oldDart.1
                (sourceLocalLayerSerialCellRebaseFaceCollarDartAt
                  web.annular.RS occurrence.1 direction)) :
    ∀ occurrence,
      (sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
          hunique offset hnext hcell).promoted occurrence = true →
        ((sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt corridor
          hunique offset hnext hcell).oldNeighbor? occurrence).isSome := by
  rw [sourceLocalLayerSerialCellRebaseExpandedFaceOccurrenceStateAt_boundaryLocal_iff]
  exact sourceLocalLayerSerialCellRebase_expandedFace_boundaryLocal_of_successor
    corridor hunique offset hnext hcell hcrossing hrung

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
