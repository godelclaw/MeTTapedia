import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorAlignedTwoTileSuccessorAbsorption
import Mettapedia.GraphTheory.FourColor.GoertzelV24VertexSetBoundaryUnionCancellation

/-!
# The full serial-boundary estimate for two aligned source windows

Two consecutive aligned two-tile windows have six-edge true frontiers and
share a two-edge transverse interface.  When both displayed boundary-dart
pairs are alpha-opposite, the whole common interface is absorbed by the
union of the two enclosed vertex sides.  The joined true frontier is then
contained in the two six-edge frontiers with those two seam edges removed,
and hence has cardinality at most eight.

This closes one physical serial-composition step.  It does not claim that
the alpha branch always occurs or that the lateral rail edges of a long
chain are eventually absorbed.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorAlignedTwoTileSerialBoundaryEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The two literal transverse edges shared by consecutive aligned windows,
written in the outgoing coordinates of the first window. -/
noncomputable def sourceTwoTileAlignedSharedTransverseEdgesAt
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
    (offset : Fin (blockLength - 5)) : Finset G.edgeSet :=
  indexedCrossingEdgeSet
    (sourceTwoTileAlignedSecondTerminalProfileDataAt realization hcubic
      hrotation htwoSided hunique
      (sourceTwoTileSuccessorStartOffset offset)).crossingEdge

theorem sourceTwoTileAlignedSharedTransverseEdgesAt_card_eq_two
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
    (offset : Fin (blockLength - 5)) :
    (sourceTwoTileAlignedSharedTransverseEdgesAt realization hcubic hrotation
      htwoSided hunique offset).card = 2 := by
  apply card_indexedCrossingEdgeSet_eq
  intro first second heq
  simp only [sourceTwoTileAlignedSecondTerminalProfileDataAt_crossingEdge]
    at heq
  exact (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
    (sourceSlabRailFinishOffset
      (sourceTwoTileSuccessorStartOffset offset))).localLayerPrefixCrossing_injective
        heq

/-- The shared transverse set lies in the first window's true frontier. -/
theorem sourceTwoTileAlignedSharedTransverseEdgesAt_subset_leftBoundary
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
    (offset : Fin (blockLength - 5)) :
    sourceTwoTileAlignedSharedTransverseEdgesAt realization hcubic hrotation
        htwoSided hunique offset ⊆
      vertexSetCrossingEdges embedded.cellulation.rotation.toRotationSystem
        ((sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
          htwoSided hunique
          (sourceTwoTileSuccessorStartOffset offset)).componentSide)ᶜ := by
  intro edge hedge
  rcases (mem_indexedCrossingEdgeSet_iff _ _).1 hedge with ⟨step, rfl⟩
  have hboundaryEq :
      vertexSetCrossingEdges embedded.cellulation.rotation.toRotationSystem
          ((sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
            htwoSided hunique
            (sourceTwoTileSuccessorStartOffset offset)).componentSide)ᶜ =
        sourceTwoTileAlignedBoundaryCrossingEdgesAt realization hcubic
          hrotation htwoSided hunique
          (sourceTwoTileSuccessorStartOffset offset) := by
    rw [vertexSetCrossingEdges_compl,
      (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique
        (sourceTwoTileSuccessorStartOffset offset)
        ).vertexSetCrossingEdges_componentSide_eq_cutEdges,
      sourceTwoTileAlignedLayerBoundaryAt_cutEdges]
  rw [hboundaryEq]
  have hedgePort :
      (sourceTwoTileAlignedSecondTerminalProfileDataAt realization hcubic
          hrotation htwoSided hunique
          (sourceTwoTileSuccessorStartOffset offset)).crossingEdge step =
        (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic
          hrotation htwoSided hunique
          (sourceTwoTileSuccessorStartOffset offset)).portEdge
            (.inl (sourceTwoTileAlignedSecondTerminalCrossingIndex step)) := by
    change _ =
      (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic
        hrotation htwoSided hunique
        (sourceTwoTileSuccessorStartOffset offset)).crossingEdge
          (sourceTwoTileAlignedSecondTerminalCrossingIndex step)
    unfold sourceTwoTileAlignedSecondTerminalCrossingIndex
    rw [sourceTwoTileAlignedSecondTerminalProfileDataAt_crossingEdge,
      sourceTwoTileAlignedTerminalProfileDataAt_crossingEdge_second]
  rw [hedgePort]
  exact
    sourceTwoTileAlignedTerminalProfileDataAt_portEdge_mem_boundary
      realization hcubic hrotation htwoSided hunique
        (sourceTwoTileSuccessorStartOffset offset)
        (.inl (sourceTwoTileAlignedSecondTerminalCrossingIndex step))

/-- The same physical transverse set lies in the successor window's true
frontier. -/
theorem sourceTwoTileAlignedSharedTransverseEdgesAt_subset_rightBoundary
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
    (offset : Fin (blockLength - 5)) :
    sourceTwoTileAlignedSharedTransverseEdgesAt realization hcubic hrotation
        htwoSided hunique offset ⊆
      vertexSetCrossingEdges embedded.cellulation.rotation.toRotationSystem
        ((sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
          htwoSided hunique
          (sourceTwoTileSuccessorNextOffset offset)).componentSide)ᶜ := by
  intro edge hedge
  rcases (mem_indexedCrossingEdgeSet_iff _ _).1 hedge with ⟨step, rfl⟩
  have hedgeEq :
      (sourceTwoTileAlignedSecondTerminalProfileDataAt realization hcubic
          hrotation htwoSided hunique
          (sourceTwoTileSuccessorStartOffset offset)).crossingEdge step =
        (sourceTwoTileAlignedFirstTerminalProfileDataAt realization hcubic
          hrotation htwoSided hunique
          (sourceTwoTileSuccessorNextOffset offset)).crossingEdge step := by
    rw [sourceTwoTileAlignedSecondTerminalProfileDataAt_crossingEdge,
      sourceTwoTileAlignedFirstTerminalProfileDataAt_crossingEdge,
      sourceSlabRailFinishOffset_eq_successorStart]
  rw [hedgeEq]
  have hboundaryEq :
      vertexSetCrossingEdges embedded.cellulation.rotation.toRotationSystem
          ((sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
            htwoSided hunique
            (sourceTwoTileSuccessorNextOffset offset)).componentSide)ᶜ =
        sourceTwoTileAlignedBoundaryCrossingEdgesAt realization hcubic
          hrotation htwoSided hunique
          (sourceTwoTileSuccessorNextOffset offset) := by
    rw [vertexSetCrossingEdges_compl,
      (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique
        (sourceTwoTileSuccessorNextOffset offset)
        ).vertexSetCrossingEdges_componentSide_eq_cutEdges,
      sourceTwoTileAlignedLayerBoundaryAt_cutEdges]
  rw [hboundaryEq]
  have hedgePort :
      (sourceTwoTileAlignedFirstTerminalProfileDataAt realization hcubic
          hrotation htwoSided hunique
          (sourceTwoTileSuccessorNextOffset offset)).crossingEdge step =
        (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic
          hrotation htwoSided hunique
          (sourceTwoTileSuccessorNextOffset offset)).portEdge
            (.inl (sourceTwoTileAlignedFirstTerminalCrossingIndex step)) := by
    change _ =
      (sourceTwoTileAlignedTerminalProfileDataAt realization hcubic
        hrotation htwoSided hunique
        (sourceTwoTileSuccessorNextOffset offset)).crossingEdge
          (sourceTwoTileAlignedFirstTerminalCrossingIndex step)
    unfold sourceTwoTileAlignedFirstTerminalCrossingIndex
    rw [sourceTwoTileAlignedFirstTerminalProfileDataAt_crossingEdge,
      sourceTwoTileAlignedTerminalProfileDataAt_crossingEdge_first]
  rw [hedgePort]
  exact
    sourceTwoTileAlignedTerminalProfileDataAt_portEdge_mem_boundary
      realization hcubic hrotation htwoSided hunique
        (sourceTwoTileSuccessorNextOffset offset)
        (.inl (sourceTwoTileAlignedFirstTerminalCrossingIndex step))

/-- In the genuine serial branch at both ports, the complete two-edge seam
is disjoint from the joined side's true frontier. -/
theorem sourceTwoTileAlignedSharedTransverseEdgesAt_disjoint_unionBoundary_of_alpha
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
    (offset : Fin (blockLength - 5))
    (halpha : ∀ step,
      embedded.cellulation.rotation.toRotationSystem.alpha
          (sourceTwoTileAlignedEnclosedOutputBoundaryDartAt realization hcubic
            hrotation htwoSided hunique offset step).1.1 =
        (sourceTwoTileAlignedEnclosedSuccessorInputBoundaryDartAt realization
          hcubic hrotation htwoSided hunique offset step).1.1) :
    Disjoint
      (sourceTwoTileAlignedSharedTransverseEdgesAt realization hcubic hrotation
        htwoSided hunique offset)
      (vertexSetCrossingEdges embedded.cellulation.rotation.toRotationSystem
        (((sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
            htwoSided hunique
            (sourceTwoTileSuccessorStartOffset offset)).componentSide)ᶜ ∪
          ((sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
            htwoSided hunique
            (sourceTwoTileSuccessorNextOffset offset)).componentSide)ᶜ)) := by
  rw [Finset.disjoint_left]
  intro edge hedgeSeam hedgeBoundary
  rcases (mem_indexedCrossingEdgeSet_iff _ _).1 hedgeSeam with ⟨step, rfl⟩
  have hedgeEq :
      (sourceTwoTileAlignedSecondTerminalProfileDataAt realization hcubic
          hrotation htwoSided hunique
          (sourceTwoTileSuccessorStartOffset offset)).crossingEdge step =
        embedded.cellulation.rotation.toRotationSystem.edgeOf
          (sourceTwoTileAlignedEnclosedOutputBoundaryDartAt realization hcubic
            hrotation htwoSided hunique offset step).1.1 := by
    calc
      _ =
          (sourceTwoTileAlignedEnclosedSecondTerminalProfileDataAt realization
            hcubic hrotation htwoSided hunique
            (sourceTwoTileSuccessorStartOffset offset)).crossingEdge step := by
          rw [sourceTwoTileAlignedSecondTerminalProfileDataAt_crossingEdge,
            sourceTwoTileAlignedEnclosedSecondTerminalProfileDataAt_crossingEdge]
      _ = _ := by
        change
          (sourceTwoTileAlignedEnclosedTerminalProfileDataAt realization hcubic
            hrotation htwoSided hunique
            (sourceTwoTileSuccessorStartOffset offset)).portEdge
              (.inl (sourceTwoTileAlignedSecondTerminalCrossingIndex step)) = _
        simpa only [sourceTwoTileAlignedEnclosedOutputBoundaryDartAt] using
          sourceTwoTileAlignedEnclosedTerminalProfileDataAt_portEdge_eq_boundaryDart
            realization hcubic hrotation htwoSided hunique
            (sourceTwoTileSuccessorStartOffset offset)
            (.inl (sourceTwoTileAlignedSecondTerminalCrossingIndex step))
  rw [hedgeEq] at hedgeBoundary
  exact sourceTwoTileAlignedEnclosed_sharedEdge_not_mem_unionCrossing_of_alpha
    realization hcubic hrotation htwoSided hunique offset step (halpha step)
      hedgeBoundary

/-- The joined true frontier is contained in the old frontiers with the
absorbed transverse seam deleted. -/
theorem sourceTwoTileAlignedEnclosed_unionBoundary_subset_without_shared_of_alpha
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
    (offset : Fin (blockLength - 5))
    (halpha : ∀ step,
      embedded.cellulation.rotation.toRotationSystem.alpha
          (sourceTwoTileAlignedEnclosedOutputBoundaryDartAt realization hcubic
            hrotation htwoSided hunique offset step).1.1 =
        (sourceTwoTileAlignedEnclosedSuccessorInputBoundaryDartAt realization
          hcubic hrotation htwoSided hunique offset step).1.1) :
    vertexSetCrossingEdges embedded.cellulation.rotation.toRotationSystem
        (((sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
            htwoSided hunique
            (sourceTwoTileSuccessorStartOffset offset)).componentSide)ᶜ ∪
          ((sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
            htwoSided hunique
            (sourceTwoTileSuccessorNextOffset offset)).componentSide)ᶜ) ⊆
      (vertexSetCrossingEdges embedded.cellulation.rotation.toRotationSystem
          ((sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
            htwoSided hunique
            (sourceTwoTileSuccessorStartOffset offset)).componentSide)ᶜ \
        sourceTwoTileAlignedSharedTransverseEdgesAt realization hcubic
          hrotation htwoSided hunique offset) ∪
      (vertexSetCrossingEdges embedded.cellulation.rotation.toRotationSystem
          ((sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
            htwoSided hunique
            (sourceTwoTileSuccessorNextOffset offset)).componentSide)ᶜ \
        sourceTwoTileAlignedSharedTransverseEdgesAt realization hcubic
          hrotation htwoSided hunique offset) := by
  exact vertexSetCrossingEdges_union_subset_sdiff_union_sdiff
    embedded.cellulation.rotation.toRotationSystem _ _ _
    (sourceTwoTileAlignedSharedTransverseEdgesAt_disjoint_unionBoundary_of_alpha
      realization hcubic hrotation htwoSided hunique offset halpha)

/-- One genuine serial join replaces two six-edge frontiers sharing two
ports by a joined true frontier of cardinality at most eight. -/
theorem sourceTwoTileAlignedEnclosed_unionBoundary_card_le_eight_of_alpha
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
    (offset : Fin (blockLength - 5))
    (halpha : ∀ step,
      embedded.cellulation.rotation.toRotationSystem.alpha
          (sourceTwoTileAlignedEnclosedOutputBoundaryDartAt realization hcubic
            hrotation htwoSided hunique offset step).1.1 =
        (sourceTwoTileAlignedEnclosedSuccessorInputBoundaryDartAt realization
          hcubic hrotation htwoSided hunique offset step).1.1) :
    (vertexSetCrossingEdges embedded.cellulation.rotation.toRotationSystem
      (((sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
          htwoSided hunique
          (sourceTwoTileSuccessorStartOffset offset)).componentSide)ᶜ ∪
        ((sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
          htwoSided hunique
          (sourceTwoTileSuccessorNextOffset offset)).componentSide)ᶜ)).card ≤ 8 := by
  let seam := sourceTwoTileAlignedSharedTransverseEdgesAt realization hcubic
    hrotation htwoSided hunique offset
  let leftBoundary := vertexSetCrossingEdges
    embedded.cellulation.rotation.toRotationSystem
    ((sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
      htwoSided hunique
      (sourceTwoTileSuccessorStartOffset offset)).componentSide)ᶜ
  let rightBoundary := vertexSetCrossingEdges
    embedded.cellulation.rotation.toRotationSystem
    ((sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
      htwoSided hunique
      (sourceTwoTileSuccessorNextOffset offset)).componentSide)ᶜ
  have hsubset :=
    sourceTwoTileAlignedEnclosed_unionBoundary_subset_without_shared_of_alpha
      realization hcubic hrotation htwoSided hunique offset halpha
  have hseamCard : seam.card = 2 := by
    exact sourceTwoTileAlignedSharedTransverseEdgesAt_card_eq_two realization
      hcubic hrotation htwoSided hunique offset
  have hseamLeft : seam ⊆ leftBoundary := by
    exact sourceTwoTileAlignedSharedTransverseEdgesAt_subset_leftBoundary
      realization hcubic hrotation htwoSided hunique offset
  have hseamRight : seam ⊆ rightBoundary := by
    exact sourceTwoTileAlignedSharedTransverseEdgesAt_subset_rightBoundary
      realization hcubic hrotation htwoSided hunique offset
  have hleftCard : leftBoundary.card = 6 := by
    dsimp [leftBoundary]
    rw [vertexSetCrossingEdges_compl,
      (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique
        (sourceTwoTileSuccessorStartOffset offset)
        ).vertexSetCrossingEdges_componentSide_eq_cutEdges,
      sourceTwoTileAlignedLayerBoundaryAt_cutEdges,
      sourceTwoTileAlignedBoundaryCrossingEdgesAt_card_eq_six]
  have hrightCard : rightBoundary.card = 6 := by
    dsimp [rightBoundary]
    rw [vertexSetCrossingEdges_compl,
      (sourceTwoTileAlignedLayerBoundaryAt realization hcubic hrotation
        htwoSided hunique
        (sourceTwoTileSuccessorNextOffset offset)
        ).vertexSetCrossingEdges_componentSide_eq_cutEdges,
      sourceTwoTileAlignedLayerBoundaryAt_cutEdges,
      sourceTwoTileAlignedBoundaryCrossingEdgesAt_card_eq_six]
  have hleftDiff : (leftBoundary \ seam).card = 4 := by
    rw [Finset.card_sdiff_of_subset hseamLeft, hleftCard, hseamCard]
  have hrightDiff : (rightBoundary \ seam).card = 4 := by
    rw [Finset.card_sdiff_of_subset hseamRight, hrightCard, hseamCard]
  calc
    _ ≤ ((leftBoundary \ seam) ∪ (rightBoundary \ seam)).card :=
      Finset.card_le_card hsubset
    _ ≤ (leftBoundary \ seam).card + (rightBoundary \ seam).card :=
      Finset.card_union_le _ _
    _ = 8 := by rw [hleftDiff, hrightDiff]

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
