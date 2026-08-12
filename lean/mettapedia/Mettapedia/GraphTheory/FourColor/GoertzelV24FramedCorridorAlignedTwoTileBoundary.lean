import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorIntercellRailSupport

/-!
# Source-aligned two-tile boundary support

The two transverse source layers account for four crossings of a two-tile
boundary.  The paired exterior rails account for the other two.  This module
assembles those four actual facial-dual walks before passing to a finite
boundary carrier, so the lateral crossings cannot disappear behind an
abstract identification of the two transverse interfaces.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceTwoSided
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorAlignedTwoTileBoundaryEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The literal closed facial-dual walk obtained from the first transverse
layer, the second exterior rail, the reversed second transverse layer, and
the reversed first exterior rail.  Its construction retains all four source
pieces; simplicity is a separate geometric property. -/
noncomputable def sourceTwoTileAlignedBoundaryWalkAt
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
    (offset : Fin (blockLength - 4)) :
    (interiorDualGraph
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))).Walk
      (sourceTwoTileFirstInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).toInterface.firstLayerFace
      (sourceTwoTileFirstInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).toInterface.firstLayerFace := by
  let first := sourceTwoTileFirstInterfaceAt realization hcubic hrotation
    htwoSided hunique offset
  let second := sourceTwoTileSecondInterfaceAt realization hcubic hrotation
    htwoSided hunique offset
  let pair := sourceTwoTileRailPairAt realization hcubic hrotation htwoSided
    hunique offset
  exact (((first.toInterface.localLayer.walk.append pair.secondRail).append
    second.toInterface.localLayer.walk.reverse).append pair.firstRail.reverse)

/-- The aligned walk has the source's exact `2 + 2 + 2` length: two steps
through each transverse layer and two exterior-rail steps in total. -/
theorem sourceTwoTileAlignedBoundaryWalkAt_length_eq_six
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
    (offset : Fin (blockLength - 4)) :
    (sourceTwoTileAlignedBoundaryWalkAt realization hcubic hrotation htwoSided
      hunique offset).length = 6 := by
  dsimp [sourceTwoTileAlignedBoundaryWalkAt]
  simp only [SimpleGraph.Walk.length_append,
    SimpleGraph.Walk.length_reverse]
  rw [(sourceTwoTileFirstInterfaceAt realization hcubic hrotation htwoSided
      hunique offset).toInterface.localLayer_walk_length_eq_two,
    (sourceTwoTileSecondInterfaceAt realization hcubic hrotation htwoSided
      hunique offset).toInterface.localLayer_walk_length_eq_two]
  have hrails := (sourceTwoTileRailPairAt realization hcubic hrotation
    htwoSided hunique offset).firstRail_length_add_secondRail_length_eq_two
  omega

/-- The two crossings supplied by the first transverse source layer. -/
noncomputable def sourceTwoTileFirstLayerCrossingEdgesAt
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
    (offset : Fin (blockLength - 4)) : Finset G.edgeSet :=
  dualWalkCrossingEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
    (sourceTwoTileFirstInterfaceAt realization hcubic hrotation htwoSided
      hunique offset).toInterface.localLayer.walk

/-- The two crossings supplied by the second transverse source layer. -/
noncomputable def sourceTwoTileSecondLayerCrossingEdgesAt
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
    (offset : Fin (blockLength - 4)) : Finset G.edgeSet :=
  dualWalkCrossingEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
    (sourceTwoTileSecondInterfaceAt realization hcubic hrotation htwoSided
      hunique offset).toInterface.localLayer.walk

/-- The primal crossing support of the source-aligned closed walk. -/
noncomputable def sourceTwoTileAlignedBoundaryCrossingEdgesAt
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
    (offset : Fin (blockLength - 4)) : Finset G.edgeSet :=
  dualWalkCrossingEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
    (sourceTwoTileAlignedBoundaryWalkAt realization hcubic hrotation htwoSided
      hunique offset)

/-- The aligned boundary support is exactly the two transverse supports plus
the retained intercell-rail support.  In particular, the two lateral source
crossings are not erased by identifying the transverse interfaces. -/
theorem sourceTwoTileAlignedBoundaryCrossingEdgesAt_eq_layers_union_rails
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
    (offset : Fin (blockLength - 4)) :
    sourceTwoTileAlignedBoundaryCrossingEdgesAt realization hcubic hrotation
        htwoSided hunique offset =
      sourceTwoTileFirstLayerCrossingEdgesAt realization hcubic hrotation
          htwoSided hunique offset ∪
        sourceTwoTileSecondLayerCrossingEdgesAt realization hcubic hrotation
            htwoSided hunique offset ∪
          sourceTwoTileRailCrossingEdgesAt realization hcubic hrotation
            htwoSided hunique offset := by
  simp only [sourceTwoTileAlignedBoundaryCrossingEdgesAt,
    sourceTwoTileAlignedBoundaryWalkAt,
    sourceTwoTileFirstLayerCrossingEdgesAt,
    sourceTwoTileSecondLayerCrossingEdgesAt,
    sourceTwoTileRailCrossingEdgesAt,
    dualWalkCrossingEdges_append, dualWalkCrossingEdges_reverse]
  ext edge
  simp only [Finset.mem_union]
  tauto

/-- Even before simplicity is used, the provenance theorem gives the sharp
six-edge upper bound: two crossings from each transverse layer and exactly
two from the exterior rails. -/
theorem sourceTwoTileAlignedBoundaryCrossingEdgesAt_card_le_six
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
    (offset : Fin (blockLength - 4)) :
    (sourceTwoTileAlignedBoundaryCrossingEdgesAt realization hcubic hrotation
      htwoSided hunique offset).card ≤ 6 := by
  let first := sourceTwoTileFirstInterfaceAt realization hcubic hrotation
    htwoSided hunique offset
  let second := sourceTwoTileSecondInterfaceAt realization hcubic hrotation
    htwoSided hunique offset
  let firstEdges := sourceTwoTileFirstLayerCrossingEdgesAt realization hcubic
    hrotation htwoSided hunique offset
  let secondEdges := sourceTwoTileSecondLayerCrossingEdgesAt realization hcubic
    hrotation htwoSided hunique offset
  let railEdges := sourceTwoTileRailCrossingEdgesAt realization hcubic hrotation
    htwoSided hunique offset
  have hfirstCard : firstEdges.card = 2 := by
    dsimp [firstEdges, sourceTwoTileFirstLayerCrossingEdgesAt]
    rw [card_dualWalkCrossingEdges_eq_length_of_isPath
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))
      (orbitFace_incidence_le_two
        embedded.cellulation.rotation.toRotationSystem)
      hunique first.toInterface.localLayer.walk
      first.toInterface.localLayer.isPath,
      first.toInterface.localLayer_walk_length_eq_two]
  have hsecondCard : secondEdges.card = 2 := by
    dsimp [secondEdges, sourceTwoTileSecondLayerCrossingEdgesAt]
    rw [card_dualWalkCrossingEdges_eq_length_of_isPath
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem))
      (orbitFace_incidence_le_two
        embedded.cellulation.rotation.toRotationSystem)
      hunique second.toInterface.localLayer.walk
      second.toInterface.localLayer.isPath,
      second.toInterface.localLayer_walk_length_eq_two]
  have hrailCard : railEdges.card = 2 := by
    exact sourceTwoTileRailCrossingEdgesAt_card_eq_two realization hcubic
      hrotation htwoSided hunique offset
  rw [sourceTwoTileAlignedBoundaryCrossingEdgesAt_eq_layers_union_rails]
  calc
    ((firstEdges ∪ secondEdges) ∪ railEdges).card ≤
        (firstEdges ∪ secondEdges).card + railEdges.card :=
      Finset.card_union_le _ _
    _ ≤ (firstEdges.card + secondEdges.card) + railEdges.card := by
      gcongr
      exact Finset.card_union_le _ _
    _ = 6 := by rw [hfirstCard, hsecondCard, hrailCard]

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
