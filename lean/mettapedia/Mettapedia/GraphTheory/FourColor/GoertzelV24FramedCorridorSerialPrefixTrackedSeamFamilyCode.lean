import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundedCarrierGraphFamilyCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialPrefixSeamRelation

/-!
# One finite carrier for the tracked source seam family

The three tracked-color residual graphs at one source Cell live on the same
ambient edge carrier and share the same two outgoing boundary edges.  Coding
their supports separately forgets both facts.  This module instead transports
the whole `TrackedColorPair`-indexed family through the common closed
edge-adjacency carrier, whose cardinality is at most fourteen.

This is a finite presentation of the literal residual family for one ambient
coloring.  It does not assert that a corridor profile determines the code or
that the code is already the complete one-Cell transfer morphism.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialPrefixTrackedSeamFamilyCodeEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- One outgoing source crossing, retained as a named point of the common
residual carrier even when it is isolated in a particular tracked graph. -/
noncomputable def sourceCorridorSerialOutgoingCrossingPointAt
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
    (offset : Fin (blockLength - 3)) (step : Fin 2) :
    {edge // edge ∈
      sourceCorridorSerialOutgoingEdgeCarrierAt realization hcubic hrotation
        htwoSided hunique offset} := by
  refine ⟨
    (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
      offset).nextLocalLayerPrefixCrossing step, ?_⟩
  apply (embedded.cellulation.rotation.toRotationSystem
    |>.mem_edgeAdjacencyClosedCarrier_iff _ _).2
  exact Or.inl ((mem_indexedCrossingEdgeSet_iff _ _).2 ⟨step, rfl⟩)

/-- The three literal tracked residual graphs on one exact finite carrier,
with the two outgoing crossings retained in the same coordinate system. -/
noncomputable def sourceCorridorSerialInputTrackedSeamFamilyCodeAt
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
    (offset : Fin (blockLength - 3)) (color : G.edgeSet → Color) :
    BoundedCarrierGraphFamilyCode 14 2 TrackedColorPair :=
  boundedCarrierGraphFamilyCode
    (sourceCorridorSerialOutgoingEdgeCarrierAt realization hcubic hrotation
      htwoSided hunique offset)
    14 2
    (sourceCorridorSerialOutgoingEdgeCarrierAt_card_le_fourteen realization
      hcubic hrotation htwoSided hunique offset)
    (sourceCorridorSerialOutgoingCrossingPointAt realization hcubic hrotation
      htwoSided hunique offset)
    (fun pair =>
      sourceCorridorSerialInputTrackedSeamGraphAt realization hcubic hrotation
        htwoSided hunique offset color
        (trackedColorPairColors pair).1 (trackedColorPairColors pair).2)

/-- The stored carrier size is the literal closed-neighborhood cardinality,
not merely the uniform upper bound fourteen. -/
theorem sourceCorridorSerialInputTrackedSeamFamilyCodeAt_vertexCount
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
    (offset : Fin (blockLength - 3)) (color : G.edgeSet → Color) :
    (sourceCorridorSerialInputTrackedSeamFamilyCodeAt realization hcubic
      hrotation htwoSided hunique offset color).vertexCount.val =
      (sourceCorridorSerialOutgoingEdgeCarrierAt realization hcubic hrotation
        htwoSided hunique offset).card := by
  exact boundedCarrierGraphFamilyCode_vertexCount_eq_card _ _ _ _ _ _

/-- The named outgoing coordinates remain distinct in the common code. -/
theorem sourceCorridorSerialInputTrackedSeamFamilyCodeAt_point_injective
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
    (offset : Fin (blockLength - 3)) (color : G.edgeSet → Color) :
    Function.Injective
      (sourceCorridorSerialInputTrackedSeamFamilyCodeAt realization hcubic
        hrotation htwoSided hunique offset color).point := by
  intro first second heq
  have hpoints :
      sourceCorridorSerialOutgoingCrossingPointAt realization hcubic hrotation
          htwoSided hunique offset first =
        sourceCorridorSerialOutgoingCrossingPointAt realization hcubic hrotation
          htwoSided hunique offset second := by
    apply (carrierCoordinate
      (sourceCorridorSerialOutgoingEdgeCarrierAt realization hcubic hrotation
        htwoSided hunique offset)).injective
    exact heq
  apply (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
    offset).nextLocalLayerPrefixCrossing_injective
  exact congrArg Subtype.val hpoints

/-- Every tracked adjacency between carrier edges is represented exactly in
the corresponding member of the finite family. -/
theorem sourceCorridorSerialInputTrackedSeamFamilyCodeAt_adj_iff
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
    (offset : Fin (blockLength - 3)) (color : G.edgeSet → Color)
    (pair : TrackedColorPair)
    (first second : {edge // edge ∈
      sourceCorridorSerialOutgoingEdgeCarrierAt realization hcubic hrotation
        htwoSided hunique offset}) :
    ((sourceCorridorSerialInputTrackedSeamFamilyCodeAt realization hcubic
        hrotation htwoSided hunique offset color).graph pair).Adj
        (carrierCoordinate
          (sourceCorridorSerialOutgoingEdgeCarrierAt realization hcubic
            hrotation htwoSided hunique offset) first)
        (carrierCoordinate
          (sourceCorridorSerialOutgoingEdgeCarrierAt realization hcubic
            hrotation htwoSided hunique offset) second) ↔
      (sourceCorridorSerialInputTrackedSeamGraphAt realization hcubic hrotation
        htwoSided hunique offset color
        (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).Adj first.1 second.1 := by
  exact boundedCarrierGraphFamilyCode_adj_iff _ _ _ _ _ _ _ _ _

/-- Reachability within the exact common carrier is preserved for every
tracked-color member of the family. -/
theorem sourceCorridorSerialInputTrackedSeamFamilyCodeAt_reachable_iff
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
    (offset : Fin (blockLength - 3)) (color : G.edgeSet → Color)
    (pair : TrackedColorPair)
    (first second : {edge // edge ∈
      sourceCorridorSerialOutgoingEdgeCarrierAt realization hcubic hrotation
        htwoSided hunique offset}) :
    ((sourceCorridorSerialInputTrackedSeamFamilyCodeAt realization hcubic
        hrotation htwoSided hunique offset color).graph pair).Reachable
        (carrierCoordinate
          (sourceCorridorSerialOutgoingEdgeCarrierAt realization hcubic
            hrotation htwoSided hunique offset) first)
        (carrierCoordinate
          (sourceCorridorSerialOutgoingEdgeCarrierAt realization hcubic
            hrotation htwoSided hunique offset) second) ↔
      ((sourceCorridorSerialInputTrackedSeamGraphAt realization hcubic hrotation
        htwoSided hunique offset color
        (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).induce
          (sourceCorridorSerialOutgoingEdgeCarrierAt realization hcubic
            hrotation htwoSided hunique offset : Set G.edgeSet)).Reachable
        first second := by
  exact boundedCarrierGraphFamilyCode_reachable_iff _ _ _ _ _ _ _ _ _

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
