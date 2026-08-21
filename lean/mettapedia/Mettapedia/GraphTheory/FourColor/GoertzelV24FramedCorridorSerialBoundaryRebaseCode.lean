import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundedCarrierGraphFamilyCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundedSupportGraphCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebase

/-!
# Finite codes for the literal serial boundary-rebase letter

The boundary rebase adds two displayed edges to an already accumulated
literal prefix.  Its complete tracked local contribution consists, for each
tracked color pair, of the graph on those two edges and the exact residual
seam.  Both graph families are transported together through one common
fourteen-edge carrier, retaining the two new crossings as named points.

The occurrence-sensitive facial seam is also transported to a finite code of
size at most fourteen.  A later joint face-update receipt must retain its
alignment with the boundary fragments; this file does not replace that
obligation or claim that the old profile determines the code.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24BoundedSupportGraphCode
open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseCodeEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- `false` selects the graph internal to the two newly displayed edges;
`true` selects the residual seam.  The second coordinate chooses the tracked
color pair. -/
abbrev SourceCorridorSerialBoundaryRebaseTrackedFactor :=
  Bool × TrackedColorPair

/-- The two tracked graph factors of one rebase, on their ambient edge
carrier. -/
def sourceCorridorSerialBoundaryRebaseTrackedGraphAt
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
    (color : G.edgeSet → Color)
    (factor : SourceCorridorSerialBoundaryRebaseTrackedFactor) :
    SimpleGraph G.edgeSet :=
  if factor.1 then
    sourceCorridorSerialBoundaryRebaseTrackedSeamAt realization hcubic
      hrotation htwoSided hunique offset hnext color
      (trackedColorPairColors factor.2).1
      (trackedColorPairColors factor.2).2
  else
    regionalTrackedEdgeGraph
      embedded.cellulation.rotation.toRotationSystem
      (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic hrotation
        htwoSided hunique offset hnext)
      color (trackedColorPairColors factor.2).1
        (trackedColorPairColors factor.2).2

/-- Both the two-edge factor and the residual factor are supported on the
same fourteen-edge carrier. -/
theorem sourceCorridorSerialBoundaryRebaseTrackedGraphAt_support_subset_carrier
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
    (color : G.edgeSet → Color)
    (factor : SourceCorridorSerialBoundaryRebaseTrackedFactor) :
    (sourceCorridorSerialBoundaryRebaseTrackedGraphAt realization hcubic
      hrotation htwoSided hunique offset hnext color factor).support ⊆
      sourceCorridorSerialBoundaryRebaseCarrierAt realization hcubic hrotation
        htwoSided hunique offset hnext := by
  rcases factor with ⟨flag, pair⟩
  cases flag
  · intro edge hedge
    rcases (SimpleGraph.mem_support _).1 hedge with ⟨neighbor, hadj⟩
    apply (embedded.cellulation.rotation.toRotationSystem
      |>.mem_edgeAdjacencyClosedCarrier_iff _ _).2
    exact Or.inl hadj.2.1
  · exact
      sourceCorridorSerialBoundaryRebaseTrackedSeamAt_support_subset_carrier
        realization hcubic hrotation htwoSided hunique offset hnext color
        (trackedColorPairColors pair).1 (trackedColorPairColors pair).2

/-- One newly displayed crossing as a named point of the common rebase
carrier. -/
noncomputable def sourceCorridorSerialBoundaryRebasePointAt
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
    (hnext : offset.val + 1 < blockLength - 3) (step : Fin 2) :
    {edge // edge ∈
      sourceCorridorSerialBoundaryRebaseCarrierAt realization hcubic hrotation
        htwoSided hunique offset hnext} := by
  refine ⟨sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
    hrotation htwoSided hunique offset hnext step, ?_⟩
  apply (embedded.cellulation.rotation.toRotationSystem
    |>.mem_edgeAdjacencyClosedCarrier_iff _ _).2
  exact Or.inl ((mem_indexedCrossingEdgeSet_iff _ _).2 ⟨step, rfl⟩)

/-- The complete tracked local part of one rebase, on canonical finite
coordinates with its two ports retained. -/
noncomputable def sourceCorridorSerialBoundaryRebaseTrackedCodeAt
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
    (color : G.edgeSet → Color) :
    BoundedCarrierGraphFamilyCode 14 2
      SourceCorridorSerialBoundaryRebaseTrackedFactor :=
  boundedCarrierGraphFamilyCode
    (sourceCorridorSerialBoundaryRebaseCarrierAt realization hcubic hrotation
      htwoSided hunique offset hnext)
    14 2
    (sourceCorridorSerialBoundaryRebaseCarrierAt_card_le_fourteen realization
      hcubic hrotation htwoSided hunique offset hnext)
    (sourceCorridorSerialBoundaryRebasePointAt realization hcubic hrotation
      htwoSided hunique offset hnext)
    (sourceCorridorSerialBoundaryRebaseTrackedGraphAt realization hcubic
      hrotation htwoSided hunique offset hnext color)

/-- The two named rebase ports remain distinct after transport. -/
theorem sourceCorridorSerialBoundaryRebaseTrackedCodeAt_point_injective
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
    (color : G.edgeSet → Color) :
    Function.Injective
      (sourceCorridorSerialBoundaryRebaseTrackedCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext color).point := by
  intro first second heq
  have hpoints :
      sourceCorridorSerialBoundaryRebasePointAt realization hcubic hrotation
          htwoSided hunique offset hnext first =
        sourceCorridorSerialBoundaryRebasePointAt realization hcubic hrotation
          htwoSided hunique offset hnext second := by
    apply (carrierCoordinate
      (sourceCorridorSerialBoundaryRebaseCarrierAt realization hcubic hrotation
        htwoSided hunique offset hnext)).injective
    exact heq
  apply (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
      (sourceCorridorSerialNextOffset offset hnext))
    |>.localLayerPrefixCrossing_injective
  exact congrArg Subtype.val hpoints

/-- Every adjacency of either tracked factor is represented exactly by the
finite code. -/
theorem sourceCorridorSerialBoundaryRebaseTrackedCodeAt_adj_iff
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
    (color : G.edgeSet → Color)
    (factor : SourceCorridorSerialBoundaryRebaseTrackedFactor)
    (first second : {edge // edge ∈
      sourceCorridorSerialBoundaryRebaseCarrierAt realization hcubic hrotation
        htwoSided hunique offset hnext}) :
    ((sourceCorridorSerialBoundaryRebaseTrackedCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext color).graph factor).Adj
        (carrierCoordinate
          (sourceCorridorSerialBoundaryRebaseCarrierAt realization hcubic
            hrotation htwoSided hunique offset hnext) first)
        (carrierCoordinate
          (sourceCorridorSerialBoundaryRebaseCarrierAt realization hcubic
            hrotation htwoSided hunique offset hnext) second) ↔
      (sourceCorridorSerialBoundaryRebaseTrackedGraphAt realization hcubic
        hrotation htwoSided hunique offset hnext color factor).Adj
          first.1 second.1 := by
  exact boundedCarrierGraphFamilyCode_adj_iff _ _ _ _ _ _ _ _ _

/-- Because each factor's support lies in the common carrier, the finite code
preserves its ambient reachability between carrier vertices. -/
theorem sourceCorridorSerialBoundaryRebaseTrackedCodeAt_reachable_iff
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
    (color : G.edgeSet → Color)
    (factor : SourceCorridorSerialBoundaryRebaseTrackedFactor)
    (first second : {edge // edge ∈
      sourceCorridorSerialBoundaryRebaseCarrierAt realization hcubic hrotation
        htwoSided hunique offset hnext}) :
    ((sourceCorridorSerialBoundaryRebaseTrackedCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext color).graph factor).Reachable
        (carrierCoordinate
          (sourceCorridorSerialBoundaryRebaseCarrierAt realization hcubic
            hrotation htwoSided hunique offset hnext) first)
        (carrierCoordinate
          (sourceCorridorSerialBoundaryRebaseCarrierAt realization hcubic
            hrotation htwoSided hunique offset hnext) second) ↔
      (sourceCorridorSerialBoundaryRebaseTrackedGraphAt realization hcubic
        hrotation htwoSided hunique offset hnext color factor).Reachable
          first.1 second.1 := by
  exact boundedCarrierGraphFamilyCode_reachable_iff_of_support_subset
    (sourceCorridorSerialBoundaryRebaseCarrierAt realization hcubic hrotation
      htwoSided hunique offset hnext)
    14 2
    (sourceCorridorSerialBoundaryRebaseCarrierAt_card_le_fourteen realization
      hcubic hrotation htwoSided hunique offset hnext)
    (sourceCorridorSerialBoundaryRebasePointAt realization hcubic hrotation
      htwoSided hunique offset hnext)
    (sourceCorridorSerialBoundaryRebaseTrackedGraphAt realization hcubic
      hrotation htwoSided hunique offset hnext color)
    factor
    (sourceCorridorSerialBoundaryRebaseTrackedGraphAt_support_subset_carrier
      realization hcubic hrotation htwoSided hunique offset hnext color factor)
    first second

/-- The occurrence-sensitive facial residual seam on canonical finite
coordinates. -/
noncomputable def sourceCorridorSerialBoundaryRebaseFaceSeamCodeAt
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
    (root : embedded.cellulation.rotation.toRotationSystem.D) :
    BoundedSupportGraphCode 14 :=
  boundedSupportCode
    (sourceCorridorSerialBoundaryRebaseFaceSeamAt realization hcubic hrotation
      htwoSided hunique offset hnext root)
    14
    (sourceCorridorSerialBoundaryRebaseFaceSeamAt_support_card_le_fourteen
      realization hcubic hrotation htwoSided hunique offset hnext root)

/-- The ambient facial seam on its participating occurrences is isomorphic
to its finite code. -/
noncomputable def sourceCorridorSerialBoundaryRebaseFaceSeamCodeIsoAt
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
    (root : embedded.cellulation.rotation.toRotationSystem.D) :
    let seam := sourceCorridorSerialBoundaryRebaseFaceSeamAt realization hcubic
      hrotation htwoSided hunique offset hnext root
    seam.induce seam.support ≃g
      (sourceCorridorSerialBoundaryRebaseFaceSeamCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root).graph := by
  dsimp only
  exact boundedSupportCodeIso
    (sourceCorridorSerialBoundaryRebaseFaceSeamAt realization hcubic hrotation
      htwoSided hunique offset hnext root)
    14
    (sourceCorridorSerialBoundaryRebaseFaceSeamAt_support_card_le_fourteen
      realization hcubic hrotation htwoSided hunique offset hnext root)

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
