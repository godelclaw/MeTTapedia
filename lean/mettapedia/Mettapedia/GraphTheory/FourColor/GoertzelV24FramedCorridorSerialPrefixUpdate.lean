import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialPrefixRegion
import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileSeamResidual

/-!
# Exact one-Cell updates of the literal source prefix

The serial source prefix is the union of the actual complementary open Cell
regions, in source order.  Adding one Cell need not be a two-factor graph
decomposition: tracked adjacency and facial continuation can turn across the
common seam without lying wholly in either displayed factor.

This file keeps that seam visible.  It specializes the generic residual
factorization to each source-indexed successor prefix and constructs the full
bounded five-field profile on the resulting literal edge region.  No
identification with a complete hex-face boundary or with the final annular
splice is made here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationFaceFragments
open GoertzelV24SimpleGraphSupResidual
open GoertzelV24TerminalProfileFaceUpdate
open GoertzelV24TerminalProfileSeamResidual
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialPrefixUpdateEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The tracked seam left after displaying the old literal prefix and the
new source Cell as separate graph factors. -/
def sourceCorridorSerialPrefixTrackedSeamGraphAt
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength cut : Nat}
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
    (hcut : cut < blockLength - 3)
    (color : G.edgeSet → Color) (first second : Color) :
    SimpleGraph G.edgeSet :=
  regionalTrackedSeamGraph
    embedded.cellulation.rotation.toRotationSystem
    (sourceCorridorSerialPrefixRegion realization hcubic hrotation htwoSided
      hunique cut)
    (sourceSlabLiteralCellRegionAt realization hcubic hrotation htwoSided
      hunique ⟨cut, hcut⟩)
    color first second

/-- The successor prefix's tracked graph is exactly old prefix, literal Cell,
and the explicit residual seam. -/
theorem sourceCorridorSerialPrefixTrackedGraph_succ_eq_three_factor
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength cut : Nat}
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
    (hcut : cut < blockLength - 3)
    (color : G.edgeSet → Color) (first second : Color) :
    regionalTrackedEdgeGraph embedded.cellulation.rotation.toRotationSystem
        (sourceCorridorSerialPrefixRegion realization hcubic hrotation
          htwoSided hunique (cut + 1)) color first second =
      (regionalTrackedEdgeGraph embedded.cellulation.rotation.toRotationSystem
          (sourceCorridorSerialPrefixRegion realization hcubic hrotation
            htwoSided hunique cut) color first second ⊔
        regionalTrackedEdgeGraph embedded.cellulation.rotation.toRotationSystem
          (sourceSlabLiteralCellRegionAt realization hcubic hrotation
            htwoSided hunique ⟨cut, hcut⟩) color first second) ⊔
        sourceCorridorSerialPrefixTrackedSeamGraphAt realization hcubic
          hrotation htwoSided hunique hcut color first second := by
  rw [sourceCorridorSerialPrefixRegion_succ realization hcubic hrotation
    htwoSided hunique hcut]
  exact regionalTrackedEdgeGraph_union_eq_sup_sup_seam
    embedded.cellulation.rotation.toRotationSystem
    (sourceCorridorSerialPrefixRegion realization hcubic hrotation htwoSided
      hunique cut)
    (sourceSlabLiteralCellRegionAt realization hcubic hrotation htwoSided
      hunique ⟨cut, hcut⟩)
    color first second

/-- Tracked connectivity in the enlarged literal prefix is the closure of
whole-component moves in the old prefix and Cell, plus literal seam turns. -/
theorem sourceCorridorSerialPrefixTrackedReachable_succ_iff
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength cut : Nat}
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
    (hcut : cut < blockLength - 3)
    (color : G.edgeSet → Color) (first second : Color)
    (left right : G.edgeSet) :
    (regionalTrackedEdgeGraph embedded.cellulation.rotation.toRotationSystem
      (sourceCorridorSerialPrefixRegion realization hcubic hrotation htwoSided
        hunique (cut + 1)) color first second).Reachable left right ↔
      Relation.ReflTransGen
        (ThreeFactorComponentStep
          (regionalTrackedEdgeGraph
            embedded.cellulation.rotation.toRotationSystem
            (sourceCorridorSerialPrefixRegion realization hcubic hrotation
              htwoSided hunique cut) color first second)
          (regionalTrackedEdgeGraph
            embedded.cellulation.rotation.toRotationSystem
            (sourceSlabLiteralCellRegionAt realization hcubic hrotation
              htwoSided hunique ⟨cut, hcut⟩) color first second)
          (sourceCorridorSerialPrefixTrackedSeamGraphAt realization hcubic
            hrotation htwoSided hunique hcut color first second)) left right := by
  rw [sourceCorridorSerialPrefixTrackedGraph_succ_eq_three_factor realization
    hcubic hrotation htwoSided hunique hcut color first second]
  exact reachable_sup_sup_iff_threeFactorComponentClosure _ _ _ _ _

/-- The occurrence-sensitive facial seam between the old literal prefix and
one newly adjoined source Cell. -/
def sourceCorridorSerialPrefixFaceSeamGraphAt
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength cut : Nat}
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
    (hcut : cut < blockLength - 3)
    (root : embedded.cellulation.rotation.toRotationSystem.D) :=
  faceRegionalSeamGraph embedded.cellulation.rotation.toRotationSystem root
    (sourceCorridorSerialPrefixRegion realization hcubic hrotation htwoSided
      hunique cut)
    (sourceSlabLiteralCellRegionAt realization hcubic hrotation htwoSided
      hunique ⟨cut, hcut⟩)

/-- Facial continuation in the successor prefix has the same exact
three-factor decomposition as tracked connectivity. -/
theorem sourceCorridorSerialPrefixFaceGraph_succ_eq_three_factor
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength cut : Nat}
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
    (hcut : cut < blockLength - 3)
    (root : embedded.cellulation.rotation.toRotationSystem.D) :
    faceRegionalAmbientPositionGraph
        embedded.cellulation.rotation.toRotationSystem root
        (sourceCorridorSerialPrefixRegion realization hcubic hrotation
          htwoSided hunique (cut + 1)) =
      (faceRegionalAmbientPositionGraph
          embedded.cellulation.rotation.toRotationSystem root
          (sourceCorridorSerialPrefixRegion realization hcubic hrotation
            htwoSided hunique cut) ⊔
        faceRegionalAmbientPositionGraph
          embedded.cellulation.rotation.toRotationSystem root
          (sourceSlabLiteralCellRegionAt realization hcubic hrotation
            htwoSided hunique ⟨cut, hcut⟩)) ⊔
        sourceCorridorSerialPrefixFaceSeamGraphAt realization hcubic hrotation
          htwoSided hunique hcut root := by
  rw [sourceCorridorSerialPrefixRegion_succ realization hcubic hrotation
    htwoSided hunique hcut]
  exact faceRegionalAmbientPositionGraph_union_eq_sup_sup_seam _ _ _ _

/-- Facial reachability in the enlarged literal prefix is the closure of
whole-fragment moves in the old prefix and Cell, plus literal seam turns. -/
theorem sourceCorridorSerialPrefixFaceReachable_succ_iff
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength cut : Nat}
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
    (hcut : cut < blockLength - 3)
    (root : embedded.cellulation.rotation.toRotationSystem.D)
    (left right : Fin
      (embedded.cellulation.rotation.toRotationSystem.faceOrbit root).card) :
    (faceRegionalAmbientPositionGraph
      embedded.cellulation.rotation.toRotationSystem root
      (sourceCorridorSerialPrefixRegion realization hcubic hrotation htwoSided
        hunique (cut + 1))).Reachable left right ↔
      Relation.ReflTransGen
        (ThreeFactorComponentStep
          (faceRegionalAmbientPositionGraph
            embedded.cellulation.rotation.toRotationSystem root
            (sourceCorridorSerialPrefixRegion realization hcubic hrotation
              htwoSided hunique cut))
          (faceRegionalAmbientPositionGraph
            embedded.cellulation.rotation.toRotationSystem root
            (sourceSlabLiteralCellRegionAt realization hcubic hrotation
              htwoSided hunique ⟨cut, hcut⟩))
          (sourceCorridorSerialPrefixFaceSeamGraphAt realization hcubic
            hrotation htwoSided hunique hcut root)) left right := by
  rw [sourceCorridorSerialPrefixFaceGraph_succ_eq_three_factor realization
    hcubic hrotation htwoSided hunique hcut root]
  exact reachable_sup_sup_iff_threeFactorComponentClosure _ _ _ _ _

/-- Complete graph-derived cut data on the literal source prefix after one
indexed Cell, using that Cell's actual outgoing two-edge interface. -/
noncomputable def sourceCorridorSerialPrefixCutDataAt
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
    (offset : Fin (blockLength - 3)) :=
  regionalBoundaryGraphCutData embedded.cellulation.rotation.toRotationSystem
    (sourceCorridorSerialPrefixRegion realization hcubic hrotation htwoSided
      hunique (offset.val + 1))
    ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
      offset).nextLocalLayerPrefixCrossing)

/-- Both outgoing source crossings are genuine edges of the corresponding
literal successor prefix. -/
theorem sourceCorridorSerialPrefixCutDataAt_portsInRegion
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
    (offset : Fin (blockLength - 3)) :
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).PortsInRegion := by
  apply regionalBoundaryGraphCutData_portsInRegion
  intro step
  apply sourceSlabLiteralCellRegionAt_subset_serialPrefix_succ realization
    hcubic hrotation htwoSided hunique offset.isLt
  exact sourceSlabLiteralCellRegionAt_rightCrossing realization hcubic
    hrotation htwoSided hunique offset step

/-- The complete bounded manuscript profile of one literal source prefix.
All five fields are computed from the same regional carrier. -/
noncomputable def sourceCorridorSerialPrefixBoundedProfileAt
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
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).nextLocalLayerPrefixCrossing step) ≠ 0) :=
  regionalBoundaryBoundedProfile
    embedded.cellulation.rotation.toRotationSystem
    (sourceCorridorSerialPrefixRegion realization hcubic hrotation htwoSided
      hunique (offset.val + 1))
    ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
      offset).nextLocalLayerPrefixCrossing)
    color hcolor

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
