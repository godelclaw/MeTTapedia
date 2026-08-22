import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundedSupportGraphCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFaceCoordinates
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFiniteSwitch

/-!
# An eight-position facial switch for a literal serial rebase

The occurrence-sensitive face seam of a successor rebase was previously
bounded through a larger edge-adjacency closure.  Its edges are more local:
every seam adjacency joins one of the at-most-six old attachment roles to one
of the two newly displayed crossings.  Two-sidedness makes projection from a
face position to its primal edge injective, so the facial seam has at most
eight participating positions.

This file records that exact finite support and transports the seam graph to
an eight-position code.  It does not yet prove that the predecessor profile
determines this code or compute the successor capped face-progress fields.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundedSupportGraphCode
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationFaceFragments
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseFaceFiniteSwitchEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Every participating position of a facial rebase seam projects to one of
the at-most-eight literal switch edges. -/
theorem sourceCorridorSerialBoundaryRebaseFaceSeamAt_support_projects_finiteSwitch
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
    ∀ position ∈
      (sourceCorridorSerialBoundaryRebaseFaceSeamAt realization hcubic
        hrotation htwoSided hunique offset hnext root).support,
      faceCycleEdge embedded.cellulation.rotation.toRotationSystem root
          position ∈
        sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
          hrotation htwoSided hunique offset hnext := by
  intro position hposition
  rcases (SimpleGraph.mem_support
      (sourceCorridorSerialBoundaryRebaseFaceSeamAt realization hcubic
        hrotation htwoSided hunique offset hnext root)).1 hposition with
    ⟨neighbor, hadj⟩
  rcases sourceCorridorSerialBoundaryRebaseFaceSeamAt_adj_oriented_roles
      realization hcubic hrotation htwoSided hunique offset hnext root hadj with
    hold | hnew
  · rcases hold with ⟨role, hpositionEq, _⟩
    rw [hpositionEq]
    exact sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt_mem_finiteSwitch
      realization hcubic hrotation htwoSided hunique offset hnext role
  · rcases hnew with ⟨_, _, hpositionNew⟩
    exact Finset.mem_union_right _ hpositionNew

/-- The occurrence-sensitive facial seam has at most eight participating
positions, not merely the fourteen positions supplied by the ambient
edge-adjacency closure. -/
theorem sourceCorridorSerialBoundaryRebaseFaceSeamAt_support_card_le_eight
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
    (sourceCorridorSerialBoundaryRebaseFaceSeamAt realization hcubic hrotation
      htwoSided hunique offset hnext root).support.ncard ≤ 8 := by
  let support :=
    (sourceCorridorSerialBoundaryRebaseFaceSeamAt realization hcubic hrotation
      htwoSided hunique offset hnext root).support
  let project := faceCycleEdge
    embedded.cellulation.rotation.toRotationSystem root
  have himage : project '' support ⊆
      (sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
        hrotation htwoSided hunique offset hnext : Set G.edgeSet) := by
    intro edge hedge
    rcases hedge with ⟨position, hposition, rfl⟩
    exact
      sourceCorridorSerialBoundaryRebaseFaceSeamAt_support_projects_finiteSwitch
        realization hcubic hrotation htwoSided hunique offset hnext root
        position hposition
  calc
    support.ncard = (project '' support).ncard :=
      (Set.ncard_image_of_injective support
        (faceCycleEdge_injective
          embedded.cellulation.rotation.toRotationSystem htwoSided root)).symm
    _ ≤ (sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
          hrotation htwoSided hunique offset hnext : Set G.edgeSet).ncard :=
      Set.ncard_le_ncard himage
    _ = (sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
          hrotation htwoSided hunique offset hnext).card :=
      Set.ncard_coe_finset _
    _ ≤ 8 :=
      sourceCorridorSerialBoundaryRebaseFiniteSwitchAt_card_le_eight realization
        hcubic hrotation htwoSided hunique offset hnext

/-- The facial seam transported to a canonical graph on at most eight
positions. -/
noncomputable def sourceCorridorSerialBoundaryRebaseFaceFiniteCodeAt
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
    BoundedSupportGraphCode 8 :=
  boundedSupportCode
    (sourceCorridorSerialBoundaryRebaseFaceSeamAt realization hcubic hrotation
      htwoSided hunique offset hnext root) 8
    (sourceCorridorSerialBoundaryRebaseFaceSeamAt_support_card_le_eight
      realization hcubic hrotation htwoSided hunique offset hnext root)

/-- The participating facial seam is isomorphic to its eight-position finite
code. -/
noncomputable def sourceCorridorSerialBoundaryRebaseFaceFiniteCodeIsoAt
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
      (sourceCorridorSerialBoundaryRebaseFaceFiniteCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root).graph := by
  dsimp only
  exact boundedSupportCodeIso
    (sourceCorridorSerialBoundaryRebaseFaceSeamAt realization hcubic hrotation
      htwoSided hunique offset hnext root) 8
    (sourceCorridorSerialBoundaryRebaseFaceSeamAt_support_card_le_eight
      realization hcubic hrotation htwoSided hunique offset hnext root)

/-- The exact family of successor boundary-fragment seams, now using the
eight-position support bound rather than the earlier fourteen-position
ambient closure. -/
noncomputable def sourceCorridorSerialBoundaryRebaseFaceFiniteCoordinateCodeAt
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
    (hnext : offset.val + 1 < blockLength - 3) :
    BoundedFaceSeamFamilyCode 4 8 := by
  let nextOffset := sourceCorridorSerialNextOffset offset hnext
  let nextData := sourceCorridorSerialInputCutDataAt realization hcubic
    hrotation htwoSided hunique nextOffset
  let fragmentCount := Fintype.card (BoundaryRegionalFragment
    embedded.cellulation.rotation.toRotationSystem
    (indexedCrossingEdgeSet
      ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        nextOffset).localLayerPrefixCrossing))
    (sourceCorridorSerialCutRegionAt realization hcubic hrotation htwoSided
      hunique nextOffset))
  have hfragmentCount : fragmentCount ≤ 4 := by
    exact regionalBoundaryGraphCutData_fragmentCount_le_two_mul
      embedded.cellulation.rotation.toRotationSystem
      (sourceCorridorSerialCutRegionAt realization hcubic hrotation htwoSided
        hunique nextOffset)
      ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        nextOffset).localLayerPrefixCrossing)
  refine
    { faceFragmentCount := ⟨fragmentCount, Nat.lt_succ_of_le hfragmentCount⟩
      seamCode := fun fragment =>
        sourceCorridorSerialBoundaryRebaseFaceFiniteCodeAt realization hcubic
          hrotation htwoSided hunique offset hnext
          (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
            (nextData.fragmentFace fragment)) }

/-- The sharper family retains exactly the same real successor fragment count
as the earlier family; only the support bound has changed. -/
theorem sourceCorridorSerialBoundaryRebaseFaceFiniteCoordinateCodeAt_count
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
    (hnext : offset.val + 1 < blockLength - 3) :
    (sourceCorridorSerialBoundaryRebaseFaceFiniteCoordinateCodeAt realization
      hcubic hrotation htwoSided hunique offset hnext).faceFragmentCount =
    (sourceCorridorSerialBoundaryRebaseFaceCoordinateCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext).faceFragmentCount := by
  rfl

/-- Each entry of the sharper family is exactly the eight-position finite
code of the corresponding successor boundary fragment's ambient face seam. -/
theorem sourceCorridorSerialBoundaryRebaseFaceFiniteCoordinateCodeAt_apply
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
    (fragment : Fin
      (sourceCorridorSerialBoundaryRebaseFaceFiniteCoordinateCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext).faceFragmentCount.val) :
    (sourceCorridorSerialBoundaryRebaseFaceFiniteCoordinateCodeAt realization
      hcubic hrotation htwoSided hunique offset hnext).seamCode fragment =
    sourceCorridorSerialBoundaryRebaseFaceFiniteCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext
      (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
        ((sourceCorridorSerialInputCutDataAt realization hcubic hrotation
          htwoSided hunique (sourceCorridorSerialNextOffset offset hnext))
          |>.fragmentFace fragment)) := by
  rfl

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
