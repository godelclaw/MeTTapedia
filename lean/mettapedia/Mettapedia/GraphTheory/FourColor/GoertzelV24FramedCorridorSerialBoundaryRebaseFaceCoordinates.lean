import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseCode

/-!
# Boundary-fragment coordinates for the serial rebase face code

The occurrence-sensitive facial seam of a serial boundary rebase already has
a finite graph code for any chosen ambient face orbit.  A profile transition,
however, observes only the boundary fragments of the successor input cut.
This file aligns those two presentations.

The generic code below stores the exact number of observed fragments and one
bounded support-graph code for each of them.  Its source specialization uses
the successor input cut's canonical fragment enumeration and the corresponding
ambient orbit-face root.  Thus no arbitrary face root remains in the stored
letter.

This is an indexed finite family of exact seam graphs.  It does not yet prove
that the old five-field profile together with this family determines the
successor profile, compute a reachable closure, or derive a threshold.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundedSupportGraphCode
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseFaceCoordinatesEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- A bounded family of local face-seam graphs.  The exact fragment count is
part of the code, so no padding coordinate can be confused with a real
boundary fragment. -/
structure BoundedFaceSeamFamilyCode (faceFragmentBound supportBound : Nat) where
  faceFragmentCount : Fin (faceFragmentBound + 1)
  seamCode : Fin faceFragmentCount.val → BoundedSupportGraphCode supportBound

instance (faceFragmentBound supportBound : Nat) :
    DecidableEq (BoundedFaceSeamFamilyCode faceFragmentBound supportBound) :=
  Classical.decEq _

private def boundedFaceSeamFamilyCodeEquiv
    (faceFragmentBound supportBound : Nat) :
    BoundedFaceSeamFamilyCode faceFragmentBound supportBound ≃
      Σ faceFragmentCount : Fin (faceFragmentBound + 1),
        Fin faceFragmentCount.val → BoundedSupportGraphCode supportBound where
  toFun code := ⟨code.faceFragmentCount, code.seamCode⟩
  invFun code := ⟨code.1, code.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance (faceFragmentBound supportBound : Nat) :
    Fintype (BoundedFaceSeamFamilyCode faceFragmentBound supportBound) :=
  Fintype.ofEquiv _
    (boundedFaceSeamFamilyCodeEquiv faceFragmentBound supportBound).symm

namespace SourceTrail

namespace AnnularEmbedding

/-- The face-seam part of one literal serial rebase, indexed by the actual
boundary fragments of the successor input state. -/
noncomputable def sourceCorridorSerialBoundaryRebaseFaceCoordinateCodeAt
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
    BoundedFaceSeamFamilyCode 4 14 := by
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
        sourceCorridorSerialBoundaryRebaseFaceSeamCodeAt realization hcubic
          hrotation htwoSided hunique offset hnext
          (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
            (nextData.fragmentFace fragment)) }

/-- The stored fragment count is exactly the successor input cut's canonical
occurrence-sensitive boundary-fragment count. -/
theorem sourceCorridorSerialBoundaryRebaseFaceCoordinateCodeAt_count
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
    (sourceCorridorSerialBoundaryRebaseFaceCoordinateCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext).faceFragmentCount.val =
      Fintype.card (BoundaryRegionalFragment
        embedded.cellulation.rotation.toRotationSystem
        (indexedCrossingEdgeSet
          ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
            hunique (sourceCorridorSerialNextOffset offset hnext))
            |>.localLayerPrefixCrossing))
        (sourceCorridorSerialCutRegionAt realization hcubic hrotation htwoSided
          hunique (sourceCorridorSerialNextOffset offset hnext))) := by
  rfl

/-- The same exact count is the face-fragment count stored by the successor
five-field serial profile. -/
theorem sourceCorridorSerialBoundaryRebaseFaceCoordinateCodeAt_count_eq_profile
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
    (hcolor : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique (sourceCorridorSerialNextOffset offset hnext))
        |>.localLayerPrefixCrossing step) ≠ 0) :
    (sourceCorridorSerialBoundaryRebaseFaceCoordinateCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext).faceFragmentCount =
      (sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
        color hcolor).faceFragmentCount := by
  apply Fin.ext
  rfl

/-- Each stored coordinate is definitionally the finite code of the rebase
seam on the corresponding successor boundary fragment's ambient face. -/
theorem sourceCorridorSerialBoundaryRebaseFaceCoordinateCodeAt_apply
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
      (sourceCorridorSerialBoundaryRebaseFaceCoordinateCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext).faceFragmentCount.val) :
    (sourceCorridorSerialBoundaryRebaseFaceCoordinateCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext).seamCode fragment =
      sourceCorridorSerialBoundaryRebaseFaceSeamCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext
        (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
          ((sourceCorridorSerialInputCutDataAt realization hcubic hrotation
            htwoSided hunique (sourceCorridorSerialNextOffset offset hnext))
            |>.fragmentFace fragment)) := by
  rfl

/-- For every successor boundary fragment, the participating ambient facial
seam is exactly isomorphic to the graph stored at that fragment coordinate. -/
noncomputable def sourceCorridorSerialBoundaryRebaseFaceCoordinateCodeIsoAt
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
      (sourceCorridorSerialBoundaryRebaseFaceCoordinateCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext).faceFragmentCount.val) :
    let root := orbitFaceRoot
      embedded.cellulation.rotation.toRotationSystem
      ((sourceCorridorSerialInputCutDataAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext))
        |>.fragmentFace fragment)
    let seam := sourceCorridorSerialBoundaryRebaseFaceSeamAt realization hcubic
      hrotation htwoSided hunique offset hnext root
    seam.induce seam.support ≃g
      ((sourceCorridorSerialBoundaryRebaseFaceCoordinateCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext).seamCode fragment).graph := by
  dsimp only
  exact sourceCorridorSerialBoundaryRebaseFaceSeamCodeIsoAt realization hcubic
    hrotation htwoSided hunique offset hnext
    (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
      ((sourceCorridorSerialInputCutDataAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext))
        |>.fragmentFace fragment))

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
