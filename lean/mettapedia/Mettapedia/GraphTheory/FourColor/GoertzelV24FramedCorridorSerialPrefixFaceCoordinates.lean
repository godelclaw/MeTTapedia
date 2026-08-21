import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundedFaceSeamFamilyCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialPrefixSeamCode

/-!
# Boundary-fragment coordinates for the serial-prefix face seam

The occurrence-sensitive facial seam between the cumulative source prefix and
one literal Cell already has a finite graph code for any chosen ambient face
orbit.  The profile on the far side of that Cell observes only its canonical
boundary fragments.  This file aligns those two presentations.

For each actual output fragment, the stored coordinate is the exact seam graph
on that fragment's ambient orbit face.  The fragment count is retained rather
than padded, and agrees definitionally with the output five-field profile.

This is the facial-coordinate half of a finite one-Cell letter.  It does not
yet prove that an old profile and a finite letter determine the new profile,
compute a reachable closure, or derive a reduction threshold.
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

local instance framedCorridorSerialPrefixFaceCoordinatesEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The facial residual seam of one literal source Cell, indexed by the
canonical boundary fragments of the literal prefix output state. -/
noncomputable def sourceCorridorSerialPrefixFaceCoordinateCodeAt
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
    BoundedFaceSeamFamilyCode 4 14 := by
  let outputData := sourceCorridorSerialPrefixCutDataAt realization hcubic
    hrotation htwoSided hunique offset
  let fragmentCount := Fintype.card (BoundaryRegionalFragment
    embedded.cellulation.rotation.toRotationSystem
    (indexedCrossingEdgeSet
      ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        offset).nextLocalLayerPrefixCrossing))
    (sourceCorridorSerialPrefixRegion realization hcubic hrotation htwoSided
      hunique (offset.val + 1)))
  have hfragmentCount : fragmentCount ≤ 4 := by
    exact regionalBoundaryGraphCutData_fragmentCount_le_two_mul
      embedded.cellulation.rotation.toRotationSystem
      (sourceCorridorSerialPrefixRegion realization hcubic hrotation htwoSided
        hunique (offset.val + 1))
      ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        offset).nextLocalLayerPrefixCrossing)
  refine
    { faceFragmentCount := ⟨fragmentCount, Nat.lt_succ_of_le hfragmentCount⟩
      seamCode := fun fragment =>
        sourceCorridorSerialInputFaceSeamCodeAt realization hcubic hrotation
          htwoSided hunique offset
          (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
            (outputData.fragmentFace fragment)) }

/-- The stored count is exactly the literal prefix output cut's canonical
occurrence-sensitive boundary-fragment count. -/
theorem sourceCorridorSerialPrefixFaceCoordinateCodeAt_count
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
    (sourceCorridorSerialPrefixFaceCoordinateCodeAt realization hcubic
      hrotation htwoSided hunique offset).faceFragmentCount.val =
      Fintype.card (BoundaryRegionalFragment
        embedded.cellulation.rotation.toRotationSystem
        (indexedCrossingEdgeSet
          ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
            hunique offset).nextLocalLayerPrefixCrossing))
        (sourceCorridorSerialPrefixRegion realization hcubic hrotation
          htwoSided hunique (offset.val + 1))) := by
  rfl

/-- The same exact count is the face-fragment count stored by the literal
prefix output's five-field profile. -/
theorem sourceCorridorSerialPrefixFaceCoordinateCodeAt_count_eq_profile
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
        hunique offset).nextLocalLayerPrefixCrossing step) ≠ 0) :
    (sourceCorridorSerialPrefixFaceCoordinateCodeAt realization hcubic
      hrotation htwoSided hunique offset).faceFragmentCount =
      (sourceCorridorSerialPrefixBoundedProfileAt realization hcubic hrotation
        htwoSided hunique offset color hcolor).faceFragmentCount := by
  apply Fin.ext
  rfl

/-- Each stored coordinate is definitionally the finite code of the first
serial seam on the corresponding output fragment's ambient face. -/
theorem sourceCorridorSerialPrefixFaceCoordinateCodeAt_apply
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
    (fragment : Fin
      (sourceCorridorSerialPrefixFaceCoordinateCodeAt realization hcubic
        hrotation htwoSided hunique offset).faceFragmentCount.val) :
    (sourceCorridorSerialPrefixFaceCoordinateCodeAt realization hcubic
      hrotation htwoSided hunique offset).seamCode fragment =
      sourceCorridorSerialInputFaceSeamCodeAt realization hcubic hrotation
        htwoSided hunique offset
        (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
          ((sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
            htwoSided hunique offset).fragmentFace fragment)) := by
  rfl

/-- For every literal prefix output fragment, the participating ambient facial
seam is exactly isomorphic to the graph stored at that fragment coordinate. -/
noncomputable def sourceCorridorSerialPrefixFaceCoordinateCodeIsoAt
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
    (fragment : Fin
      (sourceCorridorSerialPrefixFaceCoordinateCodeAt realization hcubic
        hrotation htwoSided hunique offset).faceFragmentCount.val) :
    let root := orbitFaceRoot
      embedded.cellulation.rotation.toRotationSystem
      ((sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).fragmentFace fragment)
    let seam := sourceCorridorSerialInputFaceSeamGraphAt realization hcubic
      hrotation htwoSided hunique offset root
    seam.induce seam.support ≃g
      ((sourceCorridorSerialPrefixFaceCoordinateCodeAt realization hcubic
        hrotation htwoSided hunique offset).seamCode fragment).graph := by
  dsimp only
  exact sourceCorridorSerialInputFaceSeamCodeIsoAt realization hcubic hrotation
    htwoSided hunique offset
    (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
      ((sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).fragmentFace fragment))

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
