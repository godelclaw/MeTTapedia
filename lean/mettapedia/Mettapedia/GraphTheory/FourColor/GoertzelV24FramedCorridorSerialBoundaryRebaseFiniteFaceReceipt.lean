import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFaceFiniteContinuation

/-!
# One finite face receipt for a literal serial boundary rebase

The successor face coordinates of a literal rebase have now been decoded
separately: finite component closure gives continuation and port incidence,
while predecessor component caps and two local terms give capped face
progress.  This file packages those results in one graph-free finite ABI.

For every successor fragment, a row stores one finite component step, its
distinguished output coordinate, the compact optional positions of the two
displayed ports, and the capped predecessor contribution.  The complete
receipt adds the finite face-equivalence code and the local/overlap cap table.
Lean then recovers all three face-progress subcoordinates of the literal
successor profile exactly.

This is the face part of the heterogeneous rebase letter.  It does not yet
join the tracked-strand recurrence, compose the distinct Cell and rebase
letters, measure a reachable closure, or derive a threshold.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24WidthTwoFaceEquivalenceCompression
open SimpleGraph
open SimpleGraphDartRotation

/-- One graph-free finite row used to decode a successor face fragment. -/
structure BoundedSerialBoundaryRebaseFiniteFaceRowCode where
  step : BoundedSerialBoundaryRebaseFaceStepCode
  output : Fin step.localCode.vertexCount.val
  portPositions : BoundedSerialBoundaryRebaseFacePortPositionCode step
  oldCap : Fin 6

noncomputable instance :
    DecidableEq BoundedSerialBoundaryRebaseFiniteFaceRowCode :=
  Classical.decEq _

private def boundedSerialBoundaryRebaseFiniteFaceRowCodeEquiv :
    BoundedSerialBoundaryRebaseFiniteFaceRowCode ≃
      Σ step : BoundedSerialBoundaryRebaseFaceStepCode,
        Fin step.localCode.vertexCount.val ×
          BoundedSerialBoundaryRebaseFacePortPositionCode step × Fin 6 where
  toFun code := ⟨code.step, code.output, code.portPositions, code.oldCap⟩
  invFun code :=
    { step := code.1
      output := code.2.1
      portPositions := code.2.2.1
      oldCap := code.2.2.2 }
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance :
    Fintype BoundedSerialBoundaryRebaseFiniteFaceRowCode :=
  Fintype.ofEquiv _ boundedSerialBoundaryRebaseFiniteFaceRowCodeEquiv.symm

/-- Decode whether one displayed port belongs to the successor component
named by this row. -/
def BoundedSerialBoundaryRebaseFiniteFaceRowCode.containsPort
    (row : BoundedSerialBoundaryRebaseFiniteFaceRowCode)
    (port : Fin 2) : Prop :=
  row.portPositions.containsPort row.output port

/-- The complete finite face receipt of one successor boundary rebase. -/
structure BoundedSerialBoundaryRebaseFiniteFaceReceiptCode
    (outputCount : Nat) where
  continuation : FaceEquivalenceCode outputCount
  row : Fin outputCount → BoundedSerialBoundaryRebaseFiniteFaceRowCode
  localCaps : BoundedSerialBoundaryRebaseFaceLocalCapCode outputCount

noncomputable instance (outputCount : Nat) :
    DecidableEq (BoundedSerialBoundaryRebaseFiniteFaceReceiptCode outputCount) :=
  Classical.decEq _

private def boundedSerialBoundaryRebaseFiniteFaceReceiptCodeEquiv
    (outputCount : Nat) :
    BoundedSerialBoundaryRebaseFiniteFaceReceiptCode outputCount ≃
      FaceEquivalenceCode outputCount ×
        (Fin outputCount → BoundedSerialBoundaryRebaseFiniteFaceRowCode) ×
          BoundedSerialBoundaryRebaseFaceLocalCapCode outputCount where
  toFun code := ⟨code.continuation, code.row, code.localCaps⟩
  invFun code :=
    { continuation := code.1
      row := code.2.1
      localCaps := code.2.2 }
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance (outputCount : Nat) :
    Fintype (BoundedSerialBoundaryRebaseFiniteFaceReceiptCode outputCount) :=
  Fintype.ofEquiv _
    (boundedSerialBoundaryRebaseFiniteFaceReceiptCodeEquiv outputCount).symm

/-- Decode one successor face-continuation bit. -/
def BoundedSerialBoundaryRebaseFiniteFaceReceiptCode.faceContinues
    {outputCount : Nat}
    (receipt : BoundedSerialBoundaryRebaseFiniteFaceReceiptCode outputCount)
    (left right : Fin outputCount) : Bool :=
  faceRelation receipt.continuation.1 left right

/-- Decode one successor port-incidence bit. -/
def BoundedSerialBoundaryRebaseFiniteFaceReceiptCode.fragmentContainsPort
    {outputCount : Nat}
    (receipt : BoundedSerialBoundaryRebaseFiniteFaceReceiptCode outputCount)
    (fragment : Fin outputCount) (port : Fin 2) : Prop :=
  (receipt.row fragment).containsPort port

/-- Decode one successor capped face-progress value. -/
def BoundedSerialBoundaryRebaseFiniteFaceReceiptCode.faceLengthCap
    {outputCount : Nat}
    (receipt : BoundedSerialBoundaryRebaseFiniteFaceReceiptCode outputCount)
    (fragment : Fin outputCount) : Nat :=
  receipt.localCaps.outputCap
    (fun current => (receipt.row current).oldCap.val) fragment

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseFiniteFaceReceiptEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The finite row extracted for one literal successor fragment. -/
noncomputable def sourceCorridorSerialBoundaryRebaseFiniteFaceRowCodeAt
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
    (fragment : SourceCorridorSerialBoundaryRebaseSuccessorFacePortAt
      realization hcubic hrotation htwoSided hunique offset hnext) :
    BoundedSerialBoundaryRebaseFiniteFaceRowCode := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let data := sourceCorridorSerialInputCutDataAt realization hcubic hrotation
    htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  let root := orbitFaceRoot RS (data.fragmentFace fragment)
  let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
    realization hcubic hrotation htwoSided hunique offset hnext root
  let step := sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization
    hcubic hrotation htwoSided hunique offset hnext root
  let boundaryFragment :=
    sourceCorridorSerialBoundaryRebaseSuccessorFaceFragmentAt realization
      hcubic hrotation htwoSided hunique offset hnext fragment
  let capRoot := orbitFaceRoot RS boundaryFragment.1.1
  let capCarrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
    realization hcubic hrotation htwoSided hunique offset hnext capRoot
  let capPredecessor :=
    sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext capRoot
  let capSemantic :=
    sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt_isComponentSemantic
      realization hcubic hrotation htwoSided hunique offset hnext capRoot
  let output : Fin step.localCode.vertexCount.val :=
    carrierCoordinate carrier
      (sourceCorridorSerialBoundaryRebaseSuccessorFacePositionAt realization
        hcubic hrotation htwoSided hunique offset hnext fragment)
  let capOutput : Fin capPredecessor.localCode.vertexCount.val :=
    carrierCoordinate capCarrier
      (sourceCorridorSerialBoundaryRebaseSuccessorFacePositionAt realization
        hcubic hrotation htwoSided hunique offset hnext fragment)
  exact
    { step := step
      output := output
      portPositions :=
        sourceCorridorSerialBoundaryRebaseFacePortPositionCodeAt realization
          hcubic hrotation htwoSided hunique offset hnext root
      oldCap :=
        ⟨capPredecessor.oldComponentCapSumAt capSemantic capOutput,
          Nat.lt_succ_of_le
            (capPredecessor.oldComponentCapSumAt_le_five capSemantic
              capOutput)⟩ }

/-- The one finite face receipt extracted from a literal serial rebase. -/
noncomputable def sourceCorridorSerialBoundaryRebaseFiniteFaceReceiptCodeAt
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
    BoundedSerialBoundaryRebaseFiniteFaceReceiptCode
      (sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) color
        hcolor).faceFragmentCount.val where
  continuation :=
    sourceCorridorSerialBoundaryRebaseFaceContinuationCodeAt realization
      hcubic hrotation htwoSided hunique offset hnext color hcolor
  row := fun fragment =>
    sourceCorridorSerialBoundaryRebaseFiniteFaceRowCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext fragment
  localCaps := sourceCorridorSerialBoundaryRebaseFaceLocalCapCodeAt realization
    hcubic hrotation htwoSided hunique offset hnext

/-- The joint receipt decodes literal successor face continuation exactly. -/
theorem sourceCorridorSerialBoundaryRebaseFiniteFaceReceiptCodeAt_faceContinues
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
        |>.localLayerPrefixCrossing step) ≠ 0)
    (left right : SourceCorridorSerialBoundaryRebaseSuccessorFacePortAt
      realization hcubic hrotation htwoSided hunique offset hnext) :
    (sourceCorridorSerialBoundaryRebaseFiniteFaceReceiptCodeAt realization
      hcubic hrotation htwoSided hunique offset hnext color hcolor
      ).faceContinues left right =
      (sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) color
        hcolor).profile.faceContinues left right := by
  exact
    sourceCorridorSerialInputBoundedProfileAt_next_faceContinues_eq_finiteCode
      realization hcubic hrotation htwoSided hunique offset hnext color hcolor
        left right

/-- The joint receipt decodes literal successor port incidence exactly. -/
theorem sourceCorridorSerialBoundaryRebaseFiniteFaceReceiptCodeAt_fragmentContainsPort
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
        |>.localLayerPrefixCrossing step) ≠ 0)
    (fragment : SourceCorridorSerialBoundaryRebaseSuccessorFacePortAt
      realization hcubic hrotation htwoSided hunique offset hnext)
    (port : Fin 2) :
    (sourceCorridorSerialBoundaryRebaseFiniteFaceReceiptCodeAt realization
      hcubic hrotation htwoSided hunique offset hnext color hcolor
      ).fragmentContainsPort fragment port ↔
      (sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) color
        hcolor).profile.fragmentContainsPort fragment (.inl port) = true := by
  simpa only [
      BoundedSerialBoundaryRebaseFiniteFaceReceiptCode.fragmentContainsPort,
      BoundedSerialBoundaryRebaseFiniteFaceRowCode.containsPort,
      sourceCorridorSerialBoundaryRebaseFiniteFaceReceiptCodeAt,
      sourceCorridorSerialBoundaryRebaseFiniteFaceRowCodeAt] using
    (sourceCorridorSerialInputBoundedProfileAt_next_fragmentContainsPort_iff_finitePositionCode
      realization hcubic hrotation htwoSided hunique offset hnext color hcolor
        fragment port).symm

/-- The joint receipt decodes literal successor capped face progress exactly. -/
theorem sourceCorridorSerialBoundaryRebaseFiniteFaceReceiptCodeAt_faceLengthCap
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
        |>.localLayerPrefixCrossing step) ≠ 0)
    (fragment : SourceCorridorSerialBoundaryRebaseSuccessorFacePortAt
      realization hcubic hrotation htwoSided hunique offset hnext) :
    (sourceCorridorSerialBoundaryRebaseFiniteFaceReceiptCodeAt realization
      hcubic hrotation htwoSided hunique offset hnext color hcolor
      ).faceLengthCap fragment =
      ((sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) color
        hcolor).profile.faceLengthCap fragment).val := by
  simpa only [
      BoundedSerialBoundaryRebaseFiniteFaceReceiptCode.faceLengthCap,
      BoundedSerialBoundaryRebaseFaceLocalCapCode.outputCap,
      sourceCorridorSerialBoundaryRebaseFiniteFaceReceiptCodeAt,
      sourceCorridorSerialBoundaryRebaseFiniteFaceRowCodeAt] using
    (sourceCorridorSerialInputBoundedProfileAt_next_faceLengthCap_eq_finiteCode
      realization hcubic hrotation htwoSided hunique offset hnext color hcolor
        fragment).symm

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
