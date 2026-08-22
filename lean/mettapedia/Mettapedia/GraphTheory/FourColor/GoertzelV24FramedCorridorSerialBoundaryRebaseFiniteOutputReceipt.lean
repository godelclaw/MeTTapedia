import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFiniteFaceReceipt
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseSuccessorRoles

/-!
# One finite output receipt for a literal serial boundary rebase

The boundary rebase has two independently verified finite decoders.  Its
tracked step computes successor two-colour connectivity on an at-most-eight
coordinate switch, while its face receipt computes continuation, displayed
port incidence, and capped face progress.  This file joins those decoders with
the two successor crossing colours.

Every literal source rebase supplies the resulting finite receipt, and its
five observation theorems recover every field of the successor corridor
profile exactly.  The old-component matrix inside the tracked step is still
extracted from the literal old prefix.  Thus this is a complete finite output
receipt, not yet the recurrence that computes the receipt from the incoming
finite state.  The distinct Cell/rebase composition and reachable closure also
remain separate.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24WindingClassification
open SimpleGraph
open SimpleGraphDartRotation

/-- The complete finite output receipt of one serial boundary rebase. -/
structure BoundedSerialBoundaryRebaseFiniteOutputReceiptCode
    (faceCount : Nat) where
  outputEdgeColor : Fin 2 → StrandColor
  tracked : BoundedSerialBoundaryRebaseTrackedStepCode
  face : BoundedSerialBoundaryRebaseFiniteFaceReceiptCode faceCount

noncomputable instance (faceCount : Nat) :
    DecidableEq (BoundedSerialBoundaryRebaseFiniteOutputReceiptCode faceCount) :=
  Classical.decEq _

private def boundedSerialBoundaryRebaseFiniteOutputReceiptCodeEquiv
    (faceCount : Nat) :
    BoundedSerialBoundaryRebaseFiniteOutputReceiptCode faceCount ≃
      (Fin 2 → StrandColor) × BoundedSerialBoundaryRebaseTrackedStepCode ×
        BoundedSerialBoundaryRebaseFiniteFaceReceiptCode faceCount where
  toFun code := ⟨code.outputEdgeColor, code.tracked, code.face⟩
  invFun code :=
    { outputEdgeColor := code.1
      tracked := code.2.1
      face := code.2.2 }
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance (faceCount : Nat) :
    Fintype (BoundedSerialBoundaryRebaseFiniteOutputReceiptCode faceCount) :=
  Fintype.ofEquiv _
    (boundedSerialBoundaryRebaseFiniteOutputReceiptCodeEquiv faceCount).symm

/-- Decode one successor two-colour connectivity entry. -/
def BoundedSerialBoundaryRebaseFiniteOutputReceiptCode.strandConnected
    {faceCount : Nat}
    (receipt : BoundedSerialBoundaryRebaseFiniteOutputReceiptCode faceCount)
    (pair : TrackedColorPair) (left right : Fin 2) : Prop :=
  IsTrackedColor (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2
      (receipt.outputEdgeColor left).toColor ∧
    IsTrackedColor (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2
      (receipt.outputEdgeColor right).toColor ∧
    Relation.ReflTransGen
      (boundedSerialBoundaryRebaseTrackedComponentStep receipt.tracked pair)
      (receipt.tracked.localCode.point left)
      (receipt.tracked.localCode.point right)

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseFiniteOutputReceiptEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Extract the complete finite output receipt of one literal rebase. -/
noncomputable def sourceCorridorSerialBoundaryRebaseFiniteOutputReceiptCodeAt
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
    BoundedSerialBoundaryRebaseFiniteOutputReceiptCode
      (sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) color
        hcolor).faceFragmentCount.val where
  outputEdgeColor :=
    (sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
      htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) color
      hcolor).profile.edgeColor
  tracked := sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt realization
    hcubic hrotation htwoSided hunique offset hnext color
  face := sourceCorridorSerialBoundaryRebaseFiniteFaceReceiptCodeAt realization
    hcubic hrotation htwoSided hunique offset hnext color hcolor

/-- The output receipt stores the two successor crossing colours exactly. -/
theorem sourceCorridorSerialBoundaryRebaseFiniteOutputReceiptCodeAt_edgeColor
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
    (step : Fin 2) :
    (sourceCorridorSerialBoundaryRebaseFiniteOutputReceiptCodeAt realization
      hcubic hrotation htwoSided hunique offset hnext color hcolor
      ).outputEdgeColor step =
      (sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) color
        hcolor).profile.edgeColor step := by
  rfl

/-- The output receipt decodes literal successor tracked connectivity
exactly. -/
theorem sourceCorridorSerialBoundaryRebaseFiniteOutputReceiptCodeAt_strandConnected
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
    (pair : TrackedColorPair) (left right : Fin 2) :
    ((sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
      htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) color
      hcolor).profile.strandConnected pair (.inl left) (.inl right) = true) ↔
      (sourceCorridorSerialBoundaryRebaseFiniteOutputReceiptCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext color hcolor
        ).strandConnected pair left right := by
  let data :=
    GoertzelV24RegionalBoundaryProfileFiniteState.regionalBoundaryGraphCutData
      embedded.cellulation.rotation.toRotationSystem
      (sourceCorridorSerialCutRegionAt realization hcubic hrotation htwoSided
        hunique (sourceCorridorSerialNextOffset offset hnext))
      ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        (sourceCorridorSerialNextOffset offset hnext)
        ).localLayerPrefixCrossing)
  have hleft :
      ((sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) color
        hcolor).profile.edgeColor left).toColor =
        color (sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
          hrotation htwoSided hunique offset hnext left) := by
    change ((data.regionalProfile color hcolor).edgeColor left).toColor =
      color (data.crossingEdge left)
    exact data.regionalProfile_edgeColor_toColor color hcolor left
  have hright :
      ((sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) color
        hcolor).profile.edgeColor right).toColor =
        color (sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
          hrotation htwoSided hunique offset hnext right) := by
    change ((data.regionalProfile color hcolor).edgeColor right).toColor =
      color (data.crossingEdge right)
    exact data.regionalProfile_edgeColor_toColor color hcolor right
  have hstep :=
    sourceCorridorSerialInputBoundedProfileAt_next_strandConnected_eq_true_iff_trackedStepCode
      realization hcubic hrotation htwoSided hunique offset hnext color hcolor
        pair left right
  rw [← hleft, ← hright] at hstep
  simpa only [
      BoundedSerialBoundaryRebaseFiniteOutputReceiptCode.strandConnected,
      sourceCorridorSerialBoundaryRebaseFiniteOutputReceiptCodeAt] using hstep

/-- The output receipt decodes literal successor face continuation exactly. -/
theorem sourceCorridorSerialBoundaryRebaseFiniteOutputReceiptCodeAt_faceContinues
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
    (sourceCorridorSerialBoundaryRebaseFiniteOutputReceiptCodeAt realization
      hcubic hrotation htwoSided hunique offset hnext color hcolor
      ).face.faceContinues left right =
      (sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) color
        hcolor).profile.faceContinues left right := by
  exact sourceCorridorSerialBoundaryRebaseFiniteFaceReceiptCodeAt_faceContinues
    realization hcubic hrotation htwoSided hunique offset hnext color hcolor
      left right

/-- The output receipt decodes literal successor port incidence exactly. -/
theorem sourceCorridorSerialBoundaryRebaseFiniteOutputReceiptCodeAt_fragmentContainsPort
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
    (sourceCorridorSerialBoundaryRebaseFiniteOutputReceiptCodeAt realization
      hcubic hrotation htwoSided hunique offset hnext color hcolor
      ).face.fragmentContainsPort fragment port ↔
      (sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) color
        hcolor).profile.fragmentContainsPort fragment (.inl port) = true := by
  exact
    sourceCorridorSerialBoundaryRebaseFiniteFaceReceiptCodeAt_fragmentContainsPort
      realization hcubic hrotation htwoSided hunique offset hnext color hcolor
        fragment port

/-- The output receipt decodes literal successor capped face progress
exactly. -/
theorem sourceCorridorSerialBoundaryRebaseFiniteOutputReceiptCodeAt_faceLengthCap
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
    (sourceCorridorSerialBoundaryRebaseFiniteOutputReceiptCodeAt realization
      hcubic hrotation htwoSided hunique offset hnext color hcolor
      ).face.faceLengthCap fragment =
      ((sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) color
        hcolor).profile.faceLengthCap fragment).val := by
  exact sourceCorridorSerialBoundaryRebaseFiniteFaceReceiptCodeAt_faceLengthCap
    realization hcubic hrotation htwoSided hunique offset hnext color hcolor
      fragment

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
