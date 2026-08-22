import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFiniteOutputDecoder
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseStableTrackedStepDecoder

/-!
# The finite rebase output with tracked history removed

The complete five-field rebase receipt already has a graph-free output
decoder, but its tracked subreceipt used to contain an old-component matrix
extracted from the accumulated prefix graph.  The stable tracked-step decoder
now reconstructs that matrix from the incoming profile and the eight-slot
residual state.

This file substitutes the reconstructed tracked step into the complete output
receipt.  Every literal source rebase still decodes to exactly the same
successor profile.  Consequently capped facial state is the only remaining
part of this output receipt which is still extracted from unbounded prefix
geometry.  Computing that facial state and updating both residual states are
separate obligations; no reachable count or threshold is claimed here.
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

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseStableFiniteOutputDecoderEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Replace the literal receipt's accumulated tracked matrix by the stable
finite-state reconstruction.  Colours and the finite facial receipt are left
unchanged. -/
noncomputable def sourceCorridorSerialBoundaryRebaseStableFiniteOutputReceiptCodeAt
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
    (hcurrentColor : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).nextLocalLayerPrefixCrossing step) ≠ 0)
    (hsuccessorColor : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique (sourceCorridorSerialNextOffset offset hnext))
        |>.localLayerPrefixCrossing step) ≠ 0) :
    BoundedSerialBoundaryRebaseFiniteOutputReceiptCode
      (sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) color
        hsuccessorColor).faceFragmentCount.val :=
  let literal := sourceCorridorSerialBoundaryRebaseFiniteOutputReceiptCodeAt
    realization hcubic hrotation htwoSided hunique offset hnext color
      hsuccessorColor
  { outputEdgeColor := literal.outputEdgeColor
    tracked := sourceCorridorSerialBoundaryRebaseStableTrackedStepCodeAt
      realization hcubic hrotation htwoSided hunique offset hnext color
        hcurrentColor
    face := literal.face }

/-- Stable reconstruction preserves the complete tracked-connectivity query
of the finite output receipt. -/
theorem sourceCorridorSerialBoundaryRebaseStableFiniteOutputReceiptCodeAt_strandConnected_iff_literal
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
    (hcurrentColor : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).nextLocalLayerPrefixCrossing step) ≠ 0)
    (hsuccessorColor : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique (sourceCorridorSerialNextOffset offset hnext))
        |>.localLayerPrefixCrossing step) ≠ 0)
    (pair : TrackedColorPair) (left right : Fin 2) :
    (sourceCorridorSerialBoundaryRebaseStableFiniteOutputReceiptCodeAt
        realization hcubic hrotation htwoSided hunique offset hnext color
          hcurrentColor hsuccessorColor).strandConnected pair left right ↔
      (sourceCorridorSerialBoundaryRebaseFiniteOutputReceiptCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext color hsuccessorColor
        ).strandConnected pair left right := by
  constructor
  · rintro ⟨hleft, hright, hclosure⟩
    refine ⟨hleft, hright, ?_⟩
    have hclosure' :=
      (sourceCorridorSerialBoundaryRebaseStableTrackedClosure_iff_literal
        realization hcubic hrotation htwoSided hunique offset hnext color
          hcurrentColor pair
          ((sourceCorridorSerialBoundaryRebaseStableTrackedStepCodeAt
            realization hcubic hrotation htwoSided hunique offset hnext color
              hcurrentColor).localCode.point left)
          ((sourceCorridorSerialBoundaryRebaseStableTrackedStepCodeAt
            realization hcubic hrotation htwoSided hunique offset hnext color
              hcurrentColor).localCode.point right)).1 hclosure
    simpa [sourceCorridorSerialBoundaryRebaseStableFiniteOutputReceiptCodeAt,
      sourceCorridorSerialBoundaryRebaseFiniteOutputReceiptCodeAt,
      sourceCorridorSerialBoundaryRebaseStableTrackedStepCodeAt,
      boundedSerialBoundaryRebaseTrackedStepCodeOfStableSwitch,
      sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt] using hclosure'
  · rintro ⟨hleft, hright, hclosure⟩
    refine ⟨hleft, hright, ?_⟩
    have hclosure' :=
      (sourceCorridorSerialBoundaryRebaseStableTrackedClosure_iff_literal
        realization hcubic hrotation htwoSided hunique offset hnext color
          hcurrentColor pair
          ((sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt realization
            hcubic hrotation htwoSided hunique offset hnext color
              ).localCode.point left)
          ((sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt realization
            hcubic hrotation htwoSided hunique offset hnext color
              ).localCode.point right)).2 hclosure
    simpa [sourceCorridorSerialBoundaryRebaseStableFiniteOutputReceiptCodeAt,
      sourceCorridorSerialBoundaryRebaseFiniteOutputReceiptCodeAt,
      sourceCorridorSerialBoundaryRebaseStableTrackedStepCodeAt,
      boundedSerialBoundaryRebaseTrackedStepCodeOfStableSwitch,
      sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt] using hclosure'

/-- Every literal source rebase has a complete finite output letter whose
tracked part is reconstructed from finite predecessor state and whose decoded
profile is still exactly the literal successor profile. -/
theorem exists_stableTrackedFiniteOutputLetter_outputProfile_eq_sourceCorridorSerialInput_next
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
    (hcurrentColor : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).nextLocalLayerPrefixCrossing step) ≠ 0)
    (hsuccessorColor : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique (sourceCorridorSerialNextOffset offset hnext))
        |>.localLayerPrefixCrossing step) ≠ 0) :
    ∃ code : BoundedSerialBoundaryRebaseFiniteOutputLetterCode,
      code.outputProfile =
        sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
          htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) color
            hsuccessorColor := by
  classical
  let output := sourceCorridorSerialInputBoundedProfileAt realization hcubic
    hrotation htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
      color hsuccessorColor
  let receipt :=
    sourceCorridorSerialBoundaryRebaseStableFiniteOutputReceiptCodeAt
      realization hcubic hrotation htwoSided hunique offset hnext color
        hcurrentColor hsuccessorColor
  let literal := sourceCorridorSerialBoundaryRebaseFiniteOutputReceiptCodeAt
    realization hcubic hrotation htwoSided hunique offset hnext color
      hsuccessorColor
  let code : BoundedSerialBoundaryRebaseFiniteOutputLetterCode :=
    { outputCount := output.faceFragmentCount
      receipt := receipt }
  refine ⟨code, ?_⟩
  simp only [code,
    BoundedSerialBoundaryRebaseFiniteOutputLetterCode.outputProfile]
  rw [BoundedCorridorCutProfile.mk.injEq]
  refine ⟨rfl, ?_⟩
  apply heq_of_eq
  rw [CorridorCutProfile.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext step
    exact sourceCorridorSerialBoundaryRebaseFiniteOutputReceiptCodeAt_edgeColor
      realization hcubic hrotation htwoSided hunique offset hnext color
        hsuccessorColor step
  · funext pair left right
    rcases left with left | terminal
    · rcases right with right | terminal
      · apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq, code, output, receipt]
        exact
          (sourceCorridorSerialBoundaryRebaseStableFiniteOutputReceiptCodeAt_strandConnected_iff_literal
            realization hcubic hrotation htwoSided hunique offset hnext color
              hcurrentColor hsuccessorColor pair left right).trans
            (sourceCorridorSerialBoundaryRebaseFiniteOutputReceiptCodeAt_strandConnected
              realization hcubic hrotation htwoSided hunique offset hnext color
                hsuccessorColor pair left right).symm
      · exact Fin.elim0 terminal
    · exact Fin.elim0 terminal
  · funext left right
    change literal.face.faceContinues left right = _
    exact
      sourceCorridorSerialBoundaryRebaseFiniteOutputReceiptCodeAt_faceContinues
        realization hcubic hrotation htwoSided hunique offset hnext color
          hsuccessorColor left right
  · funext fragment port
    rcases port with step | terminal
    · apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, code, output, receipt]
      change literal.face.fragmentContainsPort fragment step ↔ _
      exact
        sourceCorridorSerialBoundaryRebaseFiniteOutputReceiptCodeAt_fragmentContainsPort
          realization hcubic hrotation htwoSided hunique offset hnext color
            hsuccessorColor fragment step
    · exact Fin.elim0 terminal
  · funext fragment
    apply Fin.ext
    change literal.face.faceLengthCap fragment = _
    exact
      sourceCorridorSerialBoundaryRebaseFiniteOutputReceiptCodeAt_faceLengthCap
        realization hcubic hrotation htwoSided hunique offset hnext color
          hsuccessorColor fragment

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
