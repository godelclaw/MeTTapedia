import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseStableFiniteOutputDecoder
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseStableFaceFixedReceipt

/-!
# The finite rebase output from both fixed residual states

The stable tracked decoder reconstructs successor connectivity from the
incoming profile and its eight-slot residual state.  The stable facial decoder
reconstructs every predecessor component and capped contribution from its
fixed `Fin 16` occurrence state and four predecessor-port coordinates.

This file substitutes both reconstructions into the complete five-field
output receipt.  Every literal heterogeneous Cell--rebase letter still
decodes to exactly its literal successor profile, so no accumulated prefix
graph remains in the decoded output.

This is an exact one-step decoder, not yet a reachable-state theorem.  The
successor residual states still have to be computed from the current fixed
states and the literal local letter before a finite closure or threshold may
be claimed.
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

local instance framedCorridorSerialBoundaryRebaseStableFixedFiniteOutputDecoderEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Replace both accumulated predecessor subreceipts by their fixed-state
reconstructions.  Output colours remain literal data of the local letter. -/
noncomputable def sourceCorridorSerialBoundaryRebaseStableFixedFiniteOutputReceiptCodeAt
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
  let tracked :=
    sourceCorridorSerialBoundaryRebaseStableFiniteOutputReceiptCodeAt
      realization hcubic hrotation htwoSided hunique offset hnext color
        hcurrentColor hsuccessorColor
  { outputEdgeColor := tracked.outputEdgeColor
    tracked := tracked.tracked
    face :=
      sourceCorridorSerialBoundaryRebaseStableFixedFiniteFaceReceiptCodeAt
        realization hcubic hrotation htwoSided hunique offset hnext color
          hsuccessorColor }

/-- The complete fixed-state output receipt is exactly the earlier receipt
whose tracked part was already reconstructed and whose facial part was still
literal. -/
theorem sourceCorridorSerialBoundaryRebaseStableFixedFiniteOutputReceiptCodeAt_eq_stableTracked
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
    sourceCorridorSerialBoundaryRebaseStableFixedFiniteOutputReceiptCodeAt
        realization hcubic hrotation htwoSided hunique offset hnext color
          hcurrentColor hsuccessorColor =
      sourceCorridorSerialBoundaryRebaseStableFiniteOutputReceiptCodeAt
        realization hcubic hrotation htwoSided hunique offset hnext color
          hcurrentColor hsuccessorColor := by
  apply congrArg (fun face =>
    { outputEdgeColor :=
        (sourceCorridorSerialBoundaryRebaseStableFiniteOutputReceiptCodeAt
          realization hcubic hrotation htwoSided hunique offset hnext color
            hcurrentColor hsuccessorColor).outputEdgeColor
      tracked :=
        (sourceCorridorSerialBoundaryRebaseStableFiniteOutputReceiptCodeAt
          realization hcubic hrotation htwoSided hunique offset hnext color
            hcurrentColor hsuccessorColor).tracked
      face := face } :
      BoundedSerialBoundaryRebaseFiniteFaceReceiptCode _ →
        BoundedSerialBoundaryRebaseFiniteOutputReceiptCode _)
  exact
    sourceCorridorSerialBoundaryRebaseStableFixedFiniteFaceReceiptCodeAt_eq_literal
      realization hcubic hrotation htwoSided hunique offset hnext color
        hsuccessorColor

/-- Every literal source rebase has one complete graph-free finite output
letter, decoded from the incoming profile, both fixed residual states, and the
literal local Cell letter.  Its output is exactly the literal successor
profile. -/
theorem exists_stableFixedFiniteOutputLetter_outputProfile_eq_sourceCorridorSerialInput_next
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
    sourceCorridorSerialBoundaryRebaseStableFixedFiniteOutputReceiptCodeAt
      realization hcubic hrotation htwoSided hunique offset hnext color
        hcurrentColor hsuccessorColor
  let code : BoundedSerialBoundaryRebaseFiniteOutputLetterCode :=
    { outputCount := output.faceFragmentCount
      receipt := receipt }
  let stable :=
    sourceCorridorSerialBoundaryRebaseStableFiniteOutputReceiptCodeAt
      realization hcubic hrotation htwoSided hunique offset hnext color
        hcurrentColor hsuccessorColor
  let literal := sourceCorridorSerialBoundaryRebaseFiniteOutputReceiptCodeAt
    realization hcubic hrotation htwoSided hunique offset hnext color
      hsuccessorColor
  refine ⟨code, ?_⟩
  have hreceipt : receipt = stable := by
    simpa only [receipt, stable] using
      sourceCorridorSerialBoundaryRebaseStableFixedFiniteOutputReceiptCodeAt_eq_stableTracked
      realization hcubic hrotation htwoSided hunique offset hnext color
        hcurrentColor hsuccessorColor
  simp only [code,
    BoundedSerialBoundaryRebaseFiniteOutputLetterCode.outputProfile]
  rw [BoundedCorridorCutProfile.mk.injEq]
  refine ⟨rfl, ?_⟩
  apply heq_of_eq
  rw [CorridorCutProfile.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext step
    change receipt.outputEdgeColor step = _
    rw [hreceipt]
    exact sourceCorridorSerialBoundaryRebaseFiniteOutputReceiptCodeAt_edgeColor
      realization hcubic hrotation htwoSided hunique offset hnext color
        hsuccessorColor step
  · funext pair left right
    rcases left with left | terminal
    · rcases right with right | terminal
      · apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        change receipt.strandConnected pair left right ↔ _
        rw [hreceipt]
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
    change receipt.face.faceContinues left right = _
    rw [hreceipt]
    change literal.face.faceContinues left right = _
    exact
      sourceCorridorSerialBoundaryRebaseFiniteOutputReceiptCodeAt_faceContinues
        realization hcubic hrotation htwoSided hunique offset hnext color
          hsuccessorColor left right
  · funext fragment port
    rcases port with step | terminal
    · apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      change receipt.face.fragmentContainsPort fragment step ↔ _
      rw [hreceipt]
      change literal.face.fragmentContainsPort fragment step ↔ _
      exact
        sourceCorridorSerialBoundaryRebaseFiniteOutputReceiptCodeAt_fragmentContainsPort
          realization hcubic hrotation htwoSided hunique offset hnext color
            hsuccessorColor fragment step
    · exact Fin.elim0 terminal
  · funext fragment
    apply Fin.ext
    change receipt.face.faceLengthCap fragment = _
    rw [hreceipt]
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
