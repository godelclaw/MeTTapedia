import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFiniteOutputReceipt

/-!
# A graph-free decoder for one serial boundary-rebase output

The finite boundary-rebase receipt already computes all five coordinates of
the successor profile.  This file packages its dependent face count and turns
those separate observations into one literal profile decoder.

Every source rebase is decoded exactly.  The decoder has no ambient graph in
its type, but it is deliberately only the output half of the heterogeneous
recurrence: proving that the receipt itself is determined by the incoming
finite state, and then composing it with the distinct Cell letter, remain
separate obligations.
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

/-- A finite rebase-output letter packages the dependent successor face
count together with the already verified five-coordinate receipt. -/
structure BoundedSerialBoundaryRebaseFiniteOutputLetterCode where
  outputCount : Fin 5
  receipt : BoundedSerialBoundaryRebaseFiniteOutputReceiptCode outputCount.val

noncomputable instance :
    DecidableEq BoundedSerialBoundaryRebaseFiniteOutputLetterCode :=
  Classical.decEq _

private def boundedSerialBoundaryRebaseFiniteOutputLetterCodeEquiv :
    BoundedSerialBoundaryRebaseFiniteOutputLetterCode ≃
      Σ outputCount : Fin 5,
        BoundedSerialBoundaryRebaseFiniteOutputReceiptCode outputCount.val where
  toFun code := ⟨code.outputCount, code.receipt⟩
  invFun code := { outputCount := code.1, receipt := code.2 }
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance :
    Fintype BoundedSerialBoundaryRebaseFiniteOutputLetterCode :=
  Fintype.ofEquiv _
    boundedSerialBoundaryRebaseFiniteOutputLetterCodeEquiv.symm

/-- Decode the complete successor profile from one graph-free finite receipt.
The face cap is bounded by five by construction of the local-cap decoder. -/
noncomputable def BoundedSerialBoundaryRebaseFiniteOutputLetterCode.outputProfile
    (code : BoundedSerialBoundaryRebaseFiniteOutputLetterCode) :
    BoundedCorridorCutProfile 2 0 4 := by
  classical
  exact
    { faceFragmentCount := code.outputCount
      profile :=
        { edgeColor := code.receipt.outputEdgeColor
          strandConnected := fun pair left right =>
            match left, right with
            | .inl left, .inl right =>
                decide (code.receipt.strandConnected pair left right)
            | .inr terminal, _ => Fin.elim0 terminal
            | _, .inr terminal => Fin.elim0 terminal
          faceContinues := code.receipt.face.faceContinues
          fragmentContainsPort := fun fragment port =>
            match port with
            | .inl step =>
                decide (code.receipt.face.fragmentContainsPort fragment step)
            | .inr terminal => Fin.elim0 terminal
          faceLengthCap := fun fragment =>
            ⟨code.receipt.face.faceLengthCap fragment,
              Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ } }

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseFiniteOutputDecoderEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Every literal source rebase supplies one finite graph-free letter whose
decoded profile is exactly the successor serial input profile. -/
theorem exists_finiteOutputLetter_outputProfile_eq_sourceCorridorSerialInput_next
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
    ∃ code : BoundedSerialBoundaryRebaseFiniteOutputLetterCode,
      code.outputProfile =
        sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
          htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) color
            hcolor := by
  classical
  let output := sourceCorridorSerialInputBoundedProfileAt realization hcubic
    hrotation htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
      color hcolor
  let code : BoundedSerialBoundaryRebaseFiniteOutputLetterCode :=
    { outputCount := output.faceFragmentCount
      receipt :=
        sourceCorridorSerialBoundaryRebaseFiniteOutputReceiptCodeAt realization
          hcubic hrotation htwoSided hunique offset hnext color hcolor }
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
      realization hcubic hrotation htwoSided hunique offset hnext color hcolor
        step
  · funext pair left right
    rcases left with left | terminal
    · rcases right with right | terminal
      · apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq, code, output]
        exact
          (sourceCorridorSerialBoundaryRebaseFiniteOutputReceiptCodeAt_strandConnected
            realization hcubic hrotation htwoSided hunique offset hnext color
              hcolor pair left right).symm
      · exact Fin.elim0 terminal
    · exact Fin.elim0 terminal
  · funext left right
    exact
      sourceCorridorSerialBoundaryRebaseFiniteOutputReceiptCodeAt_faceContinues
        realization hcubic hrotation htwoSided hunique offset hnext color hcolor
          left right
  · funext fragment port
    rcases port with step | terminal
    · apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, code, output]
      exact
        sourceCorridorSerialBoundaryRebaseFiniteOutputReceiptCodeAt_fragmentContainsPort
          realization hcubic hrotation htwoSided hunique offset hnext color
            hcolor fragment step
    · exact Fin.elim0 terminal
  · funext fragment
    apply Fin.ext
    exact
      sourceCorridorSerialBoundaryRebaseFiniteOutputReceiptCodeAt_faceLengthCap
        realization hcubic hrotation htwoSided hunique offset hnext color hcolor
          fragment

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
