import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSourceOutgoingProfileCompression
import Mettapedia.GraphTheory.FourColor.GoertzelV24WidthTwoPortIncidenceCodec

/-!
# Losslessness of the source-shaped outgoing profile code

The compact outgoing ABI stores only the moving strand state, the order of
the three fixed face roles, and their capped lengths.  This file reconstructs
the omitted face-equivalence and port-incidence coordinates and proves that a
joint literal one-Cell receipt decodes back to the complete five-coordinate
profile.

Thus equality of compact codes implies equality of the complete outgoing
profiles.  The `18000`-element carrier is now safe for a source-specific
pigeonhole argument; this file does not yet identify the cumulative-prefix
word with the outgoing word.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfile
open GoertzelV24WidthTwoPortIncidenceCodec
open GoertzelV24WidthTwoPortIncidenceCompression
open SourceTrail.AnnularEmbedding.SourceCornerAlignedSlabInterface

/-- Boolean form of the fixed incidence of one stable outgoing face role. -/
noncomputable def sourceOutgoingRolePortRow
    (role : LocalLayerRightFaceRole) (step : Fin 2) : Bool :=
  decide (role.ContainsPort step)

/-- Reconstruct the complete raw outgoing profile at a stored dependent count
proved equal to three.  Keeping the original `Fin` index makes the receipt
equations definitionally aligned. -/
noncomputable def decodeSourceOutgoingProfileAt
    (count : Fin 4) (hcount : count.val = 3)
    (code : SourceOutgoingProfileCode) :
    BoundedCorridorCutProfile 2 0 3 where
  faceFragmentCount := count
  profile := {
    edgeColor := code.strand.1.1
    strandConnected := decodeStrandConnected code.strand
    faceContinues := fun left right =>
      let leftRole := code.roleOrder
        (Equiv.cast (congrArg Fin hcount) left)
      let rightRole := code.roleOrder
        (Equiv.cast (congrArg Fin hcount) right)
      decide (leftRole = rightRole)
    fragmentContainsPort := fun fragment port =>
      let role := code.roleOrder
        (Equiv.cast (congrArg Fin hcount) fragment)
      match port with
      | .inl step =>
          sourceOutgoingRolePortRow role step
    faceLengthCap := fun fragment =>
      let role := code.roleOrder
        (Equiv.cast (congrArg Fin hcount) fragment)
      (code.faceLengthCap role).1
  }

/-- Canonical count-three decoder. -/
noncomputable def decodeSourceOutgoingProfile
    (code : SourceOutgoingProfileCode) :
    BoundedCorridorCutProfile 2 0 3 :=
  decodeSourceOutgoingProfileAt ⟨3, by omega⟩ rfl code

/-- The stored-count decoder agrees with the canonical count-three decoder.
The equality proof carried by the dependent count is computationally
irrelevant. -/
theorem decodeSourceOutgoingProfileAt_eq
    (count : Fin 4) (hcount : count.val = 3)
    (code : SourceOutgoingProfileCode) :
    decodeSourceOutgoingProfileAt count hcount code =
      decodeSourceOutgoingProfile code := by
  fin_cases count <;> norm_num at hcount
  rfl

noncomputable section

/-- Decoding the code extracted from an explicit joint witness recovers the
complete outgoing profile.  Stating the core round trip at witness level
avoids making it depend on the proof term selected from an existential
receipt. -/
theorem decode_sourceOutgoingProfileCodeOfWitness
    (incoming : BoundedCorridorCutProfile 2 1 3)
    (output : BoundedCorridorCutProfile 2 0 3)
    (semantic : BoundedIsPortIncidenceSemantic output)
    (code : LocalLayerFiniteOneCellCode
      (widenFaceFragmentBoundThreeToFour incoming)
      (widenFaceFragmentBoundThreeToFour output))
    (hcount : output.faceFragmentCount.val = 3)
    (hface : ∀ left right : LocalLayerRightFaceRole,
      (widenFaceFragmentBoundThreeToFour output).profile.faceContinues
          (code.roleIndex left) (code.roleIndex right) = true ↔
        left = right)
    (hport : ∀ (role : LocalLayerRightFaceRole) (step : Fin 2),
      (widenFaceFragmentBoundThreeToFour output).profile.fragmentContainsPort
          (code.roleIndex role) (.inl step) = true ↔
        role.ContainsPort step) :
    decodeSourceOutgoingProfile
        (sourceOutgoingProfileCodeOfWitness
          incoming output semantic code hcount) =
      output := by
  rcases output with ⟨count, outputProfile⟩
  have hat :
      decodeSourceOutgoingProfileAt count hcount
          (sourceOutgoingProfileCodeOfWitness
            incoming ⟨count, outputProfile⟩ semantic code hcount) =
        ⟨count, outputProfile⟩ := by
    rw [BoundedCorridorCutProfile.mk.injEq]
    refine ⟨rfl, ?_⟩
    apply heq_of_eq
    have hdecoded := decodePortIncidence_compressPortIncidence
      outputProfile semantic
    let e : Fin count.val ≃ Fin 3 := Equiv.cast (congrArg Fin hcount)
    have hroleOrderAt (fragment : Fin count.val) :
        (sourceOutgoingProfileCodeOfWitness incoming
              ⟨count, outputProfile⟩ semantic code hcount).roleOrder
            (e fragment) =
          code.roleIndex.symm fragment := by
      change code.roleIndex.symm (e.symm (e fragment)) =
        code.roleIndex.symm fragment
      rw [e.symm_apply_apply]
    unfold decodeSourceOutgoingProfileAt
    rw [CorridorCutProfile.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [sourceOutgoingProfileCodeOfWitness,
        compressPortIncidenceBounded, decodePortIncidence] using
        congrArg CorridorCutProfile.edgeColor hdecoded
    · simpa only [sourceOutgoingProfileCodeOfWitness,
        compressPortIncidenceBounded, decodePortIncidence] using
        congrArg CorridorCutProfile.strandConnected hdecoded
    · funext left right
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hsource
        have hrole :
            code.roleIndex.symm left =
              code.roleIndex.symm right := by
          rw [hroleOrderAt left, hroleOrderAt right] at hsource
          simpa using hsource
        have hout := (hface
          (code.roleIndex.symm left)
          (code.roleIndex.symm right)).2 hrole
        change outputProfile.faceContinues
          (code.roleIndex (code.roleIndex.symm left))
          (code.roleIndex (code.roleIndex.symm right)) = true at hout
        rw [code.roleIndex.apply_symm_apply,
          code.roleIndex.apply_symm_apply] at hout
        exact hout
      · intro hactual
        have hrole :
            code.roleIndex.symm left =
              code.roleIndex.symm right :=
          (hface
            (code.roleIndex.symm left)
            (code.roleIndex.symm right)).1
              (by
                change outputProfile.faceContinues
                  (code.roleIndex (code.roleIndex.symm left))
                  (code.roleIndex (code.roleIndex.symm right)) = true
                rw [code.roleIndex.apply_symm_apply,
                  code.roleIndex.apply_symm_apply]
                exact hactual)
        rw [hroleOrderAt left, hroleOrderAt right]
        simpa using hrole
    · funext fragment port
      rcases port with step | terminal
      · apply Bool.eq_iff_iff.mpr
        constructor
        · intro hsource
          have hrole :
              (code.roleIndex.symm fragment).ContainsPort step := by
            rw [hroleOrderAt fragment] at hsource
            simpa [sourceOutgoingRolePortRow] using hsource
          have hout :=
            (hport (code.roleIndex.symm fragment) step).2 hrole
          change outputProfile.fragmentContainsPort
            (code.roleIndex (code.roleIndex.symm fragment))
            (.inl step) = true at hout
          rw [code.roleIndex.apply_symm_apply] at hout
          exact hout
        · intro hactual
          have hrole :
              (code.roleIndex.symm fragment).ContainsPort step :=
            (hport (code.roleIndex.symm fragment) step).1
              (by
                change outputProfile.fragmentContainsPort
                  (code.roleIndex (code.roleIndex.symm fragment))
                  (.inl step) = true
                rw [code.roleIndex.apply_symm_apply]
                exact hactual)
          rw [hroleOrderAt fragment]
          simpa [sourceOutgoingRolePortRow] using hrole
      · exact Fin.elim0 terminal
    · funext fragment
      rw [hroleOrderAt fragment]
      simpa only [sourceOutgoingProfileCodeOfWitness,
        compressPortIncidenceBounded, decodePortIncidence,
        code.roleIndex.apply_symm_apply] using
        congrFun (congrArg CorridorCutProfile.faceLengthCap hdecoded) fragment
  calc
    decodeSourceOutgoingProfile
        (sourceOutgoingProfileCodeOfWitness
          incoming ⟨count, outputProfile⟩ semantic code hcount) =
      decodeSourceOutgoingProfileAt count hcount
        (sourceOutgoingProfileCodeOfWitness
          incoming ⟨count, outputProfile⟩ semantic code hcount) := by
        exact (decodeSourceOutgoingProfileAt_eq count hcount _).symm
    _ = ⟨count, outputProfile⟩ := hat

/-- Decoding the code extracted from a joint receipt recovers the complete
outgoing profile.  In particular, the omitted matrices really are forced by
the proved literal Cell geometry. -/
theorem decode_sourceOutgoingProfileCodeOfReceipt
    (incoming : BoundedCorridorCutProfile 2 1 3)
    (output : BoundedCorridorCutProfile 2 0 3)
    (semantic : BoundedIsPortIncidenceSemantic output)
    (receipt : LocalLayerFiniteOneCellReceiptThree incoming output) :
    decodeSourceOutgoingProfile
        (sourceOutgoingProfileCodeOfReceipt
          incoming output semantic receipt) =
      output := by
  let code := Classical.choose receipt
  have facts := Classical.choose_spec receipt
  simpa only [sourceOutgoingProfileCodeOfReceipt] using
    decode_sourceOutgoingProfileCodeOfWitness incoming output semantic
      code facts.1 facts.2.2.2.1 facts.2.2.2.2.1

/-- The compact source-shaped code is lossless on complete profiles carrying
a joint literal one-Cell receipt. -/
theorem sourceOutgoingProfileCodeOfReceipt_injective
    {leftIncoming rightIncoming : BoundedCorridorCutProfile 2 1 3}
    {leftOutput rightOutput : BoundedCorridorCutProfile 2 0 3}
    (leftSemantic : BoundedIsPortIncidenceSemantic leftOutput)
    (rightSemantic : BoundedIsPortIncidenceSemantic rightOutput)
    (leftReceipt : LocalLayerFiniteOneCellReceiptThree
      leftIncoming leftOutput)
    (rightReceipt : LocalLayerFiniteOneCellReceiptThree
      rightIncoming rightOutput)
    (heq :
      SourceTrail.AnnularEmbedding.SourceCornerAlignedSlabInterface.sourceOutgoingProfileCodeOfReceipt
          leftIncoming leftOutput leftSemantic leftReceipt =
        SourceTrail.AnnularEmbedding.SourceCornerAlignedSlabInterface.sourceOutgoingProfileCodeOfReceipt
          rightIncoming rightOutput rightSemantic rightReceipt) :
    leftOutput = rightOutput := by
  rw [← decode_sourceOutgoingProfileCodeOfReceipt
      leftIncoming leftOutput leftSemantic leftReceipt,
    ← decode_sourceOutgoingProfileCodeOfReceipt
      rightIncoming rightOutput rightSemantic rightReceipt,
    heq]

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
