import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorFiniteOneCellSupport

/-!
# Deterministic decoder for one literal source Cell receipt

The terminal-aware one-Cell receipt already gives a graph-free relation on
the exact source coordinates: an incoming cumulative profile, the full local
Cell profile, the literal six-cycle placement, and the three-role facial
attachment table.  This file packages those finite data as a letter and
decodes the complete outgoing five-coordinate profile.

Every joint receipt is decoded by one such letter.  Consequently every
literal Tait-coloured source Cell is represented by the decoder.  The result
does not quotient heterogeneous Cells by their coarse orientation, compose
the separate boundary-rebase letter, measure a reachable closure, or derive
`V₀`.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfile
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24WindingClassification

/-- A finite terminal-aware one-Cell letter.  The dependent input fragment
count is stored with the letter, while the output has the proved three
semantic face roles. -/
structure LocalLayerFiniteOneCellLetterCode where
  inputCount : Fin 4
  cellProfile : CorridorCutProfile 6 0 0
  geometry : LocalLayerFiniteConnectivityGeometryCode
  roleIndex : LocalLayerRightFaceRole ≃ Fin 3
  faceUpdate : LocalLayerFiniteFaceUpdateCode inputCount.val

noncomputable instance : DecidableEq LocalLayerFiniteOneCellLetterCode :=
  Classical.decEq _

private def localLayerFiniteOneCellLetterCodeEquiv :
    LocalLayerFiniteOneCellLetterCode ≃
      Σ inputCount : Fin 4,
        CorridorCutProfile 6 0 0 ×
          LocalLayerFiniteConnectivityGeometryCode ×
          (LocalLayerRightFaceRole ≃ Fin 3) ×
          LocalLayerFiniteFaceUpdateCode inputCount.val where
  toFun code :=
    ⟨code.inputCount, code.cellProfile, code.geometry, code.roleIndex,
      code.faceUpdate⟩
  invFun code :=
    { inputCount := code.1
      cellProfile := code.2.1
      geometry := code.2.2.1
      roleIndex := code.2.2.2.1
      faceUpdate := code.2.2.2.2 }
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : Fintype LocalLayerFiniteOneCellLetterCode :=
  Fintype.ofEquiv _ localLayerFiniteOneCellLetterCodeEquiv.symm

/-- Reindex the incoming capped lengths after the decoder checks its stored
dependent fragment count. -/
def LocalLayerFiniteOneCellLetterCode.inputFaceLengthCap
    (code : LocalLayerFiniteOneCellLetterCode)
    (input : BoundedCorridorCutProfile 2 1 3)
    (hcount : input.faceFragmentCount.val = code.inputCount.val) :
    Fin code.inputCount.val → Fin 6 :=
  fun fragment =>
    input.profile.faceLengthCap (Fin.cast hcount.symm fragment)

/-- Compute one outgoing tracked-connectivity bit from the stable eight-edge
carrier of the literal Cell. -/
noncomputable def LocalLayerFiniteOneCellLetterCode.outputStrandConnected
    (code : LocalLayerFiniteOneCellLetterCode)
    (input : BoundedCorridorCutProfile 2 1 3)
    (pair : TrackedColorPair) (first second : Fin 2) : Bool := by
  classical
  exact decide
    (IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (code.cellProfile.edgeColor (code.geometry.outgoing first)).toColor ∧
      IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (code.cellProfile.edgeColor (code.geometry.outgoing second)).toColor ∧
      Relation.ReflTransGen
        (localLayerFiniteConnectivityStep
          (widenFaceFragmentBoundThreeToFour input)
          code.cellProfile code.geometry pair)
        (code.geometry.outgoingPort first)
        (code.geometry.outgoingPort second))

/-- Decode all five outgoing profile coordinates from one count-compatible
terminal-aware letter. -/
noncomputable def LocalLayerFiniteOneCellLetterCode.outputProfile
    (code : LocalLayerFiniteOneCellLetterCode)
    (input : BoundedCorridorCutProfile 2 1 3)
    (hcount : input.faceFragmentCount.val = code.inputCount.val) :
    BoundedCorridorCutProfile 2 0 3 where
  faceFragmentCount := ⟨3, by omega⟩
  profile :=
    { edgeColor := fun step =>
        code.cellProfile.edgeColor (code.geometry.outgoing step)
      strandConnected := fun pair left right =>
        match left, right with
        | .inl first, .inl second =>
            code.outputStrandConnected input pair first second
        | .inr terminal, _ => Fin.elim0 terminal
        | _, .inr terminal => Fin.elim0 terminal
      faceContinues := fun left right =>
        decide (code.roleIndex.symm left = code.roleIndex.symm right)
      fragmentContainsPort := fun fragment port =>
        match port with
        | .inl step =>
            decide ((code.roleIndex.symm fragment).ContainsPort step)
      faceLengthCap := fun fragment =>
        let role := code.roleIndex.symm fragment
        ⟨(code.faceUpdate role).updatedCap
            (code.inputFaceLengthCap input hcount) role,
          Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ }

/-- Apply a one-Cell letter when its stored input fragment count agrees with
the incoming profile. -/
noncomputable def LocalLayerFiniteOneCellLetterCode.decode
    (code : LocalLayerFiniteOneCellLetterCode)
    (input : BoundedCorridorCutProfile 2 1 3) :
    Option (BoundedCorridorCutProfile 2 0 3) :=
  if hcount : input.faceFragmentCount.val = code.inputCount.val then
    some (code.outputProfile input hcount)
  else
    none

/-- Executable graph-free support generated by the finite one-Cell letters. -/
def LocalLayerFiniteOneCellDecoderStep
    (input : BoundedCorridorCutProfile 2 1 3)
    (output : BoundedCorridorCutProfile 2 0 3) : Prop :=
  ∃ code : LocalLayerFiniteOneCellLetterCode,
    code.decode input = some output

/-- Every complete terminal-aware receipt is accepted by the deterministic
one-Cell decoder.  This is the source-sound direction needed before the
decoder can safely generate an over-approximate reachable closure. -/
theorem exists_letter_decode_eq_some_of_receipt
    {input : BoundedCorridorCutProfile 2 1 3}
    {output : BoundedCorridorCutProfile 2 0 3}
    (hreceipt : LocalLayerFiniteOneCellReceiptThree input output) :
    ∃ code : LocalLayerFiniteOneCellLetterCode,
      code.decode input = some output := by
  classical
  rcases output with ⟨⟨outputCount, houtputCountBound⟩, outputProfile⟩
  rcases hreceipt with
    ⟨receipt, houtputCount, hedge, hconnectivity, hface, hport, hcap⟩
  change outputCount = 3 at houtputCount
  subst outputCount
  let code : LocalLayerFiniteOneCellLetterCode :=
    { inputCount := input.faceFragmentCount
      cellProfile := receipt.cellProfile
      geometry := receipt.geometry
      roleIndex := receipt.roleIndex
      faceUpdate := receipt.faceUpdate }
  refine ⟨code, ?_⟩
  rw [LocalLayerFiniteOneCellLetterCode.decode,
    dif_pos (by simp [code])]
  apply congrArg some
  simp only [code, LocalLayerFiniteOneCellLetterCode.outputProfile]
  rw [BoundedCorridorCutProfile.mk.injEq]
  refine ⟨rfl, ?_⟩
  apply heq_of_eq
  rw [CorridorCutProfile.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext step
    exact (hedge step).symm
  · funext pair left right
    rcases left with left | terminal
    · rcases right with right | terminal
      · change code.outputStrandConnected input pair left right =
          outputProfile.strandConnected pair (.inl left) (.inl right)
        apply Bool.eq_iff_iff.mpr
        simp only [LocalLayerFiniteOneCellLetterCode.outputStrandConnected,
          decide_eq_true_eq, code]
        rw [← hedge left, ← hedge right]
        exact (hconnectivity pair left right).symm
      · exact Fin.elim0 terminal
    · exact Fin.elim0 terminal
  · funext left right
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, code]
    have hrole := hface (receipt.roleIndex.symm left)
      (receipt.roleIndex.symm right)
    rw [receipt.roleIndex.apply_symm_apply,
      receipt.roleIndex.apply_symm_apply] at hrole
    convert hrole.symm using 1 <;> rfl
  · funext fragment port
    rcases port with step | terminal
    · apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, code]
      have hcontains := hport (receipt.roleIndex.symm fragment) step
      rw [receipt.roleIndex.apply_symm_apply] at hcontains
      convert hcontains.symm using 1 <;> rfl
    · exact Fin.elim0 terminal
  · funext fragment
    apply Fin.ext
    change (receipt.faceUpdate (receipt.roleIndex.symm fragment)).updatedCap
        input.profile.faceLengthCap (receipt.roleIndex.symm fragment) =
      (outputProfile.faceLengthCap fragment).val
    have hlength := hcap (receipt.roleIndex.symm fragment)
    rw [receipt.roleIndex.apply_symm_apply] at hlength
    convert hlength.symm using 1 <;> rfl

/-- The profile computed by a count-compatible letter carries the receipt
from which that letter was decoded. -/
theorem receipt_outputProfile
    (code : LocalLayerFiniteOneCellLetterCode)
    (input : BoundedCorridorCutProfile 2 1 3)
    (hcount : input.faceFragmentCount.val = code.inputCount.val) :
    LocalLayerFiniteOneCellReceiptThree input
      (code.outputProfile input hcount) := by
  classical
  rcases input with ⟨inputCount, inputProfile⟩
  rcases code with
    ⟨codeInputCount, cellProfile, geometry, roleIndex, faceUpdate⟩
  have hcountFin : inputCount = codeInputCount := Fin.ext hcount
  subst codeInputCount
  have hcount_rfl : hcount = rfl := Subsingleton.elim _ _
  rw [hcount_rfl]
  let letter : LocalLayerFiniteOneCellLetterCode :=
    ⟨inputCount, cellProfile, geometry, roleIndex, faceUpdate⟩
  let receipt : LocalLayerFiniteOneCellCode
      (widenFaceFragmentBoundThreeToFour ⟨inputCount, inputProfile⟩)
      (widenFaceFragmentBoundThreeToFour
        (letter.outputProfile ⟨inputCount, inputProfile⟩ rfl)) :=
    { cellProfile := cellProfile
      geometry := geometry
      roleIndex := roleIndex
      faceUpdate := faceUpdate }
  refine ⟨receipt, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro step
    rfl
  · intro pair first second
    simp [receipt, widenFaceFragmentBoundThreeToFour,
      LocalLayerFiniteOneCellLetterCode.outputProfile,
      LocalLayerFiniteOneCellLetterCode.outputStrandConnected]
  · intro left right
    simp [receipt, widenFaceFragmentBoundThreeToFour,
      LocalLayerFiniteOneCellLetterCode.outputProfile]
  · intro role step
    simp only [receipt, widenFaceFragmentBoundThreeToFour,
      LocalLayerFiniteOneCellLetterCode.outputProfile, decide_eq_true_eq]
    have hrole : roleIndex.symm (roleIndex role) = role :=
      roleIndex.symm_apply_apply role
    exact ⟨fun h => Eq.mp
        (congrArg (fun current => current.ContainsPort step) hrole) h,
      fun h => Eq.mpr
        (congrArg (fun current => current.ContainsPort step) hrole) h⟩
  · intro role
    simp only [receipt, widenFaceFragmentBoundThreeToFour,
      LocalLayerFiniteOneCellLetterCode.outputProfile]
    have hrole : roleIndex.symm (roleIndex role) = role :=
      roleIndex.symm_apply_apply role
    let currentLetter : LocalLayerFiniteOneCellLetterCode :=
      ⟨inputCount, cellProfile, geometry, roleIndex, faceUpdate⟩
    have hinputCap :
        currentLetter.inputFaceLengthCap
            ⟨inputCount, inputProfile⟩ rfl =
          inputProfile.faceLengthCap := by
      funext fragment
      rfl
    let finalCap := fun current : LocalLayerRightFaceRole =>
      (faceUpdate current).updatedCap inputProfile.faceLengthCap current
    calc
      (faceUpdate (roleIndex.symm (roleIndex role))).updatedCap
          (currentLetter.inputFaceLengthCap
            ⟨inputCount, inputProfile⟩ rfl)
          (roleIndex.symm (roleIndex role)) =
        finalCap (roleIndex.symm (roleIndex role)) := by rw [hinputCap]
      _ = finalCap role := congrArg finalCap hrole

/-- Conversely, every successful decoder application satisfies the complete
terminal-aware receipt relation.  Thus the deterministic decoder neither
adds nor loses transitions relative to the declared finite receipt semantics. -/
theorem receipt_of_exists_letter_decode_eq_some
    {input : BoundedCorridorCutProfile 2 1 3}
    {output : BoundedCorridorCutProfile 2 0 3}
    (hdecode : LocalLayerFiniteOneCellDecoderStep input output) :
    LocalLayerFiniteOneCellReceiptThree input output := by
  classical
  rcases hdecode with ⟨code, hdecode⟩
  rw [LocalLayerFiniteOneCellLetterCode.decode] at hdecode
  split at hdecode
  next hcount =>
    simp only [Option.some.injEq] at hdecode
    subst output
    exact receipt_outputProfile code input hcount
  next hcount =>
    simp at hdecode

/-- Exact executable presentation of the finite terminal-aware receipt. -/
theorem localLayerFiniteOneCellDecoderStep_iff_receipt
    (input : BoundedCorridorCutProfile 2 1 3)
    (output : BoundedCorridorCutProfile 2 0 3) :
    LocalLayerFiniteOneCellDecoderStep input output ↔
      LocalLayerFiniteOneCellReceiptThree input output := by
  constructor
  · exact receipt_of_exists_letter_decode_eq_some
  · exact exists_letter_decode_eq_some_of_receipt

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance framedCorridorFiniteOneCellDecoderEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

namespace SourceCornerAlignedSlabInterface

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationBoundaryFaceCutProfile
open SimpleGraphDartRotation

variable {source : SourceTrail G}
  {embedded : source.AnnularEmbedding} {blockLength : Nat}
  {realization : BoundaryCleanCorridorRealization embedded blockLength}
  {htwoSided : OrbitFacesTwoSided
    embedded.cellulation.rotation.toRotationSystem}
  {hunique : PairwiseUniqueSharedInteriorEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
  {leftInterior : CorridorInterior blockLength}
  {hnext : leftInterior.center.val + 2 < blockLength}

/-- Every exact literal Tait-coloured source Cell is accepted by a finite
decoder letter.  The decoder remains heterogeneous in the literal Cell: this
theorem does not factor its semantics through the three coarse orientation
labels. -/
theorem exists_letter_decode_eq_some_of_literalSupport
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (input : BoundedCorridorCutProfile 2 1 3)
    (output : BoundedCorridorCutProfile 2 0 3)
    (hsupport : aligned.LiteralLocalLayerOneCellSupport input output) :
    ∃ code : LocalLayerFiniteOneCellLetterCode,
      code.decode input = some output :=
  exists_letter_decode_eq_some_of_receipt
    (aligned.localLayerFiniteOneCellReceipt_of_literalSupport
      hcubic hrotation input output hsupport)

/-- Relation form of source soundness for later reachable-closure induction. -/
theorem decoderStep_of_literalSupport
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (input : BoundedCorridorCutProfile 2 1 3)
    (output : BoundedCorridorCutProfile 2 0 3)
    (hsupport : aligned.LiteralLocalLayerOneCellSupport input output) :
    LocalLayerFiniteOneCellDecoderStep input output :=
  aligned.exists_letter_decode_eq_some_of_literalSupport
    hcubic hrotation input output hsupport

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
