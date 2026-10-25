import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllResultMethodEvidence

/-! # Independent method replay and complete Vector result identity programs -/
set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllResultComparison.Named.Assembly
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Declaration
open NativeVectorAllTypedMaps (Direction motiveTypeAt source)

local instance : DecidableRel rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel rules.cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))
local instance : DecidableRel rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def motiveEvidence : Direction → FormationSensitiveElaboration.Submission Tower.Head decoder.Code 4
  | .forward => Evidence.forwardMotiveSubmission
  | .backward => Evidence.backwardMotiveSubmission

def nilEvidence : Direction → FormationSensitiveElaboration.Submission Tower.Head decoder.Code 4
  | .forward => Evidence.forwardNilSubmission
  | .backward => Evidence.backwardNilSubmission

def consEvidence : Direction → FormationSensitiveElaboration.Submission Tower.Head decoder.Code 4
  | .forward => Evidence.forwardConsSubmission
  | .backward => Evidence.backwardConsSubmission

def familyEvidence : Direction → FormationSensitiveElaboration.Submission Tower.Head decoder.Code 4
  | .forward => Evidence.forwardFamilySubmission
  | .backward => Evidence.backwardFamilySubmission

set_option maxRecDepth 8192 in
theorem motive_replayed (direction : Direction) : FormationSensitiveElaboration.replay rules decoder ambient
    (currentMotive direction) (motiveTypeAt (.var 3)) (motiveEvidence direction) = true := by
  cases direction <;> decide +kernel

set_option maxRecDepth 8192 in
theorem nil_replayed (direction : Direction) : FormationSensitiveElaboration.replay rules decoder ambient
    (Comparison.nilCase (.var 2)) (nilInterface direction) (nilEvidence direction) = true := by
  cases direction <;> decide +kernel

set_option maxRecDepth 8192 in
theorem cons_replayed (direction : Direction) : FormationSensitiveElaboration.replay rules decoder ambient
    (Comparison.consCase direction (.var 3) (.var 2)) (consInterface direction) (consEvidence direction) = true := by
  cases direction <;> decide +kernel

set_option maxRecDepth 8192 in
theorem family_replayed (direction : Direction) : FormationSensitiveElaboration.replay rules decoder ambient
    (goalFamily direction) (sortTm evidenceUpperLevel) (familyEvidence direction) = true := by
  cases direction <;> decide +kernel

theorem checked_programme (direction : Direction) : FormationSensitive.Judgment rules .nil
    (Comparison.programme direction) (Comparison.programmeType direction) :=
  programme_typed direction
    (FormationSensitiveElaboration.replay_sound rules decoder (motive_replayed direction))
    (FormationSensitiveElaboration.replay_sound rules decoder (nil_replayed direction))
    (FormationSensitiveElaboration.replay_sound rules decoder (cons_replayed direction))
    (FormationSensitiveElaboration.replay_sound rules decoder (family_replayed direction))

def inputContext (direction : Direction) := NativeVectorAllResultComparison.context (source direction)

theorem input_context_formed (direction : Direction) : FormationSensitive.ContextFormation rules (inputContext direction) := by
  cases direction
  · exact NativeVectorAllResultComparison.lower_context_formed.includeSignature Named.signature
  · exact NativeVectorAllResultComparison.upper_context_formed.includeSignature Named.signature

def neutralProof (direction : Direction) : Tower.Tm 5 :=
  TelescopeAbstraction.applyClosed (inputContext direction) ids (liftClosed (Comparison.programme direction))

theorem comparison_type_readback (direction : Direction) :
    TelescopeAbstraction.closeType (inputContext direction)
      (Comparison.goal direction (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)) =
      Comparison.programmeType direction := rfl

theorem neutral_identity (direction : Direction) : FormationSensitive.Judgment rules (inputContext direction)
    (neutralProof direction) (Comparison.goal direction (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)) := by
  have variableAssignment : FormationSensitive.CtxMor rules (inputContext direction) (inputContext direction) ids := by
    intro index
    simpa only [subst_ids, ids] using (FormationSensitive.Typing.var (R := rules) (Γ := inputContext direction) index)
  have functionTyped : FormationSensitive.Typing rules (inputContext direction)
      (liftClosed (Comparison.programme direction))
      (liftClosed (TelescopeAbstraction.closeType (inputContext direction)
        (Comparison.goal direction (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)))) := by
    rw [comparison_type_readback]
    exact FormationCheckedTelescopePrograms.liftClosed_typing (checked_programme direction).typing _
  exact ⟨input_context_formed direction, by
    simpa only [neutralProof, subst_ids] using FormationCheckedTelescopePrograms.apply_typed variableAssignment functionTyped⟩

theorem caller_identity (direction : Direction) {n : Nat} {target : Tower.Ctx n}
    (targetFormation : FormationSensitive.ContextFormation rules target)
    {sigma : Sub Tower.Head 5 n}
    (typed : FormationSensitive.CtxMor rules (inputContext direction) target sigma) :
    FormationSensitive.Judgment rules target (subst sigma (neutralProof direction))
      (subst sigma (Comparison.goal direction (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))) :=
  ⟨targetFormation, (neutral_identity direction).typing.substitute typed⟩

namespace Controls

theorem forward_programme : FormationSensitive.Judgment rules .nil
    (Comparison.programme .forward) (Comparison.programmeType .forward) :=
  programme_typed .forward
    (FormationSensitiveElaboration.replay_sound rules decoder (motive_replayed .forward))
    (FormationSensitiveElaboration.replay_sound rules decoder (nil_replayed .forward))
    (FormationSensitiveElaboration.replay_sound rules decoder (cons_replayed .forward))
    (FormationSensitiveElaboration.replay_sound rules decoder (family_replayed .forward))

theorem backward_programme : FormationSensitive.Judgment rules .nil
    (Comparison.programme .backward) (Comparison.programmeType .backward) :=
  programme_typed .backward
    (FormationSensitiveElaboration.replay_sound rules decoder (motive_replayed .backward))
    (FormationSensitiveElaboration.replay_sound rules decoder (nil_replayed .backward))
    (FormationSensitiveElaboration.replay_sound rules decoder (cons_replayed .backward))
    (FormationSensitiveElaboration.replay_sound rules decoder (family_replayed .backward))

set_option maxRecDepth 8192 in
/-- The forward certificate cannot certify the reversed evidence interface. -/
theorem exchanged_method_refused : FormationSensitiveElaboration.replay rules decoder ambient
    (Comparison.consCase .forward (.var 3) (.var 2)) (consInterface .backward)
    Evidence.forwardConsSubmission = false := by decide +kernel

def callerContext : Tower.Ctx 6 := .snoc (inputContext .forward) NativeNaturalVectorFamilies.natTm

theorem natural_type_typed : FormationSensitive.Typing rules (inputContext .forward)
    NativeNaturalVectorFamilies.natTm (sortTm Tower.zero) := by
  have closed := (PrimitiveBase.primitive_typed (actual := NativeNaturalVectorFamilies.natName)
    (by simp [PrimitiveBase.primitiveNames]) (declared := sortTm Tower.zero) rfl).typing.includeSignature Named.signature
  exact FormationCheckedTelescopePrograms.liftClosed_typing closed _

theorem caller_context_formed : FormationSensitive.ContextFormation rules callerContext :=
  .snoc (input_context_formed .forward) natural_type_typed (.sort _)

theorem caller_assignment : FormationSensitive.CtxMor rules (inputContext .forward) callerContext (renSub wk) := by
  intro index
  simpa only [subst_renSub, callerContext, Ctx.lookup_snoc_succ, renSub, wk] using
    (FormationSensitive.Typing.var (R := rules) (Γ := callerContext) index.succ)

theorem weakened_identity : FormationSensitive.Judgment rules callerContext
    (subst (renSub wk) (neutralProof .forward))
    (subst (renSub wk) (Comparison.goal .forward (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))) :=
  caller_identity .forward caller_context_formed caller_assignment

end Controls

#print axioms checked_programme
#print axioms neutral_identity
#print axioms caller_identity
#print axioms Controls.weakened_identity
#print axioms Controls.exchanged_method_refused
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllResultComparison.Named.Assembly
