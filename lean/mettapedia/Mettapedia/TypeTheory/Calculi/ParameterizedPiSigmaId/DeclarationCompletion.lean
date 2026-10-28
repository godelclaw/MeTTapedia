import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DeclarationAdmissionReplay
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TelescopeAbstraction

/-!
# Completing one submitted signature with its checked body

The signature and defining body are proposed together, before publication.
Their names must agree. The existing prefix checker then checks formation and
the actual body against the preceding library, with the new name still absent.
An opaque entry already published in that library is not silently overwritten.
This is the closed-body admission boundary; compilation of recursive equation
families and native revision storage remain separate consumers.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace Declaration

variable {Head : Type}

def complete? (signature body : DeclName × Tm Head 0) : Option (DeclName × Entry Head) :=
  if signature.1 = body.1 then some (signature.1, ⟨signature.2, some body.2⟩) else none

theorem complete?_eq_some_iff (signature body : DeclName × Tm Head 0) (entry : DeclName × Entry Head) :
    complete? signature body = some entry ↔
      signature.1 = body.1 ∧ entry = (signature.1, ⟨signature.2, some body.2⟩) := by
  simp only [complete?]
  split
  · rename_i same
    simp [same, eq_comm]
  · rename_i different
    simp [different]

section Checking

open DeclarationAdmissionReplay

variable (base : Rules Head) [DecidableEq Head] [DecidableRel base.headEq]
variable (decoder : StructuralConversionCode.RootDecoder base.computation)
variable [∀ h u, Decidable (base.headTyping h u)] [∀ h, Decidable (base.isUniverse h)]
variable [∀ u v w, Decidable (base.join u v w)] [∀ u v, Decidable (base.cumulative u v)]

def checkComplete (prior : List (DeclName × Entry Head))
    (signature body : DeclName × Tm Head 0) (certificate : Certificate Head decoder.Code) : Bool :=
  match complete? signature body with
  | none => false
  | some entry => check base decoder prior [entry] [certificate]

theorem checkComplete_admitted {prior : List (DeclName × Entry Head)}
    {signature body : DeclName × Tm Head 0} {certificate : Certificate Head decoder.Code}
    (accepted : checkComplete base decoder prior signature body certificate = true) :
    signature.1 = body.1 ∧
      Admitted base prior [(signature.1, ⟨signature.2, some body.2⟩)] := by
  cases assembled : complete? signature body with
  | none => simp [checkComplete, assembled] at accepted
  | some entry =>
      obtain ⟨same, shape⟩ := (complete?_eq_some_iff signature body entry).mp assembled
      refine ⟨same, ?_⟩
      rw [← shape]
      exact check_sound base decoder (by simpa only [checkComplete, assembled] using accepted)

/-- The defining body is checked before the proposed name is installed.
The theorem does not assume the desired typing judgment as a structure field. -/
theorem checkComplete_body_typed {prior : List (DeclName × Entry Head)}
    {signature body : DeclName × Tm Head 0} {certificate : Certificate Head decoder.Code}
    (accepted : checkComplete base decoder prior signature body certificate = true) :
    (extendRules base (Signature.ofList prior)).constantType signature.1 = none ∧
      FormationSensitive.Typing (extendRules base (Signature.ofList prior)) .nil body.2 signature.2 := by
  obtain ⟨_, admitted⟩ := checkComplete_admitted base decoder accepted
  cases admitted with
  | cons fresh _ _ typed _ => exact ⟨fresh, typed _ rfl⟩

/-- Checked completion retains its body typing in the published library. -/
theorem checkComplete_body_typed_after {prior : List (DeclName × Entry Head)}
    {signature body : DeclName × Tm Head 0} {certificate : Certificate Head decoder.Code}
    (accepted : checkComplete base decoder prior signature body certificate = true) :
    FormationSensitive.Typing
      (extendRules base (Signature.ofList (prior ++ [(signature.1, ⟨signature.2, some body.2⟩)])))
      .nil body.2 signature.2 := by
  obtain ⟨_, admitted⟩ := checkComplete_admitted base decoder accepted
  obtain ⟨_, _, _, _, typed⟩ := admitted.member_typed base
    (item := (signature.1, ⟨signature.2, some body.2⟩)) (by simp)
  exact typed _ rfl

/-- The published type and the selected computational body come from the
same completed entry, with no earlier declaration shadowing it. -/
theorem checkComplete_selected {prior : List (DeclName × Entry Head)}
    {signature body : DeclName × Tm Head 0} {certificate : Certificate Head decoder.Code}
    (accepted : checkComplete base decoder prior signature body certificate = true) :
    let library := Signature.ofList (prior ++ [(signature.1, ⟨signature.2, some body.2⟩)])
    (extendRules base library).constantType signature.1 = some signature.2 ∧
      library.valueOf? signature.1 = some body.2 := by
  have fresh := (checkComplete_body_typed base decoder accepted).1
  have baseEmpty : base.constantType signature.1 = none := by
    cases known : base.constantType signature.1 with
    | none => rfl
    | some type => simp [extendRules, combinedType, known] at fresh
  have typeEmpty : (Signature.ofList prior).typeOf? signature.1 = none := by
    simpa only [extendRules, combinedType, baseEmpty] using fresh
  have entriesEmpty : (Signature.ofList prior).entries signature.1 = none := by
    cases known : (Signature.ofList prior).entries signature.1 with
    | none => rfl
    | some entry => simp [Signature.typeOf?, known] at typeEmpty
  have selected :
      (Signature.ofList (prior ++ [(signature.1, ⟨signature.2, some body.2⟩)])).entries signature.1 =
        some ⟨signature.2, some body.2⟩ := by
    rw [Signature.entries_ofList_append, entriesEmpty]
    simp [Signature.ofList, Signature.insert]
  simp only [extendRules, combinedType, baseEmpty, Signature.typeOf?, Signature.valueOf?, selected]
  exact ⟨rfl, rfl⟩

/-- Actual delta computation reads that same selected body. -/
theorem checkComplete_computes {prior : List (DeclName × Entry Head)}
    {signature body : DeclName × Tm Head 0} {certificate : Certificate Head decoder.Code}
    (accepted : checkComplete base decoder prior signature body certificate = true) :
    let library := Signature.ofList (prior ++ [(signature.1, ⟨signature.2, some body.2⟩)])
    (extendRules base library).computation.step (.const signature.1) body.2 := by
  have selected := (checkComplete_selected base decoder accepted).2
  simpa only [extendRules, rootComputation, TelescopeAbstraction.liftClosed_zero] using
    (RootStep.delta (base := base) (n := 0) selected)

theorem mismatched_signature_refused (prior : List (DeclName × Entry Head))
    (signature body : DeclName × Tm Head 0) (certificate : Certificate Head decoder.Code)
    (different : signature.1 ≠ body.1) :
    checkComplete base decoder prior signature body certificate = false := by
  simp [checkComplete, complete?, different]

theorem missing_body_evidence_refused (prior : List (DeclName × Entry Head))
    (signature body : DeclName × Tm Head 0) (certificate : Certificate Head decoder.Code)
    (missing : certificate.value? = none) :
    checkComplete base decoder prior signature body certificate = false := by
  by_cases same : signature.1 = body.1
  · simp [checkComplete, complete?, same, check, checkValue, missing]
  · simp [checkComplete, complete?, same]

/-- A raw annotation that has already become an authoritative constant is
not a pending declaration. Completing it requires an explicit revision route. -/
theorem published_signature_not_overwritten (prior : List (DeclName × Entry Head))
    (signature body : DeclName × Tm Head 0) (certificate : Certificate Head decoder.Code)
    (type : Tm Head 0)
    (known : (extendRules base (Signature.ofList prior)).constantType signature.1 = some type) :
    checkComplete base decoder prior signature body certificate = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have fresh := (checkComplete_body_typed base decoder accepted).1
  rw [known] at fresh
  cases fresh

/-- Formation and body derivations construct a finite certificate accepted
by this completion boundary. The body is proved in the preceding library. -/
theorem checkComplete_exists_of_typed (prior : List (DeclName × Entry Head))
    (signature body : DeclName × Tm Head 0) (same : signature.1 = body.1)
    (fresh : (extendRules base (Signature.ofList prior)).constantType signature.1 = none)
    (levelHead : Head) (isUniverse : base.isUniverse levelHead)
    (formed : FormationSensitive.Typing (extendRules base (Signature.ofList prior))
      .nil signature.2 (.head levelHead))
    (typed : FormationSensitive.Typing (extendRules base (Signature.ofList prior))
      .nil body.2 signature.2) :
    ∃ certificate, checkComplete base decoder prior signature body certificate = true := by
  obtain ⟨formation, formationChecked⟩ := checkTerm_complete base decoder prior formed
  obtain ⟨value, valueChecked⟩ := checkTerm_complete base decoder prior typed
  have assembled : complete? signature body = some (signature.1, ⟨signature.2, some body.2⟩) :=
    (complete?_eq_some_iff _ _ _).mpr ⟨same, rfl⟩
  refine ⟨⟨levelHead, formation, some value⟩, ?_⟩
  simp [checkComplete, assembled, check, fresh, isUniverse, formationChecked, checkValue, valueChecked]

end Checking

#print axioms checkComplete_exists_of_typed
#print axioms checkComplete_admitted
#print axioms checkComplete_body_typed
#print axioms checkComplete_body_typed_after
#print axioms checkComplete_selected
#print axioms checkComplete_computes
#print axioms published_signature_not_overwritten

end Declaration

namespace DeclarationConversionCode

variable {Head : Type} {BaseCode DeclaredCode : Nat → Type}

/-- Replaying a delta name reads the current body. A different body does
not validate the old endpoint pair, even when its type stayed unchanged. -/
theorem changed_delta_body_refuses_old_endpoints (signature : Declaration.Signature Head)
    (decodeBase : {n : Nat} → BaseCode n → Option (Tm Head n × Tm Head n))
    (decodeDeclared : {n : Nat} → DeclaredCode n → Option (Tm Head n × Tm Head n))
    (name : DeclName) (oldBody newBody : Tm Head 0)
    (selected : signature.valueOf? name = some newBody) (changed : newBody ≠ oldBody) :
    decode signature decodeBase decodeDeclared (.delta name : RootCode BaseCode DeclaredCode 0) ≠
      some (.const name, oldBody) := by
  simp [decode, selected, TelescopeAbstraction.liftClosed_zero, changed]

#print axioms changed_delta_body_refuses_old_endpoints

end DeclarationConversionCode
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
