import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DeclarationCompletion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationCheckedTelescopePrograms

/-!
# Checked calls of completed dependent definitions

A call receipt first unfolds the selected declaration, then applies the
existing telescope beta program. The root code stores the declaration name;
its decoder reads the current body. The beta portion retains the originally
submitted body and exact arguments. Typing and computation therefore meet at
the selected entry earned by the declaration-admission checker.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace Declaration

open StructuralConversionCode TelescopeAbstraction FormationCheckedTelescopePrograms

variable {Head : Type} {BaseCode DeclaredCode : Nat → Type} {n m : Nat}

def callCode (name : DeclName) (context : Ctx Head n) (arguments : Sub Head n m)
    (body : Tm Head n) : Code Head (DeclarationConversionCode.RootCode BaseCode DeclaredCode) m :=
  .trans (applyFunctionCode context arguments (.single (.root (.delta name))))
    (applicationCodeIn context arguments body)

theorem callCode_checked [DecidableEq Head]
    (headEq : Head → Head → Prop) [DecidableRel headEq]
    (signature : Signature Head)
    (baseDecode : {scope : Nat} → BaseCode scope → Option (Tm Head scope × Tm Head scope))
    (declaredDecode : {scope : Nat} → DeclaredCode scope → Option (Tm Head scope × Tm Head scope))
    (name : DeclName) (context : Ctx Head n) (arguments : Sub Head n m) (body : Tm Head n)
    (selected : signature.valueOf? name = some (closeTerm context body)) :
    (callCode name context arguments body).check headEq
      (DeclarationConversionCode.decode signature baseDecode declaredDecode)
      (applyClosed context arguments (.const name)) (subst arguments body) = true := by
  have delta : Code.check headEq
      (DeclarationConversionCode.decode signature baseDecode declaredDecode)
      (.single (.root (.delta name))) (.const name : Tm Head m)
      (liftClosed (closeTerm context body)) = true := by
    simp [Code.check, Code.decode, StepCode.decode, DeclarationConversionCode.decode, selected]
  exact Code.check_trans headEq _ (applyFunctionCode_checked headEq _ context arguments _ delta)
    (applicationCodeIn_checked headEq _ context arguments body)

/-- One declaration lookup and one beta step per telescope entry. This
does not count lookup cost, term copying or evaluator instructions. -/
theorem callCode_stepCount (name : DeclName) (context : Ctx Head n)
    (arguments : Sub Head n m) (body : Tm Head n) :
    (callCode (BaseCode := BaseCode) (DeclaredCode := DeclaredCode)
      name context arguments body).stepCount = n + 1 := by
  simp [callCode, Code.stepCount, applyFunctionCode_stepCount, applicationCodeIn_stepCount, Nat.add_comm]

theorem applyClosed_injective (context : Ctx Head n) (arguments : Sub Head n m) :
    Function.Injective (applyClosed context arguments) := by
  induction context with
  | nil => exact fun _ _ same => same
  | snoc prior domain ih =>
      intro first second same
      exact ih (fun index => arguments index.succ) (Tm.app.inj same).1

/-- Changing the selected body invalidates the old complete closed-call
receipt, even if the declaration's name and type have not changed. -/
theorem changed_body_refuses_call [DecidableEq Head]
    (headEq : Head → Head → Prop) [DecidableRel headEq]
    (signature : Signature Head)
    (baseDecode : {scope : Nat} → BaseCode scope → Option (Tm Head scope × Tm Head scope))
    (declaredDecode : {scope : Nat} → DeclaredCode scope → Option (Tm Head scope × Tm Head scope))
    (name : DeclName) (context : Ctx Head n) (arguments : Sub Head n 0) (body : Tm Head n)
    (replacement : Tm Head 0) (selected : signature.valueOf? name = some replacement)
    (changed : replacement ≠ closeTerm context body) :
    (callCode name context arguments body).check headEq
      (DeclarationConversionCode.decode signature baseDecode declaredDecode)
      (applyClosed context arguments (.const name)) (subst arguments body) = false := by
  let decode : {scope : Nat} → DeclarationConversionCode.RootCode BaseCode DeclaredCode scope →
      Option (Tm Head scope × Tm Head scope) :=
    DeclarationConversionCode.decode signature baseDecode declaredDecode
  have delta : Code.check headEq decode (.single (.root (.delta name)))
      (.const name : Tm Head 0) replacement = true := by
    simp [decode, Code.check, Code.decode, StepCode.decode, DeclarationConversionCode.decode,
      selected, liftClosed_zero]
  have unfolded := applyFunctionCode_checked headEq decode context arguments _ delta
  have beta := applicationCodeIn_checked headEq decode context arguments body
  have different : applyClosed context arguments replacement ≠
      applyClosed context arguments (liftClosed (closeTerm context body)) := by
    rw [liftClosed_zero]
    exact fun same => changed (applyClosed_injective context arguments same)
  have unfoldedRead : Code.decode headEq decode
      (applyFunctionCode context arguments (.single (.root (.delta name)))) =
      some (applyClosed context arguments (.const name), applyClosed context arguments replacement) :=
    of_decide_eq_true unfolded
  have betaRead : Code.decode headEq decode (applicationCodeIn context arguments body) =
      some (applyClosed context arguments (liftClosed (closeTerm context body)), subst arguments body) :=
    of_decide_eq_true beta
  change Code.check headEq decode (callCode name context arguments body) _ _ = false
  simp only [callCode, Code.check, Code.decode, unfoldedRead, betaRead,
    joinEndpoints, different, ↓reduceIte, reduceCtorEq, decide_false]

section Checking

open FormationSensitive
variable (base : Rules Head) [DecidableEq Head] [DecidableRel base.headEq]
variable (decoder : StructuralConversionCode.RootDecoder base.computation)
variable [∀ h u, Decidable (base.headTyping h u)] [∀ h, Decidable (base.isUniverse h)]
variable [∀ u v w, Decidable (base.join u v w)] [∀ u v, Decidable (base.cumulative u v)]

/-- Admission forms the declared function type and selects that same entry
for both the constant rule and unfolding. The caller supplies the independently
typed dependent argument assignment in the resulting declaration world. -/
theorem completed_call_typed (prior : List (DeclName × Entry Head)) (name : DeclName)
    (context : Ctx Head n) (body type : Tm Head n)
    (certificate : DeclarationAdmissionReplay.Certificate Head decoder.Code)
    (accepted : checkComplete base decoder prior (name, closeType context type)
      (name, closeTerm context body) certificate = true)
    (target : Ctx Head m) (arguments : Sub Head n m)
    (typed : FormationSensitive.CtxMor
      (extendRules base (Signature.ofList (prior ++ [(name, ⟨closeType context type,
        some (closeTerm context body)⟩)]))) context target arguments) :
    Typing (extendRules base (Signature.ofList (prior ++ [(name, ⟨closeType context type,
        some (closeTerm context body)⟩)]))) target
      (applyClosed context arguments (.const name)) (subst arguments type) := by
  obtain ⟨_, admitted⟩ := checkComplete_admitted base decoder accepted
  obtain ⟨_, level, isUniverse, formed, _⟩ := admitted.member_typed base
    (item := (name, ⟨closeType context type, some (closeTerm context body)⟩)) (by simp)
  have selected := (checkComplete_selected base decoder accepted).1
  exact apply_typed typed (.const selected formed isUniverse)

theorem completed_call_checked (prior : List (DeclName × Entry Head)) (name : DeclName)
    (context : Ctx Head n) (body type : Tm Head n)
    (certificate : DeclarationAdmissionReplay.Certificate Head decoder.Code)
    (accepted : checkComplete base decoder prior (name, closeType context type)
      (name, closeTerm context body) certificate = true) (arguments : Sub Head n m) :
    let entries := prior ++ [(name, ⟨closeType context type, some (closeTerm context body)⟩)]
    (callCode name context arguments body).check base.headEq
      (DeclarationConversionCode.ofList base decoder entries).decode
      (applyClosed context arguments (.const name)) (subst arguments body) = true := by
  exact callCode_checked base.headEq _ _ _ name context arguments body
    (checkComplete_selected base decoder accepted).2

end Checking

#print axioms callCode_checked
#print axioms changed_body_refuses_call
#print axioms completed_call_typed
#print axioms completed_call_checked

end Declaration
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
