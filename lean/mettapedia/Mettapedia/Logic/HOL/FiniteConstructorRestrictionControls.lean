import Mettapedia.Logic.HOL.FiniteConstructorGuardRestrictions
import Mettapedia.Logic.HOL.FiniteConstructorGuardControls

/-!
# Data restrictions separate valid payloads

A Boolean-field condition accepts one encoded tuple and refuses a changed
tuple that remains in the unrestricted constructor image. A false condition
has no admissible data, independently of the ambient payload type.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.FiniteConstructorEncoding.RestrictionControls

open Controls

def condition : ClosedTerm Constants (handlerType [.prop, .prop]) := .lam (.lam (.var (.vs .vz)))
def impossibleCondition : ClosedTerm Constants (handlerType [.prop, .prop]) := .lam (.lam .bot)

theorem first_accepted :
    (model.denote (restrictedGuard signature ⟨0, by decide⟩ condition
      (encode signature ⟨0, by decide⟩ fields)) values).down := by
  apply (restrictedGuard_denote model GuardControls.full signature ⟨0, by decide⟩ condition _ values).mpr
  exact ⟨denoteArguments model _ fields values, True.intro, generated_denotation⟩

theorem changed_still_encoded :
    (model.denote (validGuard signature (encode signature ⟨0, by decide⟩ changedFields)) values).down := by
  apply (validGuard_denote model GuardControls.full signature _ values).mpr
  exact ⟨⟨⟨0, by decide⟩, denoteArguments model _ changedFields values⟩,
    (encode_denote model signature ⟨0, by decide⟩ changedFields values).symm⟩

theorem changed_refused :
    ¬ (model.denote (restrictedGuard signature ⟨0, by decide⟩ condition
      (encode signature ⟨0, by decide⟩ changedFields)) values).down := by
  intro accepted
  obtain ⟨data, allowed, same⟩ :=
    (restrictedGuard_denote model GuardControls.full signature ⟨0, by decide⟩ condition _ values).mp accepted
  have images := (encode_denote model signature ⟨0, by decide⟩ changedFields values).symm.trans same
  have source := TypeTheory.FiniteConstructorEncoding.encode_injective _ _ images
  have dataEqual := eq_of_heq (Sigma.mk.inj source).2
  rw [← dataEqual] at allowed
  exact allowed

theorem false_condition_refuses (payload : ClosedTerm Constants (payloadType signature)) :
    ¬ (model.denote (restrictedGuard signature ⟨0, by decide⟩ impossibleCondition payload) values).down := by
  intro accepted
  obtain ⟨data, impossible, _⟩ :=
    (restrictedGuard_denote model GuardControls.full signature ⟨0, by decide⟩ impossibleCondition payload values).mp accepted
  exact impossible

#print axioms first_accepted
#print axioms changed_still_encoded
#print axioms changed_refused
#print axioms false_condition_refuses

end Mettapedia.Logic.HOL.FiniteConstructorEncoding.RestrictionControls
