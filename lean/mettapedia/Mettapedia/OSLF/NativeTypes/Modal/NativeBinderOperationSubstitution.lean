import Mettapedia.OSLF.NativeTypes.Modal.NativeRuleOccurrenceScope

/-!
# Ambient naturality of ordinary binder elimination

The existing binder operation is compared to simultaneous substitution,
including weakening beneath the eliminated variable. Reflection-specific
binder operations require their own earned comparison.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeBinderOperationSubstitution

open Mettapedia.OSLF.MeTTaIL Syntax Substitution

theorem single_after_shift (replacement body : Pattern) :
    ContextSubstitution.substitute (ContextSubstitution.single replacement)
      (liftBVars 0 1 body) = body := by
  rw [← NativeOccurrenceSubstitution.substitute_shift, ContextSubstitution.substitute_comp]
  have assignment : (fun index => ContextSubstitution.substitute
      (ContextSubstitution.single replacement) (NativeOccurrenceSubstitution.shift 0 1 index)) =
      Pattern.bvar := by
    funext index
    simp only [NativeOccurrenceSubstitution.shift, Nat.not_lt_zero, ite_false,
      ContextSubstitution.substitute, ContextSubstitution.single]
  rw [assignment, ContextSubstitution.substitute_id]

theorem ordinary (substitution : ContextSubstitution.Assignment) (replacement body : Pattern) :
    ContextSubstitution.substitute substitution (instantiateBVar replacement body) =
      instantiateBVar (ContextSubstitution.substitute substitution replacement)
        (ContextSubstitution.substitute (ContextSubstitution.lift 1 substitution) body) := by
  rw [← ContextSubstitution.substitute_single_eq_instantiateBVar,
    ← ContextSubstitution.substitute_single_eq_instantiateBVar,
    ContextSubstitution.substitute_comp, ContextSubstitution.substitute_comp]
  congr 1
  funext index
  cases index with
  | zero => rfl
  | succ index =>
      simp only [ContextSubstitution.single, ContextSubstitution.substitute,
        ContextSubstitution.lift, Nat.succ_lt_succ_iff, Nat.not_lt_zero, ite_false,
        Nat.add_sub_cancel]
      exact (single_after_shift (ContextSubstitution.substitute substitution replacement)
        (substitution index)).symm

end Mettapedia.OSLF.NativeTypes.Modal.NativeBinderOperationSubstitution
