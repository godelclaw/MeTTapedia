import Mettapedia.OSLF.NativeTypes.Modal.NativeProviderSubstitution

/-!
# The dependent occurrence substitution square

An authored occurrence supplies its local dependency arguments before using
the remaining ambient variables. Substituting the ambient context below the
dependency prefix commutes with that exact occurrence interpretation. Local
arguments are independently scoped in the local binder prefix.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeOccurrenceSubstitution

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding

def shift (cutoff amount : Nat) : ContextSubstitution.Assignment :=
  fun index => if index < cutoff then .bvar index else .bvar (index + amount)

theorem lift_shift (arity cutoff amount : Nat) :
    ContextSubstitution.lift arity (shift cutoff amount) = shift (cutoff + arity) amount := by
  funext index
  by_cases fresh : index < arity
  · have within : index < cutoff + arity := by omega
    simp only [ContextSubstitution.lift, shift, fresh, within, ite_true]
  · by_cases earlier : index - arity < cutoff
    · have within : index < cutoff + arity := by omega
      simp only [ContextSubstitution.lift, shift, fresh, earlier, within, ite_false, ite_true,
        Substitution.liftBVars, Nat.zero_le]
      congr 1
      omega
    · have outside : ¬ index < cutoff + arity := by omega
      simp only [ContextSubstitution.lift, shift, fresh, earlier, outside, ite_false,
        Substitution.liftBVars, Nat.zero_le, ite_true]
      congr 1
      omega

theorem substitute_shift (cutoff amount : Nat) (pattern : Pattern) :
    ContextSubstitution.substitute (shift cutoff amount) pattern =
      Substitution.liftBVars cutoff amount pattern := by
  induction pattern using Pattern.inductionOn generalizing cutoff with
  | hbvar index =>
      simp only [ContextSubstitution.substitute, shift, Substitution.liftBVars]
      split <;> split <;> first | rfl | omega
  | hfvar name => rfl
  | happly constructor arguments ih =>
      simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map,
        Substitution.liftBVars, Substitution.liftBVarsList_eq_map]
      exact congrArg (Pattern.apply constructor) (List.map_congr_left fun item member => ih item member cutoff)
  | hlambda binder body ih =>
      simp only [ContextSubstitution.substitute, Substitution.liftBVars, lift_shift, ih]
  | hmultiLambda arity binders body ih =>
      simp only [ContextSubstitution.substitute, Substitution.liftBVars, lift_shift, ih]
  | hsubst body replacement ihBody ihReplacement =>
      simp only [ContextSubstitution.substitute, Substitution.liftBVars, lift_shift, ihBody, ihReplacement]
  | hcollection kind elements rest ih =>
      simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map,
        Substitution.liftBVars, Substitution.liftBVarsList_eq_map]
      exact congrArg (fun values => Pattern.collection kind values rest)
        (List.map_congr_left fun item member => ih item member cutoff)

theorem occurrence_shift (dependencies depth : Nat) (arguments : List Pattern) (body : Pattern) :
    ContextSubstitution.substitute (occurrenceAssignment dependencies depth arguments)
      (Substitution.liftBVars 0 dependencies body) = Substitution.liftBVars 0 depth body := by
  rw [← substitute_shift, ContextSubstitution.substitute_comp]
  have assignments :
      (fun index => ContextSubstitution.substitute (occurrenceAssignment dependencies depth arguments)
        (shift 0 dependencies index)) = shift 0 depth := by
    funext index
    simp only [shift, Nat.not_lt_zero, ite_false, ContextSubstitution.substitute, occurrenceAssignment]
    have beyond : ¬ index + dependencies < dependencies := by omega
    simp only [beyond, ite_false]
    congr 1
    omega
  rw [assignments, substitute_shift]

theorem occurrence_square {dependencies depth : Nat} {arguments : List Pattern}
    (arity : arguments.length = dependencies)
    (localScopes : ∀ argument ∈ arguments, argument.isWellScopedAt depth = true)
    (substitution : ContextSubstitution.Assignment) :
    (fun index => ContextSubstitution.substitute (ContextSubstitution.lift depth substitution)
      (occurrenceAssignment dependencies depth arguments index)) =
      (fun index => ContextSubstitution.substitute (occurrenceAssignment dependencies depth arguments)
        (ContextSubstitution.lift dependencies substitution index)) := by
  funext index
  by_cases dependency : index < dependencies
  · have inArguments : index < arguments.length := by omega
    have scope : (arguments.getD index (.bvar 0)).isWellScopedAt depth = true := by
      simpa only [List.getD_eq_getElem arguments (.bvar 0) inArguments] using
        localScopes (arguments[index]'inArguments) (List.getElem_mem inArguments)
    simp only [occurrenceAssignment, ContextSubstitution.lift, dependency, ite_true,
      ContextSubstitution.substitute]
    apply NativeProviderSubstitution.substitute_fixed scope
    intro binder within
    simp only [ContextSubstitution.lift, within, ite_true]
  · have ambient : ¬ depth + (index - dependencies) < depth := by omega
    simp only [occurrenceAssignment, ContextSubstitution.lift, dependency, ite_false,
      ContextSubstitution.substitute, ambient]
    simp only [show depth + (index - dependencies) - depth = index - dependencies by omega]
    exact (occurrence_shift dependencies depth arguments (substitution (index - dependencies))).symm

theorem interpreted_body_square {dependencies depth : Nat} {arguments : List Pattern}
    (arity : arguments.length = dependencies)
    (localScopes : ∀ argument ∈ arguments, argument.isWellScopedAt depth = true)
    (substitution : ContextSubstitution.Assignment) (body : Pattern) :
    ContextSubstitution.substitute (ContextSubstitution.lift depth substitution)
      (ContextSubstitution.substitute (occurrenceAssignment dependencies depth arguments) body) =
      ContextSubstitution.substitute (occurrenceAssignment dependencies depth arguments)
        (ContextSubstitution.substitute (ContextSubstitution.lift dependencies substitution) body) := by
  rw [ContextSubstitution.substitute_comp, ContextSubstitution.substitute_comp,
    occurrence_square arity localScopes substitution]

end Mettapedia.OSLF.NativeTypes.Modal.NativeOccurrenceSubstitution
