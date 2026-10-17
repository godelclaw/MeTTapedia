import Mettapedia.GSLT.LanguageDef.ContextSupport
import Mettapedia.OSLF.MeTTaIL.ContextSubstitution

/-!
# Comparing named parameter and ambient context substitution

A locally scoped Pattern may abstract selected named parameters into ambient
de Bruijn references. Reopening those references agrees with assigning their
images directly, while fixing existing local binders and retaining unassigned
matcher variables. Both actions are the existing structural substitutions.
This comparison does not execute explicit substitutions or match queries.
-/

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.GSLT.LanguageDef

namespace Mettapedia.GSLT.LanguageDef.ContextSupport

/-- Opening an ambient-variable abstraction agrees with direct named
assignment. Existing local binders are preserved, and unassigned matcher
variables remain free. -/
theorem ambient_substitute_named (assignment : Assignment)
    (ambient : Mettapedia.OSLF.MeTTaIL.ContextSubstitution.Assignment)
    (depth : Nat) (pattern : Pattern)
    (wellScoped : pattern.isWellScopedAt depth = true) :
    Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
        (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift depth ambient)
        (substituteAt (fun _ => []) assignment depth pattern) =
      substituteAt (fun _ => [])
        (fun name => Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute ambient
          (assignment name)) depth pattern := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index =>
    have localBound : index < depth := of_decide_eq_true wellScoped
    simp [substituteAt, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute,
      Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift, localBound]
  | hfvar name =>
    simp only [substituteAt, List.length_nil, Nat.sub_zero]
    simpa only [Nat.zero_add,
      Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift_zero] using
      Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute_liftBVars ambient
        (assignment name) 0 depth
  | happly constructor arguments ih =>
    simp only [substituteAt,
      Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute,
      Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substituteList_eq_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro argument member
    exact ih argument member depth ((Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff _ _).mp wellScoped _ member)
  | hlambda name body ih =>
    simp only [substituteAt,
      Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute,
      Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift_lift]
    exact congrArg (Pattern.lambda name) (ih (depth + 1) wellScoped)
  | hmultiLambda arity names body ih =>
    simp only [substituteAt,
      Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute,
      Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift_lift]
    exact congrArg (Pattern.multiLambda arity names) (ih (depth + arity) wellScoped)
  | hsubst body replacement ihBody ihReplacement =>
    simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at wellScoped
    simp only [substituteAt,
      Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute,
      Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift_lift]
    exact congrArg₂ Pattern.subst (ihBody (depth + 1) wellScoped.1)
      (ihReplacement depth wellScoped.2)
  | hcollection kind elements rest ih =>
    simp only [substituteAt,
      Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute,
      Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substituteList_eq_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro element member
    exact ih element member depth ((Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff _ _).mp wellScoped _ member)

end Mettapedia.GSLT.LanguageDef.ContextSupport
