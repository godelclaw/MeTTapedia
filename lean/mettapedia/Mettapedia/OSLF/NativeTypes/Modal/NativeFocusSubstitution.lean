import Mettapedia.OSLF.NativeTypes.Modal.Instantiation
import Mettapedia.OSLF.NativeTypes.Modal.NativeRuleInstantiationSubstitution

/-!
# Authored scoped focus witnesses respect contextual substitution

The focus follows the authored pattern and its exact occurrence depth.
Binding, explicit substitution and collection matching do not justify
replacing that evidence with a raw target-tree address.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeFocusSubstitution

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching ScopedPattern
open Instantiation

/-- Count binders at every actual authored focus, including constructor
heads. Metavariable occurrence-depth lookup serves a narrower purpose. -/
def depthAt? : Pattern → List Nat → Nat → Option Nat
  | _, [], depth => some depth
  | .apply _ arguments, index :: rest, depth =>
      arguments[index]?.bind (fun argument => depthAt? argument rest depth)
  | .lambda _ body, 0 :: rest, depth => depthAt? body rest (depth + 1)
  | .multiLambda count _ body, 0 :: rest, depth => depthAt? body rest (depth + count)
  | .subst body _, 0 :: rest, depth => depthAt? body rest (depth + 1)
  | .subst _ replacement, 1 :: rest, depth => depthAt? replacement rest depth
  | .collection _ elements _, index :: rest, depth =>
      elements[index]?.bind (fun element => depthAt? element rest depth)
  | _, _ :: _, _ => none

theorem focus_substitutes {rule : RewriteRule} {spec : RuleBindingSpec}
    {source target depth focusDepth : Nat} {site : RulePatternSite} {path : List Nat}
    {initial : Assignment} {pattern actual : Pattern} {position : List Nat}
    (selected : FocusInstance Substitution.instantiateBVar rule spec source site initial
      path depth pattern position actual)
    (located : depthAt? pattern position depth = some focusDepth)
    (admitted : admittedFor rule spec = true)
    (coherent : DepthCoherent rule site path depth pattern)
    (scopes : pattern.isWellScopedAt depth = true)
    (substitution : ContextSubstitution.Assignment)
    (boundScoped : ContextSubstitution.WellScopedAssignment source target substitution) :
    FocusInstance Substitution.instantiateBVar rule spec target site
      (NativeContextualSubstitution.assignment target substitution initial)
      path depth pattern position
      (ContextSubstitution.substitute (ContextSubstitution.lift focusDepth substitution) actual) := by
  induction selected generalizing focusDepth with
  | @here path depth pattern actual interpreted =>
      have same : depth = focusDepth := by
        simpa only [depthAt?, Option.some.injEq] using located
      subst focusDepth
      exact .here (NativeRuleInstantiationSubstitution.successful_substitutes
        interpreted admitted coherent scopes substitution boundScoped)
  | @application path depth constructor arguments index argument actual rest found selected ih =>
      have localScope : argument.isWellScopedAt depth = true :=
        (isWellScopedListAt_eq_true_iff _ _).mp scopes argument (List.mem_of_getElem? found)
      have inside : depthAt? argument rest depth = some focusDepth := by
        simpa only [depthAt?, found, Option.bind_some] using located
      exact .application found (ih inside (coherent.constructorChild found) localScope)
  | @lambda path depth binder body actual rest selected ih =>
      have inside : depthAt? _ _ (depth + 1) = some focusDepth := located
      exact .lambda (ih inside coherent.lambda scopes)
  | @multiLambda path depth arity binders body actual rest selected ih =>
      have inside : depthAt? _ _ (depth + _) = some focusDepth := located
      exact .multiLambda (ih inside coherent.multiLambda scopes)
  | substitutionBody selected ih =>
      simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at scopes
      exact .substitutionBody (ih located coherent.substitutionBody scopes.1)
  | substitutionArgument selected ih =>
      simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at scopes
      exact .substitutionArgument (ih located coherent.substitutionReplacement scopes.2)
  | @collection path depth kind elements residual index element actual rest found selected ih =>
      have localScope : element.isWellScopedAt depth = true :=
        (isWellScopedListAt_eq_true_iff _ _).mp scopes element (List.mem_of_getElem? found)
      have inside : depthAt? element rest depth = some focusDepth := by
        simpa only [depthAt?, found, Option.bind_some] using located
      exact .collection found (ih inside (coherent.collectionChild found) localScope)

end Mettapedia.OSLF.NativeTypes.Modal.NativeFocusSubstitution
