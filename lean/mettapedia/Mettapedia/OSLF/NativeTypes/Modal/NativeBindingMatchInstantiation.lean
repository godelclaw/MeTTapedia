import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingAlphaReadout
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatch

/-!
# Authored matching reconstructs the alpha source tree

This comparison covers ordinary constructor/binder templates at every
ambient context and every scoped occurrence. Original display labels are
retained in instantiation; their erasure agrees with the matched source.
Extensions of the completed assignment preserve that comparison.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeBindingMatchInstantiation

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralScopedMatch

mutual
  def treeSchema : Pattern → Bool
    | .fvar _ | .bvar _ => true
    | .apply _ arguments => treeSchemas arguments
    | .lambda _ body | .multiLambda _ _ body => treeSchema body
    | _ => false
  def treeSchemas : List Pattern → Bool
    | [] => true
    | head :: tail => treeSchema head && treeSchemas tail
end

mutual
  theorem matching_reconstructs {operation : Pattern → Pattern → Pattern}
      {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat} {site : RulePatternSite}
      {path : List Nat} {depth : Nat} {initial final completed : Assignment} {pattern target : Pattern}
      (matched : Matches rule spec ambient site path depth initial pattern target final)
      (shape : treeSchema pattern = true) (extension : Extends final completed) :
      ∃ instantiatedSource, instantiateWith? operation rule spec ambient site path depth completed pattern = some instantiatedSource ∧
        instantiatedSource.eraseBinderMetadata = target.eraseBinderMetadata := by
    cases matched with
    | capture captured =>
        obtain ⟨dependencies, arguments, value, _, occurrence, _, looked, instantiated, _⟩ :=
          capture_interpretation captured
        exact ⟨_, by simp only [instantiateWith?, extension _ _ looked, occurrence]; exact instantiated, rfl⟩
    | bound => exact ⟨_, by simp only [instantiateWith?], rfl⟩
    | constructor arguments =>
        rename_i label patterns targets
        obtain ⟨results, instantiated, erased⟩ := arguments_reconstructs (operation := operation) arguments shape extension
        exact ⟨.apply label results, by simp only [instantiateWith?, instantiated]; rfl,
          by simpa only [Pattern.eraseBinderMetadata] using congrArg (Pattern.apply label) erased⟩
    | binder body =>
        rename_i display actualDisplay pattern target
        obtain ⟨result, instantiated, erased⟩ := matching_reconstructs (operation := operation) body shape extension
        exact ⟨.lambda display result, by simp only [instantiateWith?, instantiated]; rfl,
          by simpa only [Pattern.eraseBinderMetadata] using congrArg (Pattern.lambda none) erased⟩
    | binders body =>
        rename_i arity display actualDisplay pattern target
        obtain ⟨result, instantiated, erased⟩ := matching_reconstructs (operation := operation) body shape extension
        exact ⟨.multiLambda arity display result, by simp only [instantiateWith?, instantiated]; rfl,
          by simpa only [Pattern.eraseBinderMetadata] using congrArg (Pattern.multiLambda arity []) erased⟩
    | substitution | bag | vector | vectorRest => cases shape
  termination_by sizeOf pattern

  theorem arguments_reconstructs {operation : Pattern → Pattern → Pattern}
      {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat} {site : RulePatternSite}
      {path : List Nat} {depth index : Nat} {initial final completed : Assignment}
      {patterns targets : List Pattern}
      (matched : Arguments rule spec ambient site path depth initial index patterns targets final)
      (shape : treeSchemas patterns = true) (extension : Extends final completed) :
      ∃ results, instantiateArgsWith? operation rule spec ambient site path depth completed index patterns = some results ∧
        results.map Pattern.eraseBinderMetadata = targets.map Pattern.eraseBinderMetadata := by
    cases matched with
    | nil => exact ⟨[], by simp only [instantiateArgsWith?], rfl⟩
    | cons head tail =>
        have shapes := shape
        simp only [treeSchemas, Bool.and_eq_true] at shapes
        obtain ⟨result, first, erasedFirst⟩ := matching_reconstructs (operation := operation) head shapes.1
          (tail.extends.trans extension)
        obtain ⟨results, rest, erasedRest⟩ := arguments_reconstructs (operation := operation) tail shapes.2 extension
        refine ⟨result :: results, ?_, ?_⟩
        · simp only [instantiateArgsWith?, first, rest]
          rfl
        · simp only [List.map_cons, erasedFirst, erasedRest]
  termination_by sizeOf patterns
end

end Mettapedia.OSLF.NativeTypes.Modal.NativeBindingMatchInstantiation
