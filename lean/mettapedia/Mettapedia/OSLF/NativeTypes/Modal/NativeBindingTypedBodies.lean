import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingScopedBodies

/-!
# Actual typed source values opened into the generated binding clone

Canonical typed inhabitants of a base-domain arrow spine have exact source
bodies below its reversed binder context. The comparison retains the entire
source value and is compatible with ambient capture-avoiding substitution.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeBindingTypedBodies

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.NativeTypes.Generation
open CurriedBindingLanguage BindingSemanticAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted

variable {language : LanguageDef}

abbrev TypedSource (context : List String) (type : TypeExpr) :=
  {pattern : Pattern | HasType language FreeTypeContext.empty
    (Mettapedia.GSLT.Poly.BindingLanguage.typeContext context) pattern type ∧
    isObjectPattern pattern = true ∧ pattern.hasCanonicalBinderMetadata = true}

theorem wrap_injective (domains : List String) : Function.Injective (wrap domains) := by
  induction domains with
  | nil => exact fun _ _ same => same
  | cons domain domains ih =>
      intro left right same
      exact ih (Pattern.lambda.inj same).2

theorem substitute_wrap (domains : List String) (assignment : ContextSubstitution.Assignment)
    (body : Pattern) :
    ContextSubstitution.substitute assignment (wrap domains body) =
      wrap domains (ContextSubstitution.substitute
        (ContextSubstitution.lift domains.length assignment) body) := by
  have same : wrap domains = PatternRendering.wrapBinders domains := by
    funext pattern
    induction domains with
    | nil => rfl
    | cons domain domains ih => exact congrArg (Pattern.lambda none) ih
  rw [same]
  exact PatternRendering.substitute_wrapBinders domains assignment body

theorem exists_body (admitted : Admitted language)
    (labels : (language.terms.map (·.label)).Nodup)
    {type : TypeExpr} {domains : List String} {result : String}
    (spine : BinderSpine type domains result) {context : List String}
    (source : TypedSource (language := language) context type) :
    ∃ body : Term (signature language) (domains.reverse ++ context) result,
      wrap domains (toPattern body) = source.val := by
  obtain ⟨raw, printed, typed, object, canonical, _⟩ :=
    unwrap_typed spine context source.val source.property.1 source.property.2.1 source.property.2.2
  let bodySource : Source language (domains.reverse ++ context) result :=
    ⟨raw, typed, object, canonical⟩
  refine ⟨(sourceEquiv admitted labels _ _).symm bodySource, ?_⟩
  have decoded := congrArg Subtype.val ((sourceEquiv admitted labels _ _).apply_symm_apply bodySource)
  exact (congrArg (wrap domains) decoded).trans printed.symm

noncomputable def body (admitted : Admitted language)
    (labels : (language.terms.map (·.label)).Nodup)
    {type : TypeExpr} {domains : List String} {result : String}
    (spine : BinderSpine type domains result) {context : List String}
    (source : TypedSource (language := language) context type) :
    Term (signature language) (domains.reverse ++ context) result :=
  Classical.choose (exists_body admitted labels spine source)

theorem body_read (admitted : Admitted language)
    (labels : (language.terms.map (·.label)).Nodup)
    {type : TypeExpr} {domains : List String} {result : String}
    (spine : BinderSpine type domains result) {context : List String}
    (source : TypedSource (language := language) context type) :
    wrap domains (toPattern (body admitted labels spine source)) = source.val :=
  Classical.choose_spec (exists_body admitted labels spine source)

/-- Every exact contextual substitution of a typed source value decodes to
the original clone substitution under precisely its local arrow binders. -/
theorem body_substitution (admitted : Admitted language)
    (labels : (language.terms.map (·.label)).Nodup)
    {type : TypeExpr} {domains : List String} {result : String}
    (spine : BinderSpine type domains result) {source target : List String}
    (substitution : Sub (signature language) source target)
    (before : TypedSource (language := language) source type)
    (after : TypedSource (language := language) target type)
    (read : after.val = ContextSubstitution.substitute
      (NativeBindingRendering.assignment substitution) before.val) :
    body admitted labels spine after =
      Binding.bind (liftSub substitution domains.reverse) (body admitted labels spine before) := by
  apply toPattern_injective labels
  apply wrap_injective domains
  calc
    wrap domains (toPattern (body admitted labels spine after)) = after.val :=
      body_read admitted labels spine after
    _ = ContextSubstitution.substitute (NativeBindingRendering.assignment substitution) before.val := read
    _ = ContextSubstitution.substitute (NativeBindingRendering.assignment substitution)
        (wrap domains (toPattern (body admitted labels spine before))) :=
      congrArg (ContextSubstitution.substitute _) (body_read admitted labels spine before).symm
    _ = wrap domains (ContextSubstitution.substitute
        (ContextSubstitution.lift domains.length (NativeBindingRendering.assignment substitution))
        (toPattern (body admitted labels spine before))) := substitute_wrap _ _ _
    _ = wrap domains (toPattern (Binding.bind (liftSub substitution domains.reverse)
        (body admitted labels spine before))) := by
      exact congrArg (wrap domains)
        (by simpa only [List.length_reverse] using
          (NativeBindingScopedBodies.print_scoped_substitution substitution domains.reverse
            (body admitted labels spine before)).symm)

end Mettapedia.OSLF.NativeTypes.Modal.NativeBindingTypedBodies
