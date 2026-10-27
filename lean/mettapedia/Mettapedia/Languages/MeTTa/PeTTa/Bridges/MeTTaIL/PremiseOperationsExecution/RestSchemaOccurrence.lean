import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.RestSchemaRuntime
import Mettapedia.GSLT.LanguageDef.TypedOccurrenceCoverage

/-! A completed native schema check supplies typed term and rest occurrences
through the existing source zipper. The enclosing context, capture typing and
executable occurrence depth remain tied to the same original schema. Language
formation and operational context permissions remain admission obligations. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.RestSchema

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding RestOccurrenceAddress DerivedContexts OccurrenceZipperAddress
open WellSorted RestAwareTyping

theorem interpreted_occurrence_typed (host : Effects.State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr) (pattern : Pattern) (expected : TypeExpr)
    (completed : ∃ fuel, Eval.run interpretedRuntime fuel
      {state := host, control := .evaluate [] (schemaCall language free bound pattern expected)} =
      .complete host [Effects.boolean true] [] [])
    {path : List Nat} {name : String} (observed : occurrenceAt? pattern path = some name) :
    ∃ binderPrefix, TypedOccurrenceAt language (FreeTypeContext.ofList free) bound pattern expected
      binderPrefix path name :=
  (interpreted_true_source_typed host language free bound pattern expected completed).occurrenceAt_typed observed

theorem interpreted_rest_site_typed (host : Effects.State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr) (pattern : Pattern) (expected : TypeExpr)
    (completed : ∃ fuel, Eval.run interpretedRuntime fuel
      {state := host, control := .evaluate [] (schemaCall language free bound pattern expected)} =
      .complete host [Effects.boolean true] [] [])
    {path : List Nat} {site : RestSite} (decoded : restSiteAt? pattern path = some site) :
    ∃ focusBound focusType binderPrefix elementType,
      RestAwareTyping.HasType language (FreeTypeContext.ofList free) focusBound site.focus focusType ∧
      TypedAt language (FreeTypeContext.ofList free) site.focus site.context bound expected focusBound focusType ∧
      FreeTypeContext.ofList free site.name = some (.collection site.kind elementType) ∧
      focusBound = binderPrefix ++ bound ∧
      binderPrefix.length = binderCount site.context ∧
      occurrenceDepthAt? pattern path 0 = some binderPrefix.length :=
  (interpreted_true_source_typed host language free bound pattern expected completed).restSiteAt_with_descent decoded

/-- Every address reached after the completed check keeps its full source
classification and the dependent capture-instantiation obligation. -/
theorem interpreted_occurrence_instantiation (host : Effects.State) (language : LanguageDef)
    (free : List (String × TypeExpr)) (bound : List TypeExpr) (pattern : Pattern) (expected : TypeExpr)
    (completed : ∃ fuel, Eval.run interpretedRuntime fuel
      {state := host, control := .evaluate [] (schemaCall language free bound pattern expected)} =
      .complete host [Effects.boolean true] [] [])
    {path : List Nat} {name : String} (observed : occurrenceAt? pattern path = some name) :
    ∃ binderPrefix,
      TypedOccurrenceAt language (FreeTypeContext.ofList free) bound pattern expected binderPrefix path name ∧
      ∀ (dependencies : List TypeExpr) (body : Pattern) (resultType : TypeExpr) (arguments : List Pattern),
        RestAwareTyping.HasType language (FreeTypeContext.ofList free) (dependencies ++ bound) body resultType →
        List.Forall₂ (fun argument dependency =>
          RestAwareTyping.HasType language (FreeTypeContext.ofList free) (binderPrefix ++ bound) argument dependency)
          arguments dependencies →
        ∃ instantiated,
          occurrenceDepthAt? pattern path 0 = some binderPrefix.length ∧
          instantiateValue? { dependencies, ambient := bound.length, body }
            bound.length binderPrefix.length arguments = some instantiated ∧
          RestAwareTyping.HasType language (FreeTypeContext.ofList free) (binderPrefix ++ bound) instantiated resultType := by
  obtain ⟨binderPrefix, typed⟩ := interpreted_occurrence_typed host language free bound pattern expected completed observed
  refine ⟨binderPrefix, typed, ?_⟩
  intro dependencies body resultType arguments bodyTyped argumentsTyped
  exact typed.instantiateCaptured bodyTyped argumentsTyped

#print axioms interpreted_occurrence_typed
#print axioms interpreted_rest_site_typed
#print axioms interpreted_occurrence_instantiation

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.RestSchema
